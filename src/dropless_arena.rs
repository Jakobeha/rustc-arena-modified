use std::alloc::Layout;
use std::cell::{Cell, RefCell};
use std::cmp::max;
use std::mem::{needs_drop, size_of};
use std::ptr::{null_mut, write};
use std::slice::from_raw_parts_mut;

use smallvec::SmallVec;

use crate::{HUGE_PAGE, PAGE, PtrUnstables};
use crate::arena_chunk::ArenaChunk;

/// An arena that can hold objects of multiple different types that impl `Copy`
/// and/or satisfy `!mem::needs_drop`.
pub struct DroplessArena {
    /// A pointer to the start of the free space.
    start: Cell<*mut u8>,
    /// A pointer to the end of free space.
    ///
    /// The allocation proceeds downwards from the end of the chunk towards the
    /// start. (This is slightly simpler and faster than allocating upwards,
    /// see <https://fitzgeraldnick.com/2019/11/01/always-bump-downwards.html>.)
    /// When this pointer crosses the start pointer, a new chunk is allocated.
    end: Cell<*mut u8>,
    /// A vector of arena chunks.
    chunks: RefCell<Vec<ArenaChunk>>,
}

impl DroplessArena {
    /// Create a new, empty arena
    #[inline]
    fn new() -> DroplessArena {
        DroplessArena {
            start: Cell::new(null_mut()),
            end: Cell::new(null_mut()),
            chunks: Default::default(),
        }
    }

    /// Allocates a raw region of data
    #[inline]
    pub fn alloc_raw(&self, layout: Layout) -> *mut u8 {
        assert_ne!(layout.size(), 0);
        loop {
            if let Some(a) = self.alloc_raw_without_grow(layout) {
                break a;
            }
            // No free space left. Allocate a new chunk to satisfy the request.
            // On failure the grow will panic or abort.
            self.grow(layout.size());
        }
    }

    /// Allocates an object which doesn't need to be dropped.
    ///
    /// *Panics* if given a type with drop code. This method's signature looks like it can allocate
    /// any object, but it asserts ![needs_drop] at runtime.
    #[inline]
    pub fn alloc<T>(&self, object: T) -> &mut T {
        assert!(!needs_drop::<T>());

        let mem = self.alloc_raw(Layout::for_value::<T>(&object)) as *mut T;

        unsafe {
            // Write into uninitialized memory.
            write(mem, object);
            &mut *mem
        }
    }

    /// Allocates an iterator of objects which don't need to be dropped.
    ///
    /// *Panics* if you try to allocate ZSTs. Additionally, like with [Self::alloc], this *panics*
    /// if you allocate an object with drop code.
    #[inline]
    pub fn alloc_from_iter<T, I: IntoIterator<Item = T>>(&self, iter: I) -> &mut [T] {
        let iter = iter.into_iter();
        assert_ne!(size_of::<T>(), 0);
        assert!(!needs_drop::<T>());

        let size_hint = iter.size_hint();

        match size_hint {
            (min, Some(max)) if min == max => {
                // We know the exact number of elements the iterator will produce here
                let len = min;

                if len == 0 {
                    return &mut [];
                }

                let mem = self.alloc_raw(Layout::array::<T>(len).unwrap()) as *mut T;
                unsafe { self.write_from_iter(iter, len, mem) }
            }
            (_, _) => {
                crate::cold_path(move || -> &mut [T] {
                    let mut vec: SmallVec<[_; 8]> = iter.collect();
                    if vec.is_empty() {
                        return &mut [];
                    }
                    // Move the content to the arena by copying it and then forgetting
                    // the content of the SmallVec
                    unsafe {
                        let len = vec.len();
                        let start_ptr =
                            self.alloc_raw(Layout::for_value::<[T]>(vec.as_slice())) as *mut T;
                        vec.as_ptr().copy_to_nonoverlapping(start_ptr, len);
                        vec.set_len(0);
                        from_raw_parts_mut(start_ptr, len)
                    }
                })
            }
        }
    }

    /// Allocates a slice of objects that are copied into the `DroplessArena`, returning a mutable
    /// reference to it.
    ///
    /// This will *panic* if passed a zero-sized type or empty slice. Like [Self::alloc], it can't
    /// be given a type with drop code, but the `T: Copy` trait checks this at compile time.
    #[inline]
    pub fn alloc_slice<T: Copy>(&self, slice: &[T]) -> &mut [T] {
        assert_ne!(size_of::<T>(), 0);
        assert!(!slice.is_empty());

        let mem = self.alloc_raw(Layout::for_value::<[T]>(slice)) as *mut T;

        unsafe {
            mem.copy_from_nonoverlapping(slice.as_ptr(), slice.len());
            from_raw_parts_mut(mem, slice.len())
        }
    }

    #[inline]
    unsafe fn write_from_iter<T, I: Iterator<Item = T>>(
        &self,
        mut iter: I,
        len: usize,
        mem: *mut T,
    ) -> &mut [T] {
        let mut i = 0;
        // Use a manual loop since LLVM manages to optimize it better for
        // slice iterators
        loop {
            let value = iter.next();
            if i >= len || value.is_none() {
                // We only return as many items as the iterator gave us, even
                // though it was supposed to give us `len`
                return from_raw_parts_mut(mem, i);
            }
            write(mem.add(i), value.unwrap());
            i += 1;
        }
    }

    /// Allocates a byte slice with specified layout from the current memory
    /// chunk. Returns `None` if there is no free space left to satisfy the
    /// request.
    #[inline]
    fn alloc_raw_without_grow(&self, layout: Layout) -> Option<*mut u8> {
        let start = self.start.get().addr_();
        let old_end = self.end.get();
        let end = old_end.addr_();

        let align = layout.align();
        let bytes = layout.size();

        let new_end = end.checked_sub(bytes)? & !(align - 1);
        if start <= new_end {
            let new_end = old_end.with_addr_(new_end);
            self.end.set(new_end);
            Some(new_end)
        } else {
            None
        }
    }

    #[inline(never)]
    #[cold]
    fn grow(&self, additional: usize) {
        unsafe {
            let mut chunks = self.chunks.borrow_mut();
            let mut new_cap;
            if let Some(last_chunk) = chunks.last_mut() {
                // There is no need to update `last_chunk.entries` because that
                // field isn't used by `DroplessArena`.

                // If the previous chunk's capacity is less than HUGE_PAGE
                // bytes, then this chunk will be least double the previous
                // chunk's size.
                new_cap = last_chunk.capacity.min(HUGE_PAGE / 2);
                new_cap *= 2;
            } else {
                new_cap = PAGE;
            }
            // Also ensure that this chunk can fit `additional`.
            new_cap = max(additional, new_cap);

            let mut chunk = ArenaChunk::new(new_cap);
            self.start.set(chunk.storage);
            self.end.set(chunk.end());
            chunks.push(chunk);
        }
    }
}

// We can't write a good `Debug` impl for `DroplessArena` because its chunks are full of
// uninitialized memory (between alignment and their entries aren't accurate). We could only report
// the capacity, but at that point it's not worth it. `TypedArena` has a good `Debug` impl because
// we actually support iterating its memory.

impl Default for DroplessArena {
    /// Create a new, empty arena
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Send for DroplessArena {}
