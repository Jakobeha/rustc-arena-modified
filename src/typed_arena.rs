use std::cell::{Cell, RefCell};
use std::cmp::max;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use std::mem::{forget, size_of, transmute};
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::ptr::{drop_in_place, null_mut, write, NonNull};
use std::slice::{from_raw_parts, from_raw_parts_mut};

use smallvec::SmallVec;

use crate::arena_chunk::ArenaChunk;
use crate::{PtrUnstables, HUGE_PAGE, PAGE};

#[cfg(test)]
mod tests;

/// An arena that can hold objects of only one type, allocations return shared references, and can
/// iterate behind a shared reference
pub type TypedArena<T> = TypedArenaGen<T, Shared>;

/// An arena that can hold objects of only one type, allocations return mutable references, and can
/// only iterate behind a mutable reference
pub type TypedArenaMut<T> = TypedArenaGen<T, Mutable>;

/// An arena that can hold objects of only one type. `RM` determines whether the references
/// returned from allocation are mutable and whether iteration requires a mutable reference; either
/// mutating returned references or iterating via immutable reference are possible, but not both.
pub struct TypedArenaGen<T, RM: RefMutability> {
    /// The number of inserted entries
    len: Cell<usize>,
    /// A pointer to the next object to be allocated.
    ptr: Cell<*mut T>,
    /// A pointer to the end of the allocated area. When this pointer is
    /// reached, a new chunk is allocated.
    end: Cell<*mut T>,
    /// A vector of arena chunks.
    chunks: RefCell<Vec<ArenaChunk<T>>>,
    /// The # of chunks actually used by the arena. The rest were allocated but are now empty,
    /// and we will try to re-use them before allocating a new chunk.
    used_chunks: Cell<usize>,
    /// Marker indicating that dropping the arena causes its owned
    /// instances of `T` to be dropped.
    _own: PhantomData<T>,
    /// RM is a phantom type parameter so we need this
    _rm: PhantomData<RM>,
}

/// Iterates all elements in an arena, and can handle new elements being allocated during iteration.
pub type Iter<'a, T> = IterGen<'a, T, Shared>;

/// Iterates all elements in an arena.
pub type IterMut<'a, T> = IterGen<'a, T, Mutable>;

/// Iterates all elements in an arena, and if [Shared], can handle new elements being allocated
/// during iteration.
pub struct IterGen<'a, T, RM: RefMutability>(PtrIter<'a, T>, PhantomData<RM>);

/// Iterates pointers to all elements in the arena, and (if shared) can handle new elements being
/// allocated during iteration.
pub struct PtrIter<'a, T> {
    /// The arena being iterated. The actual `RM` is irrelevant, we put [Shared] because we only use
    /// it like that and there may be other active references, but it may be `transmute`d.
    arena: &'a TypedArena<T>,
    /// Index of the current chunk being iterated
    chunk_index: usize,
    /// Pointer to the next entry in the current chunk being iterated
    chunk_data: NonNull<T>,
    /// Entries remaining in the current chunk being iterated, **except** like [ArenaChunk], if we
    /// are iterating the last chunk, this will be 0 (unset) even though we have more entries
    chunk_remaining_entries: usize,
    /// Index in the arena of the current element being iterated
    element_index: usize,
}

/// An iterable which can be allocated faster into the arena than the default [IntoIterator]
/// implementation, using [TypedArenaGen::alloc_raw_slice].
///
/// `rustc_arena` uses default implementations, but those are unstable, so instead you will need to
/// call [TypedArenaGen::alloc_from_iter_fast] manually. Unlike `rustc_arena` you can implement this on
/// your own collections, although they will probably just delegate to one of builtin
/// implementations; and often, simply using [TypedArenaGen::alloc_from_iter_reg] will as fast or fast
/// enough, and you won't need a custom implementation at all.
pub trait IterWithFastAlloc<T> {
    fn alloc_into<RM: RefMutability>(self, arena: &TypedArenaGen<T, RM>) -> RM::SliceRef<'_, T>;
}

/// Whether references to allocated objects are mutable, and iteration requires a mutable reference.
pub trait RefMutability: private::Sealed + 'static {
    /// `&T` or `&mut T`
    type Ref<'a, T>
    where
        T: 'a;
    /// `&[T]` or `&mut T`
    type SliceRef<'a, T>
    where
        T: 'a;

    /// Reference to the empty slice
    fn empty<'a, T>() -> Self::SliceRef<'a, T>;
    /// Dereference a pointer
    ///
    /// # Safety
    /// The pointer must be valid: see [pointer::as_ref] and [pointer::as_mut]'s requirements (the
    /// latter's are required if `Self` is [Mutable])
    ///
    /// [pointer::as_ref]: https://doc.rust-lang.org/std/primitive.pointer.html#method.as_ref
    /// [pointer::as_mut]: https://doc.rust-lang.org/std/primitive.pointer.html#method.as_mut
    unsafe fn from_ptr<'a, T>(t: *mut T) -> Self::Ref<'a, T>;
    /// Dereference a pointer and add length metadata to make it a slice reference
    ///
    /// # Safety
    /// The pointer must be valid: see [pointer::as_ref] and [pointer::as_mut]'s requirements (the
    /// latter's are required if `Self` is [Mutable]). Additionally, you must follow the
    /// requirements of [from_raw_parts] or [from_raw_parts_mut]
    ///
    /// [pointer::as_ref]: https://doc.rust-lang.org/std/primitive.pointer.html#method.as_ref
    /// [pointer::as_mut]: https://doc.rust-lang.org/std/primitive.pointer.html#method.as_mut
    unsafe fn from_raw_parts<'a, T>(t: *mut T, len: usize) -> Self::SliceRef<'a, T>;
    /// Convert a reference of this type into a shared reference
    #[allow(clippy::wrong_self_convention)]
    fn as_ref<T>(t: Self::Ref<'_, T>) -> &T;
    /// Convert a reference of this slice type into a shared reference
    #[allow(clippy::wrong_self_convention)]
    fn as_slice_ref<T>(t: Self::SliceRef<'_, T>) -> &[T];

    /// Dereference a non-null pointer
    ///
    /// # Safety
    /// The pointer must be valid: see [NonNull::as_ref] and [NonNull::as_mut]'s requirements (the
    /// latter's are required if `Self` is [Mutable])
    #[inline]
    unsafe fn from_non_null<'a, T>(t: NonNull<T>) -> Self::Ref<'a, T> {
        Self::from_ptr(t.as_ptr())
    }
}

pub enum Shared {}
pub enum Mutable {}

impl<T, RM: RefMutability> Default for TypedArenaGen<T, RM> {
    /// Creates a new, empty arena
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T, RM: RefMutability> TypedArenaGen<T, RM> {
    /// Creates a new, empty arena
    #[inline]
    pub fn new() -> Self {
        Self {
            len: Cell::new(0),
            // We set both `ptr` and `end` to 0 so that the first call to
            // alloc() will trigger a grow().
            ptr: Cell::new(null_mut()),
            end: Cell::new(null_mut()),
            chunks: Default::default(),
            used_chunks: Cell::new(0),
            _own: PhantomData,
            _rm: PhantomData,
        }
    }

    /// Allocates an object in the `TypedArena`, returning a reference to it.
    ///
    /// If the type parameter `RM` is [Shared] we return a shared reference. If `RM` is [Mutable] we
    /// return a mutable reference.
    #[inline]
    pub fn alloc(&self, object: T) -> RM::Ref<'_, T> {
        self.len.set(self.len.get() + 1);
        if size_of::<T>() == 0 {
            // We don't actually allocate ZSTs, just prevent them from being dropped and return a
            // reference to random data (this is a valid ZST reference).
            unsafe {
                let ptr = NonNull::<T>::dangling().as_ptr();
                // This `write` is equivalent to `forget`
                write(ptr, object);
                return RM::from_ptr(ptr);
            }
        }

        if self.ptr == self.end {
            self.grow(1)
        }

        unsafe {
            let ptr = self.ptr.get();
            // Advance the pointer.
            self.ptr.set(self.ptr.get().add(1));
            // Write into uninitialized memory.
            write(ptr, object);
            RM::from_ptr(ptr)
        }
    }

    /// Allocates multiple objects in a contiguous slice, returning a reference to the slice.
    ///
    /// If the type parameter `RM` is [Shared] we return a shared reference. If `RM` is [Mutable] we
    /// return a mutable reference.
    ///
    /// This collects into a `SmallVec` and then allocates by copying from it. Use `alloc_from_iter`
    /// if possible because it's more efficient, copying directly without the intermediate
    /// collecting step. This default could be made more efficient, like
    /// [crate::DroplessArena::alloc_from_iter], but it's not hot enough to bother.
    #[inline]
    pub fn alloc_from_iter_reg(&self, iter: impl IntoIterator<Item = T>) -> RM::SliceRef<'_, T> {
        self.alloc_from_iter_fast(iter.into_iter().collect::<SmallVec<[_; 8]>>())
    }

    /// Allocates multiple objects in a contiguous slice, returning a reference to the slice.
    ///
    /// If the type parameter `RM` is [Shared] we return a shared reference. If `RM` is [Mutable] we
    /// return a mutable reference.
    ///
    /// This is equivalent semantics to [Self::alloc_from_iter_reg] except it's faster, whereas
    /// [Self::alloc_from_iter_reg] permits more types.
    #[inline]
    pub fn alloc_from_iter_fast(&self, iter: impl IterWithFastAlloc<T>) -> RM::SliceRef<'_, T> {
        iter.alloc_into(self)
    }

    /// Number of allocated elements in the arena.
    #[inline]
    pub fn len(&self) -> usize {
        self.len.get()
    }

    /// Does the arena have any allocated elements?
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterates all allocated elements in the arena behind a mutable reference.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        // SAFETY: Same repr, this transmuted version won't be publicly exposed or used incorrectly
        // (we can't use while [IterMut] is alive), and we're not actually violating any borrow
        // rules with a mutable phantom type like we would if this was a mutable reference.
        IterMut::new(unsafe { transmute(self) })
    }

    /// Iterates pointers to all allocated elements in the arena behind a shared reference. This is
    /// allows since we can have pointers even to mutably borrowed elements.
    #[inline]
    pub fn ptr_iter(&self) -> PtrIter<'_, T> {
        PtrIter::new(self)
    }

    /// Clears the arena, dropping all elements, but doesn't free up its memory.
    ///
    /// This means we can insert new elements without having to reallocate, until we reach the old
    /// capacity or allocate a slice too large to fit in an existing region.
    #[inline]
    pub fn clear(&mut self) {
        // Ensure that, even on panic, we resize len (we leak elements we didn't drop yet instead of
        // double-freeing elements we did)
        let panic_result = catch_unwind(AssertUnwindSafe(|| {
            for elem in self.ptr_iter() {
                // SAFETY: we're shrinking the arena, so we A) won't drop later if we drop the arena
                // before growing it again, and B) if we do grow it again, we'll overwrite this data
                // before setting it to "initialized" (we might also grow past this data but it will
                // still be uninitialized and therefore not dropped).
                //
                // Also, elem.as_ptr() is alive, and we have the only reference since we have a mutable
                // reference to the entire arena.
                unsafe {
                    drop_in_place(elem.as_ptr());
                }
            }
        }));

        // This code will run even if we panic
        // Update len, num used chunks, used chunk entries, ptr, and end
        self.len.set(0);
        if size_of::<T>() != 0 {
            for chunk in self
                .chunks
                .borrow_mut()
                .iter_mut()
                .take(self.used_chunks.get())
            {
                chunk.entries = 0;
            }
            self.used_chunks.set(0);
            // ptr and end can be null and we'll still reuse instead of allocating new chunks
            self.ptr.set(null_mut());
            self.end.set(null_mut());
        }

        // Still unwind if we panicked
        if let Err(caught_panic) = panic_result {
            resume_unwind(caught_panic)
        }
    }

    /// Removes some elements from this arena, and coalesces the rest so that we don't have gaps.
    ///
    /// Pointers to regions in the memory may be invalidated as elements get rearranged. This
    /// function is behind a mutable reference, which ensures that there are no references to
    /// rearranged elements, but if there are any raw pointers they can no longer be dereferenced
    /// without UB.
    #[inline]
    pub fn retain(&mut self, mut predicate: impl FnMut(&mut T) -> bool) {
        // Ensure that, even on panic, we resize len (we leak elements we didn't drop yet instead of
        // double-freeing elements we did). Furthermore, kept elements are still in the arena,
        // although this doesn't really matter and is subject to change between versions.
        let mut num_kept = 0;
        let panic_result = catch_unwind(AssertUnwindSafe(|| {
            let mut write_iter = self.ptr_iter();
            let mut is_write_iter_at_read_iter = true;
            for mut elem in self.ptr_iter() {
                let elem_ptr = elem.as_ptr();
                // SAFETY: elem is alive (Self::iter and Self::ptr_iter only iterate initialized data)
                // and we have a mutable reference to the arena, so there are no other references to
                // elem. Therefore, we can dereference and drop elem_ptr.
                //
                // write_ptr is allocated (inside this struct) and aligned (came from Self::ptr_iter).
                // It has previously pointed to a live object since it has been elem_ptr, but we may
                // have dropped that elem_ptr so it's no longer alive. However, we can still write to
                // it.
                //
                // Lastly, we can read from elem_ptr when we write to write_ptr (effectively copying the
                // value) because we will either overwrite the value when write_ptr advances to it, or
                // (if elem_ptr advances to the end first) we will shrink the arena to be before it, so
                // that it is effectively forgotten; and then it will either be re-allocated if we grow
                // the arena again, or released without drop if we drop the arena.
                unsafe {
                    if !predicate(elem.as_mut()) {
                        // Drop the element, keep write_iter at the same position
                        is_write_iter_at_read_iter = false;
                        drop_in_place(elem_ptr);
                    } else {
                        // Keep the element, but move it to write_iter if unaligned. Advance write_iter
                        num_kept += 1;

                        // If write_chunk can hold more elements (length < capacity), we should
                        // desync write_iter from read_iter and do so (length = capacity)
                        let mut next_is_write_iter_at_read_iter = is_write_iter_at_read_iter;
                        if write_iter.chunk_remaining_entries == 1 {
                            let mut chunks = self.chunks.borrow_mut();
                            let write_chunk = chunks
                                .get_mut(write_iter.chunk_index)
                                .expect("write_iter chunk index out of bounds");
                            let difference = write_chunk.capacity - write_chunk.entries;
                            if difference > 0 {
                                // If write_iter and read_iter are still synced, they'll be synced
                                // for this element and then desynced after.
                                //
                                // Also, we can't just put write_iter.next() before this block
                                // because we need to catch chunk_remaining_entries == 1 first
                                next_is_write_iter_at_read_iter = false;
                                // This may not be the last chunk, so we need to update the count.
                                // We also need to update write_iter's count so that it won't reach
                                // the chunk end until it reaches write_chunk's capacity.
                                write_chunk.entries += difference;
                                write_iter.chunk_remaining_entries += difference;
                                // Even if elem_iter (the implicit iterator returning elem) is
                                // synced, we still want it to move on, not read the chunk's
                                // remaining memory because it;s uninitialized
                            }
                        }

                        let write_ptr = write_iter.next()
                            .expect("read_iter not done but write_iter is, write_iter should always be behind")
                            .as_ptr();
                        if size_of::<T>() != 0 && !is_write_iter_at_read_iter {
                            write_ptr.write(elem_ptr.read());
                        }

                        is_write_iter_at_read_iter = next_is_write_iter_at_read_iter;
                    }
                }
            }
        }));

        // This code will run even if we panic
        // Update len, num used chunks, used chunk entries, ptr, and end
        let old_len = self.len.get();
        self.len.set(num_kept);
        if size_of::<T>() != 0 {
            let mut chunks = self.chunks.borrow_mut();
            let mut num_entries = 0;
            let used_chunks = chunks
                .iter()
                .take_while(|chunk| {
                    if num_entries < num_kept {
                        num_entries += chunk.entries;
                        true
                    } else {
                        false
                    }
                })
                .count();
            if num_entries < num_kept {
                debug_assert_eq!(used_chunks, self.used_chunks.get());
                num_entries = old_len;
            } else {
                self.used_chunks.set(used_chunks);
            }
            if used_chunks == 0 {
                // These assertions are pretty obvious
                debug_assert_eq!((num_entries, num_kept), (0, 0));
                self.ptr.set(null_mut());
                self.end.set(null_mut());
            } else {
                let num_in_last = num_entries - num_kept;
                let last_chunk = &mut chunks[used_chunks - 1];
                // This is the last chunk, so unset (0) its entries, even though there actually are some
                last_chunk.entries = 0;
                // Set ptr and end to this chunk, and make sure ptr is offset past the existing entries
                self.ptr.set(unsafe { last_chunk.storage.add(num_in_last) });
                self.end.set(last_chunk.end());
            }
        }

        // Still unwind if we panicked
        if let Err(caught_panic) = panic_result {
            resume_unwind(caught_panic)
        }
    }

    /// Return `self` but with a different [RefMutability].
    ///
    /// With a mutable reference, we can convert between mutable and immutable variants, since there
    /// are no live allocated references.
    #[inline]
    pub fn convert<RM2: RefMutability>(self) -> TypedArenaGen<T, RM2> {
        // SAFETY: Same repr
        unsafe { transmute(self) }
    }

    /// Destroys this arena and collects all elements into a vector.
    #[inline]
    pub fn into_vec(self) -> Vec<T> {
        let mut elements = Vec::with_capacity(self.len());
        if size_of::<T>() == 0 {
            // Create `len` ZSTs which will be dropped when the vector is.
            // Remember: a random non-null pointer is a valid reference to a ZST, and dereferencing
            // is probably a no-op
            elements.extend(
                (0..self.len()).map(|_| unsafe { NonNull::<T>::dangling().as_ptr().read() }),
            );
            return elements;
        }

        let mut remaining = self.len();
        let mut chunks_borrow = self.chunks.borrow_mut();
        let mut prev_chunk = None;
        for chunk in chunks_borrow.iter_mut().take(self.used_chunks.get()) {
            if let Some(prev_chunk) = prev_chunk.replace(chunk) {
                // SAFETY: This chunk has all entries filled because we've moved on to the next one
                //   (and we resize the chunk's entries when we move on, even though it has more capacity).
                let mut prev_entries = unsafe { prev_chunk.destroy_and_return(prev_chunk.entries) };
                elements.append(&mut prev_entries);
                remaining -= prev_chunk.entries;
            }
        }
        if let Some(last_chunk) = prev_chunk {
            // SAFETY: This chunk only has `remaining` entries filled
            let mut last_entries = unsafe { last_chunk.destroy_and_return(remaining) };
            elements.append(&mut last_entries);
        }
        // Ensure we don't destroy these chunks' contents in `Drop`, only free their memory
        self.used_chunks.set(0);
        elements
    }

    /// Checks if `additional` elements can be inserted into the arena without creating a new chunk
    #[inline]
    fn can_allocate(&self, additional: usize) -> bool {
        debug_assert_ne!(size_of::<T>(), 0);
        // FIXME: this should *likely* use `offset_from`, but more
        //   investigation is needed (including running tests in miri).
        let available_bytes = self.end.get().addr_() - self.ptr.get().addr_();
        let additional_bytes = additional.checked_mul(size_of::<T>()).unwrap();
        available_bytes >= additional_bytes
    }

    /// Ensures there's enough space in the current chunk to fit `len` objects. If not, it will
    /// create a new chunk.
    #[inline]
    fn ensure_capacity(&self, additional: usize) {
        if !self.can_allocate(additional) {
            self.grow(additional);
            debug_assert!(self.can_allocate(additional));
        }
    }

    /// Allocate a contiguous slice of data and return a pointer to the start of the slice. The
    /// slice is uninitialized (why we return a pointer), and you must initialize it before calling
    /// other arena methods or dropping the arena, or you will cause UB.
    ///
    /// # Safety
    ///
    /// You must initialize the slice before calling other arena methods or dropping the arena. If
    /// iterating, you must initialize the slice before advancing the iterator.
    #[inline]
    pub unsafe fn alloc_raw_slice(&self, len: usize) -> *mut T {
        assert_ne!(len, 0);

        self.len.set(self.len.get() + len);

        if size_of::<T>() == 0 {
            // ZSTs have no memory, so we won't allocate.
            // Remember: a random non-null pointer is a valid reference to a ZST
            return NonNull::<T>::dangling().as_ptr();
        }
        self.ensure_capacity(len);

        let start_ptr = self.ptr.get();
        self.ptr.set(start_ptr.add(len));
        start_ptr
    }

    /// Grows the arena = creates a new chunk which will hold at least `additional` elements,
    /// or reuses a chunk if we have extras.
    #[inline(never)]
    #[cold]
    fn grow(&self, additional: usize) {
        debug_assert_ne!(size_of::<T>(), 0);
        let used_chunks = self.used_chunks.get();
        let mut chunks = self.chunks.borrow_mut();
        let mut reused_a_chunk = false;
        for potential_reuse_idx in used_chunks..chunks.len() {
            let potential_reuse_chunk = &mut chunks[potential_reuse_idx];
            if potential_reuse_chunk.capacity >= additional {
                // We found a chunk that can hold the additional elements, so we'll use it.
                // Make sure to update the # entries; since this is the last chunk, we unset (0) it
                // even though there are actually additional (see `ArenaChunk.entries` doc)
                potential_reuse_chunk.entries = 0;
                // Set ptr and end to the reused chunk
                self.ptr.set(potential_reuse_chunk.storage);
                self.end.set(potential_reuse_chunk.end());
                if used_chunks != potential_reuse_idx {
                    // We have to ensure the reused chunk is the next one
                    chunks.swap(used_chunks, potential_reuse_idx);
                }
                reused_a_chunk = true;
                break;
            }
        }

        if !reused_a_chunk {
            // Actually grow = insert a chunk at used_chunks with the required capacity
            unsafe {
                // We need the element size to convert chunk sizes (ranging from
                // PAGE to HUGE_PAGE bytes) to element counts.
                let elem_size = max(1, size_of::<T>());
                let mut new_cap;
                if let Some(last_chunk) = used_chunks.checked_sub(1).map(|i| &mut chunks[i]) {
                    // If a type is `!needs_drop`, we don't need to keep track of how many elements
                    // the chunk stores - the field will be ignored anyway.
                    // FIXME: this should *likely* use `offset_from`, but more
                    //   investigation is needed (including running tests in miri).
                    let used_bytes = self.ptr.get().addr_() - last_chunk.storage.addr_();
                    // Set # entries since this is no longer the last chunk
                    last_chunk.entries = used_bytes / size_of::<T>();

                    // If the previous chunk's capacity is less than HUGE_PAGE
                    // bytes, then this chunk will be least double the previous
                    // chunk's size.
                    new_cap = last_chunk.capacity.min(HUGE_PAGE / elem_size / 2);
                    new_cap *= 2;
                } else {
                    new_cap = PAGE / elem_size;
                }
                // Also ensure that this chunk can fit `additional`.
                new_cap = max(additional, new_cap);

                let mut chunk = ArenaChunk::<T>::new(new_cap);
                // Set ptr and end to the new chunk
                self.ptr.set(chunk.storage);
                self.end.set(chunk.end());

                // Add chunk to index used_chunks (used_chunks will be incremented in grow())
                let last_index = chunks.len();
                chunks.push(chunk);
                if used_chunks < last_index {
                    chunks.swap(used_chunks, last_index);
                }
            }
        }

        self.used_chunks.set(used_chunks + 1);
    }

    /// Drops the contents of the last chunk. The last chunk is partially empty, unlike all other
    /// chunks.
    fn clear_last_chunk(&self, last_chunk: &mut ArenaChunk<T>) {
        debug_assert_ne!(size_of::<T>(), 0);
        // Determine how much was filled.
        let start = last_chunk.storage.addr_();
        // We obtain the value of the pointer to the first uninitialized element.
        let end = self.ptr.get().addr_();
        // We then calculate the number of elements to be dropped in the last chunk,
        // which is the filled area's length.
        // FIXME: this should *likely* use `offset_from`, but more
        //   investigation is needed (including running tests in miri).
        let diff = (end - start) / size_of::<T>();
        // Pass that to the `destroy` method.
        unsafe {
            last_chunk.destroy(diff);
        }
        // Reset the chunk.
        self.ptr.set(last_chunk.storage);
    }
}

impl<T> TypedArenaGen<T, Shared> {
    /// Iterates all allocated elements in the arena behind a shared reference.
    ///
    /// The iterator can handle new objects being allocated. If you allocate new objects they will
    /// be added to the end. If the iterator has already ended and you allocate new objects, it will
    /// suddenly have more elements; if you don't want that behavior use `fuse`.
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }
}

impl<T: Debug> Debug for TypedArena<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypedArena")?;
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T, RM: RefMutability> Drop for TypedArenaGen<T, RM> {
    fn drop(&mut self) {
        if size_of::<T>() == 0 {
            // These invariants always hold, we only assert them here
            debug_assert!(self.ptr.get().is_null());
            debug_assert!(self.end.get().is_null());
            debug_assert_eq!(self.chunks.borrow().len(), 0);
            debug_assert_eq!(self.used_chunks.get(), 0);

            // Drop `len` ZSTs.
            // Remember: a dangling pointer is a valid ZST reference, `drop_in_place` will only run
            // the ZSTs drop code (which probably shouldn't rely on the address, since it was
            // allocated into an arena and therefore already in an effectively undefined location,
            // without any adjacent structures)
            for _ in 0..self.len() {
                unsafe {
                    drop_in_place(NonNull::<T>::dangling().as_ptr());
                }
            }
        } else {
            // `ArenaChunk` drop ensures that the memory is dropped, but we have to drop the contents
            // here because chunks can't because they don't always know their size
            unsafe {
                // Determine how much was filled.
                let mut chunks_borrow = self.chunks.borrow_mut();
                // Remove unused chunks (we don't need to destroy because we've already dropped or moved
                // their contents)
                for _ in 0..(chunks_borrow.len() - self.used_chunks.get()) {
                    chunks_borrow.pop();
                }
                // Drop elements in the used chunks
                if let Some(mut last_chunk) = chunks_borrow.pop() {
                    // Drop the contents of the last chunk.
                    self.clear_last_chunk(&mut last_chunk);
                    // The last chunk will be dropped. Destroy all other chunks.
                    for chunk in chunks_borrow.iter_mut() {
                        chunk.destroy(chunk.entries);
                    }
                }
            }
        }
    }
}

impl<'a, T> IntoIterator for &'a TypedArenaGen<T, Shared> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, RM: RefMutability> IntoIterator for &'a mut TypedArenaGen<T, RM> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

unsafe impl<T: Send, RM: RefMutability> Send for TypedArenaGen<T, RM> {}

impl<'a, T> PtrIter<'a, T> {
    /// Create a new iterator for the arena
    #[inline]
    fn new<RM: RefMutability>(arena: &'a TypedArenaGen<T, RM>) -> Self {
        // SAFETY: Same repr, this transmuted version won't be publicly exposed or used incorrectly
        // (see [PtrIter] type doc), and we're not actually violating any borrow rules.
        let arena = unsafe { transmute::<&'a TypedArenaGen<T, RM>, &'a TypedArena<T>>(arena) };
        let chunks = arena.chunks.borrow();
        let chunk = chunks.first();
        Self {
            arena,
            chunk_index: 0,
            chunk_data: chunk.map_or(NonNull::dangling(), |c| NonNull::new(c.storage).unwrap()),
            chunk_remaining_entries: chunk.map_or(0, |c| c.entries),
            element_index: 0,
        }
    }

    /// Get the number of remaining elements, assuming there are no new ones
    #[inline]
    pub fn remaining(&self) -> usize {
        self.arena.len() - self.element_index
    }

    /// Whether we have a next element
    #[inline]
    pub fn has_next(&self) -> bool {
        self.remaining() > 0
    }
}

impl<'a, T> Iterator for PtrIter<'a, T> {
    type Item = NonNull<T>;

    /// Gets a the next element as a pointer
    fn next(&mut self) -> Option<Self::Item> {
        if !self.has_next() {
            return None;
        }

        let element = self.chunk_data;
        self.element_index += 1;

        // If this is a ZST we only need to count the # of items to iterate, and `chunk_data` is
        // already a dangling pointer fron `Self::new` since there are no chunks.
        if size_of::<T>() != 0 {
            // If chunk_remaining_entries is 0, we actually still have entries but are on the last
            // chunk. We'll run out when `has_next` returns false.
            if self.chunk_remaining_entries == 1 {
                // We've exhausted the current chunk, so move to the next one
                self.chunk_index += 1;
                let chunks = self.arena.chunks.borrow();
                let chunk = chunks.get(self.chunk_index).expect(
                    "ArenaIter::next invariant error: arena has more elements but no more chunks",
                );
                self.chunk_data = NonNull::new(chunk.storage).unwrap();
                self.chunk_remaining_entries = chunk.entries;
            } else {
                // SAFETY: We're still in the chunk, so we have a valid pointer and add is valid
                self.chunk_data =
                    unsafe { NonNull::new_unchecked(self.chunk_data.as_ptr().add(1)) };
                self.chunk_remaining_entries = self.chunk_remaining_entries.saturating_sub(1);
            }
        }
        Some(element)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        // We will return at least len more elements, but we can't return an upper bound in case
        // some get added
        (self.remaining(), None)
    }
}

impl<'a, T, RM: RefMutability> IterGen<'a, T, RM> {
    /// Create a new iterator for the arena
    #[inline]
    fn new(arena: &'a TypedArenaGen<T, RM>) -> Self {
        Self(PtrIter::new(arena), PhantomData)
    }

    /// Gets a the next element as a pointer
    pub fn next_ptr(&mut self) -> Option<NonNull<T>> {
        self.0.next()
    }

    /// Get the number of remaining elements, assuming there are no new ones
    #[inline]
    pub fn remaining(&self) -> usize {
        self.0.remaining()
    }

    /// Whether we have a next element
    #[inline]
    pub fn has_next(&self) -> bool {
        self.0.has_next()
    }
}

impl<'a, T> PartialEq for PtrIter<'a, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.arena, other.arena) && self.element_index == other.element_index
    }
}

impl<'a, T, RM: RefMutability> PartialEq for IterGen<'a, T, RM> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<'a, T, RM: RefMutability> Iterator for IterGen<'a, T, RM> {
    type Item = RM::Ref<'a, T>;

    /// Gets the next element as a reference. Mutable or shared depends on the `RM` type parameter.
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: The value is initialized, because the chunk has more entries and (important for
        // the last chunk) the arena has more elements
        self.next_ptr().map(|e| unsafe { RM::from_non_null(e) })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T, const N: usize> IterWithFastAlloc<T> for std::array::IntoIter<T, N> {
    #[inline]
    fn alloc_into<RM: RefMutability>(self, arena: &TypedArenaGen<T, RM>) -> RM::SliceRef<'_, T> {
        let len = self.len();
        if len == 0 {
            return RM::empty();
        }
        // Move the content to the arena by copying and then forgetting it.
        unsafe {
            let start_ptr = arena.alloc_raw_slice(len);
            self.as_slice()
                .as_ptr()
                .copy_to_nonoverlapping(start_ptr, len);
            forget(self);
            RM::from_raw_parts(start_ptr, len)
        }
    }
}

impl<T> IterWithFastAlloc<T> for Vec<T> {
    #[inline]
    fn alloc_into<RM: RefMutability>(
        mut self,
        arena: &TypedArenaGen<T, RM>,
    ) -> RM::SliceRef<'_, T> {
        let len = self.len();
        if len == 0 {
            return RM::empty();
        }
        // Move the content to the arena by copying and then forgetting it.
        unsafe {
            let start_ptr = arena.alloc_raw_slice(len);
            self.as_ptr().copy_to_nonoverlapping(start_ptr, len);
            self.set_len(0);
            RM::from_raw_parts(start_ptr, len)
        }
    }
}

impl<A: smallvec::Array> IterWithFastAlloc<A::Item> for SmallVec<A> {
    #[inline]
    fn alloc_into<RM: RefMutability>(
        mut self,
        arena: &TypedArenaGen<A::Item, RM>,
    ) -> RM::SliceRef<'_, A::Item> {
        let len = self.len();
        if len == 0 {
            return RM::empty();
        }
        // Move the content to the arena by copying and then forgetting it.
        unsafe {
            let start_ptr = arena.alloc_raw_slice(len);
            self.as_ptr().copy_to_nonoverlapping(start_ptr, len);
            self.set_len(0);
            RM::from_raw_parts(start_ptr, len)
        }
    }
}

impl RefMutability for Shared {
    type Ref<'a, T> = &'a T where T: 'a;
    type SliceRef<'a, T> = &'a [T] where T: 'a;

    fn empty<'a, T>() -> Self::SliceRef<'a, T> {
        &[]
    }

    unsafe fn from_ptr<'a, T>(t: *mut T) -> Self::Ref<'a, T> {
        &*t
    }

    unsafe fn from_raw_parts<'a, T>(t: *mut T, len: usize) -> Self::SliceRef<'a, T> {
        from_raw_parts(t, len)
    }

    fn as_ref<T>(t: Self::Ref<'_, T>) -> &T {
        t
    }

    fn as_slice_ref<T>(t: Self::SliceRef<'_, T>) -> &[T] {
        t
    }
}

impl RefMutability for Mutable {
    type Ref<'a, T> = &'a mut T where T: 'a;
    type SliceRef<'a, T> = &'a mut [T] where T: 'a;

    fn empty<'a, T>() -> Self::SliceRef<'a, T> {
        &mut []
    }

    unsafe fn from_ptr<'a, T>(t: *mut T) -> Self::Ref<'a, T> {
        &mut *t
    }

    unsafe fn from_raw_parts<'a, T>(t: *mut T, len: usize) -> Self::SliceRef<'a, T> {
        from_raw_parts_mut(t, len)
    }

    fn as_ref<T>(t: Self::Ref<'_, T>) -> &T {
        t
    }

    fn as_slice_ref<T>(t: Self::SliceRef<'_, T>) -> &[T] {
        t
    }
}

mod private {
    use super::{Mutable, Shared};

    pub trait Sealed {}

    impl Sealed for Shared {}
    impl Sealed for Mutable {}
}
