use std::mem::{forget, needs_drop, size_of, MaybeUninit};
use std::ptr::{drop_in_place, null_mut, slice_from_raw_parts_mut};

pub struct ArenaChunk<T = u8> {
    /// Pointer to raw storage for the arena chunk.
    pub storage: *mut T,
    /// The number of valid entries in the chunk (the `len` of storage), **except** the last chunk's
    /// entries is always 0 (unset), because it is being filled and we don't want to access the
    /// [ArenaChunk] on the fast path, we want to be able to only access its memory. **Also**,
    /// [crate::DroplessArena] doesn't use this, so all of its chunks' `entries` is 0
    pub entries: usize,
    /// \# of elements the raw storage can hold AKA size of the raw storage allocation
    pub capacity: usize,
}

impl<T> ArenaChunk<T> {
    #[inline]
    pub unsafe fn new(capacity: usize) -> ArenaChunk<T> {
        debug_assert_ne!(size_of::<T>(), 0);
        debug_assert_ne!(capacity, 0);
        // Vec doesn't allocate ZSTs but we want 1 byte per ZST, so if T is a ZST we allocate a u8
        // Vec instead of a `T` Vec.
        let mut vec = Vec::with_capacity(capacity);
        let storage = vec.as_mut_ptr();
        forget(vec);
        ArenaChunk {
            storage,
            entries: 0,
            capacity,
        }
    }

    /// Destroys this arena chunk.
    #[inline]
    pub unsafe fn destroy(&mut self, len: usize) {
        // The branch on needs_drop() is an -O1 performance optimization.
        // Without the branch, dropping TypedArena<u8> takes linear time.
        if needs_drop::<T>() {
            // Here we run drop code
            drop_in_place(&mut *slice_from_raw_parts_mut(self.storage, len));
        }
        // And when the `ArenaChunk` is dropped, we'll free the memory
    }

    /// Returns an iterator of this chunk's elements which effectively destroys this chunk.
    ///
    /// Even though this takes a `&mut self`, you must not access the chunk's data after calling
    /// this.
    #[inline]
    pub unsafe fn destroy_and_return(&mut self, len: usize) -> Vec<T> {
        // Vec doesn't allocate ZSTs but we want 1 byte per ZST, so if T is a ZST we allocate a u8
        // Vec instead of a `T` Vec. But...it still works, and even drops?
        // ???: this may be UB or rely on a part of `Vec`'s implementation which could change
        let vec = Vec::from_raw_parts(self.storage, len, self.capacity);
        // Set `storage` to null so that we don't try to free the memory on `Drop`
        self.storage = null_mut();
        vec
    }

    // Returns a pointer to the end of the allocated space.
    #[inline]
    pub fn end(&mut self) -> *mut T {
        unsafe { self.storage.add(self.capacity) }
    }
}

// Like [crate::DroplessArena], there's no `Debug` for [ArenaChunk]

impl<T> Drop for ArenaChunk<T> {
    fn drop(&mut self) {
        // If `storage` is null, we don't want to drop. Otherwise we've already run the drop code,
        // but need to free the memory.
        if size_of::<T>() != 0 && !self.storage.is_null() {
            // This will cause the memory to be freed, but no drop code since we use MaybeUninit
            unsafe {
                drop(Box::<[MaybeUninit<T>]>::from_raw(slice_from_raw_parts_mut(
                    self.storage.cast::<MaybeUninit<T>>(),
                    self.capacity,
                )));
            }
        }
    }
}
