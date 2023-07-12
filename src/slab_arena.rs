use std::cell::Cell;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::mem::{replace, size_of};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

use crate::TypedArenaMut;

#[cfg(test)]
mod tests;

/// A slab/arena: a [TypedArenaMut] with a linked list of free entries which have already been
/// allocated, so they can be reused behind a shared reference (but still only reclaimed behind a
/// mutable reference, by destroying).
///
/// Allocating an element returns a [RefMut]s which will add the element to the linked list when
/// dropped. You can also convert it into an [UnsafeRef] which can be copied and takes up less
/// space, but requires manually handling with unsafe operations.
pub struct SlabArena<T> {
    /// Arena
    arena: TypedArenaMut<Entry<T>>,
    /// Pointer to next free entry we've already allocated, or `None` if we need to allocate more.
    next_free: NextFree<T>,
}

/// Data allocated within a [SlabArena], which is deallocated when dropped, or you can take it out.
pub struct RefMut<'a, T> {
    /// Pointer to the entry. `None` if removed.
    entry: Option<NonNull<Entry<T>>>,
    /// Reference to the arena's `next_free`
    next_free: &'a NextFree<T>,
}

/// Data allocated within a [SlabArena] which:
///
/// - Has no lifetime, can be copied, and takes up less space
/// - *But* must be removed manually, and has the following safety requirements on all its methods:
///
/// # Safety
/// - UB if it produces a shared and mutable reference which simultaneously exist; these may be
///   references from the same [UnsafeRef] *or* references from different copies *or* from an
///   [UnsafeRef] and [RefMut] or even from 2 [RefMut]s produced by an [UnsafeRef].
/// - UB to use a reference or call any `unsafe` methods on the [UnsafeRef] after its entry is
///   removed, even if another entry replaces it.
/// - UB if the arena is mutably accessed while the [UnsafeRef] is still alive, and then one of its
///   `unsafe` methods is called, even if the entry is occupied.
pub struct UnsafeRef<T> {
    entry: NonNull<Entry<T>>,
}

#[derive(Debug)]
#[repr(C)]
enum Entry<T> {
    /// A value is present
    Occupied { value: T },
    /// A value is not present
    Vacant {
        next_free: Option<NonNull<Entry<T>>>,
    },
}

type NextFree<T> = Cell<Option<NonNull<Entry<T>>>>;

impl<T> SlabArena<T> {
    /// Create a new, empty slab/arena.
    #[inline]
    pub fn new() -> Self {
        Self {
            arena: TypedArenaMut::new(),
            next_free: Cell::new(None),
        }
    }

    /// Insert an element into the arena, returning a [RefMut] which will remove it when dropped.
    ///
    /// If there is a previously-allocated entry which was vacated, this will return that. Otherwise
    /// it will allocate a new entry in the underlying arena.
    #[inline]
    pub fn alloc(&self, value: T) -> RefMut<'_, T> {
        let entry = match self.next_free.get() {
            None => NonNull::from(self.arena.alloc(Entry::Occupied { value })),
            Some(mut next_free) => {
                // SAFETY: This entry is alive and unused by definition of being `next_free`
                let next_free_mut = unsafe { next_free.as_mut() };
                match next_free_mut {
                    Entry::Vacant {
                        next_free: next_next_free,
                    } => {
                        self.next_free.set(*next_next_free);
                    }
                    Entry::Occupied { .. } => unreachable!("next_free should always be Vacant"),
                };
                *next_free_mut = Entry::Occupied { value };
                next_free
            }
        };
        RefMut::new(entry, self)
    }

    /// Iterate all entries and free those which don't pass the predicate, dropping their contents
    /// and adding them to the free list. This also gives you mutable access to each entry.
    ///
    /// This takes a mutable reference, so there must be no active references to the arena.
    #[inline]
    pub fn retain(&mut self, mut predicate: impl FnMut(&mut T) -> bool) {
        for entry in self.arena.iter_mut() {
            let do_free = match entry {
                Entry::Occupied { value } => !predicate(value),
                Entry::Vacant { .. } => false,
            };
            if do_free {
                let entry_ptr = NonNull::new(entry as *mut Entry<T>).unwrap();
                let next_free = self.next_free.replace(Some(entry_ptr));
                debug_assert!(entry.is_occupied());
                *entry = Entry::Vacant { next_free };
            }
        }
    }

    /// Iterate all entries and free those which don't pass the predicate, dropping their contents
    /// and adding them to the free list.
    ///
    /// # Safety
    /// Each removed entry *must* have no other references, and *every* entry must have no active
    /// mutable references ([RefMut]s are OK as long as they aren't mutably dereferenced). Consider
    /// using [Self::retain], which enforces these requirements by taking a mutable reference of the
    /// entire arena.
    #[inline]
    pub unsafe fn retain_shared(&self, mut predicate: impl FnMut(&T) -> bool) {
        for mut entry in self.arena.ptr_iter() {
            let do_free = match entry.as_ref() {
                Entry::Occupied { value } => !predicate(value),
                Entry::Vacant { .. } => false,
            };
            if do_free {
                let next_free = self.next_free.replace(Some(entry));
                debug_assert!(entry.as_ref().is_occupied());
                *entry.as_mut() = Entry::Vacant { next_free };
            }
        }
    }

    // Iteration, etc. are either mutable or unsafe, because there could be arbitrary active mutable
    // references created entirely from safe code if we have a shared reference.
}

impl<T> Default for SlabArena<T> {
    #[inline]
    fn default() -> Self {
        SlabArena::new()
    }
}

impl<'a, T> RefMut<'a, T> {
    #[inline]
    fn new(entry: NonNull<Entry<T>>, arena: &'a SlabArena<T>) -> Self {
        debug_assert!(unsafe { entry.as_ref() }.is_occupied());
        Self {
            entry: Some(entry),
            next_free: &arena.next_free,
        }
    }

    /// Take the entry out of this and remove it from the arena.
    #[inline]
    pub fn take(mut self) -> T {
        // Make sure to take so we don't remove in `drop`
        // SAFETY: `RefMut`'s entry is `Some` until consumed or dropped
        let mut entry = unsafe { self.entry.take().unwrap_unchecked() };
        let next_free = self.next_free.replace(Some(entry));
        // SAFETY: `RefMut`'s entry is live and it has exclusive access
        match replace(unsafe { entry.as_mut() }, Entry::Vacant { next_free }) {
            Entry::Occupied { value } => value,
            Entry::Vacant { .. } => unreachable!("RefMut entry should always be Occupied"),
        }
    }

    /// Return a reference to the entry and don't destroy it until the arena is destroyed.
    #[inline]
    pub fn leak(mut self) -> &'a mut T {
        // Make sure to take so we don't remove in `drop`
        // SAFETY: `RefMut`'s entry is `Some` until consumed or dropped
        let mut entry = unsafe { self.entry.take().unwrap_unchecked() };
        // SAFETY: `RefMut`'s entry is live and it has exclusive access
        match unsafe { entry.as_mut() } {
            Entry::Occupied { value } => value,
            Entry::Vacant { .. } => unreachable!("RefMut entry should always be Occupied"),
        }
    }

    /// Get the underlying pointer. Dropping this afterward *will* deallocate the object and
    /// invalidate the pointer, unlike [Self::leak] and [Self::into_unsafe]. If you don't want this,
    /// use `self.leak().as_ptr()` instead.
    #[inline]
    pub fn as_ptr(&self) -> NonNull<T> {
        // SAFETY: `RefMut`'s entry is `Some` until consumed or dropped
        let mut entry = unsafe { self.entry.unwrap_unchecked() };
        // SAFETY: `RefMut`'s entry is live and it has exclusive access
        match unsafe { entry.as_mut() } {
            Entry::Occupied { value } => NonNull::new(value).unwrap(),
            Entry::Vacant { .. } => unreachable!("RefMut entry should always be Occupied"),
        }
    }

    /// Convert into an [UnsafeRef]. Afterwards, you are responsible for calling [UnsafeRef::take]
    /// or [UnsafeRef::discard] or the entry will never be freed. Additionally, you are responsible
    /// for maintaining all of [UnsafeRef]'s invariants (see its doc).
    ///
    /// Doing the conversion itself is safe, because at worst it will only leak memory during the
    /// arena's lifetime (not even in general) which is not UB. *Using* the [UnsafeRef] is unsafe.
    #[inline]
    pub fn into_unsafe(mut self) -> UnsafeRef<T> {
        // Make sure to take so we don't remove in `drop`
        UnsafeRef {
            entry: self.entry.take().unwrap(),
        }
    }
}

impl<'a, T: Debug> Debug for RefMut<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("RefMut").field(self).finish()
    }
}

impl<'a, T: Display> Display for RefMut<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        T::fmt(self, f)
    }
}

impl<'a, T> Deref for RefMut<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // SAFETY: `RefMut`'s entry is live and it has exclusive access
        match unsafe { self.entry.unwrap_unchecked().as_ref() } {
            Entry::Occupied { value } => value,
            Entry::Vacant { .. } => unreachable!("RefMut entry should always be Occupied"),
        }
    }
}

impl<'a, T> DerefMut for RefMut<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: `RefMut`'s entry is live and it has exclusive access
        match unsafe { self.entry.unwrap_unchecked().as_mut() } {
            Entry::Occupied { value } => value,
            Entry::Vacant { .. } => unreachable!("RefMut entry should always be Occupied"),
        }
    }
}

impl<'a, T> Drop for RefMut<'a, T> {
    #[inline]
    fn drop(&mut self) {
        let Some(mut entry) = self.entry.take() else {
            // Already removed
            return
        };

        let next_free = self.next_free.replace(Some(entry));
        debug_assert!(unsafe { entry.as_ref() }.is_occupied());
        // SAFETY: `RefMut`'s entry is live and it has exclusive access
        unsafe {
            *entry.as_mut() = Entry::Vacant { next_free };
        }
    }
}

impl<T> UnsafeRef<T> {
    /// Convert a pointer to an occupied entry back into an [UnsafeRef].
    ///
    /// # Safety
    /// The pointer must be valid and point to an occupied entry in the arena.
    #[inline]
    pub unsafe fn from_ptr(ptr: NonNull<T>) -> Self {
        Self {
            entry: NonNull::new_unchecked(
                ptr.as_ptr()
                    .cast::<u8>()
                    .sub(Entry::<T>::offset_of_occupied_value())
                    .cast(),
            ),
        }
    }

    /// Convert a reference to an occupied entry back into an [UnsafeRef].
    ///
    /// # Safety
    /// The reference must point to an occupied entry in the arena.
    #[inline]
    pub unsafe fn from_ref(r#ref: &T) -> Self {
        Self::from_ptr(NonNull::from(r#ref))
    }

    /// Convert back into a safe [RefMut].
    ///
    /// # Safety
    /// All of [UnsafeRef]'s requirements must be met (see type doc), and `arena` must be the arena
    /// this ref originated from.
    #[inline]
    pub unsafe fn into_safe(self, arena: &SlabArena<T>) -> RefMut<'_, T> {
        RefMut::new(self.entry, arena)
    }

    /// Remove and return the entry.
    ///
    /// # Safety
    /// All of [UnsafeRef]'s requirements must be met (see type doc), and `arena` must be the arena
    /// this ref originated from.
    #[inline]
    pub unsafe fn take(self, arena: &SlabArena<T>) -> T {
        self.into_safe(arena).take()
    }

    /// Remove the entry.
    ///
    /// # Safety
    /// All of [UnsafeRef]'s requirements must be met (see type doc), and `arena` must be the arena
    /// this ref originated from.
    #[inline]
    pub unsafe fn discard(self, arena: &SlabArena<T>) {
        drop(self.into_safe(arena))
    }

    /// Get the entry as a shared reference
    ///
    /// # Safety
    /// All of [UnsafeRef]'s requirements must be met (see type doc), and `&'a T` must not outlive
    /// this ref OR live when a mutable reference to its data is created.
    #[inline]
    pub unsafe fn as_ref<'a>(&self) -> &'a T {
        match self.entry.as_ref() {
            Entry::Occupied { value } => value,
            Entry::Vacant { .. } => {
                unreachable!("UnsafeRef entry should always be Occupied, was it removed?")
            }
        }
    }

    /// Get the entry as a mutable reference
    ///
    /// # Safety
    /// All of [UnsafeRef]'s requirements must be met (see type doc), and `&'a mut T` must not
    /// outlive this ref OR live when another reference to its data is created.
    #[inline]
    pub unsafe fn as_mut<'a>(&mut self) -> &'a mut T {
        // SAFETY: `UnsafeRef`'s entry is live and it has exclusive access
        match self.entry.as_mut() {
            Entry::Occupied { value } => value,
            Entry::Vacant { .. } => {
                unreachable!("UnsafeRef entry should always be Occupied, was it removed?")
            }
        }
    }

    /// Get the entry as a pointer. Note that this still requires the entry to be alive and owned by
    /// this ref; it's still unsafe and requires all of [UnsafeRef]'s requirements.
    ///
    /// # Safety
    /// All of [UnsafeRef]'s requirements must be met (see type doc).
    #[inline]
    pub unsafe fn as_ptr(&self) -> NonNull<T> {
        NonNull::from(self.as_ref())
    }

    /// Whether both [UnsafeRef]s point to the same element
    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        self.entry == other.entry
    }
}

impl<T> Clone for UnsafeRef<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for UnsafeRef<T> {}

impl<T> PartialEq for UnsafeRef<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.entry == other.entry
    }
}

impl<T> Eq for UnsafeRef<T> {}

impl<T> Hash for UnsafeRef<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.entry.hash(state)
    }
}

impl<T> Entry<T> {
    #[inline]
    const fn offset_of_occupied_value() -> usize {
        size_of::<Self>() - size_of::<T>()
    }

    #[inline]
    fn is_occupied(&self) -> bool {
        match self {
            Entry::Occupied { .. } => true,
            Entry::Vacant { .. } => false,
        }
    }

    #[inline]
    #[allow(dead_code)]
    fn is_vacant(&self) -> bool {
        match self {
            Entry::Occupied { .. } => false,
            Entry::Vacant { .. } => true,
        }
    }
}
