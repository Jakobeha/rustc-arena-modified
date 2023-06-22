//! Original code from [rustc_arena](https://doc.rust-lang.org/stable/nightly-rustc/rustc_arena/index.html).
//! There are some modifications, including converting unstable features to stable equivalents,
//! allocating shared references and adding iteration, and adding the ability to filter and coalesce
//! behind a mutable reference.
//!
//! The arena, a fast but limited type of allocator.
//!
//! Arenas are a type of allocator that destroy the objects within, all at once, once the arena
//! itself is destroyed. They do not support deallocation of individual objects while the arena
//! itself is still alive. The benefit of an arena is very fast allocation; just a pointer bump.

// TODO:
//   - add tests for untested (e.g. dropless arena)

use std::mem::{align_of, transmute};

pub use self::typed_arena::{TypedArena, TypedArenaGen, TypedArenaMut};
pub use dropless_arena::DroplessArena;
#[cfg(feature = "slab")]
pub use slab_arena::SlabArena;

mod arena_chunk;
pub mod dropless_arena;
#[cfg(feature = "slab")]
pub mod slab_arena;
pub mod typed_arena;

// The arenas start with PAGE-sized chunks, and then each new chunk is twice as
// big as its predecessor, up until we reach HUGE_PAGE-sized chunks, whereupon
// we stop growing. This scales well, from arenas that are barely used up to
// arenas that are used for 100s of MiBs. Note also that the chosen sizes match
// the usual sizes of pages and huge pages on Linux.
const PAGE: usize = 4096;
const HUGE_PAGE: usize = 2 * 1024 * 1024;

#[inline(never)]
#[cold]
fn cold_path<F: FnOnce() -> R, R>(f: F) -> R {
    f()
}

// region stable implementations of unstable functions
trait PtrUnstables<T: ?Sized> {
    #[must_use]
    fn wrapping_byte_offset_(self, count: isize) -> Self;
    #[must_use]
    fn addr_(self) -> usize;
    #[must_use]
    fn with_addr_(self, addr: usize) -> Self;
}

//noinspection DuplicatedCode
impl<T> PtrUnstables<T> for *const T {
    #[inline(always)]
    fn wrapping_byte_offset_(self, count: isize) -> Self {
        // Right now we can get away with using regular wrapping offset and requiring alignment,
        // because we never use this with an unaligned count
        if count % align_of::<T>() as isize == 0 {
            self.wrapping_offset(count / align_of::<T>() as isize)
        } else {
            panic!("wrapping_byte_offset_ called with unaligned count")
        }
    }

    #[inline(always)]
    fn addr_(self) -> usize {
        // XXXXX(strict_provenance_magic): I am magic and should be a compiler intrinsic.
        // SAFETY: Pointer-to-integer transmutes are valid (if you are okay with losing the
        // provenance).
        #[allow(clippy::transmutes_expressible_as_ptr_casts)]
        unsafe {
            transmute(self.cast::<()>())
        }
    }

    #[inline]
    fn with_addr_(self, addr: usize) -> Self {
        // XXXXX(strict_provenance_magic): I am magic and should be a compiler intrinsic.
        //
        // In the mean-time, this operation is defined to be "as if" it was
        // a wrapping_offset, so we can emulate it as such. This should properly
        // restore pointer provenance even under today's compiler.
        let self_addr = self.addr_() as isize;
        let dest_addr = addr as isize;
        let offset = dest_addr.wrapping_sub(self_addr);

        // This is the canonical desugarring of this operation
        self.wrapping_byte_offset_(offset)
    }
}

//noinspection DuplicatedCode
impl<T> PtrUnstables<T> for *mut T {
    #[inline(always)]
    fn wrapping_byte_offset_(self, count: isize) -> Self {
        // Right now we can get away with using regular wrapping offset and requiring alignment,
        // because we never use this with an unaligned count
        if count % align_of::<T>() as isize == 0 {
            self.wrapping_offset(count / align_of::<T>() as isize)
        } else {
            panic!("wrapping_byte_offset_ called with unaligned count")
        }
    }

    #[inline(always)]
    fn addr_(self) -> usize {
        // XXXXX(strict_provenance_magic): I am magic and should be a compiler intrinsic.
        // SAFETY: Pointer-to-integer transmutes are valid (if you are okay with losing the
        // provenance).
        #[allow(clippy::transmutes_expressible_as_ptr_casts)]
        unsafe {
            transmute(self.cast::<()>())
        }
    }

    #[inline]
    fn with_addr_(self, addr: usize) -> Self {
        // XXXXX(strict_provenance_magic): I am magic and should be a compiler intrinsic.
        //
        // In the mean-time, this operation is defined to be "as if" it was
        // a wrapping_offset, so we can emulate it as such. This should properly
        // restore pointer provenance even under today's compiler.
        let self_addr = self.addr_() as isize;
        let dest_addr = addr as isize;
        let offset = dest_addr.wrapping_sub(self_addr);

        // This is the canonical desugarring of this operation
        self.wrapping_byte_offset_(offset)
    }
}
