use std::iter::{once, repeat};
use std::mem::size_of;

use rand::{Rng, SeedableRng};
use rand::rngs::SmallRng;

use super::*;

#[test]
pub fn test_make_empty() {
    let arena = TypedArena::<u8>::new();
    assert_eq!(arena.len(), 0);
}

#[test]
pub fn test_alloc() {
    let arena = TypedArena::new();
    let a = arena.alloc(1);
    let b = arena.alloc(2);
    let c = arena.alloc(3);
    assert_eq!(*a, 1);
    assert_eq!(*b, 2);
    assert_eq!(*c, 3);
}

#[test]
pub fn test_iter() {
    let arena = TypedArena::new();
    arena.alloc(1);
    arena.alloc(2);
    arena.alloc(3);

    let mut iter = arena.iter();

    assert_eq!(*iter.next().unwrap(), 1);
    assert_eq!(*iter.next().unwrap(), 2);
    assert_eq!(*iter.next().unwrap(), 3);
    assert!(iter.next().is_none());
}

#[test]
pub fn test_reuse_chunks_clear() {
    let mut arena = TypedArena::new();
    arena.alloc(1);
    arena.alloc(2);
    assert_eq!(arena.used_chunks.get(), 1);

    arena.clear();
    assert_eq!(arena.used_chunks.get(), 0);

    arena.alloc(3);
    // Should reuse the chunk we previously freed
    assert_eq!(arena.used_chunks.get(), 1);
}

#[test]
pub fn test_reuse_chunks_retain() {
    let mut arena = TypedArena::new();
    arena.alloc(1);
    arena.alloc(2);
    assert_eq!(arena.used_chunks.get(), 1);

    arena.retain(|_| false);
    assert_eq!(arena.used_chunks.get(), 0);

    arena.alloc(3);
    // Should reuse the chunk we previously freed
    assert_eq!(arena.used_chunks.get(), 1);
}

#[test]
pub fn test_into_vec() {
    let arena = TypedArena::new();
    arena.alloc(1);
    arena.alloc(2);
    arena.alloc(3);

    let vec = arena.into_vec();
    assert_eq!(vec, vec![1, 2, 3]);
}

#[test]
pub fn test_allocation_from_iter() {
    let arena = TypedArena::new();
    let values = vec![1, 2, 3, 4, 5];
    let slice = arena.alloc_from_iter(values.into_iter());

    assert_eq!(slice, &[1, 2, 3, 4, 5]);
}

#[test]
pub fn test_ptr_iter() {
    let arena = TypedArena::new();
    let a = arena.alloc(1);
    let b = arena.alloc(2);
    let c = arena.alloc(3);

    let mut iter = arena.ptr_iter();

    assert_eq!(iter.next().unwrap().as_ptr().cast_const(), a as *const _);
    assert_eq!(iter.next().unwrap().as_ptr().cast_const(), b as *const _);
    assert_eq!(iter.next().unwrap().as_ptr().cast_const(), c as *const _);
    assert!(iter.next().is_none());
}

#[test]
pub fn test_retain() {
    let mut arena = TypedArena::new();
    arena.alloc(1);
    arena.alloc(2);
    arena.alloc(3);

    arena.retain(|&x| x % 2 == 0);

    let mut iter = arena.iter();
    assert_eq!(*iter.next().unwrap(), 2);
    assert!(iter.next().is_none());
}

#[test]
pub fn test_retain_no_change() {
    let mut arena = TypedArena::new();
    arena.alloc(1);
    arena.alloc(2);
    arena.alloc(3);

    // Retain all elements
    arena.retain(|_| true);

    // All elements should still be in the arena
    assert_eq!(arena.into_vec(), vec![1, 2, 3]);
}

#[test]
pub fn test_retain_no_change_empty() {
    let mut arena = TypedArena::<u8>::new();

    // Empty arena should remain empty after retain
    arena.retain(|_| true);
    assert!(arena.into_vec().is_empty());
}

#[test]
pub fn test_retain_coalesce() {
    let mut arena = TypedArena::new();
    // 3, 6, 11, 22, 43, 86, 171, 342, 683, 1366 | 1355
    // Allocating the minimum # required for the arena to waste as much memory as possible
    // (10 items = 10 chunks), then we allocate just enough to fill the coalesced arena
    // (total = 4088; 8 + 16 + 32 + 64 + 128 + 256 + 512 + 1024 + 2048)
    let bad_sequence = (2..).map(|mut i| {
        let mut res = 1 << i;
        while i > 1 {
            i -= 2;
            res -= 1 << i;
        }
        res
    }).take(10).chain(once(1355));
    for i in bad_sequence {
        arena.alloc_from_iter_fast(vec![[i; PAGE / size_of::<usize>() / 8]; i]);
    }

    assert_eq!(arena.used_chunks.get(), 10);

    arena.retain(|_| true);

    assert_eq!(arena.used_chunks.get(), 9);
}

#[test]
pub fn test_iter_after_allocation() {
    let arena = TypedArena::new();
    arena.alloc(1);
    let mut iter = arena.iter();
    assert_eq!(*iter.next().unwrap(), 1);
    assert!(iter.next().is_none());

    // Allocating new elements after the iterator is created
    arena.alloc(2);
    arena.alloc(3);

    // The iterator should be able to handle new elements being added
    assert_eq!(*iter.next().unwrap(), 2);
    assert_eq!(*iter.next().unwrap(), 3);
    assert!(iter.next().is_none());
}

#[test]
pub fn test_alloc_zero_elements() {
    let arena = TypedArena::<usize>::new();
    let slice = arena.alloc_from_iter(vec![].into_iter());

    assert!(slice.is_empty());
    assert_eq!(arena.len(), 0);
    assert_eq!(arena.used_chunks.get(), 0);
}

#[test]
pub fn test_grow_in_small_increments() {
    let arena = TypedArena::new();
    for i in 1..=10000 {
        arena.alloc(i);
    }

    // Shouldn't have grown too much, as each allocation was small
    assert!(arena.chunks.borrow().len() < 20);
}

#[test]
pub fn test_grow_in_large_increments() {
    let arena = TypedArena::new();
    for _ in 1..=10 {
        let range: Vec<_> = (1..=HUGE_PAGE).collect();
        arena.alloc_from_iter(range.into_iter());
    }

    // Should have grown 10 times because each allocation was large
    assert_eq!(arena.chunks.borrow().len(), 10);
}

#[test]
pub fn test_grow_uneven() {
    let arena = TypedArena::new();
    let mut rand = SmallRng::seed_from_u64(9238157);
    for _ in 1..=100 {
        let range: Vec<_> = (1..=(10u32.pow(rand.gen_range(3..5) + 1))).collect();
        arena.alloc_from_iter(range.into_iter());
    }

    // Should have grown, but not 1000 times, because some allocations were large
    assert!(arena.chunks.borrow().len() > 10 && arena.chunks.borrow().len() < 90);
}

#[test]
pub fn test_alloc_raw_slice() {
    let arena = TypedArena::<u32>::new();
    let ptr = unsafe { arena.alloc_raw_slice(100) };

    // The returned pointer should not be null
    assert!(!ptr.is_null());
}

#[test]
pub fn test_alloc_a_lot() {
    let arena = TypedArena::<usize>::new();
    arena.alloc_from_iter(1..=1000000);
    assert_eq!(arena.len(), 1000000);
    // Still only 1 chunk
    assert_eq!(arena.used_chunks.get(), 1);
}

#[test]
pub fn test_len_after_allocations() {
    let arena = TypedArena::new();
    arena.alloc(1);
    arena.alloc(2);
    arena.alloc_from_iter(vec![3, 4, 5]);

    // The length should match the number of allocated elements
    assert_eq!(arena.len(), 5);

    arena.alloc(6);
    arena.alloc(7);
    assert_eq!(arena.len(), 7);
}

#[test]
pub fn test_len_after_big_allocations() {
    let arena = TypedArena::new();
    arena.alloc([1; 400]);
    arena.alloc([2; 400]);
    arena.alloc_from_iter(vec![[3; 400], [4; 400], [5; 400]]);

    // The length should match the number of allocated elements
    assert_eq!(arena.len(), 5);

    arena.alloc([6; 400]);
    arena.alloc([7; 400]);
    assert_eq!(arena.len(), 7);
}

#[test]
pub fn test_large_allocations() {
    let arena = TypedArena::new();
    for i in 0..10_000 {
        let arr = [i; 1024];
        arena.alloc(arr);
    }

    // The length should match the number of allocated elements
    assert_eq!(arena.len(), 10_000);

    for i in 10_000..11_000 {
        let vec = vec![[i; 1024]; 32];
        arena.alloc_from_iter(vec);
    }
    assert_eq!(arena.len(), 42_000);
}

#[test]
pub fn test_iter_large_allocations_uneven() {
    let arena = TypedArena::new();
    let mut rand = SmallRng::seed_from_u64(1234898324);

    for _ in 0..100 {
        let len = rand.gen_range(0..20);
        let vec = (0..len).map(|_| rand.gen::<u16>().saturating_add(1)).collect::<Vec<_>>();
        let vec = arena.alloc_from_iter(vec);
        assert!(vec.iter().all(|e| *e > 0));
    }

    // Test iterator
    let mut iter = arena.iter();
    let mut total_elems = 0;
    while let Some(elem) = iter.next_ref() {
        total_elems += 1;
        assert!(*elem > 0);
    }

    // The length should match the number of iterated elements
    assert_eq!(arena.len(), total_elems);
}

#[test]
pub fn test_foo_bar() {
    let arena = TypedArena::new();
    let foos = vec!["foo1", "foo2", "foo3", "foo4", "foo5"];
    let bars = vec!["bar1", "bar2", "bar3", "bar4", "bar5"];

    arena.alloc_from_iter(foos);
    arena.alloc_from_iter(bars);

    assert_eq!(arena.len(), 10);

    let mut iter = arena.iter();
    for _ in 0..5 {
        assert!(iter.next_ref().unwrap().starts_with("foo"));
    }
    for _ in 0..5 {
        assert!(iter.next_ref().unwrap().starts_with("bar"));
    }
}

#[test]
pub fn test_retain_again() {
    let mut arena = TypedArena::new();
    for i in 1..=100 {
        arena.alloc(i);
    }

    arena.retain(|&x| x % 3 == 0);

    let mut iter = arena.iter();
    while let Some(&elem) = iter.next_ref() {
        assert_eq!(elem % 3, 0);
    }
}

#[test]
pub fn test_allocation_pattern() {
    let arena = TypedArena::new();
    for i in 0..100 {
        if i % 2 == 0 {
            let arr = [i; 128];
            arena.alloc(arr);
        } else {
            let vec = vec![[i; 128]; 128];
            arena.alloc_from_iter(vec);
        }
    }

    // The length should match the number of allocated elements
    assert_eq!(arena.len(), 50 * 128 + 50);
}

#[test]
pub fn test_reuse_of_empty_chunks() {
    let mut arena = TypedArena::new();
    let large_number = 1_000;

    // Fill the arena with large_number of elements, each of size 4096.
    for _ in 0..large_number {
        arena.alloc([0u8; PAGE]);
    }

    // We should have at least large_number chunks (or less if the chunk size has increased).
    let initial_chunk_count = arena.chunks.borrow().len();

    // Clear all the data from the arena.
    arena.retain(|_| false);

    // The chunks should still be there, but the used_chunks should be 0
    assert_eq!(arena.chunks.borrow().len(), initial_chunk_count);
    assert_eq!(arena.used_chunks.get(), 0);

    // Now, allocate the data again. This should reuse the chunks without allocating new ones.
    for _i in 0..large_number {
        arena.alloc([0u8; PAGE]);
    }

    // The number of chunks should not have increased.
    assert_eq!(arena.chunks.borrow().len(), initial_chunk_count);
}

// TODO: This test fails sometimes when run with all others (chunks == 10), but never independently
//   and not consistently
#[test]
pub fn test_reuse_of_some_empty_chunks() {
    let mut arena = TypedArena::new();

    // Fill the arena with large_number of elements, each of size 4096.
    for i in 0..1_000 {
        arena.alloc([i; PAGE / (size_of::<u32>() / size_of::<u8>())]);
    }

    // We should have at least large_number chunks (or less if the chunk size has increased).
    let initial_chunk_count = arena.chunks.borrow().len();

    // Clear some of the data from the arena.
    arena.retain(|e| e[0] % 4 == 0);

    // The chunks should still be there, but some of them should be unused
    assert_eq!(arena.chunks.borrow().len(), initial_chunk_count);
    // Coalescing means we will use less chunks, but we'll still use some.
    // With { type_size = 1 page, num_allocations = 1_000 }, we should use 8
    // (2^9 - 1 = 255, we have 250 entries)
    assert_eq!(arena.used_chunks.get(), 8);

    // Now, allocate the data again. This should reuse the chunks and only allocate some new ones.
    for i in 0..5_000 {
        arena.alloc([i; PAGE / (size_of::<u32>() / size_of::<u8>())]);
    }

    // The number of chunks should have increased, but not doubled.
    assert_eq!(arena.chunks.borrow().len(), 17);
}

#[test]
pub fn test_arena_with_struct() {
    #[derive(Debug, PartialEq, Eq)]
    struct TestStruct {
        a: u32,
        b: u32,
    }

    let arena = TypedArena::new();
    for i in 0..100 {
        arena.alloc(TestStruct { a: i, b: 2 * i });
    }

    // Check that all elements are present and correct.
    let mut iter = arena.iter();
    for i in 0..100 {
        let expected = TestStruct { a: i, b: 2 * i };
        assert_eq!(*iter.next_ref().unwrap(), expected);
    }
}

#[test]
pub fn test_alloc_larger_than_huge_page() {
    let arena = TypedArena::new();

    // Can't create objects on the stack larger than HUGE_PAGE, but we can allocate a slice from the
    // heap
    arena.alloc_from_iter_fast(vec![0u8; HUGE_PAGE + 1]);
    arena.alloc_from_iter_fast(vec![1u8; HUGE_PAGE + 1]);

    assert_eq!(arena.chunks.borrow().len(), 2);
}

#[test]
pub fn test_arena_with_zst() {
    // Zero-sized types
    struct Zst;

    let arena = TypedArena::new();
    for _ in 0..1_000 {
        arena.alloc(Zst);
    }

    assert_eq!(arena.len(), 1_000);
    assert!(arena.ptr.get().is_null());
    assert!(arena.end.get().is_null());
    assert!(arena.chunks.borrow().is_empty());
    assert_eq!(arena.used_chunks.get(), 0);
}

#[test]
pub fn test_arena_with_zst_beyond_page() {
    struct Zst;

    let arena = TypedArena::new();
    for _ in 0..(HUGE_PAGE - 1) {
        arena.alloc(Zst);
    }

    assert_eq!(arena.len(), HUGE_PAGE - 1);
    assert!(arena.ptr.get().is_null());
    assert!(arena.end.get().is_null());
    assert!(arena.chunks.borrow().is_empty());
    assert_eq!(arena.used_chunks.get(), 0);
}

#[test]
pub fn test_arena_with_zst_iter() {
    struct Zst;

    let arena = TypedArena::new();
    for _ in 0..100 {
        arena.alloc(Zst);
    }

    // Iterate over the items and ensure the expected number of items are present.
    let mut iter = arena.iter();
    for _ in 0..100 {
        assert!(iter.next_ref().is_some());
    }

    // After 100 elements, the iterator should return None.
    assert!(iter.next_ref().is_none());
}

#[test]
pub fn test_arena_intermingled_allocations() {
    let arena = TypedArena::new();
    let mut rand = SmallRng::seed_from_u64(28573469145);

    for _i in 0..100 {
        arena.alloc(false);
        arena.alloc_from_iter(repeat(true).take(10usize.pow(rand.gen_range(0..3) + 1)));
    }

    assert!(arena.len() > 200);
}

#[test]
pub fn test_arena_zst_retain() {
    struct Zst;

    let mut arena = TypedArena::new();

    for _ in 0..1_000 {
        arena.alloc(Zst);
    }

    let mut do_retain = true;
    arena.retain(|_| {
        do_retain = !do_retain;
        do_retain
    });

    assert_eq!(arena.len(), 500);

    for _ in 0..250 {
        arena.alloc(Zst);
    }

    assert_eq!(arena.len(), 750);
}
