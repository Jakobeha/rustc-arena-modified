use std::cmp::max;
use std::iter::zip;
use std::mem::size_of;
use std::rc::Rc;

use once_cell::unsync::Lazy;
use rand::rngs::SmallRng;
use rand::seq::SliceRandom;
use rand::{Rng, SeedableRng};

use crate::TypedArena;

use super::*;

/// Test basic `alloc` functionality and check length
#[test]
fn test_alloc_and_len() {
    let arena = SlabArena::<usize>::new();
    let item1 = arena.alloc(1);
    let item2 = arena.alloc(2);
    assert_eq!(*item1, 1);
    assert_eq!(*item2, 2);
    assert_eq!(arena.arena.len(), 2);
}

/// Test taking an item from the RefMut and ensuring its removal from the arena
#[test]
fn test_take_front_loaded() {
    let mut arena = SlabArena::<usize>::new();
    let mut item_refs = Vec::new();
    let mut items = Vec::new();

    for i in 0..10 {
        item_refs.push(arena.alloc(i));
    }
    assert_eq!(arena.arena.len(), item_refs.len());
    assert_eq!(arena.next_free.get(), None);
    for item_ref in item_refs {
        items.push(item_ref.take());
    }
    assert_eq!(arena.arena.len(), items.len());
    let last_entry = NonNull::from(arena.arena.iter_mut().last().unwrap());
    assert_eq!(arena.next_free.get(), Some(last_entry));
    for entry in &mut arena.arena {
        assert!(entry.is_vacant());
    }

    assert_eq!(items, (0..10).collect::<Vec<_>>());
}

/// Test taking an item and reusing its entry
#[test]
fn test_take_and_reuse() {
    let mut arena = SlabArena::<usize>::new();
    let mut items = Vec::new();

    for i in 0..10 {
        let item_ref = arena.alloc(i);
        items.push(item_ref.take());
        assert_eq!(arena.arena.len(), 1);
        let first_entry = NonNull::from(arena.arena.iter_mut().next().unwrap());
        assert_eq!(arena.next_free.get(), Some(first_entry));
        let entry = arena.arena.iter_mut().next().unwrap();
        assert!(entry.is_vacant());
    }
    assert_eq!(arena.arena.len(), 1);
    let first_entry = NonNull::from(arena.arena.iter_mut().next().unwrap());
    assert_eq!(arena.next_free.get(), Some(first_entry));

    assert_eq!(items, (0..10).collect::<Vec<_>>());
}

/// Test leaking an item
#[test]
fn test_leak() {
    let mut arena = SlabArena::<String>::new();

    let item1 = arena.alloc(String::from("hello"));
    let leaked_item1 = item1.leak();
    assert_eq!(leaked_item1, "hello");

    let mut iter_mut = arena.arena.iter_mut();

    // Verify that the leaked item is still present in the underlying `TypedArena`
    if let Some(Entry::Occupied { value }) = iter_mut.next() {
        assert_eq!(value, "hello");
    } else {
        panic!("Expected 1 entry in Arena");
    }

    assert!(iter_mut.next().is_none());
}

/// Test converting a RefMut into an UnsafeRef and back to a RefMut
#[test]
fn test_convert_unsafe() {
    let arena = SlabArena::<usize>::new();

    let item1 = arena.alloc(1);
    let item1_as_unsafe_ref = item1.into_unsafe();

    let item1_as_safe_ref = unsafe { item1_as_unsafe_ref.into_safe(&arena) };

    // Checking the length to ensure no unexpected changes
    assert_eq!(arena.arena.len(), 1);

    // Convert back to the RefMut and check that it still holds the correct value
    assert_eq!(*item1_as_safe_ref, 1);
}

#[test]
fn test_alloc_and_unsafe_as_ref() {
    let mut arena = SlabArena::new();
    let val = 42;
    let entry_ptr = arena.alloc(val);
    let returned_entry = entry_ptr.into_unsafe();
    let entry_val = unsafe { *returned_entry.as_ref() };
    assert_eq!(entry_val, val);
    match arena.arena.iter_mut().next() {
        Some(Entry::Occupied { value }) => assert_eq!(*value, entry_val),
        _ => panic!("Expected occupied entry in Arena"),
    }
    assert_eq!(arena.next_free.get(), None);
}

#[test]
fn test_alloc_and_unsafe_take() {
    let mut arena = SlabArena::new();
    let val = 42;
    let entry_ptr = arena.alloc(val);
    let returned_entry = entry_ptr.into_unsafe();
    let entry_val = unsafe { returned_entry.take(&arena) };
    assert_eq!(entry_val, val);
    assert!(arena.arena.iter_mut().next().unwrap().is_vacant());
    let first_entry = NonNull::from(arena.arena.iter_mut().next().unwrap());
    assert_eq!(arena.next_free.get(), Some(first_entry));
}

#[test]
fn test_drop_and_reuse_ptr() {
    let arena = SlabArena::new();
    let val = "value";
    let val2 = "value2";
    let entry1 = arena.alloc(val);
    let entry1_ptr = entry1.as_ptr();
    drop(entry1);
    let entry2 = arena.alloc(val2);
    let entry_ptr2 = entry2.as_ptr();
    assert_eq!(entry1_ptr, entry_ptr2);
}

#[test]
fn test_discard_and_reuse_ptr() {
    let arena = SlabArena::new();
    let val = 42;
    let val2 = 24;
    let entry1 = arena.alloc(val);
    let unsafe_entry1 = entry1.into_unsafe();
    let entry1_ptr = unsafe { unsafe_entry1.as_ptr() };
    unsafe {
        unsafe_entry1.discard(&arena);
    }
    let entry2 = arena.alloc(val2);
    let entry2_ptr = entry2.as_ptr();
    assert_eq!(entry2_ptr, entry1_ptr);
}

#[test]
fn test_alloc_twice_and_dont_reuse_ptr() {
    let arena = SlabArena::new();
    let val1 = 1;
    let val2 = 2;
    let entry1 = arena.alloc(val1);
    let entry1_ptr = entry1.as_ptr().as_ptr();
    let entry2 = arena.alloc(val2);
    let entry2_ptr = entry2.as_ptr().as_ptr();
    assert_eq!(*entry1, val1);
    assert_eq!(*entry2, val2);
    assert_eq!(entry2_ptr, unsafe {
        entry1_ptr
            .cast::<u8>()
            .add(size_of::<Entry<i32>>())
            .cast::<i32>()
    });
}

#[test]
fn test_alloc_leak_and_dont_reuse_ptr() {
    let arena = SlabArena::new();
    let val1 = 1;
    let val2 = 2;
    let entry1 = arena.alloc(val1);
    let entry1_ptr = entry1.as_ptr().as_ptr();
    entry1.leak();
    let entry2 = arena.alloc(val2);
    let entry2_ptr = entry2.as_ptr().as_ptr();
    assert_eq!(*entry2, val2);
    assert_eq!(entry2_ptr, unsafe {
        entry1_ptr
            .cast::<u8>()
            .add(size_of::<Entry<i32>>())
            .cast::<i32>()
    });
}

/// Test multiple operations including take, leak, and convert unsafe together
#[test]
fn test_multiple_operations_large() {
    let arena = SlabArena::<String>::new();
    let mut rng = SmallRng::seed_from_u64(0xf00ba7);

    struct ItemRefs<'a> {
        r#unsafe: UnsafeRef<String>,
        leaked: Option<&'a mut String>,
        safe: Option<RefMut<'a, String>>,
    }
    fn occupied_len(arena: &SlabArena<String>) -> usize {
        arena
            .arena
            .ptr_iter()
            .map(|e| unsafe { e.as_ref() })
            .filter(|e| e.is_occupied())
            .count()
    }

    let mut item_refs = Vec::new();

    for _ in 0..10 {
        let old_occupied_len = occupied_len(&arena);
        let old_len = arena.arena.len();

        let mut items = (0..10).map(|i| arena.alloc(format!("item_{}", i)));

        for _ in 0..rng.gen_range(0..10) {
            let item = items.next().unwrap();
            let unsafe_item = item.into_unsafe();
            let item = unsafe { unsafe_item.into_safe(&arena) };
            item_refs.push(ItemRefs {
                r#unsafe: unsafe_item,
                leaked: Some(item.leak()),
                safe: None,
            });
        }

        for item in items {
            let unsafe_item = item.into_unsafe();
            let item = unsafe { unsafe_item.into_safe(&arena) };
            item_refs.push(ItemRefs {
                r#unsafe: unsafe_item,
                leaked: None,
                safe: Some(item),
            });
        }

        let new_occupied_len = occupied_len(&arena);
        let new_len = arena.arena.len();
        assert_eq!(new_occupied_len, old_occupied_len + item_refs.len());
        assert_eq!(new_len, max(old_occupied_len + item_refs.len(), old_len));

        let mut num_refs = 0;
        for item_ref in &mut item_refs {
            if let Some(leaked) = item_ref.leaked.as_mut() {
                assert_eq!(*leaked, unsafe { item_ref.r#unsafe.as_ref() });
                leaked.push_str("_foo");
                assert_eq!(*leaked, unsafe { item_ref.r#unsafe.as_ref() });
            }
            if let Some(mut safe) = item_ref.safe.take() {
                assert_eq!(&*safe, &*unsafe { item_ref.r#unsafe.as_ref() });
                safe.push_str("_bar");
                assert_eq!(&*safe, &*unsafe { item_ref.r#unsafe.as_ref() });
                num_refs += 1;
            }
        }

        let new_occupied_len2 = occupied_len(&arena);
        let new_len2 = arena.arena.len();
        assert_eq!(new_occupied_len2, new_occupied_len - num_refs);
        assert_eq!(new_len2, new_len);

        for item_ref in &mut item_refs {
            if let Some(leaked) = item_ref.leaked.as_mut() {
                assert_eq!(*leaked, unsafe { item_ref.r#unsafe.as_ref() });
                leaked.push_str("_baz");
                assert_eq!(*leaked, unsafe { item_ref.r#unsafe.as_ref() });
            }
        }

        item_refs.clear();
        let new_occupied_len3 = occupied_len(&arena);
        let new_len3 = arena.arena.len();
        assert_eq!(new_occupied_len3, new_occupied_len2);
        assert_eq!(new_len3, new_len2);
    }
}

/// Test allocating a new SlabArena using String type and filling it with 1000 strings
#[test]
fn test_fill_with_1000_strings() {
    let arena = SlabArena::<String>::new();

    for i in 0..1_000 {
        let data = format!("entry_{}", i);
        let mut_ref = arena.alloc(data).leak();
        assert_eq!(*mut_ref, format!("entry_{}", i));
    }
    assert_eq!(arena.arena.len(), 1_000);
}

/// Stress test performing allocations, takes, and leaks "concurrently" (but deterministically)
#[test]
fn stress_test_concurrent_operations() {
    const NUM_COROUTINES: usize = 10;
    const NUM_OPERATIONS_PER_COROUTINE: usize = 1_000;

    // Boilerplate for ops, there could be more for cleaner ops
    type DynLazy<'a, T> = Rc<Lazy<T, Box<dyn FnOnce() -> T + 'a>>>;
    enum Op<'a> {
        Alloc(DynLazy<'a, RefMut<'a, usize>>),
        Deref(DynLazy<'a, &'a usize>),
        Do(DynLazy<'a, ()>),
    }
    impl<'a> Op<'a> {
        fn force(&self) {
            match self {
                Op::Alloc(res) => {
                    Lazy::force(res);
                }
                Op::Deref(res) => {
                    Lazy::force(res);
                }
                Op::Do(res) => {
                    Lazy::force(res);
                }
            }
        }
    }
    fn alloc<'a>(
        ops: &TypedArena<Op<'a>>,
        f: impl FnOnce() -> RefMut<'a, usize> + 'a,
    ) -> DynLazy<'a, RefMut<'a, usize>> {
        let Op::Alloc(res) = ops.alloc(Op::Alloc(Rc::new(Lazy::new(Box::new(f))))) else {
            unreachable!()
        };
        res.clone()
    }
    fn deref<'a>(
        ops: &TypedArena<Op<'a>>,
        f: impl FnOnce() -> &'a usize + 'a,
    ) -> DynLazy<'a, &'a usize> {
        let Op::Deref(res) = ops.alloc(Op::Deref(Rc::new(Lazy::new(Box::new(f))))) else {
            unreachable!()
        };
        res.clone()
    }
    fn r#do<'a>(ops: &TypedArena<Op<'a>>, f: impl FnOnce() + 'a) -> DynLazy<'a, ()> {
        let Op::Do(res) = ops.alloc(Op::Do(Rc::new(Lazy::new(Box::new(f))))) else {
            unreachable!()
        };
        res.clone()
    }

    // Data
    let arena = SlabArena::<usize>::new();
    let arena_ref = &arena;
    let ops = TypedArena::<Op<'_>>::new();

    // Add ops
    for i in 0..NUM_COROUTINES {
        for j in 0..NUM_OPERATIONS_PER_COROUTINE {
            let val1 = i * NUM_OPERATIONS_PER_COROUTINE + j * 2;
            let val2 = i * NUM_OPERATIONS_PER_COROUTINE + j * 2 + 1;

            let a = alloc(&ops, move || arena_ref.alloc(val1));
            let b = alloc(&ops, move || arena_ref.alloc(val2));

            let a2 = a.clone();
            r#do(&ops, move || assert_eq!(***a2, val1));
            r#do(&ops, move || assert_eq!(***b, val2));

            let a_leaked = deref(&ops, move || unsafe { a.as_ptr().as_ref() });

            r#do(&ops, move || assert_eq!(***a_leaked, val1));
        }
    }

    // Run ops. Because `Lazy`, dependent ops will run their dependencies and then when we get to
    // the dependencies running will just do nothing.

    let mut ops_refs = ops.iter().collect::<Vec<_>>();
    ops_refs.shuffle(&mut SmallRng::seed_from_u64(0xf00ba7));
    for op in ops_refs {
        op.force();
    }
}

/// Test guaranteeing the order of allocations matches the arena indexes as specified
#[test]
fn test_allocation_order() {
    let mut arena = SlabArena::<usize>::new();

    let item1 = arena.alloc(1).into_unsafe();
    let _item2 = arena.alloc(2).into_unsafe();
    let item3 = arena.alloc(3).into_unsafe();

    let mut arena_iter = arena.arena.iter_mut();
    assert!(matches!(
        arena_iter.next().unwrap(),
        Entry::Occupied { value: 1 }
    ));
    assert!(matches!(
        arena_iter.next().unwrap(),
        Entry::Occupied { value: 2 }
    ));
    assert!(matches!(
        arena_iter.next().unwrap(),
        Entry::Occupied { value: 3 }
    ));
    assert!(arena_iter.next().is_none());

    // Now, removing an entry and checking the order again after another allocation
    unsafe { item3.take(&arena) };
    unsafe { item1.take(&arena) };
    let _item4 = arena.alloc(4).into_unsafe();

    let mut arena_iter = arena.arena.iter_mut();
    assert!(matches!(
        arena_iter.next().unwrap(),
        Entry::Occupied { value: 4 }
    ));
    assert!(matches!(
        arena_iter.next().unwrap(),
        Entry::Occupied { value: 2 }
    ));
    assert!(matches!(
        arena_iter.next().unwrap(),
        Entry::Vacant { next_free: None }
    ));
    assert!(arena_iter.next().is_none());
}

/// Test iter_mut results matching the expected occupied entries in the underlying `TypedArena`
#[test]
fn test_iter_mut_results() {
    let mut arena = SlabArena::<usize>::new();

    let items = (0..10)
        .map(|i| arena.alloc(i).into_unsafe())
        .collect::<Vec<_>>();
    let iter_mut_items = arena.arena.iter_mut().collect::<Vec<_>>();

    assert_eq!(iter_mut_items.len(), items.len());

    for (iter_mut_item, item) in zip(iter_mut_items, items) {
        // We have to destroy the &mut reference in `iter_mut_item` before we read `item`
        let Entry::Occupied { value: iter_mut_item } = iter_mut_item else {
            panic!("Expected occupied entry");
        };
        let iter_mut_item = *iter_mut_item;
        let item = unsafe { *item.as_ref() };
        assert_eq!(iter_mut_item, item);
    }
}

/// Test the discard operation to ensure that it removes the currently reference entry
#[test]
fn test_discard_and_verify_removal() {
    let mut arena = SlabArena::<usize>::new();
    let unsafe_entry1 = arena.alloc(1).into_unsafe();
    let unsafe_entry2 = arena.alloc(2).into_unsafe();
    let unsafe_entry3 = arena.alloc(3).into_unsafe();

    assert_eq!(unsafe { unsafe_entry1.as_ref() }, &1);
    assert_eq!(unsafe { unsafe_entry2.as_ref() }, &2);
    assert_eq!(unsafe { unsafe_entry3.as_ref() }, &3);

    // Discard the second and third entries and ensure their removal
    unsafe { unsafe_entry2.discard(&arena) };
    unsafe { unsafe_entry3.discard(&arena) };

    let mut iter_mut = arena.arena.iter_mut();

    match iter_mut.next().expect("expected the first entry to exist") {
        Entry::Occupied { value } => assert_eq!(value, &1),
        Entry::Vacant { .. } => panic!("Expected the first entry to be occupied"),
    };

    match iter_mut.next().expect("expected the second entry to exist") {
        Entry::Occupied { .. } => panic!("Expected the second entry to be vacant"),
        Entry::Vacant { next_free } => assert!(next_free.is_none()),
    }

    match iter_mut.next().expect("expected the third entry to exist") {
        Entry::Occupied { .. } => panic!("Expected the third entry to be vacant"),
        Entry::Vacant { next_free } => assert!(next_free.is_some()),
    }

    assert!(iter_mut.next().is_none());
}

/// Test `retain` functionality, using underlying [TypedArena] iteration as the ground truth.
#[test]
fn test_retain() {
    let mut arena = SlabArena::new();

    for i in 0..10000 {
        arena.alloc(i).leak();
    }

    arena.retain(|x| *x % 5 != 0);

    let mut num_vacant = 0;
    let mut num_occupied = 0;
    for entry in &mut arena.arena {
        match entry {
            Entry::Occupied { value } => {
                assert_ne!(*value % 5, 0);
                num_occupied += 1;
            }
            Entry::Vacant { .. } => num_vacant += 1,
        }
    }
    assert_eq!(num_occupied, 8000);
    assert_eq!(num_vacant, 2000);
}

/// Test `retain_shared` functionality, using underlying [TypedArena] iteration as the ground truth.
#[test]
fn test_retain_shared() {
    let mut arena = SlabArena::new();
    let mut retained = Vec::new();

    for i in 0..10000 {
        let r#ref = arena.alloc(i);
        if i % 5 == 0 {
            retained.push(r#ref.leak());
        }
    }
    assert_eq!(retained.len(), 2000, "obvious case failed?");

    unsafe { arena.retain_shared(|x| *x % 5 == 0) };

    let mut num_vacant = 0;
    let mut num_occupied = 0;
    for entry in &mut arena.arena {
        match entry {
            Entry::Occupied { value } => {
                assert_eq!(*value % 5, 0);
                num_occupied += 1;
            }
            Entry::Vacant { .. } => num_vacant += 1,
        }
    }
    assert_eq!(num_occupied, 2000);
    assert_eq!(num_vacant, 8000);

    // Ensure that the retained references are still valid
    for i in 0..2000 {
        retained[i] += 2;
        assert_eq!(*retained[i], i * 5 + 2);
    }

    // Make it clear retained can no longer be held at the calls to retained_shared
    drop(retained);

    arena.retain(|x| *x % 5 == 0);
    // Just to be extra safe
    unsafe { arena.retain_shared(|x| *x % 5 == 0) };

    for entry in &mut arena.arena {
        if let Entry::Occupied { value } = entry {
            panic!(
                "Expected all entries to be vacant, but at least one is occupied: {}",
                value
            );
        }
    }
}
