#![cfg_attr(feature = "nightly", feature(rustc_private))]

extern crate rand;
#[cfg(feature = "nightly")]
extern crate rustc_arena;
#[cfg(feature = "nightly")]
extern crate rustc_driver;

use rand::{rngs::SmallRng, Rng, SeedableRng};
use rustc_arena_modified::typed_arena::RefMutability;
use std::marker::PhantomData;

// region benchmark abstraction / implementation
trait Bencher {
    fn black_box<T>(x: T) -> T;
    fn iter<Return>(&mut self, f: impl FnMut() -> Return);
    fn iter_batched<I, O>(&mut self, setup: impl FnMut() -> I, routine: impl FnMut(I) -> O);
}

/// Doesn't actually bench, runs the benchmarks only to test and debug them.
#[cfg(not(feature = "bench"))]
struct MockBencher;

#[cfg(feature = "bench")]
impl<'a, M: criterion::measurement::Measurement> Bencher for criterion::Bencher<'a, M> {
    fn black_box<T>(x: T) -> T {
        criterion::black_box(x)
    }

    fn iter<Return>(&mut self, f: impl FnMut() -> Return) {
        self.iter(f)
    }

    fn iter_batched<I, O>(&mut self, setup: impl FnMut() -> I, routine: impl FnMut(I) -> O) {
        self.iter_batched(setup, routine, criterion::BatchSize::LargeInput)
    }
}

#[cfg(not(feature = "bench"))]
impl Bencher for MockBencher {
    fn black_box<T>(x: T) -> T {
        x
    }

    fn iter<Return>(&mut self, mut f: impl FnMut() -> Return) {
        f();
    }

    fn iter_batched<I, O>(
        &mut self,
        mut setup: impl FnMut() -> I,
        mut routine: impl FnMut(I) -> O,
    ) {
        routine(setup());
    }
}
// endregion

// region arena abstraction and implementation
trait TypedArena<T>: Default {
    type Iter<'a>: Iterator<Item = &'a mut T>
    where
        Self: 'a,
        T: 'a;

    fn alloc(&self, value: T) -> &T;
    fn alloc_from_iter(&self, values: impl Iterator<Item = T>) -> &[T];
    fn iter(&mut self) -> Self::Iter<'_>;
    fn into_vec(self) -> Vec<T>;
    fn supports(bench_fn: &'static str) -> bool;
}

impl<T, RM: RefMutability> TypedArena<T> for rustc_arena_modified::TypedArenaGen<T, RM> {
    type Iter<'a> = rustc_arena_modified::typed_arena::IterMut<'a, T> where T: 'a;

    fn alloc(&self, value: T) -> &T {
        RM::as_ref(self.alloc(value))
    }

    fn alloc_from_iter(&self, values: impl Iterator<Item = T>) -> &[T] {
        RM::as_slice_ref(self.alloc_from_iter_reg(values))
    }

    fn iter(&mut self) -> Self::Iter<'_> {
        self.iter_mut()
    }

    fn into_vec(self) -> Vec<T> {
        self.into_vec()
    }

    fn supports(_bench_fn: &'static str) -> bool {
        true
    }
}

#[cfg(feature = "slab")]
impl<T> TypedArena<T> for rustc_arena_modified::SlabArena<T> {
    type Iter<'a> = std::iter::Empty<&'a mut T> where T: 'a;

    fn alloc(&self, value: T) -> &T {
        self.alloc(value).leak()
    }

    fn alloc_from_iter(&self, _values: impl Iterator<Item = T>) -> &[T] {
        panic!("rustc_arena_modified::SlabArena doesn't implement alloc_from_iter")
    }

    fn iter(&mut self) -> Self::Iter<'_> {
        panic!("rustc_arena_modified::SlabArena doesn't implement iter")
    }

    fn into_vec(self) -> Vec<T> {
        panic!("rustc_arena_modified::SlabArena doesn't implement into_vec")
    }

    fn supports(bench_fn: &'static str) -> bool {
        match bench_fn {
            "bench_alloc" => true,
            "bench_alloc_from_iter" | "bench_iter" | "bench_into_vec" => false,
            _ => panic!("Unknown bench function: {}", bench_fn),
        }
    }
}

#[cfg(feature = "nightly")]
impl<T> TypedArena<T> for rustc_arena::TypedArena<T> {
    type Iter<'a> = std::iter::Empty<&'a mut T> where T: 'a;

    fn alloc(&self, value: T) -> &T {
        self.alloc(value)
    }

    fn alloc_from_iter(&self, values: impl Iterator<Item = T>) -> &[T] {
        self.alloc_from_iter(values)
    }

    fn iter(&mut self) -> Self::Iter<'_> {
        panic!("rustc_arena::TypedArena doesn't implement iter")
    }

    fn into_vec(self) -> Vec<T> {
        panic!("rustc_arena::TypedArena doesn't implement into_vec")
    }

    fn supports(bench_fn: &'static str) -> bool {
        match bench_fn {
            "bench_alloc" | "bench_alloc_from_iter" => true,
            "bench_iter" | "bench_into_vec" => false,
            _ => panic!("Unknown bench function: {}", bench_fn),
        }
    }
}

impl<T> TypedArena<T> for typed_arena::Arena<T> {
    type Iter<'a> = typed_arena::IterMut<'a, T> where T: 'a;

    fn alloc(&self, value: T) -> &T {
        self.alloc(value)
    }

    fn alloc_from_iter(&self, values: impl Iterator<Item = T>) -> &[T] {
        self.alloc_extend(values)
    }

    fn iter(&mut self) -> Self::Iter<'_> {
        self.iter_mut()
    }

    fn into_vec(self) -> Vec<T> {
        self.into_vec()
    }

    fn supports(_bench_fn: &'static str) -> bool {
        true
    }
}

/// Instead of allocating to an arena, we just allocate and leak the memory.
struct AllocAndLeak<T>(PhantomData<T>);

impl<T> Default for AllocAndLeak<T> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<T> TypedArena<T> for AllocAndLeak<T> {
    type Iter<'a> = std::iter::Empty<&'a mut T> where T: 'a;

    fn alloc(&self, value: T) -> &T {
        Box::leak(Box::new(value))
    }

    fn alloc_from_iter(&self, values: impl Iterator<Item = T>) -> &[T] {
        Box::leak(values.collect::<Vec<_>>().into_boxed_slice())
    }

    fn iter(&mut self) -> Self::Iter<'_> {
        panic!("AllocAndLeak \"arena\" doesn't implement iter")
    }

    fn into_vec(self) -> Vec<T> {
        panic!("AllocAndLeak \"arena\" doesn't implement into_vec")
    }

    fn supports(bench_fn: &'static str) -> bool {
        match bench_fn {
            "bench_alloc" | "bench_alloc_from_iter" => true,
            "bench_iter" | "bench_into_vec" => false,
            _ => panic!("Unknown bench function: {}", bench_fn),
        }
    }
}
// endregion

trait Benchmarks: Bencher {
    fn bench_alloc<T: TypedArena<usize>>(&mut self, n_allocations: usize) {
        let mut rng = SmallRng::seed_from_u64(42);
        let arena = T::default();

        self.iter(|| {
            for _ in 0..n_allocations {
                Self::black_box(arena.alloc(rng.gen()));
            }
        });
    }

    fn bench_alloc_from_iter<T: TypedArena<usize>>(
        &mut self,
        n_allocations: usize,
        max_iter_size: usize,
    ) {
        let mut rng = SmallRng::seed_from_u64(42);
        let arena = T::default();

        self.iter(|| {
            let mut i = 0;
            while i < n_allocations {
                let iter_size = rng.gen_range(0..max_iter_size);
                Self::black_box(arena.alloc_from_iter((0..iter_size).map(|_| rng.gen())));
                i += iter_size;
            }
        });
    }

    fn bench_iter<T: TypedArena<usize>>(&mut self, n_allocations: usize) {
        let mut rng = SmallRng::seed_from_u64(42);
        let mut arena = T::default();

        for _ in 0..n_allocations {
            arena.alloc(rng.gen());
        }

        self.iter(|| {
            for i in arena.iter() {
                Self::black_box(i);
            }
        });
    }

    fn bench_into_vec<T: TypedArena<usize>>(&mut self, n_allocations: usize) {
        let mut rng = SmallRng::seed_from_u64(42);

        self.iter_batched(
            || {
                let arena = T::default();
                for _ in 0..n_allocations {
                    arena.alloc(rng.gen());
                }
                arena
            },
            |arena| Self::black_box(arena.into_vec()),
        );
    }
}

impl<B: Bencher> Benchmarks for B {}

macro_rules! generate_bench_group {
    ($bench_name:ident: $bench_fn:ident $bench_args:tt, {
        $($(#[$attr:meta])? $arena_name:ident: $arena_ty:ty),* $(,)?
    }) => {
        #[cfg(feature = "bench")]
        fn $bench_name(c: &mut criterion::Criterion) {
            #[allow(unused_mut)]
            let mut group = c.benchmark_group(stringify!($bench_name));
            $(
                $(#[$attr])?
                if <$arena_ty as TypedArena<_>>::supports(stringify!($bench_fn)) {
                    group.bench_function(
                        stringify!($arena_name),
                        |b| b.$bench_fn::<$arena_ty> $bench_args,
                    );
                }
            )*
            group.finish();
        }

        #[cfg(not(feature = "bench"))]
        mod $bench_name {
            use super::*;

            $(
                $(#[$attr])?
                #[test]
                fn $arena_name() {
                    if <$arena_ty as TypedArena<_>>::supports(stringify!($bench_fn)) {
                        MockBencher.$bench_fn::<$arena_ty> $bench_args;
                    }
                }
            )*
        }
    }
}

macro_rules! generate_benches {
    ($($bench_name:ident: $bench_fn:ident($($bench_arg:expr),*)),* $(,)?) => {
        #[cfg(feature = "bench")]
        criterion::criterion_group! {
            name = benches;
            config = criterion::Criterion::default().sample_size(sample_size());
            targets = $($bench_name),*
        }

        $(
            generate_bench_group!($bench_name: $bench_fn($($bench_arg),*), {
                rustc_arena_modified: rustc_arena_modified::TypedArena<usize>,
                #[cfg(feature = "slab")]
                slab_arena: rustc_arena_modified::SlabArena<usize>,
                #[cfg(feature = "nightly")]
                rustc_arena: rustc_arena::TypedArena<usize>,
                typed_arena: typed_arena::Arena<usize>,
                alloc_and_leak: AllocAndLeak<usize>,
            });
        )*
    };
}

#[cfg(feature = "bench")]
fn sample_size() -> usize {
    std::env::var("SAMPLE_SIZE")
        .ok()
        .filter(|s| !s.is_empty())
        .map_or(10, |s| {
            s.parse().expect("SAMPLE_SIZE must be an integer or unset")
        })
}

#[cfg(feature = "bench")]
criterion::criterion_main!(benches);
generate_benches! {
    alloc: bench_alloc(1_000_000),
    alloc_from_iter: bench_alloc_from_iter(1_000_000, 10_000),
    iter: bench_iter(1_000_000),
    into_vec: bench_into_vec(1_000_000),
}
