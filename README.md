# rustc-arena-modified: rustc-arena ported to stable rust with additional features

[![CI](https://github.com/Jakobeha/rustc-arena-modified/workflows/CI/badge.svg)](https://github.com/Jakobeha/rustc-arena-modified/actions)
[![Crate informations](https://img.shields.io/crates/v/rustc-arena-modified.svg?style=flat-square)](https://crates.io/crates/rustc-arena-modified)
[![License](https://img.shields.io/crates/l/rustc-arena-modified.svg?style=flat-square)](https://github.com/Jakobeha/rustc-arena-modified#license)
[![Documentation](https://img.shields.io/badge/docs-latest-blue.svg?style=flat-square)](https://docs.rs/rustc-arena-modified)

## Why would you want this?

- Allocating objects in an arena can be faster then regular allocation
- An arena doubles as a collection where you can insert objects behind a shared reference. Instead of `Clone`ing objects and possibly using `Rc`s, use an `Arena` and copy the references.

### What about [`typed-arena`](https://crates.io/crates/typed-arena) and [`bumpalo`](https://crates.io/crates/bumpalo)?

- `rustc_arena_modified::TypedArena` allows coalescing and clearing objects behind a mutable reference, while saving the chunks so they don't need to be re-allocated. This is equivalent to calling `into_vec` and then converting the vector back into an arena, but faster, because you don't need to allocate anything.
- `rustc_arena_modified::TypedArena` is also significantly faster at iteration according to the benchmarks (other differences are neglibable; see [benchmarks](#benchmarks))
- `rustc_arena_modified::TypedArena` returns a shared reference to allocated values, so it can iterate values behind a shared reference like [`typed-arena-nomut`](https://crates.io/crates/typed-arena-nomut)
- TODO: Comparisons between `DroplessArena` and `Bump` (note: maybe `Bump` is objectively better)

## What is it?

A port of [`rustc_arena`](https://doc.rust-lang.org/stable/nightly-rustc/rustc_arena/index.html) into stable rust with the following new features:

- `TypedArena::iter` to iterate over all objects in the arena
- `TypedArena::retain` and `TypedArena::clear` to coalesce clearing objects behind a mutable reference, while saving the chunks so they don't need to be re-allocated.

## Benchmarks

![benchmarks](criterion/report.html)

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

Forked from [rustc-arena](https://doc.rust-lang.org/stable/nightly-rustc/rustc_arena/index.html) ([Github](https://github.com/rust-lang/rust/tree/master/compiler/rustc_arena)), which is also licensed under MIT "or" Apache 2.0.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.