# rustc-arena-modified-benchmarks

## Why is this a separate workspace?

See [typed-arena-benchmarks](https://github.com/thomcc/rust-typed-arena/blob/master/benches/README.md). tldr: criterion takes a long time to build, so we want to only include it for benchmarks, not other tests.

Note: In order to run the `nightly` feature you will need nightly rust and `rustc-dev`. Run

```bash
rustup toolchain install nightly
rustup component add rustc-dev
```