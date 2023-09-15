# contiguous_mem

contiguous_mem streamlines storage and management of data stored in contiguous
blocks of memory.

[![Crate](https://img.shields.io/crates/v/contiguous_mem?style=for-the-badge&logo=docs.rs)](https://crates.io/crates/contiguous_mem)
[![Documentation](https://img.shields.io/docsrs/contiguous-mem?style=for-the-badge&logo=rust)](https://docs.rs/contiguous-mem)
[![CI Status](https://img.shields.io/github/actions/workflow/status/Caellian/contiguous_mem/rust.yml?style=for-the-badge&logo=githubactions&logoColor=%23fff&label=CI)](https://github.com/Caellian/contiguous_mem/actions/workflows/rust.yml)
[![Zlib or MIT or Apache 2.0 license](https://img.shields.io/crates/l/contiguous-mem?style=for-the-badge)](https://github.com/Caellian/contiguous_mem#license)

## Stability

All versions prior to 1.0.0 are not considered production ready. This is my
first crate and there's still a lot of edge cases I didn't get a chance to
consider yet.

Prelimenary tests are in place but I don't consider them sufficient to guarantee
correctness of behavior.

## Key Features

- `no_std` support!
- Simple and straightforward interface similar to standard containers.
- Support for dynamic resizing of allocated memory keeping the created
  references functional (for safe implementations).

### Specialized implementations

You can pick and choose which implementation suits your use case best allowing
you to avoid runtime cost of synchronization and additionally memory cost of
safely wrapping referenced data if you don't need it.

Default implementation keeps relative offsets of stored data which are resolved
on access.

## Use cases

- Ensuring stored data is placed adjacently in memory. ([example](./examples/game_loading.rs))
- Storing differently typed/sized data. ([example](./examples/default_impl.rs))

## Tradeoffs

- Works without nightly but leaks data requiring Drop or drop glue, enable
  `ptr_metadata` or disable default `leak_data` feature flag if memory leaks are
  an issue:
  - `ptr_metadata` requires nightly,
  - disabling `leak_data` imposes `Copy` requirement on stored types.

## Getting Started

Add the crate to your dependencies:

```toml
[dependencies]
contiguous_mem = { version = "0.4.*" }
```

Optionally disable the `std` feature and enable `no_std` feature to use in `no_std` environment:

```toml
[dependencies]
contiguous_mem = { version = "0.4.*", default-features = false, features = ["no_std"] }
```

### Features

- `no_std` - enables `no_std` dependencies for atomics, mutexes and rwlocks
- `leak_data` (**default**) - disables `Copy` requirement for stored types, but any
  references in stored data will be leaked when the memory container is dropped
- `debug` - enables `derive(Debug)` on structures unrelated to error handling
- [`ptr_metadata`](https://doc.rust-lang.org/beta/unstable-book/library-features/ptr-metadata.html)
  &lt;_nightly_&gt; - enables support for casting returned references into
  `dyn Trait` types as well as cleaning up any types that implement `Drop` or
  generate drop glue
- [`error_in_core`](https://dev-doc.rust-lang.org/stable/unstable-book/library-features/error-in-core.html)
  &lt;_nightly_&gt; - enables support for `core::error::Error` in `no_std`
  environment

### Usage

```rust
use contiguous_mem::prelude::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Data {
    value: u32,
}

fn main() {
    // Create a ContiguousMemory instance with a capacity of 1024 bytes and 1-byte alignment
    let mut memory = ContiguousMemory::new(1024);

    // Store data in the memory container
    let data = Data { value: 42 };
    let stored_number: ContiguousMemoryRef<u64> = memory.push(22u64);
    let stored_data: ContiguousMemoryRef<Data> = memory.push(data);

    // Retrieve and use the stored data
    assert_eq!(*stored_data.get(), data);
    assert_eq!(*stored_number.get(), 22);
}
```

- References have a similar API as
  [`RefCell`](https://doc.rust-lang.org/stable/std/cell/struct.RefCell.html)

<cite>Note that reference types returned by store are inferred and only shown
here for demonstration purposes.</cite>

## Alternatives

- manually managing memory to ensure contiguous placement of data
  - prone to errors and requires unsafe code
- using a custom allocator like
  [blink-alloc](https://crates.io/crates/blink-alloc) to ensure contiguous
  placement of data
  - requires [`allocator_api`](https://doc.rust-lang.org/beta/unstable-book/library-features/allocator-api.html)
    feature
  - `blink-alloc` provides a similar functionality as this crate without the
    `allocator_api` feature; intended for use in loops so it doesn't support
    freeing _some_ values while retaining other

## Contributions

Contributions are welcome, feel free to
[create an issue](https://github.com/Caellian/contiguous_mem/issues) or a
[pull request](https://github.com/Caellian/contiguous_mem/pulls).

All contributions to the project are licensed under the Zlib/MIT/Apache 2.0
license unless you explicitly state otherwise.

## License

This project is licensed under [Zlib](./LICENSE_ZLIB), [MIT](./LICENSE_MIT), or
[Apache-2.0](./LICENSE_APACHE) license, choose whichever suits you most.
