# contiguous_mem

contiguous_mem streamlines storage and management of data stored in contiguous
memory block.

[![CI](https://github.com/Caellian/contiguous_mem/actions/workflows/rust.yml/badge.svg)](https://github.com/Caellian/contiguous_mem/actions/workflows/rust.yml)
[![Crates.io](https://img.shields.io/crates/v/contiguous_mem)](https://crates.io/crates/contiguous_mem)
[![Documentation](https://docs.rs/contiguous_mem/badge.svg)](https://docs.rs/contiguous_mem)

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

## Tradeoffs

- Works without nightly but leaks data, enable `ptr_metadata` or disable default
  `leak_data` feature flag if memory leaks are an issue:

  - `ptr_metadata` requires nightly,
  - disabling `leak_data` imposes `Copy` requirement on stored types.

- References returned by `store` function follow the same borrow restrictions as the
  language, `Deref` is implemented for `ContiguousMemoryRef` but it will panic on
  dereference if it's been already mutably borrowed somewhere else.
  Use `ContiguousMemoryRef::try_get` if you'd like to handle that properly.

## Getting Started

Add the crate to your dependencies:

```toml
[dependencies]
contiguous_mem = { version = "0.3.0" }
```

Optionally disable the `std` feature and enable `no_std` feature to use in `no_std` environment:

```toml
[dependencies]
contiguous_mem = { version = "0.3.0", default-features = false, features = ["no_std"] }
```

### Features

- `std` (**default**) - use `std` environment sync primitives and locks
- `no_std` - enables `no_std` dependencies
- `leak_data` (**default**) - disables `Copy` requirement for stored types, but any
  references in stored data will be leaked when the memory container is dropped
- `debug` - enables `derive(Debug)` on structures unrelated to error handling
- `ptr_metadata` &lt;_nightly_&gt; - enables support for casting returned references
  into `dyn Trait` types as well as cleaning up any types that implement `Drop`
  or generate drop glue
- `error_in_core` &lt;_nightly_&gt; - enables support for `core::error::Error` in `no_std` environment

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
    let stored_number: ContiguousMemoryRef<u64> = memory.store(22u64);
    let stored_data: ContiguousMemoryRef<Data> = memory.store(data);

    // Retrieve and use the stored data
    assert_eq!(*stored_data.get(), data);
    assert_eq!(*stored_number.get(), 22);
}
```

<cite>Note that reference types returned by store are inferred and only shown
here for demonstration purposes.</cite>

## Contributions

Contributions are welcome, feel free to
[create an issue](https://github.com/Caellian/contiguous_mem/issues) or a
[pull request](https://github.com/Caellian/contiguous_mem/pulls).

All contributions to the project are licensed under the Zlib/MIT/Apache 2.0
license unless you explicitly state otherwise.

## License

This project is licensed under [Zlib](./LICENSE_ZLIB), [MIT](./LICENSE_MIT), or
[Apache-2.0](./LICENSE_APACHE) license, choose whichever suits you most.
