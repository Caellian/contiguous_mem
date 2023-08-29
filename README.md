# contiguous_mem

contiguous_mem implements a contiguous memory storage container for arbitrary data types.

[![CI](https://github.com/Caellian/contiguous_mem/actions/workflows/rust.yml/badge.svg)](https://github.com/Caellian/contiguous_mem/actions/workflows/rust.yml)
[![Crates.io](https://img.shields.io/crates/v/contiguous_mem)](https://crates.io/crates/contiguous_mem)
[![Documentation](https://docs.rs/contiguous_mem/badge.svg)](https://docs.rs/contiguous_mem)

Designed for both standard and no_std environments, this library ensures efficient memory
allocation while being simple and (somewhat) safe to use.

## Tradeoffs

- Works without nightly but leaks data, enable `ptr_metadata` or disable default `leak_data`
  feature flag if memory leaks are an issue:

  - `ptr_metadata` requires nightly,
  - disabling `leak_data` imposes `Copy` requirement on stored types.

- References returned by `store` function follow the same borrow restrictions as the
  language, `Deref` is implemented for `ContiguousMemoryRef` but it will panic on
  dereference if it's been already mutably borrowed somewhere else.
  Use `ContiguousMemoryRef::try_get` if you'd like to handle that properly.

## Key Features

- Type Agnostic: Support for various data types, including mixed types within the same container.

- Multiple Implementations: Choose from specialized strategies to match your requirements:
  - SyncContiguousMemory (ImplConcurrent): Enables asynchronous data access, ensuring safety in concurrent scenarios.
  - GrowableContiguousMemory (ImplDefault): Synchronous, mutex-free implementation for speed and dynamic resizing.
  - FixedContiguousMemory (ImplFixed): Highly optimized but unsafe for precise sizing and long-lived references.

## Getting Started

Add the crate to your dependencies:

```toml
[dependencies]
contiguous_mem = { version = "0.2.*" }
```

Optionally disable the `std` feature and enable `no_std` feature to use in `no_std` environment:

```toml
[dependencies]
contiguous_mem = { version = "0.2.*", default-features = false, features = ["no_std"] }
```

### Features

- `std` (**default**) - enables support for `std` environment
- `no_std` - enables support for `no_std` environment
- `leak_data` (**default**) - disables `Copy` requirement for stored types, but any
  references in stored data will be leaked when the memory container is dropped
- `debug` - enables `derive(Debug)` on structures unrelated to error handling
- `ptr_metadata` &lt;_nightly_&gt; - enables support for casting returned references
  into `dyn Trait` types as well as cleaning up any types that implement `Drop`
  or generate drop glue
- `error_in_core` &lt;_nightly_&gt; - enables support for `core::error::Error` in `no_std` environment

### Usage

```rust
use contiguous_mem::GrowableContiguousMemory;

struct Data {
    value: u32,
}

fn main() {
    // Create a ContiguousMemory instance with a capacity of 1024 bytes and 1-byte alignment
    let mut memory = GrowableContiguousMemory::new(1024);

    // Store data in the memory container
    let data = Data { value: 42 };
    let stored_number = memory.store(22u64);
    let stored_data = memory.store(data);

    // Retrieve and use the stored data
    println!("Retrieved data: {}", *stored_data);
    println!("Retrieved number: {}", *stored_number);
}
```

## Contributions

Contributions are welcome, feel free to create an issue or a pull request.

All contributions to the project are licensed under the zlib/MIT/Apache 2.0 license unless you explicitly state otherwise.

## License

This project is licensed under [Zlib](./LICENSE_ZLIB), [MIT](./LICENSE_MIT), or
[Apache-2.0](./LICENSE_APACHE) license, choose whichever suits you most.
