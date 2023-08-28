# contiguous_mem

Contiguous memory is memory that is allocated in one contiguous block.
Designed for both standard and no_std environments, this library ensures efficient memory allocation while being simple and (somewhat) safe to use.

## Key Features

- Type Agnostic: Support for various data types, including mixed types within the same container.

- Multiple Implementations: Choose from specialized strategies to match your requirements:
  - SyncContiguousMemory (ThreadSafeImpl): Enables asynchronous data access, ensuring safety in concurrent scenarios.
  - GrowableContiguousMemory (NotThreadSafeImpl): Synchronous, mutex-free implementation for speed and dynamic resizing.
  - FixedContiguousMemory (FixedSizeImpl): Highly optimized but unsafe for precise sizing and long-lived references.

## Getting Started

Add the crate to your dependencies:

```toml
[dependencies]
contiguous_mem = "0.1.0"
```

Optionally disable the `std` feature to use in `no_std` environment:

```toml
[dependencies]
contiguous_mem = { version = "0.1.0", default-features = false }
```

### Example usage

```rust
use contiguous_mem::GrowableContiguousMemory;

struct Data {
    value: u32,
}

fn main() {
    // Create a ContiguousMemory instance with a capacity of 1024 bytes and 8-byte alignment
    let mut memory = GrowableContiguousMemory::new(1024, 8).unwrap();

    // Store data in the memory container
    let data = Data { value: 42 };
    let stored_number = memory.store(22u64).unwrap();
    let stored_data = memory.store(data).unwrap();

    // Retrieve and use the stored data
    let retrieved_data = stored_data.get().unwrap();
    println!("Retrieved data: {}", retrieved_data.value);
    let retrieved_number = stored_number.get().unwrap();
    println!("Retrieved number: {}", retrieved_number);
}
```

## Contributions

Contribtions are welcome, feel free to create an issue or a pull request.

All contributions to the project are licensed under the zlib/MIT/Apache 2.0 license unless you explicitly state otherwise.

## License

This project is licensed under [Zlib](./LICENSE_ZLIB), [MIT](./LICENSE_MIT), or
[Apache-2.0](./LICENSE_APACHE) license, choose whichever suits you most.
