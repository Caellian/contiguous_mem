contiguous_mem streamlines storage and management of data stored in contiguous
blocks of memory.

## Implementations

Primary interface of the crate is the [`ContiguousMemoryStorage`] structure
which is re-exported under following type aliases with specified implementation
details flag:

- [`ContiguousMemory`]
- [`SyncContiguousMemory`]
- [`UnsafeContiguousMemory`]

See individual items for usage examples, as well as project
[`examples`](https://github.com/Caellian/contiguous_mem/tree/trunk/examples)
directory.

## Features

- `no_std` - enables `no_std` dependencies for atomics, mutexes and rwlocks
- `debug` - enables `derive(Debug)` on structures unrelated to error handling
- [`ptr_metadata`](https://doc.rust-lang.org/beta/unstable-book/library-features/ptr-metadata.html)
  &lt;_nightly_&gt; - allows casting references into `dyn Trait`
- [`error_in_core`](https://dev-doc.rust-lang.org/stable/unstable-book/library-features/error-in-core.html)
  &lt;_nightly_&gt; - enables support for `core::error::Error` in `no_std`
  environment

## Contributions

Contributions are welcome, feel free to
[create an issue](https://github.com/Caellian/contiguous_mem/issues) or a
[pull request](https://github.com/Caellian/contiguous_mem/pulls).

All contributions to the project are licensed under the Zlib/MIT/Apache 2.0
license unless you explicitly state otherwise.

## License

This project is licensed under [Zlib](./LICENSE_ZLIB), [MIT](./LICENSE_MIT), or
[Apache-2.0](./LICENSE_APACHE) license, choose whichever suits you most.
