contiguous_mem streamlines storage and management of data stored in contiguous
block of memory.

## Features

- `no_std` - enables `no_std` dependencies for atomics, mutexes and rwlocks
- `debug` - enables `derive(Debug)` on structures unrelated to error handling
- [`ptr_metadata`](https://doc.rust-lang.org/beta/unstable-book/library-features/ptr-metadata.html)
  &lt;_nightly_&gt; - allows casting references into `dyn Trait`
- [`error_in_core`](https://dev-doc.rust-lang.org/stable/unstable-book/library-features/error-in-core.html)
  &lt;_nightly_&gt; - enables support for `core::error::Error` in `no_std`
  environment
- `sync` (default) - enables `SyncContiguousMemory` and related error code
  implementation
- `unsafe` (default) - enables `UnsafeContiguousMemory`

## Contributions

Contributions are welcome, feel free to
[create an issue](https://github.com/Caellian/contiguous_mem/issues) or a
[pull request](https://github.com/Caellian/contiguous_mem/pulls).

All contributions to the project are licensed under the Zlib/MIT/Apache 2.0
license unless you explicitly state otherwise.

## License

This project is licensed under [Zlib](./LICENSE_ZLIB), [MIT](./LICENSE_MIT), or
[Apache-2.0](./LICENSE_APACHE) license, choose whichever suits you most.
