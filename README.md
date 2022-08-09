# heapify

[![Crates.io](https://img.shields.io/crates/v/heapify.svg)](https://crates.io/crates/heapify)
[![Docs.rs](https://docs.rs/heapify/badge.svg)](https://docs.rs/heapify)
[![CI](https://github.com/ethereal-sheep/heapify/workflows/CI/badge.svg)](https://github.com/ethereal-sheep/heapify/actions)
[![Coverage Status](https://coveralls.io/repos/github/ethereal-sheep/heapify/badge.svg?branch=main)](https://coveralls.io/github/ethereal-sheep/heapify?branch=main)

<!-- cargo-rdme start -->

A collection of convenience functions for heapifying a slice in `rust`.

## Quick Start
A simple way to use `heapify` is with a `Vec<T>`.
```rust
use heapify::*;
let mut vec = vec![5, 7, 9];
make_heap(&mut vec);

pop_heap(&mut vec);
assert_eq!(vec.pop(), Some(9));

pop_heap(&mut vec);
assert_eq!(vec.pop(), Some(7));

assert_eq!(peek_heap(&mut vec), Some(&5));
```

<!-- cargo-rdme end -->

## Installation

### Cargo

* Install the rust toolchain in order to have cargo installed by following
  [this](https://www.rust-lang.org/tools/install) guide.
* run `cargo install heapify`

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

See [CONTRIBUTING.md](CONTRIBUTING.md).
