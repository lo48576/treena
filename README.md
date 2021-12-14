# Treena

[![Build Status](https://gitlab.com/nop_thread/treena/badges/develop/pipeline.svg)](https://gitlab.com/nop_thread/treena/pipelines/)
[![Latest version](https://img.shields.io/crates/v/treena.svg)](https://crates.io/crates/treena)
[![Documentation](https://docs.rs/treena/badge.svg)](https://docs.rs/treena)
![Minimum supported rustc version: 1.56](https://img.shields.io/badge/rustc-1.56+-lightgray.svg)

Treena: Trees stored in an arena.

## Yet another arena-tree?

Treena is heavily inspired by [indextree] crate, but has extra goals.

[indextree]: https://crates.io/crates/indextree

* Provide an arena to contain multiple independent trees.
    * Even when users are manipulating single trees, they may want to create
      temporary tree. Forest supports such use case.
    * Forest provided by treena is a true forest: root nodes of trees in an
      arena have no siblings relationships among each other.
* Use clear and unambiguous names.
    * Traditional function names which are often used for tree manipulation
      are very unclear for non-native English speakers.
        * For example, what does `A.insert_before(B)` mean?
          "insert A before B" or "insert B before A"?
        * `P.insert_before(A, B)` can be interpreted relatively naturally:
          "P (parent) inserts the node A before the node B".
          However, `P` here is completely redundant since it must be the
          parent of `A`.
    * Treena provides these functions as `A.adopt(B, AsFoo)` and
      `forest.insert(A, AsFooOf(B))`. They are much clearer than the traditional
      names.
        * For example, `A.adopt(B, AdoptAs::LastChild)` can be read as
          "the node A adopts the node B as the last child of A".
        * Another example: `forest.insert(A, InsertAs::NextSiblingOf(B))` can
          be read as "insert the node A as the next sibling of the node B".
* Be safe and easy to debug.
    * No unsafe codes (at least for now). This means that the crate won't run
      into undefined behavior.
    * Using `.expect()` everywhere with meaningful message when it won't fail
      or should panic for some reason.
        * For example, if treena panics with `[precondition] node must be alive`,
          you can be aware immediately that the passed node is not alive but it
          violates precondition of the function.
        * Another example: if treena panics with `[consistency] foobarbaz`,
          it is sure that this is a bug of treena (not you).

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE.txt](LICENSE-APACHE.txt) or
  <https://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT.txt](LICENSE-MIT.txt) or
  <https://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
