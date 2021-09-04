//! Treena: Tree stored in an arena.
#![forbid(unsafe_code)]
#![warn(rust_2018_idioms)]
// `clippy::missing_docs_in_private_items` implies `missing_docs`.
#![warn(clippy::missing_docs_in_private_items)]
#![warn(clippy::unwrap_used)]
#![cfg_attr(not(feature = "std"), no_std)]

mod nonmax;
