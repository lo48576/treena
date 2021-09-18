//! Trees and forests with mutable hierarchy.

mod anchor;
pub mod forest;
mod hierarchy;
mod id;

pub use self::anchor::{AdoptAs, InsertAs};
pub use self::forest::Forest;
pub use self::id::NodeId;
