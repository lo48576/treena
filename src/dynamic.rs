//! Trees and forests with mutable hierarchy.

pub mod forest;
mod hierarchy;
mod id;

pub use self::forest::Forest;
pub use self::id::NodeId;
