//! Forests with mutable hierarchy.

mod anchor;
mod forest;
mod hierarchy;
mod id;

pub use self::anchor::{AdoptAs, InsertAs};
pub use self::forest::traverse::{Ancestors, DepthFirstTraverse, DftEvent, Siblings};
#[cfg(any(feature = "debug-print"))]
pub use self::forest::DebugPrint;
pub use self::forest::{Forest, Node, NodeMut, StructureError, TreeBuilder};
pub use self::id::NodeId;
