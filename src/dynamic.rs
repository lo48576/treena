//! Forests with dynamic (mutable) hierarchy.
//!
//! # Concepts
//!
//! ## Forest
//!
//! Forest is a set of trees. A forest is represented by [`Forest`] type.
//!
//! ## Root nodes in a forest
//!
//! Every tree has its own root node, but they don't have any relations with
//! other root nodes in a forest. This means you cannot reach to other trees
//! from a node of another tree.
//!
//! ## Node ID
//!
//! Each node has internally unique node ID. A node ID is represented by
//! [`NodeIdUsize`] type.
//!
//! Note that node IDs are not guaranteed to be unique among forests. In fact,
//! node IDs will conflict almost certainly in the current
//! implementation<!-- current: develop branch @2021-09-26 -->.
//! You must be careful not to use node IDs for unintended forests.
//!
//! ## Proxy to node objects
//!
//! While almost all features are implemented as methods of [`Forest`], some
//! operations are available through [`Node`] and [`NodeMut`] types.
//! [`Node`] and [`NodeMut`] are conceptually a pair of a forest and a node ID.

mod anchor;
mod forest;
mod hierarchy;
mod id;

pub use self::anchor::{AdoptAs, InsertAs};
pub use self::forest::traverse::{
    AllocatingBreadthFirstTraverse, Ancestors, BreadthFirstTraverse, DepthFirstTraverse, DftEvent,
    ShallowDepthFirstTraverse, Siblings,
};
#[cfg(any(feature = "debug-print"))]
pub use self::forest::DebugPrint;
pub use self::forest::{Forest, Node, NodeMut, StructureError, TreeBuilder};
pub use self::id::{InternalNodeId, NodeId, NodeIdUsize};
