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
//! Each node has internally unique node ID. A node ID type should implement
//! [`NodeId`] trait. Some ID types are provided from `treena` crate, but users
//! are encouraged to define dedicated ID types for their usage.
//!
//! Note that node IDs are not guaranteed to be unique among forests. In fact,
//! node IDs will conflict almost certainly in the current
//! implementation<!-- current: develop branch @2021-11-12 -->.
//! You must be careful not to use node IDs for unintended forests.
//!
//! Using different node ID types will reduce such accidental unintended use of
//! node IDs from unrelated forests.
//!
//! ### Internal node ID
//!
//! A node ID type should be a simple wrapper of an **internal node ID**, which
//! is also provided from `treena` crate.
//! Users cannot implement custom internal node ID types, since it will allow
//! users to craft invalid ID value in meaningless way and it also restricts
//! internal structure of the internal node ID types.
//!
//! For the list of available internal node ID types, see the documentation for
//! [`InternalNodeId`] trait.
//!
//! ### Implementing custom node ID
//!
//! Define your custom node ID type as a wrapper (strong typedef) of an internal
//! node ID type.
//!
//! You can use [`impl_dynamic_node_id`][`crate::impl_dynamic_node_id`] macro
//! to implement [`NodeId`] trait for your type.
//! It is possible to implement `NodeId` trait manually, but it is boilerplate
//! and you won't need to do that in almost all cases.
//!
//! ```
//! // Macro for convenience.
//! use treena::impl_dynamic_node_id;
//! // `NodeIdUsize` implements `InternalNodeId` trait.
//! use treena::dynamic::NodeIdUsize;
//!
//! // Node ID types should implement `Debug`, `Copy`, `Eq`, and `Hash`.
//! #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
//! // Use `NodeIdUsize` as an internal node ID type.
//! pub struct MyNodeId(NodeIdUsize);
//!
//! // Arguments are:
//! //  * custom node ID type,
//! //  * internal node ID type, and
//! //  * accessor for the internal node ID field.
//! //
//! // You can access the internal node ID as `self.0` (where `self: MyNodeId`),
//! // so use `0` as an accessor.
//! impl_dynamic_node_id!(MyNodeId, NodeIdUsize, 0);
//! ```
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
use self::id::NodeIdExt;
pub use self::id::{InternalNodeId, NodeId, NodeIdUsize};
