//! Tree and forest builder.

use std::mem;

use crate::dynamic::forest::Forest;
use crate::dynamic::{InsertAs, NodeId};

/// Nest-style tree builder.
///
/// # Examples
///
/// ```
/// # use treena::dynamic::NestTreeBuilder;
/// use treena::dynamic::{Forest, NodeIdUsize, ChainTreeBuilder};
///
/// let mut forest: Forest<NodeIdUsize, &'static str> = Forest::new();
/// let mut builder = NestTreeBuilder::new(&mut forest, "root");
///
/// builder.create_tree("0", |b| {
///     b.add_child("0-0");
///     b.add_child("0-1");
/// });
/// builder.create_tree("1", |b| {
///     b.add_child("1-0");
///     b.create_tree("1-1", |b| {
///         b.add_child("1-1-0");
///         b.add_child("1-1-1");
///     });
/// });
/// builder.add_child("2");
///
/// let root = builder.root();
/// let expected = r#"root
/// |-- 0
/// |   |-- 0-0
/// |   `-- 0-1
/// |-- 1
/// |   |-- 1-0
/// |   `-- 1-1
/// |       |-- 1-1-0
/// |       `-- 1-1-1
/// `-- 2"#;
/// assert_eq!(forest.debug_print(root).to_string(), expected);
/// ```
#[derive(Debug)]
pub struct NestTreeBuilder<'a, Id: NodeId, T> {
    /// Target forest.
    forest: &'a mut Forest<Id, T>,
    /// Node ID of the root node.
    root: Id,
    /// Current node.
    current: Option<Id>,
}

impl<'a, Id: NodeId, T> NestTreeBuilder<'a, Id, T> {
    /// Creates a new nested tree builder.
    pub fn new(forest: &'a mut Forest<Id, T>, data: T) -> Self {
        let root = forest.create_root(data);
        Self {
            forest,
            root,
            current: None,
        }
    }

    /// Add a child leaf node.
    pub fn add_child(&mut self, data: T) {
        let new_id = self.forest.create_root(data);
        match self.current {
            Some(prev_sib) => {
                self.forest
                    .insert(new_id, InsertAs::NextSiblingOf(prev_sib))
                    .expect("[consistency] `root` and `current` is created by `NestTreeBuilder`, and must be consistent");
            }
            None => {
                self.forest
                    .insert(new_id, InsertAs::FirstChildOf(self.root))
                    .expect("[consistency] `root` and `current` is created by `NestTreeBuilder`, and must be consistent");
            }
        }
        self.current = Some(new_id);
    }

    /// Add a child possibly with its children.
    pub fn create_tree<F>(&mut self, data: T, f: F)
    where
        F: FnOnce(&mut NestTreeBuilder<'a, Id, T>),
    {
        self.add_child(data);
        let new_root = self
            .current
            .take()
            .expect("[consistency] `add_child` makes `current` `Some`");
        let old_root = mem::replace(&mut self.root, new_root);

        f(self);

        self.current = Some(new_root);
        self.root = old_root;
    }

    /// Returns the root node ID for the tree.
    #[inline]
    #[must_use]
    pub fn root(&self) -> Id {
        self.root
    }
}
