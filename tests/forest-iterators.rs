//! Tests for iterators of forest.

use treena::dynamic::{DftEvent, Forest, NodeId, TreeBuilder};

/// Returns the sample tree as a forest and the root node ID.
///
/// Tree to be built:
///
/// ```text
/// root
/// |-- 0
/// |   |-- 0-0
/// |   |-- 0-1
/// |   |   |-- 0-1-0
/// |   |   |-- 0-1-1
/// |   |   `-- 0-1-2
/// |   `-- 0-2
/// |-- 1
/// |-- 2
/// |   |-- 2-0
/// |   |-- 2-1
/// |   `-- 2-2
/// |       `-- 2-2-0
/// `-- 3
/// ```
fn sample_tree() -> (Forest<&'static str>, NodeId) {
    let mut forest = Forest::new();
    let root = TreeBuilder::new(&mut forest, "root")
        .child("0")
        .child("0-0")
        .sibling("0-1")
        .child("0-1-0")
        .sibling("0-1-1")
        .sibling("0-1-2")
        .parent()
        .sibling("0-2")
        .parent()
        .sibling("1")
        .sibling("2")
        .child("2-0")
        .sibling("2-1")
        .sibling("2-2")
        .child("2-2-0")
        .parent()
        .parent()
        .sibling("3")
        .root_id();
    (forest, root)
}

const SAMPLE_TREE_DFT_EVENTS: &[DftEvent<&str>] = &[
    DftEvent::Open("root"),
    DftEvent::Open("0"),
    DftEvent::Open("0-0"),
    DftEvent::Close("0-0"),
    DftEvent::Open("0-1"),
    DftEvent::Open("0-1-0"),
    DftEvent::Close("0-1-0"),
    DftEvent::Open("0-1-1"),
    DftEvent::Close("0-1-1"),
    DftEvent::Open("0-1-2"),
    DftEvent::Close("0-1-2"),
    DftEvent::Close("0-1"),
    DftEvent::Open("0-2"),
    DftEvent::Close("0-2"),
    DftEvent::Close("0"),
    DftEvent::Open("1"),
    DftEvent::Close("1"),
    DftEvent::Open("2"),
    DftEvent::Open("2-0"),
    DftEvent::Close("2-0"),
    DftEvent::Open("2-1"),
    DftEvent::Close("2-1"),
    DftEvent::Open("2-2"),
    DftEvent::Open("2-2-0"),
    DftEvent::Close("2-2-0"),
    DftEvent::Close("2-2"),
    DftEvent::Close("2"),
    DftEvent::Open("3"),
    DftEvent::Close("3"),
    DftEvent::Close("root"),
];

#[test]
fn dft_forward() {
    let (tree, root) = sample_tree();

    let actual = tree
        .depth_first_traverse(root)
        .map(|ev| ev.map(|node| *node.data()))
        .collect::<Vec<_>>();

    assert_eq!(actual, SAMPLE_TREE_DFT_EVENTS);
}

#[test]
fn dft_backward() {
    let (tree, root) = sample_tree();

    // Collect items by reverse iteration.
    let mut actual = tree
        .depth_first_traverse(root)
        .rev()
        .map(|ev| ev.map(|node| *node.data()))
        .collect::<Vec<_>>();
    // Reverse the result.
    actual.reverse();

    assert_eq!(actual, SAMPLE_TREE_DFT_EVENTS);
}
