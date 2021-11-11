//! Tests for iterators of forest.

use core::mem;

use treena::dynamic::{DftEvent, Forest, Node, NodeIdUsize, TreeBuilder};

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
fn sample_tree() -> (Forest<NodeIdUsize, &'static str>, NodeIdUsize) {
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

fn to_content_and_depth<'f, I>(iter: I) -> Vec<(DftEvent<&'static str>, usize)>
where
    I: Iterator<Item = DftEvent<Node<'f, NodeIdUsize, &'static str>>>,
{
    iter.map(|ev| ev.map(|node| *node.data()))
        .scan(0, |depth, ev| {
            let ret_depth = match ev {
                DftEvent::Open(_) => mem::replace(depth, *depth + 1),
                DftEvent::Close(_) => {
                    *depth -= 1;
                    *depth
                }
            };
            Some((ev, ret_depth))
        })
        .collect()
}

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

#[test]
fn shallow_dft_forward_with_limit() {
    let (tree, root) = sample_tree();

    for max_depth in 0..=3 {
        let actual = tree
            .shallow_depth_first_traverse(root, Some(max_depth))
            .map(|(ev, depth)| (ev.map(|node| *node.data()), depth))
            .collect::<Vec<_>>();

        let expected = to_content_and_depth(tree.depth_first_traverse(root))
            .into_iter()
            .filter(|(_, ref depth)| *depth <= max_depth)
            .collect::<Vec<_>>();

        assert_eq!(actual, expected, "max_depth = {}", max_depth);
    }
}

#[test]
fn shallow_dft_backward_with_limit() {
    let (tree, root) = sample_tree();

    for max_depth in 0..=3 {
        let mut actual = tree
            .shallow_depth_first_traverse(root, Some(max_depth))
            .rev()
            .map(|(ev, depth)| (ev.map(|node| *node.data()), depth))
            .collect::<Vec<_>>();
        actual.reverse();

        let expected = to_content_and_depth(tree.depth_first_traverse(root))
            .into_iter()
            .filter(|(_, ref depth)| *depth <= max_depth)
            .collect::<Vec<_>>();

        assert_eq!(actual, expected, "max_depth = {}", max_depth);
    }
}

#[test]
fn shallow_dft_forward_without_limit() {
    let (tree, root) = sample_tree();

    let actual = tree
        .shallow_depth_first_traverse(root, None)
        .map(|(ev, depth)| (ev.map(|node| *node.data()), depth))
        .collect::<Vec<_>>();
    let expected = to_content_and_depth(tree.depth_first_traverse(root));

    assert_eq!(actual, expected);
}

#[test]
fn shallow_dft_backward_without_limit() {
    let (tree, root) = sample_tree();

    let mut actual = tree
        .shallow_depth_first_traverse(root, None)
        .rev()
        .map(|(ev, depth)| (ev.map(|node| *node.data()), depth))
        .collect::<Vec<_>>();
    actual.reverse();
    let expected = to_content_and_depth(tree.depth_first_traverse(root));

    assert_eq!(actual, expected);
}
