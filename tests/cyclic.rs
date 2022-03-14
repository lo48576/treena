//! Tests to ensure forests prevent users from making cyclic links.

use treena::dynamic::{DftEvent, Forest, InsertAs, NodeIdUsize, StructureError};

/// Insert the next sibling as a previous sibling.
#[test]
fn prev_sibling_as_next_sibling() {
    let mut forest = Forest::<NodeIdUsize, _>::new();
    let root = forest.create_root("root");
    let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    let child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    //  root
    //  |-- 0
    //  `-- 1
    forest
        .insert(child0, InsertAs::NextSiblingOf(child1))
        .expect("should succeed");
    //  root
    //  |-- 1
    //  `-- 0

    let actual = forest
        .depth_first_traverse(root)
        .map(|ev| ev.map(|node| *node.data()))
        .collect::<Vec<_>>();
    let expected = &[
        DftEvent::Open("root"),
        DftEvent::Open("1"),
        DftEvent::Close("1"),
        DftEvent::Open("0"),
        DftEvent::Close("0"),
        DftEvent::Close("root"),
    ];
    assert_eq!(actual, expected);
}

/// Insert the next of the next sibling as a previous sibling.
#[test]
fn prev_prev_sibling_as_next_sibling() {
    let mut forest = Forest::<NodeIdUsize, _>::new();
    let root = forest.create_root("root");
    let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    let _child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    let child2 = forest.create_insert("2", InsertAs::LastChildOf(root));
    //  root
    //  |-- 0
    //  |-- 1
    //  `-- 2
    forest
        .insert(child0, InsertAs::NextSiblingOf(child2))
        .expect("should succeed");
    //  root
    //  |-- 1
    //  |-- 2
    //  `-- 0

    let actual = forest
        .depth_first_traverse(root)
        .map(|ev| ev.map(|node| *node.data()))
        .collect::<Vec<_>>();
    let expected = &[
        DftEvent::Open("root"),
        DftEvent::Open("1"),
        DftEvent::Close("1"),
        DftEvent::Open("2"),
        DftEvent::Close("2"),
        DftEvent::Open("0"),
        DftEvent::Close("0"),
        DftEvent::Close("root"),
    ];
    assert_eq!(actual, expected);
}

/// Insert the next sibling as a previous sibling.
#[test]
fn next_sibling_as_prev_sibling() {
    let mut forest = Forest::<NodeIdUsize, _>::new();
    let root = forest.create_root("root");
    let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    let child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    //  root
    //  |-- 0
    //  `-- 1
    forest
        .insert(child1, InsertAs::PreviousSiblingOf(child0))
        .expect("should succeed");
    //  root
    //  |-- 1
    //  `-- 0

    let actual = forest
        .depth_first_traverse(root)
        .map(|ev| ev.map(|node| *node.data()))
        .collect::<Vec<_>>();
    let expected = &[
        DftEvent::Open("root"),
        DftEvent::Open("1"),
        DftEvent::Close("1"),
        DftEvent::Open("0"),
        DftEvent::Close("0"),
        DftEvent::Close("root"),
    ];
    assert_eq!(actual, expected);
}

/// Insert the next of the next sibling as a previous sibling.
#[test]
fn next_next_sibling_as_prev_sibling() {
    let mut forest = Forest::<NodeIdUsize, _>::new();
    let root = forest.create_root("root");
    let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    let _child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    let child2 = forest.create_insert("2", InsertAs::LastChildOf(root));
    //  root
    //  |-- 0
    //  |-- 1
    //  `-- 2
    forest
        .insert(child2, InsertAs::PreviousSiblingOf(child0))
        .expect("should succeed");
    //  root
    //  |-- 2
    //  |-- 0
    //  `-- 1

    let actual = forest
        .depth_first_traverse(root)
        .map(|ev| ev.map(|node| *node.data()))
        .collect::<Vec<_>>();
    let expected = &[
        DftEvent::Open("root"),
        DftEvent::Open("2"),
        DftEvent::Close("2"),
        DftEvent::Open("0"),
        DftEvent::Close("0"),
        DftEvent::Open("1"),
        DftEvent::Close("1"),
        DftEvent::Close("root"),
    ];
    assert_eq!(actual, expected);
}

/// Insert the previous sibling as a child.
#[test]
fn prev_sibling_as_child() {
    let mut forest = Forest::<NodeIdUsize, _>::new();
    let root = forest.create_root("root");
    let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    let child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    //  root
    //  |-- 0
    //  `-- 1
    forest
        .insert(child0, InsertAs::LastChildOf(child1))
        .expect("should succeed");
    //  root
    //  `-- 1
    //      `-- 0

    let actual = forest
        .depth_first_traverse(root)
        .map(|ev| ev.map(|node| *node.data()))
        .collect::<Vec<_>>();
    let expected = &[
        DftEvent::Open("root"),
        DftEvent::Open("1"),
        DftEvent::Open("0"),
        DftEvent::Close("0"),
        DftEvent::Close("1"),
        DftEvent::Close("root"),
    ];
    assert_eq!(actual, expected);
}

/// Insert the next sibling as a child.
#[test]
fn next_sibling_as_child() {
    let mut forest = Forest::<NodeIdUsize, _>::new();
    let root = forest.create_root("root");
    let child0 = forest.create_insert("0", InsertAs::LastChildOf(root));
    let child1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    //  root
    //  |-- 0
    //  `-- 1
    forest
        .insert(child1, InsertAs::LastChildOf(child0))
        .expect("should succeed");
    //  root
    //  `-- 0
    //      `-- 1

    let actual = forest
        .depth_first_traverse(root)
        .map(|ev| ev.map(|node| *node.data()))
        .collect::<Vec<_>>();
    let expected = &[
        DftEvent::Open("root"),
        DftEvent::Open("0"),
        DftEvent::Open("1"),
        DftEvent::Close("1"),
        DftEvent::Close("0"),
        DftEvent::Close("root"),
    ];
    assert_eq!(actual, expected);
}

/// Insert the parent as a child.
#[test]
fn parent_as_child() {
    let mut forest = Forest::<NodeIdUsize, _>::new();
    let root = forest.create_root("root");
    let depth1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    let depth2 = forest.create_insert("2", InsertAs::LastChildOf(depth1));
    //  root
    //  `-- 1
    //      `-- 2
    let result = forest.insert(depth1, InsertAs::LastChildOf(depth2));
    assert!(matches!(
        result,
        Err(StructureError::AncestorDescendantLoop)
    ));
}

/// Insert the grandparent as a child.
#[test]
fn grandparent_as_child() {
    let mut forest = Forest::<NodeIdUsize, _>::new();
    let root = forest.create_root("root");
    let depth1 = forest.create_insert("1", InsertAs::LastChildOf(root));
    let depth2 = forest.create_insert("2", InsertAs::LastChildOf(depth1));
    let depth3 = forest.create_insert("3", InsertAs::LastChildOf(depth2));
    //  root
    //  `-- 1
    //      `-- 2
    //          `-- 3
    let result = forest.insert(depth1, InsertAs::LastChildOf(depth3));
    assert!(matches!(
        result,
        Err(StructureError::AncestorDescendantLoop)
    ));
}
