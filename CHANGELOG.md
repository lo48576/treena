# Change Log

## [Unreleased]

* Bump minimum supported rust version to 1.56.

### Changed (breaking)

* Bump minimum supported rust version to 1.56.

## [0.0.2]

* Implement `std::error::Error` trait for an error type.
* Make more long-living reference from `Node::data()`.
* Add `Forest::clone_{local,forest}_tree{,_with_id_mapping}()`.
* Add `TreeBuilder::forest()` and `TreeBuilder::forest_mut()`.
* Add `NodeMut::into_data_mut_ref()`.
* Add `peek()` and `peek_back()` methods to iterators where possible.

### Added

* Implement `std::error::Error` trait for an error type.
* Add `Forest::clone_{local,forest}_tree{,_with_id_mapping}()`.
* Add `TreeBuilder::forest()` and `TreeBuilder::forest_mut()`.
* Add `NodeMut::into_data_mut_ref()` that returns reference to the data with longer lifetime.
* Add `peek()` and `peek_back()` methods to iterators where possible.
    + `DepthFirstTraverse`, `ShallowDepthFirstTraverse`, and `Siblings` get both
      `peek()` and `peek_back()` methods.
    + `Ancestors` and `AllocatingBreadthFirstTraverse` get only `peek()` method.

### Changed (non-breaking)
* Make more long-living reference from `Node::data()`.

## [0.0.1]

Initial release.

[Unreleased]: <https://github.com/lo48576/fbxcel/compare/v0.0.2...develop>
[0.0.2]: <https://github.com/lo48576/fbxcel/releases/tag/v0.0.2>
[0.0.1]: <https://github.com/lo48576/fbxcel/releases/tag/v0.0.1>
