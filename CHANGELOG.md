# Change Log

## [Unreleased]

* Update document about precondition of `Forest::create_insert` method.
* Remove `debug-print` feature.
    + Related items are now always available without any additional features.
* Internal improvements.
    + Pre-monomorphize methods of `Forest` and related types, in order to reduce
      code bloat.

### Changed (non-breaking)

* Update document about precondition of `Forest::create_insert` method.
    + Make it clear that it can panic when the node ID is one from another
      forest, even when the corresponding node is alive.
    + Panic message for such case is improved. Previously it was shown as
      internal consistency error, but now it is shown as precondition violation.
    + This is only documentation and message refinement. Panic condition is
      actually not changed.
* Remove `debug-print` feature.
    + Related items are now always available without any additional features.
    + The feature is removed since it pulls no additional dependencies and
      considered bothersome rather than useful.
    + Original intention of the flag is to make the feature semi-experimental,
      since the output format is not guaranteed to be stable. However, many
      types does not guarantee the stableness of `Display` and `Debug`
      formatting explicitly, so this is not considered worth doing.
* Internal improvements.
    + Pre-monomorphize methods of `Forest` and related types, in order to reduce
      code bloat.

## [0.0.3]

* Bump minimum supported rust version to 1.56.
* Now `Forest` and related types takes a node ID type as a type parameter.
    + You can implement custom ID types.
* `NodeIdU{8,16,32,64}` types are added.

### Changed (breaking)

* Bump minimum supported rust version to 1.56.
* Now `Forest` and related types takes a node ID type as a type parameter.
    + You can implement custom ID types.
    + A forest with the ID type `MyId` and the node data `MyData` is now
      `Forest<MyId, MyData>` type.
    + About node ID types and how to implement it, see the documentation for `dynamic` module.

### Added

* `NodeIdU{8,16,32,64}` types are added.
    + They are `u{8,16,32,64}` version of `NodeIdUsize`, and can be used both as
      internal node ID types and normal node ID types.

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

[Unreleased]: <https://gitlab.com/lo48576/treena/-/compare/v0.0.3...develop>
[0.0.3]: <https://gitlab.com/lo48576/treena/-/tags/v0.0.3>
[0.0.2]: <https://gitlab.com/lo48576/treena/-/tags/v0.0.2>
[0.0.1]: <https://gitlab.com/lo48576/treena/-/tags/v0.0.1>
