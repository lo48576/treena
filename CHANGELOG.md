# Change Log

## [Unreleased]

* Implement `std::error::Error` trait for an error type.
* Make more long-living reference from `Node::data()`.
* Add `NodeMut::into_data_mut_ref()`.

### Added

* Implement `std::error::Error` trait for an error type.
* Add `NodeMut::into_data_mut_ref()` that returns reference to the data with longer lifetime.

### Changed (non-breaking)
* Make more long-living reference from `Node::data()`.

## [0.0.1]

Initial release.

[Unreleased]: <https://github.com/lo48576/fbxcel/compare/v0.0.1...develop>
[0.0.1]: <https://github.com/lo48576/fbxcel/releases/tag/v0.0.1>
