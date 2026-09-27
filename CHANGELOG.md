# Changelog

## 0.3.0 (2026-09-27)
- Declare Rust 1.85 as the minimum supported version.
- Fix raw slice pointer conversions without creating references to their data.
- Preserve address bits outside the flag mask and check public atomic storage
  operations for null pointers.
- Replace `PtrMeta::clone_storage` with `ClonePtrMeta` for shared cloning that
  preserves references to the original pointee.
- Revalidate pointer/flag compatibility after cloning.
- Preserve ownership when flag decoding unwinds during `dissolve`.
- Tighten variance and atomic sharing requirements to prevent lifetime and
  cross-thread ownership violations.
- Clarify unsafe pointer conversion and cloning contracts. See the migration
  [guide](docs/migrating-to-0.3.md) for the source compatibility changes.

## 0.1.0
- Initial release
- Basic tagged pointer implementation
- Support for common pointer types
- Comprehensive documentation

## 0.1.1
- `miri` tests
- All pointers with provenance

## 0.1.2
- implementation fix for `[T]` and `dyn T`
- implementation for `fmt::Pointer` trait
- add `FlaggedPtr::try_new` method

## 0.1.3
- more traits implementation
- remove unnecessary `unwrap` and check
- some bugfix
- better error handling with `thiserror` crate

## 0.2.0
- support for `AtomicPtr` for thin pointers
- improved methods
- more tests

## 0.2.1
- more methods
- optimize `PointerStorage::set` for atomic pointers

## 0.2.2
- better doc
- panic safe for `PtrMeta::clone_storage` method
