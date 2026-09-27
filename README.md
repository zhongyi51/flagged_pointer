# Flagged Pointer

[![crates.io](https://img.shields.io/crates/v/flagged_pointer.svg)](https://crates.io/crates/flagged_pointer)
[![Documentation](https://docs.rs/flagged_pointer/badge.svg)](https://docs.rs/flagged_pointer)
[![CI](https://github.com/zhongyi51/flagged_pointer/actions/workflows/rust.yml/badge.svg)](https://github.com/zhongyi51/flagged_pointer/actions/workflows/rust.yml)
[![Rust 1.85+](https://img.shields.io/badge/rust-1.85%2B-blue.svg)](Cargo.toml)

Store typed flags in a pointer's unused alignment bits while retaining the
ownership behavior of `Box`, `Rc`, or `Arc`. Raw `NonNull` pointers are also
supported. For thin pointers, flags fit in the pointer's own storage; slices
and trait objects keep their metadata separately.

Use this when a data structure has many pointer handles with a few state bits,
such as visited or dirty flags on node handles. Prefer ordinary fields when
space is not a constraint, when the pointee has insufficient alignment, or
when state belongs to the shared object rather than each individual handle.
This crate does not provide memory reclamation or a complete concurrent data
structure.

```sh
cargo add flagged_pointer enumflags2
```

## Example: node state

```rust
use enumflags2::{bitflags, BitFlags};
use flagged_pointer::alias::FlaggedBox;

#[bitflags]
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum State {
    Visited = 1,
    Dirty = 2,
}

// This example requires Node alignment >= 4 (as on x86_64).
struct Node {
    key: u32,
    value: u32,
}

let mut node: FlaggedBox<Node, BitFlags<State>> =
    FlaggedBox::new(Box::new(Node { key: 7, value: 10 }), State::Visited.into());
node.value += 1;
node.set_flag(State::Visited | State::Dirty);

let (owned, state) = node.dissolve();
assert_eq!((owned.key, owned.value), (7, 11));
assert!(state.contains(State::Dirty));
```

Run the [complete example](examples/node_flags.rs), which also compares handle
sizes on your target:

```sh
cargo run --example node_flags
```

Measured on x86_64 Linux with Rust 1.98.1 and 1.85.0:

| Handle | Size |
| --- | ---: |
| `Box<Node>` | 8 bytes |
| `Box<Node>` with a separate `BitFlags<State>` field | 16 bytes |
| `FlaggedBox<Node, BitFlags<State>>` | 8 bytes |
| `FlaggedBoxSlice<Node, BitFlags<State>>` | 16 bytes |

These are handle sizes for this example on this target, not timing results or
total heap usage. Both owning node handles allocate the same `Node` separately;
the slice handle also stores its length. Run the example to check your target.

`FlaggedBox`, `FlaggedRc`, and `FlaggedArc` have slice and trait-object variants;
see the [alias reference](https://docs.rs/flagged_pointer/latest/flagged_pointer/alias/index.html)
for the full list. Cloning a boxed pointer clones its contents, while cloning
an `Rc` or `Arc` shares the allocation. Flags belong to each handle.

## Alignment and safety

An alignment of 4 leaves two low address bits available; alignment of 8 leaves
three. All bits used by the **flag type** must fit, even if a particular value
sets fewer bits. `new` checks compatibility at compile time where possible and
at runtime otherwise. Use `try_new` when incompatibility should return an
error instead of panicking; the error retains the supplied pointer.

The built-in pointer and flag implementations provide a safe API. Implementing
custom pointer or flag traits is `unsafe` and requires following their
[documented contracts](https://docs.rs/flagged_pointer/latest/flagged_pointer/).
Tagged pointer arithmetic preserves provenance. CI runs Miri with strict
provenance under both Stacked Borrows and Tree Borrows; these checks cover the
tests, not a proof of soundness for every use.

Slice lengths and trait-object metadata are stored separately, so a tagged
fat pointer is not necessarily one machine word. Trait objects use `ptr_meta`;
their concrete alignment is checked at runtime. Atomic aliases support atomic
pointer/flag replacement, but do not make the pointee itself atomic or supply
safe concurrent dereferencing and reclamation.

## Compatibility and contributing

The minimum supported Rust version is **1.85** (edition 2024), checked in CI
alongside stable. Version 0.3 changes the custom pointer cloning contract and
tightens variance and atomic sharing bounds. See the
[0.3 migration guide](docs/migrating-to-0.3.md) and [changelog](CHANGELOG.md).

Bug reports with a small reproducer and the Rust version are welcome. For API
proposals, include the intended data structure or use case. To check a change:

```sh
cargo fmt --all -- --check
cargo test --all-targets
cargo test --doc
cargo clippy --all-targets -- -D warnings
```

Unsafe-code changes should also run the Miri configurations in
[CI](.github/workflows/rust.yml). Please keep safety reasoning next to the code
and add a regression test for fixes where practical.

Licensed under [MIT](LICENSE-MIT). If the crate is useful to you, a GitHub star
is welcome.
