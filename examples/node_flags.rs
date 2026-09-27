//! Keep two state bits on an owning node handle and measure its storage.
//!
//! Run with `cargo run --example node_flags`.

use enumflags2::{BitFlags, bitflags};
use flagged_pointer::alias::{FlaggedBox, FlaggedBoxSlice};
use std::mem::{align_of, size_of};

#[bitflags]
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum State {
    Visited = 1,
    Dirty = 2,
}

struct Node {
    key: u32,
    value: u32,
}

struct PlainNodeHandle {
    node: Box<Node>,
    state: BitFlags<State>,
}

type CompactNodeHandle = FlaggedBox<Node, BitFlags<State>>;

fn main() {
    // This example requires Node alignment >= 4, as on the measured x86_64
    // target. No extra alignment is requested just to obtain flag bits.
    let mut plain = PlainNodeHandle {
        node: Box::new(Node { key: 7, value: 10 }),
        state: State::Visited.into(),
    };
    let mut compact =
        CompactNodeHandle::new(Box::new(Node { key: 7, value: 10 }), State::Visited.into());

    plain.node.value += 1;
    plain.state |= State::Dirty;
    compact.value += 1;
    compact.set_flag(compact.flag() | State::Dirty);

    let (node, state) = compact.dissolve();
    assert_eq!((node.key, node.value), (plain.node.key, plain.node.value));
    assert_eq!(state, plain.state);
    assert!(state.contains(State::Dirty));

    println!(
        "Target: {}-{}, {}-bit pointers",
        std::env::consts::ARCH,
        std::env::consts::OS,
        usize::BITS,
    );
    println!("Node alignment: {} bytes", align_of::<Node>());
    println!("Box<Node>: {} bytes", size_of::<Box<Node>>());
    println!(
        "Box<Node> + separate flags: {} bytes",
        size_of::<PlainNodeHandle>(),
    );
    println!("FlaggedBox<Node>: {} bytes", size_of::<CompactNodeHandle>());
    println!(
        "FlaggedBoxSlice<Node>: {} bytes (includes length metadata)",
        size_of::<FlaggedBoxSlice<Node, BitFlags<State>>>(),
    );
    println!("These are handle sizes on this target, not heap usage or timing results.");
    println!("Both owning handles allocate the same Node separately.");
}
