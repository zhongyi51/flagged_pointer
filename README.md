# Flagged Pointer

A safe Rust abstraction for creating tagged pointers that store additional flag information within the unused bits of aligned pointers.

## Features

- **Type-safe**: Uses Rust's type system && compile time check to prevent misuse
- **Compact thin pointers**: Flags share the pointer's unused alignment bits
- **Flexible**: Works with various pointer types (`Box`, `Rc`, `Arc`, `NonNull`)
- **Arbitrary Flags**: Supports flags defined by `enumflags2`, also allow user define their own flag type

## Usage

### Basic Example

```rust
use flagged_pointer::alias::FlaggedBox;
use enumflags2::{bitflags, BitFlags};

#[bitflags]
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Color {
    Red = 1 << 0,
    Blue = 1 << 1,
}

let boxed = Box::new("hello world");
let mut flagged = FlaggedBox::new(boxed, BitFlags::from(Color::Red));

assert_eq!(*flagged, "hello world");
assert_eq!(flagged.flag(), BitFlags::from(Color::Red));

// Update flags
flagged.set_flag(BitFlags::from(Color::Blue));
assert_eq!(flagged.flag(), BitFlags::from(Color::Blue));

// Extract original pointer and flags
let (recovered_box, flags) = flagged.dissolve();
assert_eq!(*recovered_box, "hello world");
assert_eq!(flags, BitFlags::from(Color::Blue));
```

### With Different Pointer Types

```rust
use flagged_pointer::alias::*;
use std::sync::Arc;
use enumflags2::{bitflags, BitFlags};

#[bitflags]
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Color {
    Red = 1 << 0,
    Blue = 1 << 1,
}

// With Box
let boxed: FlaggedBox<i32, BitFlags<Color>> = FlaggedBox::new(Box::new(42), BitFlags::from(Color::Red));

// With Arc
let shared: FlaggedArc<String, BitFlags<Color>> = FlaggedArc::new(Arc::new("hello".to_string()), BitFlags::from(Color::Red));
```

### With Trait Objects

```rust
use flagged_pointer::alias::*;
use enumflags2::{bitflags, BitFlags};
use ptr_meta::pointee;

#[bitflags]
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Color {
    Red = 1 << 0,
    Blue = 1 << 1,
}

#[pointee]
trait MySimpleTrait {
    fn get_value(&self) -> &str;
}

impl MySimpleTrait for String {
    fn get_value(&self) -> &str {
        self.as_str()
    }
}

// With trait objects
let trait_obj: FlaggedBoxDyn<dyn MySimpleTrait, BitFlags<Color>> = 
    FlaggedBoxDyn::new(Box::new("hello".to_string()), BitFlags::from(Color::Red | Color::Blue));
println!("Value: {}", trait_obj.get_value());
```

## How It Works

The library exploits the fact that aligned pointers have unused low-order bits (e.g., 4-byte aligned pointers have 2 unused bits), 
stored pointer and flag bits are separated using bitwise operations, and the flag bits are stored in the unused bits of the pointer.
Due to the platform reason, high bits of the pointer are not used but I am working in progress.

## Limitations

For trait objects (e.g., 'dyn MyTrait'), their alignment cannot be determined in compile time,
so the assertion can only be done in runtime.

The standard library's `ptr_metadata` API is still unstable, so trait objects use
the `ptr_meta` crate.

## Migrating to 0.3

Version 0.3 removes `PtrMeta::clone_storage`. Remove that method from custom
`PtrMeta` implementations. To support `FlaggedPtr::clone`, also implement
`ptr::ClonePtrMeta`: it clones the represented pointer through shared access,
not the metadata. The hook must preserve ownership and existing references to
the original pointee, including when cloning panics. Do not reconstruct a
temporary owning `Box` or create a mutable reference to the original value.

The crate supplies this hook for `NonNull`, `Rc`, `Arc`, `Box<T>` with `T: Clone`,
and `Box<[T]>` with `T: Clone`. Cloning a `Box<dyn Trait>` needs a hook that uses
the trait's own shared cloning operation, as in this complete example:

```rust
use enumflags2::{bitflags, BitFlags};
use flagged_pointer::{
    alias::FlaggedBoxDyn,
    ptr::{ptr_impl::WithMaskMeta, ClonePtrMeta, PtrMeta},
};
use std::ptr::NonNull;

#[bitflags]
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Flag {
    Marked = 1,
}

#[ptr_meta::pointee]
trait Value {
    fn number(&self) -> u64;
    fn clone_box(&self) -> Box<dyn Value>;
}

impl Value for u64 {
    fn number(&self) -> u64 {
        *self
    }

    fn clone_box(&self) -> Box<dyn Value> {
        Box::new(*self)
    }
}

impl Clone for Box<dyn Value> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

type ValueMeta = WithMaskMeta<dyn Value>;

// SAFETY: clone_box reads through &dyn Value and returns a new owned Box.
// It never takes ownership of the source or invalidates its shared references.
unsafe impl ClonePtrMeta<ValueMeta> for Box<dyn Value> {
    unsafe fn clone_storage_shared(ptr: NonNull<()>, meta: ValueMeta) -> Self {
        // SAFETY: The caller guarantees a live pointer, matching metadata,
        // and shared access to the pointee.
        unsafe { Self::map_pointee(ptr, meta).as_ref().clone_box() }
    }
}

let original: FlaggedBoxDyn<dyn Value, BitFlags<Flag>> =
    FlaggedBoxDyn::new(Box::new(42_u64), Flag::Marked.into());
let borrowed = &*original;
let cloned = original.clone();
assert_eq!(borrowed.number(), cloned.number());
assert_eq!(cloned.flag(), original.flag());
```

A trait object clone may choose a different concrete implementation with a
different alignment; cloning rechecks that the flags fit and panics safely if
they do not.

Pointer and flag type parameters are now invariant, so implicit lifetime
shortening through a flagged pointer is no longer available. Sharing atomic
flagged pointers also requires `Send` for the represented pointer and flags,
in addition to `Sync`, because replacement can transfer their values between
threads. Existing code using thread-safe owned pointers and ordinary bit flags
continues to work.

## Contributing

Contributions are welcome! Please feel free to submit issues or pull requests.

## License

- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

## Changelog

### 0.3.0 (2026-09-27)
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
  section above for the source compatibility changes.

### 0.1.0
- Initial release
- Basic tagged pointer implementation
- Support for common pointer types
- Comprehensive documentation

### 0.1.1
- `miri` tests
- All pointers with provanance

### 0.1.2
- implementation fix for `[T]` and `dyn T`
- implementation for `fmt::Pointer` trait
- add `FlaggedPtr::try_new` method

### 0.1.3
- more traits implementation
- remove unnecessary `unwrap` and check
- some bugfix
- better error handling with `thiserror` crate

### 0.2.0
- support for `AtomicPtr` for thin pointers
- improved methods
- more tests

### 0.2.1
- more methods
- optimize `PointerStorage::set` for atomic pointers

### 0.2.2
- better doc
- panic safe for `PtrMeta::clone_storage` method
