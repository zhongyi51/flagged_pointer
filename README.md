# Flagged Pointer

A safe Rust abstraction for creating tagged pointers that store additional flag information within the unused bits of aligned pointers.

## Features

- **Type-safe**: Uses Rust's type system && compile time check to prevent misuse
- **Zero-cost**: No runtime overhead compared to raw tagged pointers
- **Flexible**: Works with various pointer types (`Box`, `Rc`, `Arc`, `NonNull`)
- **Arbitrary Flags**: Supports flags defined by `enumflags2`, also allow user define their own flag type

## Usage

### Basic Example

```rust
use flagged_pointer::FlaggedPtr;
use enumflags2::{bitflags, BitFlags};

#[bitflags]
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Color {
    Red = 1 << 0,
    Blue = 1 << 1,
    Green = 1 << 2,
}

let boxed = Box::new("hello world");
let flagged = FlaggedPtr::new(boxed, Color::Red | Color::Blue);

assert_eq!(*flagged, "hello world");
assert_eq!(flagged.flag(), Color::Red | Color::Blue);

// Update flags
flagged.set_flag(Color::Green.into());
assert_eq!(flagged.flag(), Color::Green);

// Extract original pointer and flags
let (recovered_box, flags) = flagged.dissolve();
assert_eq!(*recovered_box, "hello world");
assert_eq!(flags, Color::Green);
```

### With Different Pointer Types

```rust
use flagged_pointer::alias::*;
use std::sync::Arc;

#[bitflags]
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Color {
    Red = 1 << 0,
    Blue = 1 << 1,
    Green = 1 << 2,
}

// With Box
let boxed: FlaggedBox<i32, u8> = FlaggedBox::new(Box::new(42), Color::Red | Color::Blue);

// With Arc
let shared: FlaggedArc<String, Color> = FlaggedArc::new(Arc::new("hello".to_string()), Color::Red | Color::Blue);

// With slices
let slice: FlaggedBoxSlice<i32, Color> = FlaggedBoxSlice::new(Box::new([1, 2, 3, 4]), Color::Red | Color::Blue);
```

### With Trait Objects

```rust
use flagged_pointer::alias::*;
use std::sync::Arc;

// Use `ptr_meta` to get the alignment of the trait object
#[ptr_meta::pointee]
trait MyTrait {
    fn method(&self);
}

impl MyTrait for i32 {
    fn method(&self) {
        println!("i32 method");
    }
}

impl MyTrait for String {
    fn method(&self) {
        println!("String method");
    }
}

// With trait objects
let trait_obj: FlaggedBoxDyn<dyn MyTrait, Color> = FlaggedBoxDyn::new(Box::new(42), Color::Red | Color::Blue);
trait_obj.method(); // Prints "i32 method"

let trait_obj: FlaggedBoxDyn<dyn MyTrait, Color> = FlaggedBoxDyn::new(Box::new("hello".to_string()), Color::Red | Color::Blue);
trait_obj.method(); // Prints "String method"
```

## How It Works

The library exploits the fact that aligned pointers have unused low-order bits (e.g., 4-byte aligned pointers have 2 unused bits), 
stored pointer and flag bits are separated using bitwise operations, and the flag bits are stored in the unused bits of the pointer.
Due to the platform reason, high bits of the pointer are not used but I am working in progress.

## Limitations

For trait objects (e.g., 'dyn MyTrait'), their alignment cannot be determined in compile time,
so the assertion can only be done in runtime.

Also, `ptr_meta` is not stable yet, so you have to use `ptr_meta`

## Contributing

Contributions are welcome! Please feel free to submit issues or pull requests.

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

## Changelog

### 0.1.0
- Initial release
- Basic tagged pointer implementation
- Support for common pointer types
- Comprehensive documentation