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
}

let boxed = Box::new("hello world");
let mut flagged = FlaggedPtr::new(boxed, BitFlags::from(Color::Red));

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

Also, `ptr_meta` is not stable yet, so you have to use `ptr_meta` crate for your trait objects.

## Contributing

Contributions are welcome! Please feel free to submit issues or pull requests.

## License

- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

## Changelog

### 0.1.0
- Initial release
- Basic tagged pointer implementation
- Support for common pointer types
- Comprehensive documentation

### 0.1.1
- `miri` tests
- All pointers with provanance
