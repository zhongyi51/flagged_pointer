# Migrating to 0.3

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

[Back to the README](../README.md)
