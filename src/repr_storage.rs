use std::{
    ptr::NonNull,
    sync::atomic::{AtomicPtr, Ordering},
};

mod private {
    pub trait Sealed {}
}

/// A marker trait for atomic pointer storage.
pub trait AtomicPointerStorage: PointerStorage {
    /// Atomically replaces `current` with `new`, returning the previous value.
    ///
    /// # Panics
    /// Panics if the observed value is null. An `AtomicPtr` can be constructed
    /// independently of `FlaggedPtr`, so its non-null invariant is checked.
    fn compare_exchange(
        &self,
        current: NonNull<()>,
        new: NonNull<()>,
    ) -> Result<NonNull<()>, NonNull<()>>;
}

/// A storage trait for flagged pointers' `repr` field.
pub trait PointerStorage: Sized + private::Sealed {
    fn new(ptr: NonNull<()>) -> Self;
    /// Loads the stored pointer. Panics if the stored value is null.
    fn load(&self) -> NonNull<()>;
    /// Replaces the stored pointer. Panics if the previous value is null.
    fn set(&mut self, ptr: NonNull<()>) -> NonNull<()>;
}

impl private::Sealed for NonNull<()> {}

impl PointerStorage for NonNull<()> {
    fn new(ptr: NonNull<()>) -> Self {
        ptr
    }
    fn load(&self) -> NonNull<()> {
        *self
    }
    fn set(&mut self, ptr: NonNull<()>) -> NonNull<()> {
        let old = *self;
        *self = ptr;
        old
    }
}

impl private::Sealed for AtomicPtr<()> {}

impl PointerStorage for AtomicPtr<()> {
    fn new(ptr: NonNull<()>) -> Self {
        Self::new(ptr.as_ptr())
    }
    fn load(&self) -> NonNull<()> {
        NonNull::new(self.load(Ordering::Acquire)).expect("pointer storage must be non-null")
    }
    fn set(&mut self, ptr: NonNull<()>) -> NonNull<()> {
        let storage = self.get_mut();
        let old = NonNull::new(*storage).expect("pointer storage must be non-null");
        *storage = ptr.as_ptr();
        old
    }
}

impl AtomicPointerStorage for AtomicPtr<()> {
    fn compare_exchange(
        &self,
        current: NonNull<()>,
        new: NonNull<()>,
    ) -> Result<NonNull<()>, NonNull<()>> {
        let res = self.compare_exchange(
            current.as_ptr(),
            new.as_ptr(),
            Ordering::AcqRel,
            Ordering::Acquire,
        );

        match res {
            Ok(ptr) => Ok(NonNull::new(ptr).expect("pointer storage must be non-null")),
            Err(ptr) => Err(NonNull::new(ptr).expect("pointer storage must be non-null")),
        }
    }
}
