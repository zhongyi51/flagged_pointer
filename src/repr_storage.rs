use std::{
    ptr::NonNull,
    sync::atomic::{AtomicPtr, Ordering},
};

mod private {
    pub trait Sealed {}
}

/// A marker trait for atomic pointer storage.
pub trait AtomicPointerStorage: PointerStorage {
    fn compare_exchange(
        &self,
        current: NonNull<()>,
        new: NonNull<()>,
    ) -> Result<NonNull<()>, NonNull<()>>;
}

/// A storage trait for flagged pointers' `repr` field.
pub trait PointerStorage: Sized + private::Sealed {
    fn new(ptr: NonNull<()>) -> Self;
    fn load(&self) -> NonNull<()>;
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
        unsafe { NonNull::new_unchecked(self.load(Ordering::Acquire)) }
    }
    fn set(&mut self, ptr: NonNull<()>) -> NonNull<()> {
        let old = *self.get_mut();
        *self.get_mut() = ptr.as_ptr();
        unsafe { NonNull::new_unchecked(old) }
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
            Ok(ptr) => unsafe { Ok(NonNull::new_unchecked(ptr)) },
            Err(ptr) => unsafe { Err(NonNull::new_unchecked(ptr)) },
        }
    }
}
