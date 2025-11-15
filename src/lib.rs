//! # Flagged Pointer
//!
//! A library for creating tagged pointers that store flags within the unused bits of pointers.
//!
//! This crate provides a safe abstraction for tagged pointers by utilizing unused bits
//! in aligned pointers to store additional flag information. This is particularly useful
//! for implementing space-efficient data structures like tagged unions or specialized
//! memory allocators.
use std::{
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

use crate::{flag::FlagMeta, ptr::PtrMeta};

pub mod flag;
pub mod ptr;
pub mod error;

/// A pointer that stores flags within unused bits of the pointer representation.
///
/// This struct combines a pointer and flag information into a single `usize` value
/// by utilizing unused bits in the pointer due to alignment requirements.
///
/// # Type Parameters
/// - `P`: The pointer type (e.g., `Box<T>`, `NonNull<T>`, `Rc<T>`)
/// - `F`: The flag type (must implement `FlagMeta`)
/// - `M`: Metadata associated with the pointer
///
/// # Examples
///
/// ```
/// use flagged_pointer::FlaggedPtr;
/// use enumflags2::{bitflags, BitFlags};
///
/// #[bitflags]
/// #[repr(u8)]
/// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// enum Color {
///     Red = 1 << 0,
///     Blue = 1 << 1,
///     Green = 1 << 2,
/// }
///
/// let boxed = Box::new("hello");
/// let flagged = FlaggedPtr::new(boxed, Color::Red | Color::Blue);
///
/// assert_eq!(*flagged, "hello");
/// assert_eq!(flagged.flag(), Color::Red | Color::Blue);
/// ```
///
/// # Example with trait object
///
/// ```
/// use flagged_pointer::alias::*;
/// use std::sync::Arc;
/// use ptr_meta::pointee;
/// use enumflags2::{bitflags,BitFlags};
///
/// #[bitflags]
/// #[repr(u8)]
/// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// enum Color {
///     Red = 1 << 0,
///     Blue = 1 << 1,
///     Green = 1 << 2,
/// }
///
/// #[ptr_meta::pointee]
/// trait MyTrait {
///    fn method(&self);
/// }
///
/// impl MyTrait for i64 {
///    fn method(&self) {
///        println!("i32 method");
///    }
/// }
///
/// impl MyTrait for String {
///    fn method(&self) {
///        println!("String method");
///    }
/// }
///
/// let trait_obj: FlaggedBoxDyn<dyn MyTrait, BitFlags<Color>> = FlaggedBoxDyn::new(Box::new(42_i64), Color::Red | Color::Blue);
/// trait_obj.method();
/// let trait_obj: FlaggedArcDyn<dyn MyTrait, BitFlags<Color>> = FlaggedArcDyn::new(Arc::new("hello".to_string()), Color::Red | Color::Blue);
/// trait_obj.method();
///
/// ```
pub struct FlaggedPtr<P, F, M>
where
    P: PtrMeta<M>,
    F: FlagMeta,
    M: Copy,
{
    /// The combined pointer and flag representation.
    ///
    /// This stores both the actual pointer value and the flag bits.
    /// The unused bits due to alignment are used for flags.
    repr: NonNull<()>,

    /// Metadata associated with the pointer.
    ///
    /// This is used for fat pointers (like slices or trait objects)
    /// to store additional information like length or vtable.
    meta: M,

    /// Phantom data to ensure proper variance and ownership semantics.
    _marker: PhantomData<(P, F)>,
}

impl<P, F, M> FlaggedPtr<P, F, M>
where
    P: PtrMeta<M>,
    F: FlagMeta,
    M: Copy,
{
    /// Assert that the pointer and flag bits do not overlap.
    /// This assertion may still pass because `P`'s alignment cannot be guaranteed at compile time.
    const _ASSERT: () = assert!(
        P::USED_PTR_BITS_MASK & F::USED_FLAG_BITS_MASK == 0,
        "Pointer and flag bits overlap - this indicates an alignment issue or too many flag bits"
    );

    /// Creates a new `FlaggedPtr` from a pointer and flags.
    ///
    /// # Arguments
    /// - `ptr`: The pointer to store
    /// - `flag`: The flags to encode in the unused bits
    ///
    /// # Examples
    ///
    /// ```
    /// use flagged_pointer::FlaggedPtr;
    /// use enumflags2::bitflags;
    /// use std::ptr::NonNull;
    ///
    /// #[bitflags]
    /// #[repr(u8)]
    /// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    /// enum MyFlags {
    ///     A = 1 << 0,
    ///     B = 1 << 1,
    /// }
    ///
    /// let boxed = Box::new(42);
    /// let flagged = FlaggedPtr::new(boxed, MyFlags::A | MyFlags::B);
    /// assert_eq!(*flagged, 42);
    /// ```
    ///
    /// # Panics
    /// Panics if the pointer and flag bits overlap, which should not happen
    /// for properly aligned pointers and reasonable flag values.
    pub fn new(ptr: P, flag: F) -> Self {
        // Static assert, which will be checked at compile time.
        #[allow(path_statements)]
        Self::_ASSERT;
        let (ptr, meta) = ptr.to_pointee_ptr_and_meta();
        // Runtime assert, which will be checked at runtime, for `dyn XXX` types.
        assert!(
            F::mask() & P::mask(meta) == 0,
            "Pointer and flag bits overlap - this indicates an alignment issue or too many flag bits"
        );
        let repr = unsafe { NonNull::new_unchecked(ptr.as_ptr().map_addr(|addr| addr | flag.to_usize()))};
        Self {
            repr,
            meta,
            _marker: PhantomData,
        }
    }

    /// Creates a new `FlaggedPtr` from a pointer and flags, returning an error if they overlap.
    ///
    /// # Arguments
    /// - `ptr`: The pointer to store
    /// - `flag`: The flags to encode in the unused bits
    ///
    /// # Returns
    /// - `Ok(Self)` if the pointer and flag bits do not overlap
    /// - `Err(FlagOverlapError)` if they do overlap
    ///
    /// # Examples
    ///
    /// ```
    /// use flagged_pointer::FlaggedPtr;
    /// use enumflags2::{bitflags,BitFlags};
    /// use std::ptr::NonNull;
    ///
    /// #[bitflags]
    /// #[repr(u8)]
    /// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    /// enum MyFlags {
    ///     A = 1 << 0,
    ///     B = 1 << 1,
    /// }
    /// 
    /// #[bitflags]
    /// #[repr(u8)]
    /// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    /// enum MyFlagsInvalid {
    ///     A = 1 << 6,
    ///     B = 1 << 7,
    /// }
    ///
    /// let boxed = Box::new(42);
    /// let flagged:Result<FlaggedPtr<_,BitFlags<MyFlags>,_>,_> = FlaggedPtr::try_new(boxed.clone(), MyFlags::A.into());
    /// assert!(flagged.is_ok());
    /// 
    /// let flagged:Result<FlaggedPtr<_,BitFlags<MyFlagsInvalid>,_>,_> = FlaggedPtr::try_new(boxed, MyFlagsInvalid::B.into());
    /// assert!(flagged.is_err());
    /// ```
    pub fn try_new(ptr: P, flag: F) -> Result<Self, crate::error::FlagOverlapError> {
        let (ptr, meta) = ptr.to_pointee_ptr_and_meta();
        // Runtime assert, which will be checked at runtime, for `dyn XXX` types.
        if F::mask() & P::mask(meta) != 0 {
            // allowing drop origin pointer
            unsafe { P::from_pointee_ptr_and_meta(ptr, meta) };
            return Err(crate::error::FlagOverlapError::new(P::mask(meta), F::mask()));
        }
        let repr = unsafe { NonNull::new_unchecked(ptr.as_ptr().map_addr(|addr| addr | flag.to_usize()))};
        Ok(Self {
            repr,
            meta,
            _marker: PhantomData,
        })
    }
}

impl<P, F, M> FlaggedPtr<P, F, M>
where
    P: PtrMeta<M>,
    F: FlagMeta,
    M: Copy,
{
    /// Returns the flags stored in this pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use flagged_pointer::FlaggedPtr;
    /// use enumflags2::bitflags;
    ///
    /// #[bitflags]
    /// #[repr(u8)]
    /// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    /// enum MyFlags {
    ///     A = 1 << 0,
    ///     B = 1 << 1,
    /// }
    ///
    /// let boxed = Box::new(123);
    /// let flagged = FlaggedPtr::new(boxed, MyFlags::A | MyFlags::B);
    /// assert_eq!(flagged.flag(), MyFlags::A | MyFlags::B);
    /// ```
    pub fn flag(&self) -> F {
        let flag_repr = F::mask() & self.repr.as_ptr() as usize;
        // SAFETY: We know the flag bits are valid because they were set by `new`
        // or `set_flag`, both of which ensure the bits are within the valid range
        unsafe { F::from_usize(flag_repr) }
    }

    /// Sets new flags for this pointer.
    ///
    /// # Arguments
    /// - `flag`: The new flags to set
    ///
    /// # Examples
    ///
    /// ```
    /// use flagged_pointer::FlaggedPtr;
    /// use enumflags2::bitflags;
    ///
    /// #[bitflags]
    /// #[repr(u8)]
    /// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    /// enum MyFlags {
    ///     A = 1 << 0,
    ///     B = 1 << 1,
    /// }
    ///
    /// let boxed = Box::new(123);
    /// let mut flagged = FlaggedPtr::new(boxed, MyFlags::A | MyFlags::B);
    /// flagged.set_flag(MyFlags::B.into());
    /// assert_eq!(flagged.flag(), MyFlags::B);
    /// ```
    pub fn set_flag(&mut self, flag: F) {
        let flag_repr = flag.to_usize();
        let ptr_repr = self.ptr_repr();
        self.repr = ptr_repr.map_addr(|addr| addr | flag_repr);
    }

    /// Consumes this `FlaggedPtr` and returns the original pointer and flags.
    ///
    /// This is the inverse operation of `new()`.
    ///
    /// # Returns
    /// A tuple containing `(original_pointer, flags)`
    ///
    /// # Examples
    ///
    /// ```
    /// use flagged_pointer::FlaggedPtr;
    /// use enumflags2::bitflags;
    ///
    /// #[bitflags]
    /// #[repr(u8)]
    /// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    /// enum MyFlags {
    ///     A = 1 << 0,
    ///     B = 1 << 1,
    /// }
    ///
    /// let boxed = Box::new(42);
    /// let flagged = FlaggedPtr::new(boxed, MyFlags::A | MyFlags::B);
    /// let (recovered_box, flags) = flagged.dissolve();
    ///
    /// assert_eq!(*recovered_box, 42);
    /// assert_eq!(flags, MyFlags::A | MyFlags::B);
    /// ```
    pub fn dissolve(self) -> (P, F) {
        let ptr_repr = self.repr.as_ptr();
        let flag_repr = F::mask() & ptr_repr as usize;

        // SAFETY: We know these values are valid because:
        // 1. The pointer was originally created from a valid P
        // 2. We've masked out the flag bits, leaving only valid pointer bits
        // 3. The metadata is preserved from construction
        let ptr = unsafe {
            P::from_pointee_ptr_and_meta(self.ptr_repr(), self.meta)
        };
        let flag = unsafe { F::from_usize(flag_repr) };

        // Prevent the destructor from running since we're taking ownership
        mem::forget(self);
        (ptr, flag)
    }

    fn ptr_repr(&self) -> NonNull<()> {
        let ptr_val = self.repr.as_ptr().map_addr(|addr| addr & P::mask(self.meta)); 
        unsafe { NonNull::new_unchecked(ptr_val) }
    }

    /// Returns a raw pointer to the pointee.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the pointer is valid for the lifetime of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use flagged_pointer::FlaggedPtr;
    /// use enumflags2::bitflags;
    ///
    /// #[bitflags]
    /// #[repr(u8)]
    /// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    /// enum MyFlags {
    ///     A = 1 << 0,
    ///     B = 1 << 1,
    /// }
    ///
    /// let boxed = Box::new(123);
    /// let flagged = FlaggedPtr::new(boxed, MyFlags::A | MyFlags::B);
    /// let ptr = flagged.as_ptr();
    /// assert_eq!(unsafe { *ptr.as_ref() }, 123);
    /// ```
    pub fn as_ptr(&self) -> NonNull<P::Pointee> {
        let ptr_repr = self.ptr_repr();
        unsafe { P::map_pointee(ptr_repr, self.meta) }
    }

    /// Consumes this `FlaggedPtr` and returns the original pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use flagged_pointer::FlaggedPtr;
    /// use enumflags2::bitflags;
    ///
    /// #[bitflags]
    /// #[repr(u8)]
    /// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    /// enum MyFlags {
    ///     A = 1 << 0,
    ///     B = 1 << 1,
    /// }
    ///
    /// let boxed = Box::new(123);
    /// let flagged = FlaggedPtr::new(boxed, MyFlags::A | MyFlags::B);
    /// let ptr = flagged.into_ptr();
    /// assert_eq!(unsafe { *ptr.as_ref() }, 123);
    /// ```
    pub fn into_ptr(self) -> P {
        let ptr_repr = self.ptr_repr();
        let ptr = unsafe { P::from_pointee_ptr_and_meta(ptr_repr, self.meta) };
        // Prevent the destructor from running since we're taking ownership
        mem::forget(self);
        ptr
    }

    /// Consumes this `FlaggedPtr` and returns the original flags.
    ///
    /// # Examples
    ///
    /// ```
    /// use flagged_pointer::FlaggedPtr;
    /// use enumflags2::bitflags;
    ///
    /// #[bitflags]
    /// #[repr(u8)]
    /// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    /// enum MyFlags {
    ///     A = 1 << 0,
    ///     B = 1 << 1,
    /// }
    ///
    /// let boxed = Box::new(123);
    /// let flagged = FlaggedPtr::new(boxed, MyFlags::A | MyFlags::B);
    /// let flag = flagged.into_flag();
    /// assert_eq!(flag, MyFlags::A | MyFlags::B);
    /// ```
    pub fn into_flag(self) -> F {
        self.flag()
    }

    /// Replaces the flags of this `FlaggedPtr` with the given `new` flags.
    ///
    /// # Returns
    /// The previous flags.
    ///
    /// # Examples
    ///
    /// ```
    /// use flagged_pointer::FlaggedPtr;
    /// use enumflags2::{BitFlags, bitflags};
    ///
    /// #[bitflags]
    /// #[repr(u8)]
    /// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    /// enum MyFlags {
    ///     A = 1 << 0,
    ///     B = 1 << 1,
    /// }
    ///
    /// let boxed = Box::new(123);
    /// let mut flagged = FlaggedPtr::new(boxed.clone(), BitFlags::from(MyFlags::A | MyFlags::B));
    /// let prev_flag = flagged.replace_flag(BitFlags::from(MyFlags::B));
    /// assert_eq!(prev_flag, BitFlags::from(MyFlags::A | MyFlags::B));
    /// assert_eq!(flagged.into_flag(), BitFlags::from(MyFlags::B));
    /// ```
    pub fn replace_flag(&mut self, new: F) -> F{
        let prev_flag=self.flag();
        self.set_flag(new);
        prev_flag
    }
}

impl<P, F, M> Deref for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M> + Deref<Target = P::Pointee>,
    F: FlagMeta,
    M: Copy,
{
    type Target = P::Pointee;

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // 1. We maintain the invariant that `self.repr` always contains valid pointer bits
        // 2. `as_ptr()` correctly masks out flag bits to get the actual pointer
        // 3. The pointer is guaranteed to be valid for the lifetime of self
        unsafe { self.as_ptr().as_ref() }
    }
}

impl<P, F, M> DerefMut for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M> + DerefMut<Target = P::Pointee>,
    F: FlagMeta,
    M: Copy,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: Same safety guarantees as Deref, plus we have exclusive access
        unsafe { self.as_ptr().as_mut() }
    }
}

impl<P, F, M> Drop for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M>,
    F: FlagMeta,
    M: Copy,
{
    fn drop(&mut self) {
        // SAFETY:
        // 1. We're reconstructing the original pointer to ensure proper cleanup
        // 2. The pointer bits are extracted using the same mask as during construction
        // 3. The metadata is preserved from construction
        // 4. The value is dropped immediately, preventing use-after-free
        unsafe {
            let _ = P::from_pointee_ptr_and_meta(self.ptr_repr(), self.meta);
        }
    }
}

impl<P,F,M> AsRef<P::Pointee> for FlaggedPtr<P,F,M>
where
    P: PtrMeta<M> + Deref<Target = P::Pointee>,
    F: FlagMeta,
    M: Copy,
{
    fn as_ref(&self) -> &P::Pointee {
        self.deref()
    }
}

impl<P,F,M> AsMut<P::Pointee> for FlaggedPtr<P,F,M>
where
    P: PtrMeta<M> + DerefMut<Target = P::Pointee>,
    F: FlagMeta,
    M: Copy,
{
    fn as_mut(&mut self) -> &mut P::Pointee {
        self.deref_mut()
    }
}

impl<P, F, M> Clone for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M> + Clone,
    F: FlagMeta,
    M: Copy,
{
    fn clone(&self) -> Self {
        let ptr_repr = self.ptr_repr();
        let cloned_ptr_storage = unsafe { P::clone_storage(ptr_repr, self.meta) };
        let flag = self.flag();
        Self::new(cloned_ptr_storage, flag)
    }
}

impl<P, F, M> std::fmt::Pointer for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M>,
    F: FlagMeta,
    M: Copy,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ptr = self.as_ptr();
        std::fmt::Pointer::fmt(&ptr, f)
    }
}

unsafe impl<P, F, M> Send for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M> + Send,
    F: FlagMeta + Send,
    M: Send + Copy,
{
}

unsafe impl<P, F, M> Sync for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M> + Sync,
    F: FlagMeta + Sync,
    M: Sync + Copy,
{
}

unsafe impl<P, F, M> stable_deref_trait::StableDeref for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M> + Deref<Target = P::Pointee> + stable_deref_trait::StableDeref,
    F: FlagMeta,
    M: Copy,
{
}

unsafe impl<P, F, M> stable_deref_trait::CloneStableDeref for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M> + Deref<Target = P::Pointee> + stable_deref_trait::CloneStableDeref,
    F: FlagMeta,
    M: Copy,
{
}

/// Type aliases for common pointer combinations.
///
/// This module provides convenient type aliases for using `FlaggedPtr`
/// with standard pointer types like `Box`, `Rc`, `Arc`, and `NonNull`.
///
/// # Available Types
///
/// - `FlaggedNonNull<T,F>` - For `NonNull<T>` pointers
/// - `FlaggedBox<T,F>` - For `Box<T>` pointers
/// - `FlaggedRc<T,F>` - For `Rc<T>` pointers
/// - `FlaggedArc<T,F>` - For `Arc<T>` pointers
///
/// And their slice and dynamic dispatch variants:
/// - `FlaggedNonNullSlice<T,F>` - For `NonNull<[T]>` slice pointers
/// - `FlaggedBoxDyn<T,F>` - For `Box<dyn Trait>` trait objects
/// - etc.
///
/// # Examples
///
/// ```
/// use flagged_pointer::alias::FlaggedBox;
/// use enumflags2::{bitflags, BitFlags};
///
/// #[bitflags]
/// #[repr(u8)]
/// #[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// enum Status {
///     Active = 1 << 0,
///     Dirty = 1 << 1,
/// }
///
/// let boxed = Box::new("hello");
/// let flagged: FlaggedBox<_, BitFlags<Status>> = FlaggedBox::new(boxed, Status::Active.into());
/// ```
pub mod alias {
    use std::{ptr::NonNull, rc::Rc, sync::Arc};

    use crate::{FlaggedPtr, ptr::ptr_impl::WithMaskMeta};

    /// A flagged `NonNull<T>` pointer.
    pub type FlaggedNonNull<T, F> = FlaggedPtr<NonNull<T>, F, ()>;

    /// A flagged `NonNull<[T]>` slice pointer.
    pub type FlaggedNonNullSlice<T, F> = FlaggedPtr<NonNull<[T]>, F, usize>;

    /// A flagged `NonNull<dyn Trait>` trait object pointer.
    pub type FlaggedNonNullDyn<T, F> = FlaggedPtr<NonNull<T>, F, WithMaskMeta<T>>;

    /// A flagged `Box<T>` pointer.
    pub type FlaggedBox<T, F> = FlaggedPtr<Box<T>, F, ()>;

    /// A flagged `Box<[T]>` slice pointer.
    pub type FlaggedBoxSlice<T, F> = FlaggedPtr<Box<[T]>, F, usize>;

    /// A flagged `Box<dyn Trait>` trait object pointer.
    pub type FlaggedBoxDyn<T, F> = FlaggedPtr<Box<T>, F, WithMaskMeta<T>>;

    /// A flagged `Rc<T>` pointer.
    pub type FlaggedRc<T, F> = FlaggedPtr<Rc<T>, F, ()>;

    /// A flagged `Rc<[T]>` slice pointer.
    pub type FlaggedRcSlice<T, F> = FlaggedPtr<Rc<[T]>, F, usize>;

    /// A flagged `Rc<dyn Trait>` trait object pointer.
    pub type FlaggedRcDyn<T, F> = FlaggedPtr<Rc<T>, F, WithMaskMeta<T>>;

    /// A flagged `Arc<T>` pointer.
    pub type FlaggedArc<T, F> = FlaggedPtr<Arc<T>, F, ()>;

    /// A flagged `Arc<[T]>` slice pointer.
    pub type FlaggedArcSlice<T, F> = FlaggedPtr<Arc<[T]>, F, usize>;

    /// A flagged `Arc<dyn Trait>` trait object pointer.
    pub type FlaggedArcDyn<T, F> = FlaggedPtr<Arc<T>, F, WithMaskMeta<T>>;
}

#[cfg(test)]
mod tests {
    use crate::alias::FlaggedBoxSlice;

    use super::*;
    use enumflags2::{BitFlags, bitflags};
    use std::sync::Arc;

    #[bitflags]
    #[repr(u8)]
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    enum TestFlag {
        A = 1 << 0, // 0b001
        B = 1 << 1, // 0b010
        C = 1 << 2, // 0b100
    }

    #[test]
    fn test_box_sized() {
        let mut data = 42;
        let ptr = Box::new(&mut data);
        let flags = TestFlag::A | TestFlag::C;

        let mut flagged_ptr = FlaggedPtr::new(ptr, flags);

        assert_eq!(**flagged_ptr, 42);
        **flagged_ptr = 99;
        assert_eq!(**flagged_ptr, 99);

        assert_eq!(flagged_ptr.flag(), flags);

        let new_flags = TestFlag::A;
        flagged_ptr.set_flag(new_flags.into());
        assert_eq!(flagged_ptr.flag(), new_flags);

        let (ptr_out, flags_out) = flagged_ptr.dissolve();
        assert_eq!(flags_out, new_flags);
        assert_eq!(**ptr_out, 99);
    }

    #[test]
    fn test_arc_sized_clone() {
        let data = Arc::new(1337_u64);
        let flags = TestFlag::A | TestFlag::B;

        let flagged_ptr1 = FlaggedPtr::new(data, flags);
        let (cloned, _) = flagged_ptr1.clone().dissolve();
        assert_eq!(Arc::strong_count(&cloned), 2);

        let flagged_ptr2 = flagged_ptr1.clone();

        assert_eq!(*flagged_ptr1, 1337);
        assert_eq!(flagged_ptr1.flag(), flags);
        assert_eq!(*flagged_ptr2, 1337);
        assert_eq!(flagged_ptr2.flag(), flags);

        assert_eq!(Arc::strong_count(&flagged_ptr1.dissolve().0), 3);
    }

    #[test]
    fn test_box_slice() {
        let data: Box<[u64]> = Box::new([1, 2, 3, 4, 5]);
        let flags = TestFlag::B;

        let mut flagged_ptr: FlaggedPtr<Box<[u64]>, _, usize> =
            FlaggedBoxSlice::new(data, flags.into());

        assert_eq!(&*flagged_ptr, &[1, 2, 3, 4, 5]);
        flagged_ptr[2] = 99;
        assert_eq!(&*flagged_ptr, &[1, 2, 99, 4, 5]);

        assert_eq!(flagged_ptr.flag(), flags);
        flagged_ptr.set_flag(TestFlag::A.into());
        assert_eq!(flagged_ptr.flag(), TestFlag::A);

        let (ptr_out, flags_out): (_, BitFlags<TestFlag>) = flagged_ptr.dissolve();
        assert_eq!(flags_out, TestFlag::A);
        assert_eq!(&*ptr_out, &[1, 2, 99, 4, 5]);
    }

    #[ptr_meta::pointee]
    trait TestDyn: Send + Sync {
        fn value(&self) -> i32;
        fn set_value(&mut self, val: i32);
    }

    struct DynImpl {
        val: i128,
    }

    impl TestDyn for DynImpl {
        fn value(&self) -> i32 {
            self.val as i32
        }
        fn set_value(&mut self, val: i32) {
            self.val = val as i128;
        }
    }

    #[test]
    fn test_box_dyn_trait() {
        let instance: Box<dyn TestDyn> = Box::new(DynImpl { val: 100 });
        let flags = TestFlag::C;

        let mut flagged_ptr: FlaggedPtr<
            Box<dyn TestDyn>,
            BitFlags<TestFlag, u8>,
            ptr::ptr_impl::WithMaskMeta<dyn TestDyn>,
        > = FlaggedPtr::new(instance, flags.into());

        assert_eq!(flagged_ptr.value(), 100);
        flagged_ptr.set_value(200);
        assert_eq!(flagged_ptr.value(), 200);

        assert_eq!(flagged_ptr.flag(), flags);
        flagged_ptr.set_flag(TestFlag::A | TestFlag::B);
        assert_eq!(flagged_ptr.flag(), TestFlag::A | TestFlag::B);

        let (ptr_out, flags_out) = flagged_ptr.dissolve();
        assert_eq!(flags_out, TestFlag::A | TestFlag::B);
        assert_eq!(ptr_out.value(), 200);
    }

    #[test]
    fn test_arc_send_sync() {
        let data = Arc::new(vec![10, 20, 30]);
        let flags = TestFlag::A;

        let flagged_ptr: FlaggedPtr<Arc<Vec<i32>>, BitFlags<TestFlag, u8>, ()> =
            FlaggedPtr::new(data, flags.into());

        let handle = std::thread::spawn(move || {
            assert_eq!(flagged_ptr.flag(), TestFlag::A);
            assert_eq!(flagged_ptr[1], 20);
            flagged_ptr.dissolve()
        });

        let (ptr_out, flags_out) = handle.join().unwrap();
        assert_eq!(flags_out, TestFlag::A);
        assert_eq!(*ptr_out, vec![10, 20, 30]);
        assert_eq!(Arc::strong_count(&ptr_out), 1);
    }

    #[test]
    fn test_arc_dyn_trait_clone_and_send() {
        let instance: Arc<dyn TestDyn> = Arc::new(DynImpl { val: 777 });
        let flags = TestFlag::B | TestFlag::C;

        let flagged_ptr = FlaggedPtr::new(instance, flags);
        assert_eq!(Arc::strong_count(&flagged_ptr.clone().dissolve().0), 2);

        let cloned_flagged_ptr = flagged_ptr.clone();
        assert_eq!(Arc::strong_count(&flagged_ptr.clone().dissolve().0), 3);

        let handle = std::thread::spawn(move || {
            assert_eq!(cloned_flagged_ptr.value(), 777);
            assert_eq!(cloned_flagged_ptr.flag(), flags);
            cloned_flagged_ptr
        });

        let ptr_from_thread = handle.join().unwrap();
        assert_eq!(ptr_from_thread.value(), 777);
        assert_eq!(ptr_from_thread.flag(), flags);

        assert_eq!(Arc::strong_count(&flagged_ptr.dissolve().0), 2);
    }

    #[test]
    fn test_send_and_sync() {
        let data = Arc::new(vec![10, 20, 30]);
        let flags = TestFlag::A;

        let flagged_ptr: FlaggedPtr<Arc<Vec<i32>>, BitFlags<TestFlag, u8>, ()> =
            FlaggedPtr::new(data, flags.into());

        let handle = std::thread::spawn(move || {
            assert_eq!(flagged_ptr.flag(), TestFlag::A);
            assert_eq!(flagged_ptr[1], 20);
            flagged_ptr.dissolve()
        });

        let (ptr_out, flags_out) = handle.join().unwrap();
        assert_eq!(flags_out, TestFlag::A);
        assert_eq!(*ptr_out, vec![10, 20, 30]);
        assert_eq!(Arc::strong_count(&ptr_out), 1);
    }
}
