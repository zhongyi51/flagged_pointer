//! # Pointer Metadata
//!
//! This module defines the `PtrMeta` trait for handling different pointer types
//! and their associated metadata, particularly for fat pointers like slices and trait objects.
//!
//! # Safety
//!
//! Implementations must correctly handle pointer metadata and ensure that
//! the unused bits calculation is accurate for the target architecture.

use std::ptr::NonNull;

/// Metadata trait for pointer types that can be used with `FlaggedPtr`.
///
/// This trait abstracts over different pointer types (thin and fat pointers)
/// to provide a uniform interface for encoding flags in unused bits.
///
/// # Type Parameters
/// - `M`: The metadata type associated with the pointer (e.g., `()` for thin pointers, `usize` for slices)
///
/// # Safety
///
/// Implementors must ensure:
/// 1. `mask(meta)` is stable for a given metadata value and retains every bit
///    required to reconstruct an appropriately aligned data pointer. The static
///    mask must not claim that required pointer bits are available for flags.
/// 2. `to_pointee_ptr_and_meta` transfers the pointer's ownership, if any, into
///    the returned representation without invalidating its provenance.
///    `from_pointee_ptr_and_meta` reverses that transfer exactly once.
/// 3. `map_pointee` returns the original pointee address and metadata without
///    taking ownership or invalidating existing references. For `Deref` and
///    `DerefMut` implementors, this must be the same pointee those traits expose.
/// 4. Safe conversion methods must accept every valid value of `Self`. In
///    particular, a `NonNull` pointer need not be dereferenceable or exclusive;
///    converting it must not create a reference to its pointee.
///
/// # Examples
///
/// The crate provides implementations for common pointer types:
/// - `NonNull<T>` - Thin pointers
/// - `Box<T>` - Owned pointers
/// - `NonNull<[T]>` - Slice pointers
/// - `Box<dyn Trait>` - Trait object pointers
pub unsafe trait PtrMeta<M>
where
    M: Copy,
{
    /// Bitmask indicating which bits are used by the actual pointer (not flags).
    /// This should exclude bits that are guaranteed to be zero due to alignment.
    const USED_PTR_BITS_MASK: usize;

    /// The type that this pointer points to.
    type Pointee: ?Sized;

    /// Returns the bitmask for pointer bits.
    /// Defaults to `USED_PTR_BITS_MASK` but can be overridden for dynamic masks.
    fn mask(_meta: M) -> usize {
        Self::USED_PTR_BITS_MASK
    }

    /// Converts the pointer into its raw representation and metadata.
    fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, M);

    /// Reconstructs the pointer from its raw representation and metadata.
    ///
    /// # Safety
    /// `nz` and `meta` must describe a representation produced by
    /// `to_pointee_ptr_and_meta`, with the original provenance and all flag bits
    /// removed. For owning pointers, the caller must transfer the represented
    /// ownership exactly once and satisfy the pointer type's aliasing rules.
    unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, meta: M) -> Self;

    /// Maps the raw pointer representation to a `NonNull` pointer to the pointee.
    ///
    /// # Safety
    /// `nz` and `meta` must describe the original data pointer and metadata, with
    /// the original provenance and all flag bits removed. The implementation
    /// must not dereference raw pointers merely to reconstruct their metadata.
    unsafe fn map_pointee(nz: NonNull<()>, meta: M) -> NonNull<Self::Pointee>;
}

/// Clones pointer storage while preserving shared references to its pointee.
///
/// This trait clones the represented pointer, not its metadata.
///
/// This capability is separate from [`PtrMeta`] because reconstructing an
/// owning pointer, such as `Box`, can invalidate references even when that
/// temporary pointer is never dropped. Implementors must clone through shared
/// access instead. A clone may have a different address or alignment; callers
/// must validate it before combining it with flags.
///
/// # Safety
///
/// Implementations must return a valid, independently owned clone (or a copy
/// for non-owning pointers), leave the original represented ownership intact,
/// and preserve all existing shared references to the source pointee. These
/// requirements also apply if cloning panics. Implementations must not create
/// a temporary exclusive owner of, or a mutable reference to, the source.
/// The result must uphold `Self::clone`'s guarantees, including the identical
/// pointee address required when `Self` implements `CloneStableDeref`.
pub unsafe trait ClonePtrMeta<M: Copy>: PtrMeta<M> + Clone {
    /// Clones the represented pointer without taking ownership of the source.
    ///
    /// # Safety
    ///
    /// `nz` and `meta` must describe a representation produced by
    /// `to_pointee_ptr_and_meta`, with the original provenance and all flag bits
    /// removed. Its represented ownership must remain live for the call. For
    /// owning pointers the pointee must permit shared access; non-owning raw
    /// pointers need not be dereferenceable and must only be copied.
    unsafe fn clone_storage_shared(nz: NonNull<()>, meta: M) -> Self;
}

pub mod ptr_impl {
    use core::slice;
    use std::{
        ptr::{self, NonNull},
        rc::Rc,
        sync::Arc,
    };

    use ptr_meta::DynMetadata;

    use crate::ptr::{ClonePtrMeta, PtrMeta};

    /// Metadata wrapper for dynamic dispatch pointers (trait objects).
    ///
    /// This struct holds both the dynamic metadata (vtable) and the calculated
    /// mask for unused bits for trait object pointers.
    ///
    /// # Type Parameters
    /// - `T`: The trait type (e.g., `dyn MyTrait`)
    pub struct WithMaskMeta<T>
    where
        T: ?Sized,
    {
        /// Dynamic metadata for the trait object (vtable pointer).
        pub(crate) data: DynMetadata<T>,
        /// Calculated mask for unused bits based on the actual alignment.
        pub(crate) mask: usize,
    }

    impl<T> Clone for WithMaskMeta<T>
    where
        T: ?Sized,
    {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<T> Copy for WithMaskMeta<T> where T: ?Sized {}

    unsafe impl<T> PtrMeta<()> for NonNull<T> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = T;

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, ()) {
            let ptr = self.as_ptr();
            let nz = unsafe { NonNull::new_unchecked(ptr as *mut ()) };
            (nz, ())
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, __meta: ()) -> Self {
            let ptr = nz.as_ptr() as *mut T;
            unsafe { NonNull::new_unchecked(ptr) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, __meta: ()) -> NonNull<Self::Pointee> {
            let ptr = nz.as_ptr() as *mut T;
            unsafe { NonNull::new_unchecked(ptr) }
        }
    }

    unsafe impl<T> PtrMeta<usize> for NonNull<[T]> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = [T];

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, usize) {
            (self.cast(), self.len())
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, meta: usize) -> Self {
            NonNull::slice_from_raw_parts(nz.cast(), meta)
        }

        unsafe fn map_pointee(nz: NonNull<()>, meta: usize) -> NonNull<Self::Pointee> {
            let ptr = ptr::slice_from_raw_parts_mut(nz.as_ptr() as *mut T, meta);
            unsafe { NonNull::new_unchecked(ptr) }
        }
    }

    unsafe impl<T> PtrMeta<WithMaskMeta<T>> for NonNull<T>
    where
        T: ?Sized + ptr_meta::Pointee<Metadata = DynMetadata<T>>,
    {
        // We cannot determine the align of `T` at compile time, so we set it to 0.
        const USED_PTR_BITS_MASK: usize = { 0_usize };

        type Pointee = T;

        fn mask(meta: WithMaskMeta<T>) -> usize {
            meta.mask
        }

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, WithMaskMeta<T>) {
            let (ptr, meta) = ptr_meta::to_raw_parts(self.as_ptr());
            let align = meta.align_of();
            let align_bits = align.ilog2() as usize;
            let mask = usize::MAX << align_bits;
            // our pointer is from `NonNull`
            (
                unsafe { NonNull::new_unchecked(ptr as *mut ()) },
                WithMaskMeta { data: meta, mask },
            )
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, meta: WithMaskMeta<T>) -> Self {
            let ptr = nz.as_ptr();
            unsafe { NonNull::new_unchecked(ptr_meta::from_raw_parts_mut(ptr, meta.data)) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, meta: WithMaskMeta<T>) -> NonNull<Self::Pointee> {
            let ptr = nz.as_ptr();
            unsafe { NonNull::new_unchecked(ptr_meta::from_raw_parts_mut(ptr, meta.data)) }
        }
    }

    unsafe impl<T> PtrMeta<()> for Box<T> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = T;

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, ()) {
            let ptr = Box::into_raw(self);
            let nz = unsafe { NonNull::new_unchecked(ptr as *mut ()) };
            (nz, ())
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, _meta: ()) -> Self {
            let ptr = nz.as_ptr() as *mut T;
            unsafe { Box::from_raw(ptr) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, _meta: ()) -> NonNull<Self::Pointee> {
            let ptr = nz.as_ptr() as *mut T;
            unsafe { NonNull::new_unchecked(ptr) }
        }
    }

    unsafe impl<T> PtrMeta<usize> for Box<[T]> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = [T];

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, usize) {
            let len = self.len();
            let ptr = Box::into_raw(self) as *mut T;
            let nz = unsafe { NonNull::new_unchecked(ptr as *mut ()) };
            (nz, len)
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, meta: usize) -> Self {
            let ptr = nz.as_ptr() as *mut T;
            let slice = ptr::slice_from_raw_parts_mut(ptr, meta);
            unsafe { Box::from_raw(slice) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, meta: usize) -> NonNull<Self::Pointee> {
            let ptr = ptr::slice_from_raw_parts_mut(nz.as_ptr() as *mut T, meta);
            unsafe { NonNull::new_unchecked(ptr) }
        }
    }

    unsafe impl<T> PtrMeta<WithMaskMeta<T>> for Box<T>
    where
        T: ?Sized + ptr_meta::Pointee<Metadata = DynMetadata<T>>,
    {
        // We cannot determine the align of `T` at compile time, so we set it to 0.
        const USED_PTR_BITS_MASK: usize = { 0_usize };

        type Pointee = T;

        fn mask(meta: WithMaskMeta<T>) -> usize {
            meta.mask
        }

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, WithMaskMeta<T>) {
            let ptr = Box::into_raw(self);
            let (raw_ptr, meta) = ptr_meta::to_raw_parts(ptr);
            let align = meta.align_of();
            let align_bits = align.ilog2() as usize;
            let mask = usize::MAX << align_bits;
            // our pointer is from `NonNull`
            (
                unsafe { NonNull::new_unchecked(raw_ptr as *mut ()) },
                WithMaskMeta { data: meta, mask },
            )
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, meta: WithMaskMeta<T>) -> Self {
            let ptr = nz.as_ptr();
            unsafe { Box::from_raw(ptr_meta::from_raw_parts_mut(ptr, meta.data)) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, meta: WithMaskMeta<T>) -> NonNull<Self::Pointee> {
            let ptr = nz.as_ptr();
            unsafe { NonNull::new_unchecked(ptr_meta::from_raw_parts_mut(ptr, meta.data)) }
        }
    }

    unsafe impl<T> PtrMeta<()> for Rc<T> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = T;

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, ()) {
            let ptr = Rc::into_raw(self) as *mut T;
            let nz = unsafe { NonNull::new_unchecked(ptr as *mut ()) };
            (nz, ())
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, _meta: ()) -> Self {
            let ptr = nz.as_ptr() as *const T;
            unsafe { Rc::from_raw(ptr) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, _meta: ()) -> NonNull<Self::Pointee> {
            let ptr = nz.as_ptr() as *mut T;
            unsafe { NonNull::new_unchecked(ptr) }
        }
    }

    unsafe impl<T> PtrMeta<()> for Arc<T> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = T;

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, ()) {
            let ptr = Arc::into_raw(self) as *mut T;
            let nz = unsafe { NonNull::new_unchecked(ptr as *mut ()) };
            (nz, ())
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, _meta: ()) -> Self {
            let ptr = nz.as_ptr() as *const T;
            unsafe { Arc::from_raw(ptr) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, _meta: ()) -> NonNull<Self::Pointee> {
            let ptr = nz.as_ptr() as *mut T;
            unsafe { NonNull::new_unchecked(ptr) }
        }
    }

    unsafe impl<T> PtrMeta<usize> for Rc<[T]> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = [T];

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, usize) {
            let len = self.len();
            let ptr_slice = Rc::into_raw(self);
            let ptr = ptr_slice as *const T as *mut T;
            let nz = unsafe { NonNull::new_unchecked(ptr as *mut ()) };
            (nz, len)
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, meta: usize) -> Self {
            let ptr = nz.as_ptr() as *const T;
            let slice = ptr::slice_from_raw_parts(ptr, meta);
            unsafe { Rc::from_raw(slice) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, meta: usize) -> NonNull<Self::Pointee> {
            let ptr = nz.as_ptr() as *const T;
            let slice = ptr::slice_from_raw_parts_mut(ptr as *mut T, meta);
            unsafe { NonNull::new_unchecked(slice) }
        }
    }

    unsafe impl<T> PtrMeta<usize> for Arc<[T]> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = [T];

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, usize) {
            let len = self.len();
            let ptr_slice = Arc::into_raw(self);
            let ptr = ptr_slice as *const T as *mut T;
            let nz = unsafe { NonNull::new_unchecked(ptr as *mut ()) };
            (nz, len)
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, meta: usize) -> Self {
            let ptr = nz.as_ptr() as *const T;
            let slice = ptr::slice_from_raw_parts(ptr, meta);
            unsafe { Arc::from_raw(slice) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, meta: usize) -> NonNull<Self::Pointee> {
            let ptr = nz.as_ptr() as *const T;
            let slice = ptr::slice_from_raw_parts_mut(ptr as *mut T, meta);
            unsafe { NonNull::new_unchecked(slice) }
        }
    }

    unsafe impl<T> PtrMeta<WithMaskMeta<T>> for Rc<T>
    where
        T: ?Sized + ptr_meta::Pointee<Metadata = DynMetadata<T>>,
    {
        // We cannot determine the align of `T` at compile time, so we set it to 0.
        const USED_PTR_BITS_MASK: usize = { 0_usize };

        type Pointee = T;

        fn mask(meta: WithMaskMeta<T>) -> usize {
            meta.mask
        }

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, WithMaskMeta<T>) {
            let ptr = Rc::into_raw(self);
            let (raw_ptr, meta) = ptr_meta::to_raw_parts(ptr);
            let align = meta.align_of();
            let align_bits = align.ilog2() as usize;
            let mask = usize::MAX << align_bits;
            // our pointer is from `NonNull`
            (
                unsafe { NonNull::new_unchecked(raw_ptr as *mut ()) },
                WithMaskMeta { data: meta, mask },
            )
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, meta: WithMaskMeta<T>) -> Self {
            let ptr = nz.as_ptr();
            unsafe { Rc::from_raw(ptr_meta::from_raw_parts(ptr, meta.data)) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, meta: WithMaskMeta<T>) -> NonNull<Self::Pointee> {
            let ptr = nz.as_ptr();
            unsafe { NonNull::new_unchecked(ptr_meta::from_raw_parts_mut(ptr, meta.data)) }
        }
    }

    unsafe impl<T> PtrMeta<WithMaskMeta<T>> for Arc<T>
    where
        T: ?Sized + ptr_meta::Pointee<Metadata = DynMetadata<T>>,
    {
        // We cannot determine the align of `T` at compile time, so we set it to 0.
        const USED_PTR_BITS_MASK: usize = { 0_usize };

        type Pointee = T;

        fn mask(meta: WithMaskMeta<T>) -> usize {
            meta.mask
        }

        fn to_pointee_ptr_and_meta(self) -> (NonNull<()>, WithMaskMeta<T>) {
            let ptr = Arc::into_raw(self);
            let (raw_ptr, meta) = ptr_meta::to_raw_parts(ptr);
            let align = meta.align_of();
            let align_bits = align.ilog2() as usize;
            let mask = usize::MAX << align_bits;
            // our pointer is from `NonNull`
            (
                unsafe { NonNull::new_unchecked(raw_ptr as *mut ()) },
                WithMaskMeta { data: meta, mask },
            )
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonNull<()>, meta: WithMaskMeta<T>) -> Self {
            let ptr = nz.as_ptr();
            unsafe { Arc::from_raw(ptr_meta::from_raw_parts(ptr, meta.data)) }
        }

        unsafe fn map_pointee(nz: NonNull<()>, meta: WithMaskMeta<T>) -> NonNull<Self::Pointee> {
            let ptr = nz.as_ptr();
            unsafe { NonNull::new_unchecked(ptr_meta::from_raw_parts_mut(ptr, meta.data)) }
        }
    }

    // SAFETY: A raw pointer clone only copies its address and metadata. It does
    // not dereference the pointee or transfer any ownership.
    unsafe impl<T: ?Sized, M: Copy> ClonePtrMeta<M> for NonNull<T>
    where
        Self: PtrMeta<M, Pointee = T>,
    {
        unsafe fn clone_storage_shared(nz: NonNull<()>, meta: M) -> Self {
            // SAFETY: The caller provides the original untagged representation.
            unsafe { Self::map_pointee(nz, meta) }
        }
    }

    // SAFETY: Incrementing the reference count creates a distinct owned handle
    // without requiring exclusive access to the allocation's pointee.
    unsafe impl<T: ?Sized, M: Copy> ClonePtrMeta<M> for Rc<T>
    where
        Self: PtrMeta<M, Pointee = T>,
    {
        unsafe fn clone_storage_shared(nz: NonNull<()>, meta: M) -> Self {
            // SAFETY: The representation came from a live Rc<T>, and map_pointee
            // restores the original pointee pointer, including any metadata.
            let ptr = unsafe { Self::map_pointee(nz, meta) }.as_ptr();
            unsafe {
                Rc::increment_strong_count(ptr);
                Rc::from_raw(ptr)
            }
        }
    }

    // SAFETY: As for Rc, with an atomic strong-count increment.
    unsafe impl<T: ?Sized, M: Copy> ClonePtrMeta<M> for Arc<T>
    where
        Self: PtrMeta<M, Pointee = T>,
    {
        unsafe fn clone_storage_shared(nz: NonNull<()>, meta: M) -> Self {
            // SAFETY: The representation came from a live Arc<T>; incrementing
            // first gives from_raw a new owned reference to consume.
            let ptr = unsafe { Self::map_pointee(nz, meta) }.as_ptr();
            unsafe {
                Arc::increment_strong_count(ptr);
                Arc::from_raw(ptr)
            }
        }
    }

    // SAFETY: Cloning reads through a shared reference and creates a fresh Box.
    // If T::clone panics, the original allocation and references remain intact.
    unsafe impl<T: Clone> ClonePtrMeta<()> for Box<T> {
        unsafe fn clone_storage_shared(nz: NonNull<()>, _meta: ()) -> Self {
            // SAFETY: The caller guarantees a live T permitting shared access.
            Box::new(unsafe { nz.cast::<T>().as_ref() }.clone())
        }
    }

    // SAFETY: Slice cloning only borrows the source. Vec handles partial-clone
    // cleanup on panic, and the returned Box owns a separate allocation.
    unsafe impl<T: Clone> ClonePtrMeta<usize> for Box<[T]> {
        unsafe fn clone_storage_shared(nz: NonNull<()>, meta: usize) -> Self {
            // SAFETY: The caller supplies the original pointer and slice length
            // and guarantees that all elements permit shared access.
            let source = unsafe { slice::from_raw_parts(nz.cast::<T>().as_ptr(), meta) };
            source.to_vec().into_boxed_slice()
        }
    }
}
