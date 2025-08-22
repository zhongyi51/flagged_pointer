use std::{num::NonZeroUsize, ops::Deref, ptr::NonNull};

/// Metadata for the pointer.
pub unsafe trait PtrMeta<M>
where
    M: Copy,
{
    const USED_PTR_BITS_MASK: usize;

    // Internal pointed data type.
    type Pointee: ?Sized;

    fn mask(meta: &M) -> usize {
        Self::USED_PTR_BITS_MASK
    }

    fn to_pointee_ptr_and_meta(self) -> (NonZeroUsize, M);

    unsafe fn from_pointee_ptr_and_meta(nz: NonZeroUsize, meta: M) -> Self;

    unsafe fn map_pointee(nz: NonZeroUsize, meta: M) -> NonNull<Self::Pointee>;

    unsafe fn clone_storage(nz: NonZeroUsize, meta: &M) -> Self
    where
        Self: Clone;
}

pub mod ptr_impl {
    use core::slice;
    use std::{mem, num::NonZeroUsize, ptr::{self, NonNull}, rc::Rc, sync::Arc};

    use ptr_meta::DynMetadata;

    use crate::ptr::PtrMeta;

    pub struct WithMaskMeta<T>
    where
        T: ?Sized,
    {
        pub(crate) data: DynMetadata<T>,
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

        fn to_pointee_ptr_and_meta(self) -> (std::num::NonZeroUsize, ()) {
            let ptr = self.as_ptr();
            let nz = unsafe { NonZeroUsize::new_unchecked(ptr as usize) };
            (nz, ())
        }

        unsafe fn from_pointee_ptr_and_meta(nz: std::num::NonZeroUsize, meta: ()) -> Self {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            unsafe { NonNull::new_unchecked(ptr) }
        }

        unsafe fn map_pointee(nz: std::num::NonZeroUsize, meta: ()) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            unsafe { NonNull::new_unchecked(ptr) }
        }

        unsafe fn clone_storage(nz: NonZeroUsize, meta: &()) -> Self
        where
            Self: Clone,
        {
            unreachable!("Box does not support clone storage")
        }
    }

    unsafe impl<T> PtrMeta<usize> for NonNull<[T]> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = [T];

        fn to_pointee_ptr_and_meta(mut self) -> (NonZeroUsize, usize) {
            let slice = unsafe { self.as_mut() };
            let len = slice.len();
            let ptr = slice.as_mut_ptr();
            let nz = unsafe { NonZeroUsize::new_unchecked(ptr as usize) };
            (nz, len)
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonZeroUsize, meta: usize) -> Self {
            let slice = unsafe { slice::from_raw_parts_mut(nz.get() as *mut T, meta) };
            Self::from_mut(slice)
        }

        unsafe fn map_pointee(nz: std::num::NonZeroUsize, meta: usize) -> NonNull<Self::Pointee> {
            let ptr = 
                ptr::slice_from_raw_parts_mut(NonZeroUsize::get(nz) as *mut T, meta);
            unsafe { NonNull::new_unchecked(ptr) }
        }

        unsafe fn clone_storage(nz: NonZeroUsize, meta: &usize) -> Self
        where
            Self: Clone,
        {
            unreachable!("Box does not support clone storage")
        }
    }

    unsafe impl<T> PtrMeta<WithMaskMeta<T>> for NonNull<T>
    where
        T: ?Sized + ptr_meta::Pointee<Metadata = DynMetadata<T>>,
    {
        // We cannot determine the align of `T` at compile time, so we set it to 0.
        const USED_PTR_BITS_MASK: usize = { 0_usize };

        type Pointee = T;

        fn mask(meta: &WithMaskMeta<T>) -> usize {
            meta.mask
        }

        fn to_pointee_ptr_and_meta(self) -> (NonZeroUsize, WithMaskMeta<T>) {
            let (ptr, meta) = ptr_meta::to_raw_parts(self.as_ptr());
            let align = meta.align_of();
            let align_bits = align.ilog2() as usize;
            let mask = usize::MAX << align_bits;
            (
                NonZeroUsize::new(ptr as usize).unwrap(),
                WithMaskMeta { data: meta, mask },
            )
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonZeroUsize, meta: WithMaskMeta<T>) -> Self {
            let ptr = NonZeroUsize::get(nz) as *mut ();
            unsafe { NonNull::new_unchecked(ptr_meta::from_raw_parts_mut(ptr, meta.data)) }
        }

        unsafe fn map_pointee(nz: NonZeroUsize, meta: WithMaskMeta<T>) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *mut ();
            unsafe { NonNull::new_unchecked(ptr_meta::from_raw_parts_mut(ptr, meta.data)) }
        }

        unsafe fn clone_storage(nz: NonZeroUsize, meta: &WithMaskMeta<T>) -> Self
        where
            Self: Clone,
        {
            unreachable!("Box does not support clone storage")
        }
    }

    unsafe impl<T> PtrMeta<()> for Box<T> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = T;

        fn to_pointee_ptr_and_meta(self) -> (std::num::NonZeroUsize, ()) {
            let ptr = Box::into_raw(self);
            let nz = unsafe { NonZeroUsize::new_unchecked(ptr as usize) };
            (nz, ())
        }

        unsafe fn from_pointee_ptr_and_meta(nz: std::num::NonZeroUsize, meta: ()) -> Self {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            unsafe { Box::from_raw(ptr) }
        }

        unsafe fn map_pointee(nz: std::num::NonZeroUsize, meta: ()) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            unsafe { NonNull::new_unchecked(ptr) }
        }

        unsafe fn clone_storage(nz: std::num::NonZeroUsize, meta: &()) -> Self
        where
            Self: Clone,
        {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            let boxed = unsafe { Box::from_raw(ptr) };
            let cloned = boxed.clone();
            mem::forget(boxed);
            cloned
        }
    }

    unsafe impl<T> PtrMeta<usize> for Box<[T]> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = [T];

        fn to_pointee_ptr_and_meta(self) -> (NonZeroUsize, usize) {
            let ptr_slice = Box::into_raw(self);
            let len = ptr_slice.len();
            let ptr = ptr_slice as *mut T;
            let nz = unsafe { NonZeroUsize::new_unchecked(ptr as usize) };
            (nz, len)
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonZeroUsize, meta: usize) -> Self {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            let slice = unsafe { std::slice::from_raw_parts_mut(ptr, meta) };
            unsafe { Box::from_raw(slice) }
        }

        unsafe fn map_pointee(nz: NonZeroUsize, meta: usize) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            let slice = ptr::slice_from_raw_parts_mut(ptr, meta);
            unsafe { NonNull::new_unchecked(slice) }
        }

        unsafe fn clone_storage(nz: NonZeroUsize, meta: &usize) -> Self
        where
            Self: Clone,
        {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            let slice = unsafe { std::slice::from_raw_parts_mut(ptr, *meta) };
            let boxed = unsafe { Box::from_raw(slice) };
            let cloned = boxed.clone();
            mem::forget(boxed);
            cloned
        }
    }

    unsafe impl<T> PtrMeta<WithMaskMeta<T>> for Box<T>
    where
        T: ?Sized + ptr_meta::Pointee<Metadata = DynMetadata<T>>,
    {
        // We cannot determine the align of `T` at compile time, so we set it to 0.
        const USED_PTR_BITS_MASK: usize = { 0_usize };

        type Pointee = T;

        fn mask(meta: &WithMaskMeta<T>) -> usize {
            meta.mask
        }

        fn to_pointee_ptr_and_meta(self) -> (NonZeroUsize, WithMaskMeta<T>) {
            let ptr = Box::into_raw(self);
            let (raw_ptr, meta) = ptr_meta::to_raw_parts(ptr);
            let align = meta.align_of();
            let align_bits = align.ilog2() as usize;
            let mask = usize::MAX << align_bits;
            (
                NonZeroUsize::new(raw_ptr as usize).unwrap(),
                WithMaskMeta { data: meta, mask },
            )
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonZeroUsize, meta: WithMaskMeta<T>) -> Self {
            let ptr = NonZeroUsize::get(nz) as *mut ();
            unsafe { Box::from_raw(ptr_meta::from_raw_parts_mut(ptr, meta.data)) }
        }

        unsafe fn map_pointee(nz: NonZeroUsize, meta: WithMaskMeta<T>) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *mut ();
            unsafe { NonNull::new_unchecked(ptr_meta::from_raw_parts_mut(ptr, meta.data)) }
        }

        unsafe fn clone_storage(nz: NonZeroUsize, meta: &WithMaskMeta<T>) -> Self
        where
            Self: Clone,
        {
            let ptr = NonZeroUsize::get(nz) as *mut ();
            let boxed: Box<T> =
                unsafe { Box::from_raw(ptr_meta::from_raw_parts_mut(ptr, meta.data)) };
            let cloned = boxed.clone();
            mem::forget(boxed);
            cloned
        }
    }

    unsafe impl<T> PtrMeta<()> for Rc<T> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = T;

        fn to_pointee_ptr_and_meta(self) -> (std::num::NonZeroUsize, ()) {
            let ptr = Rc::into_raw(self);
            let nz = unsafe { NonZeroUsize::new_unchecked(ptr as usize) };
            (nz, ())
        }
        unsafe fn from_pointee_ptr_and_meta(nz: std::num::NonZeroUsize, meta: ()) -> Self {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            unsafe { Rc::from_raw(ptr) }
        }
        unsafe fn map_pointee(nz: std::num::NonZeroUsize, meta: ()) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            unsafe { NonNull::new_unchecked(ptr) }
        }
        unsafe fn clone_storage(nz: std::num::NonZeroUsize, meta: &()) -> Self
        where
            Self: Clone,
        {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            unsafe { Rc::increment_strong_count(ptr) };
            unsafe { Rc::from_raw(ptr) }
        }
    }

    unsafe impl<T> PtrMeta<()> for Arc<T> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = T;

        fn to_pointee_ptr_and_meta(self) -> (std::num::NonZeroUsize, ()) {
            let ptr = Arc::into_raw(self);
            let nz = unsafe { NonZeroUsize::new_unchecked(ptr as usize) };
            (nz, ())
        }
        unsafe fn from_pointee_ptr_and_meta(nz: std::num::NonZeroUsize, meta: ()) -> Self {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            unsafe { Arc::from_raw(ptr) }
        }
        unsafe fn map_pointee(nz: std::num::NonZeroUsize, meta: ()) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            unsafe { NonNull::new_unchecked(ptr) }
        }
        unsafe fn clone_storage(nz: std::num::NonZeroUsize, meta: &()) -> Self
        where
            Self: Clone,
        {
            let ptr = NonZeroUsize::get(nz) as *mut T;
            unsafe { Arc::increment_strong_count(ptr) };
            unsafe { Arc::from_raw(ptr) }
        }
    }

    unsafe impl<T> PtrMeta<usize> for Rc<[T]> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = [T];

        fn to_pointee_ptr_and_meta(self) -> (NonZeroUsize, usize) {
            let ptr_slice = Rc::into_raw(self);
            let len = unsafe { (&(*ptr_slice)).len() };
            let ptr = ptr_slice as *const T;
            let nz = unsafe { NonZeroUsize::new_unchecked(ptr as usize) };
            (nz, len)
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonZeroUsize, meta: usize) -> Self {
            let ptr = NonZeroUsize::get(nz) as *const T;
            let slice = unsafe { std::slice::from_raw_parts(ptr, meta) };
            unsafe { Rc::from_raw(slice) }
        }

        unsafe fn map_pointee(nz: NonZeroUsize, meta: usize) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *const T;
            let slice = ptr::slice_from_raw_parts_mut(ptr as *mut T, meta);
            unsafe { NonNull::new_unchecked(slice) }
        }

        unsafe fn clone_storage(nz: NonZeroUsize, meta: &usize) -> Self
        where
            Self: Clone,
        {
            let ptr = NonZeroUsize::get(nz) as *const T;
            unsafe { Rc::increment_strong_count(ptr) };
            let slice = unsafe { std::slice::from_raw_parts(ptr, *meta) };
            unsafe { Rc::from_raw(slice) }
        }
    }

    unsafe impl<T> PtrMeta<usize> for Arc<[T]> {
        const USED_PTR_BITS_MASK: usize = {
            let align = std::mem::align_of::<T>();
            let align_bits = align.ilog2() as usize;
            usize::MAX << align_bits
        };

        type Pointee = [T];

        fn to_pointee_ptr_and_meta(self) -> (NonZeroUsize, usize) {
            let ptr_slice = Arc::into_raw(self);
            let len = unsafe { (&(*ptr_slice)).len() };
            let ptr = ptr_slice as *const T;
            let nz = unsafe { NonZeroUsize::new_unchecked(ptr as usize) };
            (nz, len)
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonZeroUsize, meta: usize) -> Self {
            let ptr = NonZeroUsize::get(nz) as *const T;
            let slice = unsafe { std::slice::from_raw_parts(ptr, meta) };
            unsafe { Arc::from_raw(slice) }
        }

        unsafe fn map_pointee(nz: NonZeroUsize, meta: usize) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *const T;
            let slice = ptr::slice_from_raw_parts_mut(ptr as *mut T, meta);
            unsafe { NonNull::new_unchecked(slice) }
        }

        unsafe fn clone_storage(nz: NonZeroUsize, meta: &usize) -> Self
        where
            Self: Clone,
        {
            let ptr = NonZeroUsize::get(nz) as *const T;
            unsafe { Arc::increment_strong_count(ptr) };
            let slice = unsafe { std::slice::from_raw_parts(ptr, *meta) };
            unsafe { Arc::from_raw(slice) }
        }
    }

    unsafe impl<T> PtrMeta<WithMaskMeta<T>> for Rc<T>
    where
        T: ?Sized + ptr_meta::Pointee<Metadata = DynMetadata<T>>,
    {
        // We cannot determine the align of `T` at compile time, so we set it to 0.
        const USED_PTR_BITS_MASK: usize = { 0_usize };

        type Pointee = T;

        fn mask(meta: &WithMaskMeta<T>) -> usize {
            meta.mask
        }

        fn to_pointee_ptr_and_meta(self) -> (NonZeroUsize, WithMaskMeta<T>) {
            let ptr = Rc::into_raw(self);
            let (raw_ptr, meta) = ptr_meta::to_raw_parts(ptr);
            let align = meta.align_of();
            let align_bits = align.ilog2() as usize;
            let mask = usize::MAX << align_bits;
            (
                NonZeroUsize::new(raw_ptr as usize).unwrap(),
                WithMaskMeta { data: meta, mask },
            )
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonZeroUsize, meta: WithMaskMeta<T>) -> Self {
            let ptr = NonZeroUsize::get(nz) as *const ();
            unsafe { Rc::from_raw(ptr_meta::from_raw_parts(ptr, meta.data)) }
        }

        unsafe fn map_pointee(nz: NonZeroUsize, meta: WithMaskMeta<T>) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *const ();
            unsafe {
                NonNull::new_unchecked(ptr_meta::from_raw_parts_mut(ptr as *mut (), meta.data))
            }
        }

        unsafe fn clone_storage(nz: NonZeroUsize, meta: &WithMaskMeta<T>) -> Self
        where
            Self: Clone,
        {
            let ptr = NonZeroUsize::get(nz) as *const ();
            unsafe { Rc::increment_strong_count(ptr) };
            unsafe { Rc::from_raw(ptr_meta::from_raw_parts(ptr, meta.data)) }
        }
    }

    unsafe impl<T> PtrMeta<WithMaskMeta<T>> for Arc<T>
    where
        T: ?Sized + ptr_meta::Pointee<Metadata = DynMetadata<T>>,
    {
        // We cannot determine the align of `T` at compile time, so we set it to 0.
        const USED_PTR_BITS_MASK: usize = { 0_usize };

        type Pointee = T;

        fn mask(meta: &WithMaskMeta<T>) -> usize {
            meta.mask
        }

        fn to_pointee_ptr_and_meta(self) -> (NonZeroUsize, WithMaskMeta<T>) {
            let ptr = Arc::into_raw(self);
            let (raw_ptr, meta) = ptr_meta::to_raw_parts(ptr);
            let align = meta.align_of();
            let align_bits = align.ilog2() as usize;
            let mask = usize::MAX << align_bits;
            (
                NonZeroUsize::new(raw_ptr as usize).unwrap(),
                WithMaskMeta { data: meta, mask },
            )
        }

        unsafe fn from_pointee_ptr_and_meta(nz: NonZeroUsize, meta: WithMaskMeta<T>) -> Self {
            let ptr = NonZeroUsize::get(nz) as *const ();
            unsafe { Arc::from_raw(ptr_meta::from_raw_parts(ptr, meta.data)) }
        }

        unsafe fn map_pointee(nz: NonZeroUsize, meta: WithMaskMeta<T>) -> NonNull<Self::Pointee> {
            let ptr = NonZeroUsize::get(nz) as *const ();
            unsafe {
                NonNull::new_unchecked(ptr_meta::from_raw_parts_mut(ptr as *mut (), meta.data))
            }
        }

        unsafe fn clone_storage(nz: NonZeroUsize, meta: &WithMaskMeta<T>) -> Self
        where
            Self: Clone,
        {
            let ptr = NonZeroUsize::get(nz) as *const ();
            unsafe { Arc::increment_strong_count(ptr) };
            unsafe { Arc::from_raw(ptr_meta::from_raw_parts(ptr, meta.data)) }
        }
    }
}
