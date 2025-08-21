use std::{
    marker::PhantomData,
    num::NonZeroUsize,
    ops::{Deref, DerefMut}, ptr::NonNull,
};

use crate::{flag::FlagMeta, ptr::PtrMeta};

pub mod flag;
pub mod ptr;
pub struct FlaggedPtr<P, F, M>
where
    P: PtrMeta<M>,
    F: FlagMeta,
    M: Copy,
{
    repr: NonZeroUsize,
    meta: M,
    _marker: PhantomData<(P, F)>,
}

// Because const ops (e.g. `BitAnd`) are not stable, we need to assert for each concrete type.
impl<P, F, M> FlaggedPtr<P, F, M>
where
    P: PtrMeta<M>,
    F: FlagMeta,
    M: Copy,
{
    const _ASSERT: () = assert!(P::USED_PTR_BITS_MASK & F::USED_FLAG_BITS_MASK as usize == 0);

    pub fn new(ptr: P, flag: F) -> Self {
        // Static assert, which will be checked at compile time.
        let _ = Self::_ASSERT;
        let (ptr, meta) = ptr.to_pointee_ptr_and_meta();
        // Runtime assert, which will be checked at runtime, for `dyn XXX` types.
        assert!(F::USED_FLAG_BITS_MASK & P::mask(&meta) == 0);
        let repr = NonZeroUsize::new(ptr.get() | flag.to_usize()).unwrap();
        Self {
            repr,
            meta,
            _marker: PhantomData,
        }
    }
}

impl<P, F, M> FlaggedPtr<P, F, M>
where
    P: PtrMeta<M>,
    F: FlagMeta,
    M: Copy,
{
    pub fn flag(&self) -> F {
        let flag_repr = F::mask() & self.repr.get();
        unsafe { F::from_usize(flag_repr) }
    }

    pub fn set_flag(&mut self, flag: F) {
        let flag_repr = flag.to_usize();
        let ptr_repr = self.repr.get() & P::mask(&self.meta);
        self.repr = NonZeroUsize::new(ptr_repr | flag_repr).unwrap();
    }

    pub fn dissolve(self) -> (P, F) {
        let ptr_repr = self.repr.get() & P::mask(&self.meta);
        let flag_repr = F::mask() & self.repr.get();
        let ptr = unsafe {
            P::from_pointee_ptr_and_meta(NonZeroUsize::new(ptr_repr).unwrap_unchecked(), self.meta)
        };
        let flag = unsafe { F::from_usize(flag_repr) };
        (ptr, flag)
    }

    fn ptr_repr(&self) -> NonZeroUsize {
        let ptr_val = self.repr.get() & P::mask(&self.meta);
        unsafe { NonZeroUsize::new_unchecked(ptr_val) }
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
        let ptr_repr = self.ptr_repr();
        unsafe {
            P::map_pointee(ptr_repr, self.meta)
                .as_ref()
                .unwrap_unchecked()
        }
    }
}

impl<P, F, M> DerefMut for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M> + DerefMut<Target = P::Pointee>,
    F: FlagMeta,
    M: Copy,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        let ptr_repr = self.ptr_repr();
        unsafe {
            P::map_pointee_mut(ptr_repr, self.meta)
                .as_mut()
                .unwrap_unchecked()
        }
    }
}

impl<P, F, M> Drop for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M>,
    F: FlagMeta,
    M: Copy,
{
    fn drop(&mut self) {
        let ptr_repr = self.ptr_repr().get();
        if ptr_repr != 0 {
            unsafe {
                let _ = P::from_pointee_ptr_and_meta(self.ptr_repr(), self.meta);
            }
        }
    }
}

impl<P, F, M> Clone for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M> + Clone,
    F: FlagMeta,
    M: Copy,
{
    fn clone(&self) -> Self {
        let ptr_repr = self.repr.get() & P::mask(&self.meta);
        let nz = NonZeroUsize::new(ptr_repr).unwrap();
        let cloned_ptr_storage = unsafe { P::clone_storage(nz, &self.meta) };
        let flag = self.flag();
        Self::new(cloned_ptr_storage, flag)
    }
}

impl<P, F, M> Default for FlaggedPtr<P, F, M>
where
    P: PtrMeta<M> + Default,
    F: FlagMeta + Default,
    M: Default + Copy,
{
    fn default() -> Self {
        let storage = P::default();
        let flag = F::default();
        Self::new(storage, flag)
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
