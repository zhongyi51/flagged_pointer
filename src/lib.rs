use std::{
    marker::PhantomData, mem, num::NonZeroUsize, ops::{Deref, DerefMut}, ptr::NonNull
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
        assert!(F::mask() & P::mask(&meta) == 0);
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
        mem::forget(self);
        (ptr, flag)
    }

    fn ptr_repr(&self) -> NonZeroUsize {
        let ptr_val = self.repr.get() & P::mask(&self.meta);
        unsafe { NonZeroUsize::new_unchecked(ptr_val) }
    }

    fn as_ptr(&self) -> NonNull<P::Pointee> {
        let ptr_repr = self.ptr_repr();
        unsafe { P::map_pointee(ptr_repr, self.meta) }
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
        unsafe {
            let _ = P::from_pointee_ptr_and_meta(self.ptr_repr(), self.meta);
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

pub mod alias{
    use std::{ptr::NonNull, rc::Rc, sync::Arc};

    use crate::{ptr::ptr_impl::WithMaskMeta, FlaggedPtr};


    pub type FlaggedNonNull<T,F>=FlaggedPtr<NonNull<T>,F,()>;
    pub type FlaggedNonNullSlice<T,F>=FlaggedPtr<NonNull<[T]>,F,usize>;
    pub type FlaggedNonNullDyn<T,F>=FlaggedPtr<NonNull<T>,F,WithMaskMeta<T>>;
    pub type FlaggedBox<T,F>=FlaggedPtr<Box<T>,F,()>;
    pub type FlaggedBoxSlice<T,F>=FlaggedPtr<Box<[T]>,F,usize>;
    pub type FlaggedBoxDyn<T,F>=FlaggedPtr<Box<T>,F,WithMaskMeta<T>>;
    pub type FlaggedRc<T,F>=FlaggedPtr<Rc<T>,F,()>;
    pub type FlaggedRcSlice<T,F>=FlaggedPtr<Rc<[T]>,F,usize>;
    pub type FlaggedRcDyn<T,F>=FlaggedPtr<Rc<T>,F,WithMaskMeta<T>>;
    pub type FlaggedArc<T,F>=FlaggedPtr<Arc<T>,F,()>;
    pub type FlaggedArcSlice<T,F>=FlaggedPtr<Arc<[T]>,F,usize>;
    pub type FlaggedArcDyn<T,F>=FlaggedPtr<Arc<T>,F,WithMaskMeta<T>>;

}


#[cfg(test)]
mod tests {
    use crate::alias::FlaggedBoxSlice;

    use super::*;
    use enumflags2::{bitflags, BitFlags};
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
        let (cloned,_)=flagged_ptr1.clone().dissolve();
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

        let mut flagged_ptr: FlaggedPtr<Box<[u64]>, _, usize>= FlaggedBoxSlice::new(data, flags.into());

        assert_eq!(&*flagged_ptr, &[1, 2, 3, 4, 5]);
        flagged_ptr[2] = 99;    
        assert_eq!(&*flagged_ptr, &[1, 2, 99, 4, 5]);

        assert_eq!(flagged_ptr.flag(), flags);
        flagged_ptr.set_flag(TestFlag::A.into());
        assert_eq!(flagged_ptr.flag(), TestFlag::A);

        let (ptr_out, flags_out): (_,BitFlags<TestFlag>) = flagged_ptr.dissolve();
        assert_eq!(flags_out, TestFlag::A);
        assert_eq!(&*ptr_out, &[1, 2, 99, 4, 5]);
    }

    #[ptr_meta::pointee]
    trait TestDyn:Send+Sync {
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

        let mut flagged_ptr: FlaggedPtr<Box<dyn TestDyn>, BitFlags<TestFlag, u8>, ptr::ptr_impl::WithMaskMeta<dyn TestDyn>> = FlaggedPtr::new(instance, flags.into());

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

        let flagged_ptr: FlaggedPtr<Arc<Vec<i32>>, BitFlags<TestFlag, u8>, ()> = FlaggedPtr::new(data, flags.into());

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
}