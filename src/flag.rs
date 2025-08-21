pub unsafe trait FlagMeta: Copy {
    const USED_FLAG_BITS_MASK: usize;

    fn mask() -> usize {
        Self::USED_FLAG_BITS_MASK
    }

    fn to_usize(self) -> usize;

    unsafe fn from_usize(nz: usize) -> Self;
}

mod enumflag_impl {
    use std::mem::transmute_copy;

    use enumflags2::{BitFlag, BitFlags};

    use crate::flag::FlagMeta;

    enum NumType {
        Usize,
        U64,
        U32,
        U16,
        U8,
    }

    trait ConstNumType: Copy {
        const NUM_TYPE: NumType;
    }

    impl ConstNumType for u8 {
        const NUM_TYPE: NumType = NumType::U8;
    }
    impl ConstNumType for u16 {
        const NUM_TYPE: NumType = NumType::U16;
    }
    impl ConstNumType for u32 {
        const NUM_TYPE: NumType = NumType::U32;
    }
    impl ConstNumType for u64 {
        const NUM_TYPE: NumType = NumType::U64;
    }
    impl ConstNumType for usize {
        const NUM_TYPE: NumType = NumType::Usize;
    }

    const fn cast_from_usize<N>(nz: usize) -> N
    where
        N: ConstNumType,
    {
        if size_of::<N>() > size_of::<usize>() {
            panic!("cast_to_usize: num size is larger than usize");
        }

        match N::NUM_TYPE {
            NumType::U8 => unsafe { transmute_copy(&(nz as u8)) },
            NumType::U16 => unsafe { transmute_copy(&(nz as u16)) },
            NumType::U32 => unsafe { transmute_copy(&(nz as u32)) },
            NumType::U64 => unsafe { transmute_copy(&(nz as u64)) },
            NumType::Usize => unsafe { transmute_copy(&(nz as usize)) },
        }
    }

    const fn cast_to_usize<N>(num: N) -> usize
    where
        N: ConstNumType,
    {
        if size_of::<N>() > size_of::<usize>() {
            panic!("cast_to_usize: num size is larger than usize");
        }

        match N::NUM_TYPE {
            NumType::U8 => unsafe {
                let n_u8: u8 = transmute_copy(&num);
                n_u8 as usize
            },
            NumType::U16 => unsafe {
                let n_u16: u16 = transmute_copy(&num);
                n_u16 as usize
            },
            NumType::U32 => unsafe {
                let n_u32: u32 = transmute_copy(&num);
                n_u32 as usize
            },
            NumType::U64 => unsafe {
                let n_u64: u64 = transmute_copy(&num);
                n_u64 as usize
            },
            NumType::Usize => unsafe {
                let n_usize: usize = transmute_copy(&num);
                n_usize
            },
        }
    }

    unsafe impl<F> FlagMeta for BitFlags<F>
    where
        F: BitFlag,
        F::Numeric: ConstNumType,
    {
        const USED_FLAG_BITS_MASK: usize = cast_to_usize(F::ALL_BITS);

        fn to_usize(self) -> usize {
            cast_to_usize(self.bits())
        }

        unsafe fn from_usize(nz: usize) -> Self {
            unsafe { Self::from_bits_unchecked(cast_from_usize(nz)) }
        }
    }
}
