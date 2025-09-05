//! # Flag Metadata
//!
//! This module defines the `FlagMeta` trait and implementations for encoding
//! flag information within unused pointer bits.

/// A trait for types that can be encoded as flags in unused pointer bits.
///
/// This trait is `unsafe` to implement because it requires careful attention to
/// bit patterns and must not conflict with valid pointer bits.
///
/// # Safety
///
/// Implementors must ensure:
/// 1. usize returned by `mask()` includes all bits that are guaranteed to be unused in pointers, more is ok but less is not
/// 2. `to_usize` and `from_usize` are inverse operations
/// 3. All possible values of `USED_FLAG_BITS_MASK` are valid for the type
///
/// # Examples
///
/// ```
/// use flagged_pointer::flag::FlagMeta;
///
/// #[derive(Copy, Clone)]
/// struct MyFlags(u8);
///
/// unsafe impl FlagMeta for MyFlags {
///     const USED_FLAG_BITS_MASK: usize = 0b111; // Use bottom 3 bits
///     
///     fn to_usize(self) -> usize {
///         self.0 as usize
///     }
///     
///     unsafe fn from_usize(nz: usize) -> Self {
///         MyFlags(nz as u8)
///     }
/// }
/// ```
pub unsafe trait FlagMeta: Copy {
    /// Bitmask indicating which bits are used for flags, only for compile time check
    /// If bitmask is not known at compile time, set it to 0 (means no compile time check)
    const USED_FLAG_BITS_MASK: usize;

    /// Returns the bitmask for flag bits.
    /// Defaults to `USED_FLAG_BITS_MASK` but can be overridden for dynamic masks.
    fn mask() -> usize {
        Self::USED_FLAG_BITS_MASK
    }

    /// Converts the flag type to a `usize` for storage in pointer bits.
    fn to_usize(self) -> usize;

    /// Converts a `usize` back to the flag type.
    /// The caller can garantee that `nz` contains only valid flag bits.
    unsafe fn from_usize(nz: usize) -> Self;
}

/// Implement `FlagMeta` for `enumflags2::BitFlags`
/// Because `const_ops` is not stable, we have to record the num type and manually cast it in compile time
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
