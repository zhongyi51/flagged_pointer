use enumflags2::{BitFlags, bitflags};
use flagged_pointer::{
    alias::{FlaggedBox, FlaggedBoxSlice, FlaggedNonNull, FlaggedNonNullSlice},
    repr_storage::{AtomicPointerStorage, PointerStorage},
};
use std::{
    cell::Cell,
    panic::{AssertUnwindSafe, catch_unwind},
    ptr::{self, NonNull},
    rc::Rc,
    sync::atomic::AtomicPtr,
};

#[bitflags]
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Flag {
    A = 1,
}

type Flags = BitFlags<Flag>;

#[test]
fn raw_slice_dangling_roundtrip_does_not_access_memory() {
    for len in [0, 1, usize::MAX] {
        let raw = NonNull::slice_from_raw_parts(NonNull::<u64>::dangling(), len);
        let flagged = FlaggedNonNullSlice::new(raw, Flags::empty());
        let (recovered, flags) = flagged.dissolve();
        assert_eq!(recovered.cast::<u64>(), raw.cast::<u64>());
        assert_eq!(recovered.len(), len);
        assert!(flags.is_empty());
    }
}

#[test]
fn raw_slice_roundtrip_preserves_shared_borrow() {
    let values = [10_u64, 20];
    let shared = &values[..];
    let raw = NonNull::from(shared);
    let flagged = FlaggedNonNullSlice::new(raw, Flags::from(Flag::A));
    assert_eq!(shared, [10, 20]);
    let recovered = flagged.into_ptr();
    assert_eq!(recovered.cast::<u64>(), raw.cast::<u64>());
    assert_eq!(recovered.len(), shared.len());
    assert_eq!(shared, [10, 20]);
}

#[test]
fn sparse_flags_preserve_unused_address_bits() {
    // NonNull does not require alignment. Bit 1 belongs to this raw address,
    // even though u64 alignment would make it zero for a dereferenceable u64.
    let raw = NonNull::<u16>::dangling().cast::<u64>();
    let flagged = FlaggedNonNull::new(raw, Flags::from(Flag::A));
    assert_eq!(flagged.as_ptr(), raw);
    assert_eq!(flagged.flag(), Flag::A);
    assert_eq!(flagged.into_ptr(), raw);
}

#[test]
#[should_panic]
fn atomic_storage_load_rejects_null() {
    let storage = AtomicPtr::<()>::new(ptr::null_mut());
    let _ = PointerStorage::load(&storage);
}

#[test]
#[should_panic]
fn atomic_storage_set_rejects_null_old_value() {
    let mut storage = AtomicPtr::<()>::new(ptr::null_mut());
    let _ = PointerStorage::set(&mut storage, NonNull::dangling());
}

#[test]
#[should_panic]
fn atomic_storage_compare_exchange_rejects_null_actual_value() {
    let storage = AtomicPtr::<()>::new(ptr::null_mut());
    let _ =
        AtomicPointerStorage::compare_exchange(&storage, NonNull::dangling(), NonNull::dangling());
}

#[test]
fn box_clone_preserves_live_shared_borrow() {
    let owner = FlaggedBox::new(Box::new(42_u64), Flags::from(Flag::A));
    let borrowed: &u64 = &owner;
    let cloned = owner.clone();
    assert_eq!(*borrowed, 42);
    assert_eq!(*cloned, 42);
    assert_ne!(owner.as_ptr(), cloned.as_ptr());
}

#[test]
fn boxed_slice_clone_preserves_live_shared_borrow() {
    let owner = FlaggedBoxSlice::new(vec![10_u64, 20].into_boxed_slice(), Flags::empty());
    let borrowed: &[u64] = &owner;
    let cloned = owner.clone();
    assert_eq!(borrowed, [10, 20]);
    assert_eq!(&*cloned, borrowed);
    assert_ne!(owner.as_ptr().cast::<u64>(), cloned.as_ptr().cast::<u64>());
}

struct PanickingClone {
    value: u64,
    drops: Rc<Cell<usize>>,
}

impl Clone for PanickingClone {
    fn clone(&self) -> Self {
        panic!("deliberate clone failure");
    }
}

impl Drop for PanickingClone {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

#[test]
fn panicking_box_clone_preserves_original_ownership_and_borrow() {
    let drops = Rc::new(Cell::new(0));
    let owner = FlaggedBox::new(
        Box::new(PanickingClone {
            value: 42,
            drops: Rc::clone(&drops),
        }),
        Flags::empty(),
    );
    let borrowed: &PanickingClone = &owner;
    let result = catch_unwind(AssertUnwindSafe(|| owner.clone()));
    assert!(result.is_err());
    assert_eq!(borrowed.value, 42);
    assert_eq!(drops.get(), 0);
    drop(owner);
    assert_eq!(drops.get(), 1);
}

mod dynamic_cloning {
    use super::*;
    use flagged_pointer::{
        alias::FlaggedBoxDyn,
        ptr::{ClonePtrMeta, PtrMeta, ptr_impl::WithMaskMeta},
    };

    thread_local! {
        static ORIGINAL_DROPS: Cell<usize> = const { Cell::new(0) };
        static CLONE_DROPS: Cell<usize> = const { Cell::new(0) };
    }

    #[ptr_meta::pointee]
    trait Item {
        fn clone_box(&self) -> Box<dyn Item>;
        fn value(&self) -> u8;
    }

    impl Clone for Box<dyn Item> {
        fn clone(&self) -> Self {
            self.clone_box()
        }
    }

    // SAFETY: Cloning borrows the original pointee only through a shared
    // reference. It returns a separately owned allocation, including on unwind.
    unsafe impl ClonePtrMeta<WithMaskMeta<dyn Item>> for Box<dyn Item> {
        unsafe fn clone_storage_shared(nz: NonNull<()>, meta: WithMaskMeta<dyn Item>) -> Self {
            // SAFETY: The caller provides a live pointer and matching metadata;
            // map_pointee and as_ref introduce no exclusive borrow or owner.
            unsafe { Self::map_pointee(nz, meta).as_ref().clone_box() }
        }
    }

    #[repr(align(8))]
    struct High(u8);

    struct Low(u8);

    impl Item for High {
        fn clone_box(&self) -> Box<dyn Item> {
            Box::new(Low(self.0))
        }

        fn value(&self) -> u8 {
            self.0
        }
    }

    impl Item for Low {
        fn clone_box(&self) -> Box<dyn Item> {
            Box::new(Self(self.0))
        }

        fn value(&self) -> u8 {
            self.0
        }
    }

    impl Drop for High {
        fn drop(&mut self) {
            ORIGINAL_DROPS.with(|drops| drops.set(drops.get() + 1));
        }
    }

    impl Drop for Low {
        fn drop(&mut self) {
            CLONE_DROPS.with(|drops| drops.set(drops.get() + 1));
        }
    }

    #[test]
    fn dynamic_clone_rechecks_alignment_and_drops_rejected_clone_once() {
        ORIGINAL_DROPS.with(|drops| drops.set(0));
        CLONE_DROPS.with(|drops| drops.set(0));
        let original: FlaggedBoxDyn<dyn Item, Flags> =
            FlaggedBoxDyn::new(Box::new(High(42)), Flags::from(Flag::A));
        let borrowed: &dyn Item = &*original;

        // The clone's concrete type has alignment 1, so there are no spare
        // flag bits, regardless of the allocator's chosen address.
        let result = catch_unwind(AssertUnwindSafe(|| original.clone()));
        assert!(result.is_err());
        assert_eq!(borrowed.value(), 42);
        ORIGINAL_DROPS.with(|drops| assert_eq!(drops.get(), 0));
        CLONE_DROPS.with(|drops| assert_eq!(drops.get(), 1));
        drop(original);
        ORIGINAL_DROPS.with(|drops| assert_eq!(drops.get(), 1));
        CLONE_DROPS.with(|drops| assert_eq!(drops.get(), 1));
    }
}
