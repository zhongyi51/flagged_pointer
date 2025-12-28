use thiserror::Error;

#[derive(Error)]
pub enum FlaggedPointerError<P> {
    #[error("flag overlap: pointer mask {:x} and flag mask {:x} overlap", .ptr_mask, .flag_mask)]
    FlagOverlap { ptr_mask: usize, flag_mask: usize, origin_pointer:P},
    #[error("misalignment: pointer addr {:x} and flag mask {:x} are not aligned", .ptr_addr, .flag_mask)]
    Misalignment { ptr_addr: usize, flag_mask: usize, origin_pointer:P},
}

impl<P> std::fmt::Debug for FlaggedPointerError<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FlagOverlap { ptr_mask, flag_mask, .. } => {
                f.debug_struct("FlagOverlap")
                    .field("ptr_mask", ptr_mask)
                    .field("flag_mask", flag_mask)
                    .finish()
            }
            Self::Misalignment { ptr_addr, flag_mask, .. } => {
                f.debug_struct("Misalignment")
                    .field("ptr_addr", ptr_addr)
                    .field("flag_mask", flag_mask)
                    .finish()
            }
        }
    }
}