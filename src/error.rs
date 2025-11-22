use thiserror::Error;

#[derive(Error, Debug)]
pub enum FlaggedPointerError {
    #[error("flag overlap: pointer mask {:x} and flag mask {:x} overlap", .ptr_mask, .flag_mask)]
    FlagOverlap { ptr_mask: usize, flag_mask: usize },
    #[error("misalignment: pointer addr {:x} and flag mask {:x} are not aligned", .ptr_addr, .flag_mask)]
    Misalignment { ptr_addr: usize, flag_mask: usize },
}
