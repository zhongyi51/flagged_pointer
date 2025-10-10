#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FlagOverlapError {
    pub ptr_mask: usize,
    pub flag_mask: usize,
}

impl FlagOverlapError {
    pub fn new(ptr_mask: usize, flag_mask: usize) -> Self {
        Self { ptr_mask, flag_mask }
    }
}

impl std::error::Error for FlagOverlapError {}

impl std::fmt::Display for FlagOverlapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "FlagOverlapError: pointer mask {:x} and flag mask {:x} overlap",
            self.ptr_mask, self.flag_mask
        )
    }
}