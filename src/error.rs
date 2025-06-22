//! Errors produced by the crate.

#[cfg(any(feature = "error_in_core", feature = "std"))]
use crate::types::Error;

use core::fmt::Debug;
#[cfg(any(feature = "std", feature = "error_in_core"))]
use core::fmt::{Display, Formatter, Result as FmtResult};

use crate::{range::ByteRange, reference::BorrowState};

#[cfg(nightly)]
use core::alloc::AllocError;
#[cfg(not(nightly))]
use allocator_api2::alloc::AllocError;

/// Represents a class of errors returned by invalid memory operations and
/// allocator failure.
#[derive(Debug, Clone, Copy)]
pub enum MemoryError {
    /// Tried allocating memory chunk larger than [`isize::MAX`] or what is
    /// currently available.
    TooLarge,
    /// Allocation failure caused by either resource exhaustion or invalid
    /// arguments being provided to an allocator.
    Allocator(
        /// Cause allocator error.
        AllocError,
    ),
}

impl From<core::alloc::LayoutError> for MemoryError {
    fn from(_: core::alloc::LayoutError) -> Self {
        Self::TooLarge
    }
}

#[cfg(any(feature = "std", feature = "error_in_core"))]
impl Display for MemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            MemoryError::TooLarge => write!(
                f,
                "Tried allocating container capacity larger than `isize::MAX`"
            ),
            MemoryError::Allocator(_) => write!(f, "Allocator error"),
        }
    }
}

#[cfg(any(feature = "std", feature = "error_in_core"))]
impl Error for MemoryError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            MemoryError::Allocator(inner) => Some(inner),
            _ => None,
        }
    }
}

impl From<AllocError> for MemoryError {
    fn from(err: AllocError) -> Self {
        MemoryError::Allocator(err)
    }
}

/// Error returned when concurrent mutable access to the same memory region is
/// attempted.
#[derive(Debug)]
pub struct RegionBorrowError {
    /// Range that was attempted to be borrowed.
    pub range: ByteRange,
    /// State of the borrow before failiure.
    pub borrow_state: BorrowState,
}
#[cfg(any(feature = "std", feature = "error_in_core"))]
impl Display for RegionBorrowError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self.borrow_state {
            BorrowState::Read(_) => write!(
                f,
                "Attempted to mutably borrow already immuatably borrowed memory region: {}",
                self.range
            ),
            BorrowState::Write => write!(
                f,
                "Attempted to immutably borrow already mutably borrowed memory region: {}",
                self.range
            ),
        }
    }
}

#[cfg(any(feature = "std", feature = "error_in_core"))]
impl Error for RegionBorrowError {}
