//! Errors produced by the crate.

#[cfg(any(feature = "error_in_core", not(feature = "no_std")))]
use crate::types::Error;

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
use core::fmt::{Display, Formatter, Result as FmtResult};
use core::{cell::Ref, fmt::Debug};

use crate::{
    memory::ManageMemory,
    range::ByteRange,
    reference::BorrowState,
    types::{ImplDetails, ImplReferencing, ReadableInner, WritableInner},
};

/// Represents a class of errors returned by invalid memory operations and
/// allocator failiure.
#[derive(Debug, Clone, Copy)]
pub enum MemoryError {
    /// Tried allocating container capacity larger than `isize::MAX`
    TooLarge,
    /// Allocation failure caused by either resource exhaustion or invalid
    /// arguments being provided to an allocator.
    Allocator(
        #[cfg(feature = "allocator_api")] core::alloc::AllocError,
        #[cfg(not(feature = "allocator_api"))] (),
    ),
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
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

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for MemoryError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            #[cfg(feature = "allocator_api")]
            MemoryError::Allocator(inner) => Some(inner),
            _ => None,
        }
    }
}

#[cfg(feature = "allocator_api")]
impl From<core::alloc::AllocError> for MemoryError {
    fn from(err: core::alloc::AllocError) -> Self {
        MemoryError::Allocator(err)
    }
}

/// Error returned when concurrent mutable access is attempted to the same
/// memory region.
#[derive(Debug)]
pub struct RegionBorrowError {
    /// Range that was attempted to be borrowed.
    pub range: ByteRange,
    /// State of the borrow before failiure.
    pub borrow_state: BorrowState,
}
#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
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

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for RegionBorrowError {}
