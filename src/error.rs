//! Errors produced by the crate.

#[cfg(feature = "error_in_core")]
use core::error::Error;
#[cfg(all(not(feature = "error_in_core"), not(feature = "no_std")))]
use std::error::Error;

#[cfg(not(feature = "no_std"))]
use std::sync::MutexGuard;
#[cfg(not(feature = "no_std"))]
use std::sync::PoisonError;

use core::alloc::LayoutError;
use core::fmt::Debug;
#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
use core::fmt::{Display, Formatter, Result as FmtResult};

use crate::range::ByteRange;

/// Error returned when a [`Mutex`](crate::types::Mutex) or a
/// [`RwLock`](crate::types::RwLock) isn't lockable.
#[derive(Debug)]
pub enum LockingError {
    /// Not lockable because the mutex/lock was poisoned.
    Poisoned {
        /// Specifies source of poisoning.
        source: LockSource,
    },
    /// Not lockable because the lock would be blocking.
    WouldBlock {
        /// Specifies which mutex/lock would block.
        source: LockSource,
    },
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for LockingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            LockingError::Poisoned { source } => write!(
                f,
                "Cannot acquire lock: {}",
                match source {
                    LockSource::BaseAddress => {
                        "base address Mutex was poisoned"
                    }
                    LockSource::AllocationTracker => "AllocationTracker Mutex was poisoned",
                    LockSource::Reference =>
                        "reference concurrent mutable access exclusion flag Mutex was poisoned",
                }
            ),
            LockingError::WouldBlock { source } => write!(
                f,
                "Lock would block the current thread: {}",
                match source {
                    LockSource::BaseAddress => "base address already borrowed",
                    LockSource::AllocationTracker => "AllocationTracker already borrowed",
                    LockSource::Reference => "reference already borrowed",
                }
            ),
        }
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for LockingError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

#[cfg(not(feature = "no_std"))]
impl From<PoisonError<MutexGuard<'_, *mut u8>>> for LockingError {
    fn from(_: PoisonError<MutexGuard<'_, *mut u8>>) -> Self {
        LockingError::Poisoned {
            source: LockSource::BaseAddress,
        }
    }
}

#[cfg(not(feature = "no_std"))]
impl From<PoisonError<MutexGuard<'_, crate::tracker::AllocationTracker>>> for LockingError {
    fn from(_: PoisonError<MutexGuard<'_, crate::tracker::AllocationTracker>>) -> Self {
        LockingError::Poisoned {
            source: LockSource::AllocationTracker,
        }
    }
}

/// Error returned when concurrent mutable access is attempted to the same
/// memory region.
#[derive(Debug)]
pub struct RegionBorrowedError {
    /// [`ByteRange`] that was attempted to be borrowed.
    pub range: ByteRange,
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for RegionBorrowedError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "attempted to borrow already mutably borrowed memory region: {}",
            self.range
        )
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for RegionBorrowedError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

/// Represents errors that can occur while using the
/// [`ContiguousMemoryStorage`](crate::ContiguousMemoryStorage) container.
#[derive(Debug)]
#[non_exhaustive]
pub enum ContiguousMemoryError {
    /// Tried to store data that does not fit into any of the remaining free
    /// memory regions.
    NoStorageLeft,
    /// Attempted to occupy a memory region that is already marked as taken.
    AlreadyUsed,
    /// Attempted to operate on a memory region that is not contained within the
    /// [`AllocationTracker`](crate::tracker::AllocationTracker).
    NotContained,
    /// Attempted to free memory that has already been deallocated.
    DoubleFree,
    /// The [`AllocationTracker`](crate::tracker::AllocationTracker) does not
    /// allow shrinking to the expected size.
    Unshrinkable {
        /// The minimum required size to house currently stored data.
        required_size: usize,
    },
    /// Indicates that a mutex wasn't lockable.
    Lock(LockingError),
    /// Indicates that the provided [`Layout`](core::alloc::Layout) is invalid.
    Layout(
        /// The underlying error that caused the [`Layout`](core::alloc::Layout)
        /// to be considered invalid.
        LayoutError,
    ),
    /// Tried mutably borrowing already borrowed region of memory
    BorrowMut(RegionBorrowedError),
}

/// Represents possible poisoning sources for mutexes and locks.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub enum LockSource {
    /// Mutex containing the base memory offset was poisoned.
    BaseAddress,
    /// `AllocationTracker` mutex was poisoned.
    AllocationTracker,
    /// Concurrent mutable access exclusion flag in `ReferenceState` was
    /// poisoned.
    Reference,
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for ContiguousMemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            ContiguousMemoryError::NoStorageLeft => {
                write!(f, "Insufficient free storage available")
            }
            ContiguousMemoryError::NotContained => {
                write!(f, "Attempted to mark a memory region that isn't contained")
            }
            ContiguousMemoryError::AlreadyUsed => write!(
                f,
                "Attempted to take a memory region that is already marked as occupied"
            ),
            ContiguousMemoryError::DoubleFree => write!(
                f,
                "Attempted to free a memory region that is already marked as free"
            ),
            ContiguousMemoryError::Unshrinkable {
                required_size: min_required,
            } => write!(
                f,
                "Cannot shrink memory regions; minimum required space: {} bytes",
                min_required
            ),
            ContiguousMemoryError::Lock(it) => write!(f, "Poison error: {}", it),
            ContiguousMemoryError::Layout(it) => write!(f, "Layout error: {}", it),
            ContiguousMemoryError::BorrowMut(it) => write!(f, "Borrow mutable error: {}", it),
        }
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for ContiguousMemoryError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ContiguousMemoryError::Layout(it) => Some(it),
            ContiguousMemoryError::Lock(it) => Some(it),
            _ => None,
        }
    }
}

impl From<LockingError> for ContiguousMemoryError {
    fn from(layout_err: LockingError) -> Self {
        ContiguousMemoryError::Lock(layout_err)
    }
}

impl From<LayoutError> for ContiguousMemoryError {
    fn from(layout_err: LayoutError) -> Self {
        ContiguousMemoryError::Layout(layout_err)
    }
}
