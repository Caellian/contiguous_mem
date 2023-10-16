//! Errors produced by the crate.

#[cfg(any(feature = "error_in_core", not(feature = "no_std")))]
use crate::types::Error;

use core::fmt::Debug;
#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
use core::fmt::{Display, Formatter, Result as FmtResult};

use crate::range::ByteRange;

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

/// Error indicating that the container is full.
#[derive(Debug, Clone, Copy)]
pub struct NoFreeMemoryError;

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for NoFreeMemoryError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Insufficient free memory")
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for NoFreeMemoryError {}

/// Error returned when concurrent mutable access is attempted to the same
/// memory region.
#[derive(Debug)]
pub struct RegionBorrowError {
    /// [`ByteRange`] that was attempted to be borrowed.
    pub range: ByteRange,
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Display for RegionBorrowError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "Attempted to borrow already mutably borrowed memory region: {}",
            self.range
        )
    }
}

#[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
impl Error for RegionBorrowError {}

/// Represents possible poisoning or stalling sources for mutexes and locks.
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub enum LockTarget {
    /// Refers to mutex containing the base memory offset.
    BaseAddress,
    /// Refers to segment tracker mutex.
    SegmentTracker,
    /// Refers to concurrent mutable access exclusion flag in reference state.
    Reference,
}

#[cfg(feature = "sync_impl")]
impl LockTarget {
    const fn as_str(&self) -> &'static str {
        match self {
            LockTarget::BaseAddress => "base address",
            LockTarget::SegmentTracker => "segment tracker",
            LockTarget::Reference => "reference",
        }
    }
}

#[cfg(feature = "sync_impl")]
mod sync {
    use super::*;

    #[cfg(not(feature = "no_std"))]
    use std::sync::MutexGuard;
    #[cfg(not(feature = "no_std"))]
    use std::sync::PoisonError;

    /// Error returned when a [`Mutex`](crate::types::Mutex) or a
    /// [`RwLock`](crate::types::RwLock) isn't lockable.
    #[derive(Debug)]
    pub enum LockingError {
        /// Describes failure due to the accessed Mutex/RwLock being poisoned.
        Poisoned {
            /// Specifies source of poisoning.
            target: LockTarget,
        },
        /// Describes failure due to the fact that locking a resource would block.
        WouldBlock {
            /// Specifies which mutex/lock would block.
            target: LockTarget,
        },
    }

    #[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
    impl Display for LockingError {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            match self {
                LockingError::Poisoned { target } => {
                    write!(f, "Cannot lock {}, it was poisoned", target.as_str())
                }
                LockingError::WouldBlock { target } => write!(
                    f,
                    "Locking {} would block the current thread",
                    target.as_str()
                ),
            }
        }
    }

    #[cfg(any(not(feature = "no_std"), feature = "error_in_core"))]
    impl Error for LockingError {}

    #[cfg(not(feature = "no_std"))]
    impl From<PoisonError<MutexGuard<'_, *mut u8>>> for LockingError {
        fn from(_: PoisonError<MutexGuard<'_, *mut u8>>) -> Self {
            LockingError::Poisoned {
                target: LockTarget::BaseAddress,
            }
        }
    }

    #[cfg(not(feature = "no_std"))]
    impl From<PoisonError<MutexGuard<'_, crate::memory::SegmentTracker>>> for LockingError {
        fn from(_: PoisonError<MutexGuard<'_, crate::memory::SegmentTracker>>) -> Self {
            LockingError::Poisoned {
                target: LockTarget::SegmentTracker,
            }
        }
    }

    /// A wrapper that represents either a memory error or a locking error.
    pub enum SyncMemoryError {
        /// A memory error.
        Memory(MemoryError),
        /// A locking error.
        Lock(LockingError),
    }

    impl From<MemoryError> for SyncMemoryError {
        fn from(err: MemoryError) -> Self {
            SyncMemoryError::Memory(err)
        }
    }
    impl From<LockingError> for SyncMemoryError {
        fn from(err: LockingError) -> Self {
            SyncMemoryError::Lock(err)
        }
    }
}
#[cfg(feature = "sync_impl")]
pub use sync::*;
