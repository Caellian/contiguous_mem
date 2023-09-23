//! Implementation details for behavior specialization marker structs.
//!
//! End-users aren't meant to interact with traits defined in this module
//! directly and they exist solely to simplify implementation of
//! [`ContiguousMemoryStorage`](ContiguousMemoryStorage) by erasing
//! type details of different implementations.
//!
//! Any changes to these traits aren't considered a breaking change and won't
//! be reflected in version numbers.

use core::{
    alloc::Layout,
    cell::{Cell, RefCell, RefMut},
    ptr::null_mut,
};

use crate::types::*;

use crate::{
    error::ContiguousMemoryError,
    range::ByteRange,
    refs::{sealed::*, ContiguousEntryRef},
    tracker::AllocationTracker,
    MemoryState,
};

#[cfg(feature = "sync")]
use crate::error::{LockSource, LockingError};
#[cfg(feature = "sync")]
use crate::SyncContiguousEntryRef;

/// Implementation details shared between [storage](StorageDetails) and
/// [`reference`](ReferenceDetails) implementations.
pub trait ImplBase: Sized {
    /// The type representing reference to internal state
    type StorageState: Clone;

    /// The type of reference returned by store operations.
    type ReferenceType<T: ?Sized>: Clone;

    /// The type representing result of accessing data that is locked in async
    /// context
    type LockResult<T>;

    /// The type representing the allocation tracker reference type.
    type ATGuard<'a>;
}

/// Implementation that's not thread-safe but performs faster as it avoids
/// mutexes and locks.
///
/// For example usage of default implementation see: [`ContiguousMemory`](crate::ContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ImplDefault;
impl ImplBase for ImplDefault {
    type StorageState = Rc<MemoryState<Self>>;
    type ReferenceType<T: ?Sized> = ContiguousEntryRef<T>;
    type LockResult<T> = T;
    type ATGuard<'a> = RefMut<'a, AllocationTracker>;
}

/// Thread-safe implementation utilizing mutexes and locks to prevent data
/// races.
///
/// For example usage of default implementation see:
/// [`SyncContiguousMemory`](crate::SyncContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg(feature = "sync")]
pub struct ImplConcurrent;
#[cfg(feature = "sync")]
impl ImplBase for ImplConcurrent {
    type StorageState = Arc<MemoryState<Self>>;
    type ReferenceType<T: ?Sized> = SyncContiguousEntryRef<T>;
    type LockResult<T> = Result<T, LockingError>;
    type ATGuard<'a> = MutexGuard<'a, AllocationTracker>;
}

/// Implementation which provides direct (unsafe) access to stored entries.
///
/// For example usage of default implementation see:
/// [`UnsafeContiguousMemory`](crate::UnsafeContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg(feature = "unsafe")]
pub struct ImplUnsafe;
#[cfg(feature = "unsafe")]
impl ImplBase for ImplUnsafe {
    type StorageState = MemoryState<Self>;
    type ReferenceType<T: ?Sized> = *mut T;
    type LockResult<T> = T;
    type ATGuard<'a> = &'a mut AllocationTracker;
}

/// Implementation details of
/// [`ContiguousMemoryStorage`](ContiguousMemoryStorage).
pub trait StorageDetails: ImplBase {
    /// The type representing the base memory and allocation tracking.
    type Base;

    /// The type representing the allocation tracker discrete type.
    type AllocationTracker;

    /// The type representing [`Layout`] entries with inner mutability.
    type SizeType;

    /// The type representing result of storing data.
    type PushResult<T>;

    /// Dereferences the inner state smart pointer and returns it by reference.
    fn deref_state(state: &Self::StorageState) -> &MemoryState<Self>;

    /// Retrieves the base pointer from the base instance.
    fn get_base(base: &Self::Base) -> Self::LockResult<*mut u8>;

    /// Retrieves the base pointer from the base instance. Non blocking version.
    fn try_get_base(base: &Self::Base) -> Self::LockResult<*mut u8>;

    /// Retrieves the capacity from the state.
    fn get_capacity(capacity: &Self::SizeType) -> usize;

    /// Returns a writable reference to AllocationTracker.
    fn get_allocation_tracker(
        state: &mut Self::StorageState,
    ) -> Self::LockResult<Self::ATGuard<'_>>;

    /// Deallocates the base memory using layout information.
    fn deallocate(base: &mut Self::Base, layout: Layout);
}

#[cfg(feature = "sync")]
impl StorageDetails for ImplConcurrent {
    type Base = RwLock<*mut u8>;
    type AllocationTracker = Mutex<AllocationTracker>;
    type SizeType = AtomicUsize;
    type PushResult<T> = Result<Self::ReferenceType<T>, LockingError>;

    #[inline]
    fn deref_state(state: &Self::StorageState) -> &MemoryState<Self> {
        state
    }

    #[inline]
    fn get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        base.read_named(LockSource::BaseAddress)
            .map(|result| *result)
    }

    #[inline]
    fn try_get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        base.try_read_named(LockSource::BaseAddress)
            .map(|result| *result)
    }

    #[inline]
    fn get_capacity(capacity: &Self::SizeType) -> usize {
        capacity.load(Ordering::Acquire)
    }

    #[inline]
    fn get_allocation_tracker(
        state: &mut Self::StorageState,
    ) -> Self::LockResult<Self::ATGuard<'_>> {
        state.tracker.lock_named(LockSource::AllocationTracker)
    }

    #[inline]
    fn deallocate(base: &mut Self::Base, layout: Layout) {
        if let Ok(mut lock) = base.write_named(LockSource::BaseAddress) {
            unsafe { allocator::dealloc(*lock, layout) };
            *lock = null_mut();
        }
    }
}

impl StorageDetails for ImplDefault {
    type Base = Cell<*mut u8>;
    type AllocationTracker = RefCell<AllocationTracker>;
    type SizeType = Cell<usize>;
    type PushResult<T> = ContiguousEntryRef<T>;

    #[inline]
    fn deref_state(state: &Self::StorageState) -> &MemoryState<Self> {
        state
    }

    #[inline]
    fn get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        base.get()
    }

    #[inline]
    fn try_get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        Self::get_base(base)
    }

    #[inline]
    fn get_capacity(capacity: &Self::SizeType) -> usize {
        capacity.get()
    }

    #[inline]
    fn get_allocation_tracker(
        state: &mut Self::StorageState,
    ) -> Self::LockResult<Self::ATGuard<'_>> {
        state.tracker.borrow_mut()
    }

    #[inline]
    fn deallocate(base: &mut Self::Base, layout: Layout) {
        unsafe { allocator::dealloc(base.get(), layout) };
        base.set(null_mut())
    }
}

#[cfg(feature = "unsafe")]
impl StorageDetails for ImplUnsafe {
    type Base = *mut u8;
    type AllocationTracker = AllocationTracker;
    type SizeType = usize;
    type PushResult<T> = Result<*mut T, ContiguousMemoryError>;

    #[inline]
    fn deref_state(state: &Self::StorageState) -> &MemoryState<Self> {
        state
    }

    #[inline]
    fn get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        *base
    }

    #[inline]
    fn try_get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        Self::get_base(base)
    }

    #[inline]
    fn get_capacity(capacity: &Self::SizeType) -> usize {
        *capacity
    }

    #[inline]
    fn get_allocation_tracker(
        state: &mut Self::StorageState,
    ) -> Self::LockResult<Self::ATGuard<'_>> {
        &mut state.tracker
    }

    #[inline]
    fn deallocate(base: &mut Self::Base, layout: Layout) {
        unsafe {
            allocator::dealloc(*base, layout);
        }
        *base = null_mut();
    }
}

/// Implementation details of returned [reference types](crate::refs).
pub trait ReferenceDetails: ImplBase {
    /// The type representing internal state of the reference.
    type RefState<T: ?Sized>: Clone;

    /// The type handling concurrent mutable access exclusion.
    type BorrowLock;

    /// Type of the concurrent mutable access exclusion read guard.
    type ReadGuard<'a>: DebugReq;
    /// Type of the concurrent mutable access exclusion write guard.
    type WriteGuard<'a>: DebugReq;

    /// Releases the specified memory region back to the allocation tracker.
    fn free_region(
        tracker: Self::LockResult<Self::ATGuard<'_>>,
        base: Self::LockResult<*mut u8>,
        range: ByteRange,
    ) -> Option<*mut ()>;

    /// Marks reference state as no longer being borrowed.
    fn unborrow_ref<T: ?Sized>(_state: &Self::RefState<T>, _kind: BorrowKind) {}
}

#[cfg(feature = "sync")]
impl ReferenceDetails for ImplConcurrent {
    type RefState<T: ?Sized> = Arc<ReferenceState<T, Self>>;
    type BorrowLock = RwLock<()>;
    type ReadGuard<'a> = RwLockReadGuard<'a, ()>;
    type WriteGuard<'a> = RwLockWriteGuard<'a, ()>;

    fn free_region(
        tracker: Self::LockResult<Self::ATGuard<'_>>,
        base: Self::LockResult<*mut u8>,
        range: ByteRange,
    ) -> Option<*mut ()> {
        if let Ok(mut lock) = tracker {
            let _ = lock.release(range);

            if let Ok(base) = base {
                unsafe { Some(base.add(range.0) as *mut ()) }
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl ReferenceDetails for ImplDefault {
    type RefState<T: ?Sized> = Rc<ReferenceState<T, Self>>;
    type BorrowLock = Cell<BorrowState>;
    type ReadGuard<'a> = ();
    type WriteGuard<'a> = ();

    fn free_region(
        mut tracker: Self::LockResult<Self::ATGuard<'_>>,
        base: Self::LockResult<*mut u8>,
        range: ByteRange,
    ) -> Option<*mut ()> {
        let _ = tracker.release(range);
        unsafe { Some(base.add(range.0) as *mut ()) }
    }

    fn unborrow_ref<T: ?Sized>(state: &Self::RefState<T>, _kind: BorrowKind) {
        let next = match state.borrow_kind.get() {
            BorrowState::Read(count) => BorrowState::Read(count - 1),
            BorrowState::Write => BorrowState::Read(0),
        };
        state.borrow_kind.set(next)
    }
}

#[cfg(feature = "unsafe")]
impl ReferenceDetails for ImplUnsafe {
    type RefState<T: ?Sized> = ();
    type BorrowLock = ();
    type ReadGuard<'a> = ();
    type WriteGuard<'a> = ();

    fn free_region(
        tracker: Self::LockResult<Self::ATGuard<'_>>,
        base: Self::LockResult<*mut u8>,
        range: ByteRange,
    ) -> Option<*mut ()> {
        let _ = tracker.release(range);

        unsafe { Some(base.add(range.0) as *mut ()) }
    }
}

/// Trait representing requirements for implementation details of the
/// [`ContiguousMemoryStorage`](crate::ContiguousMemory).
///
/// This trait is implemented by:
/// - [`ImplDefault`]
/// - [`ImplConcurrent`]
/// - [`ImplUnsafe`]
pub trait ImplDetails: ImplBase + StorageDetails + ReferenceDetails {}
impl<Impl: ImplBase + StorageDetails + ReferenceDetails> ImplDetails for Impl {}
