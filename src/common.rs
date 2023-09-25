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
};

use crate::{
    raw::{BaseAddress, ManageMemory},
    types::*,
};

use crate::{
    range::ByteRange,
    refs::{sealed::*, ContiguousEntryRef},
    tracker::AllocationTracker,
    MemoryState,
};

#[cfg(feature = "sync_impl")]
use crate::error::{LockTarget, LockingError};
#[cfg(feature = "sync_impl")]
use crate::SyncContiguousEntryRef;

/// Implementation details shared between [storage](StorageDetails) and
/// [`reference`](ReferenceDetails) implementations.
pub trait ImplBase: Sized {
    /// The type representing reference to internal state
    type StorageState<A: ManageMemory>;

    /// The type of reference returned by store operations.
    type ReferenceType<T: ?Sized, A: ManageMemory>: Clone;

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
    type StorageState<A: ManageMemory> = Rc<MemoryState<Self, A>>;
    type ReferenceType<T: ?Sized, A: ManageMemory> = ContiguousEntryRef<T, A>;
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
#[cfg(feature = "sync_impl")]
pub struct ImplConcurrent;
#[cfg(feature = "sync_impl")]
impl ImplBase for ImplConcurrent {
    type StorageState<A: ManageMemory> = Arc<MemoryState<Self, A>>;
    type ReferenceType<T: ?Sized, A: ManageMemory> = SyncContiguousEntryRef<T, A>;
    type LockResult<T> = Result<T, LockingError>;
    type ATGuard<'a> = MutexGuard<'a, AllocationTracker>;
}

/// Implementation which provides direct (unsafe) access to stored entries.
///
/// For example usage of default implementation see:
/// [`UnsafeContiguousMemory`](crate::UnsafeContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg(feature = "unsafe_impl")]
pub struct ImplUnsafe;
#[cfg(feature = "unsafe_impl")]
impl ImplBase for ImplUnsafe {
    type StorageState<A: ManageMemory> = MemoryState<Self, A>;
    type ReferenceType<T: ?Sized, A: ManageMemory> = *mut T;
    type LockResult<T> = T;
    type ATGuard<'a> = &'a mut AllocationTracker;
}

/// Implementation details of
/// [`ContiguousMemoryStorage`](ContiguousMemoryStorage).
pub trait StorageDetails<A: ManageMemory>: ImplBase {
    /// The type representing the base memory and allocation tracking.
    type Base;

    /// The type representing the allocation tracker discrete type.
    type AllocationTracker;

    /// The type representing [`Layout`] entries with inner mutability.
    type SizeType;

    /// Dereferences the inner state smart pointer and returns it by reference.
    fn deref_state(state: &Self::StorageState<A>) -> &MemoryState<Self, A>;

    /// Retrieves the base pointer from the base instance.
    fn get_base(base: &Self::Base) -> Self::LockResult<BaseAddress>;

    /// Retrieves the base pointer from the base instance. Non blocking version.
    fn try_get_base(base: &Self::Base) -> Self::LockResult<BaseAddress>;

    /// Retrieves the capacity from the state.
    fn get_capacity(capacity: &Self::SizeType) -> usize;

    /// Returns a writable reference to AllocationTracker.
    fn get_allocation_tracker(
        state: &mut Self::StorageState<A>,
    ) -> Self::LockResult<Self::ATGuard<'_>>;

    /// Deallocates the base memory using layout information.
    unsafe fn deallocate(alloc: &A, base: &mut Self::Base, layout: Layout);
}

#[cfg(feature = "sync_impl")]
impl<A: ManageMemory> StorageDetails<A> for ImplConcurrent {
    type Base = RwLock<BaseAddress>;
    type AllocationTracker = Mutex<AllocationTracker>;
    type SizeType = AtomicUsize;

    #[inline]
    fn deref_state(state: &Self::StorageState<A>) -> &MemoryState<Self, A> {
        state
    }

    #[inline]
    fn get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        base.read_named(LockTarget::BaseAddress)
            .map(|result| *result)
    }

    #[inline]
    fn try_get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        base.try_read_named(LockTarget::BaseAddress)
            .map(|result| *result)
    }

    #[inline]
    fn get_capacity(capacity: &Self::SizeType) -> usize {
        capacity.load(Ordering::Acquire)
    }

    #[inline]
    fn get_allocation_tracker(
        state: &mut Self::StorageState<A>,
    ) -> Self::LockResult<Self::ATGuard<'_>> {
        state.tracker.lock_named(LockTarget::AllocationTracker)
    }

    #[inline]
    unsafe fn deallocate(alloc: &A, base: &mut Self::Base, layout: Layout) {
        if let Ok(mut lock) = base.write_named(LockTarget::BaseAddress) {
            unsafe { alloc.deallocate(*lock, layout) };
            *lock = None;
        }
    }
}

impl<A: ManageMemory> StorageDetails<A> for ImplDefault {
    type Base = Cell<BaseAddress>;
    type AllocationTracker = RefCell<AllocationTracker>;
    type SizeType = Cell<usize>;

    #[inline]
    fn deref_state(state: &Self::StorageState<A>) -> &MemoryState<Self, A> {
        state
    }

    #[inline]
    fn get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        base.get()
    }

    #[inline]
    fn try_get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        <Self as StorageDetails<A>>::get_base(base)
    }

    #[inline]
    fn get_capacity(capacity: &Self::SizeType) -> usize {
        capacity.get()
    }

    #[inline]
    fn get_allocation_tracker(
        state: &mut Self::StorageState<A>,
    ) -> Self::LockResult<Self::ATGuard<'_>> {
        state.tracker.borrow_mut()
    }

    #[inline]
    unsafe fn deallocate(alloc: &A, base: &mut Self::Base, layout: Layout) {
        unsafe { alloc.deallocate(base.get(), layout) };
        base.set(None)
    }
}

#[cfg(feature = "unsafe_impl")]
impl<A: ManageMemory> StorageDetails<A> for ImplUnsafe {
    type Base = BaseAddress;
    type AllocationTracker = AllocationTracker;
    type SizeType = usize;

    #[inline]
    fn deref_state(state: &Self::StorageState<A>) -> &MemoryState<Self, A> {
        state
    }

    #[inline]
    fn get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        *base
    }

    #[inline]
    fn try_get_base(base: &Self::Base) -> Self::LockResult<BaseAddress> {
        <Self as StorageDetails<A>>::get_base(base)
    }

    #[inline]
    fn get_capacity(capacity: &Self::SizeType) -> usize {
        *capacity
    }

    #[inline]
    fn get_allocation_tracker(
        state: &mut Self::StorageState<A>,
    ) -> Self::LockResult<Self::ATGuard<'_>> {
        &mut state.tracker
    }

    #[inline]
    unsafe fn deallocate(alloc: &A, base: &mut Self::Base, layout: Layout) {
        unsafe {
            alloc.deallocate(*base, layout);
        }
        *base = None;
    }
}

/// Implementation details of returned [reference types](crate::refs).
pub trait ReferenceDetails<A: ManageMemory>: ImplBase {
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
        base: Self::LockResult<BaseAddress>,
        range: ByteRange,
    ) -> Option<*mut ()>;

    /// Marks reference state as no longer being borrowed.
    fn unborrow_ref<T: ?Sized>(_state: &Self::RefState<T>, _kind: BorrowKind) {}
}

#[cfg(feature = "sync_impl")]
impl<A: ManageMemory> ReferenceDetails<A> for ImplConcurrent {
    type RefState<T: ?Sized> = Arc<ReferenceState<T, Self, A>>;
    type BorrowLock = RwLock<()>;
    type ReadGuard<'a> = RwLockReadGuard<'a, ()>;
    type WriteGuard<'a> = RwLockWriteGuard<'a, ()>;

    fn free_region(
        tracker: Self::LockResult<Self::ATGuard<'_>>,
        base: Self::LockResult<BaseAddress>,
        range: ByteRange,
    ) -> Option<*mut ()> {
        if let Ok(mut lock) = tracker {
            let _ = lock.release(range);

            if let Ok(base) = base {
                range.offset_base(base)
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl<A: ManageMemory> ReferenceDetails<A> for ImplDefault {
    type RefState<T: ?Sized> = Rc<ReferenceState<T, Self, A>>;
    type BorrowLock = Cell<BorrowState>;
    type ReadGuard<'a> = ();
    type WriteGuard<'a> = ();

    fn free_region(
        mut tracker: Self::LockResult<Self::ATGuard<'_>>,
        base: Self::LockResult<BaseAddress>,
        range: ByteRange,
    ) -> Option<*mut ()> {
        let _ = tracker.release(range);
        range.offset_base(base)
    }

    fn unborrow_ref<T: ?Sized>(state: &Self::RefState<T>, _kind: BorrowKind) {
        let next = match state.borrow_kind.get() {
            BorrowState::Read(count) => BorrowState::Read(count - 1),
            BorrowState::Write => BorrowState::Read(0),
        };
        state.borrow_kind.set(next)
    }
}

#[cfg(feature = "unsafe_impl")]
impl<A: ManageMemory> ReferenceDetails<A> for ImplUnsafe {
    type RefState<T: ?Sized> = ();
    type BorrowLock = ();
    type ReadGuard<'a> = ();
    type WriteGuard<'a> = ();

    fn free_region(
        tracker: Self::LockResult<Self::ATGuard<'_>>,
        base: Self::LockResult<BaseAddress>,
        range: ByteRange,
    ) -> Option<*mut ()> {
        let _ = tracker.release(range);
        range.offset_base(base)
    }
}

/// Trait representing requirements for implementation details of the
/// [`ContiguousMemoryStorage`](crate::ContiguousMemory).
///
/// This trait is implemented by:
/// - [`ImplDefault`]
/// - [`ImplConcurrent`]
/// - [`ImplUnsafe`]
pub trait ImplDetails<A: ManageMemory>: ImplBase + StorageDetails<A> + ReferenceDetails<A> {}
impl<A: ManageMemory, Impl: ImplBase + StorageDetails<A> + ReferenceDetails<A>> ImplDetails<A>
    for Impl
{
}
