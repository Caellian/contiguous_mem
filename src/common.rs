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
    mem::size_of,
    ptr::null_mut,
};

use crate::types::*;
use core::marker::PhantomData;

use crate::{
    error::{ContiguousMemoryError, LockSource, LockingError},
    range::ByteRange,
    refs::{sealed::*, ContiguousEntryRef, SyncContiguousEntryRef},
    tracker::AllocationTracker,
    BaseLocation, MemoryState,
};

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
pub struct ImplConcurrent;
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
pub struct ImplUnsafe;
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

    /// Resizes and reallocates the base memory according to new capacity.
    fn resize_container(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError>;

    /// Deallocates the base memory using layout information.
    fn deallocate(base: &mut Self::Base, layout: Layout);

    /// Resizes the allocation tracker to the new capacity.
    fn resize_tracker(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError>;

    /// Shrinks tracked area of the allocation tracker to smallest that can fit
    /// currently stored data.
    fn shrink_tracker(state: &mut Self::StorageState) -> Self::LockResult<Option<usize>>;

    /// Finds the next free memory region for given layout in the tracker.
    fn track_next(
        state: &mut Self::StorageState,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError>;

    /// Returns whether a given layout can be stored or returns an error if
    /// [`AllocationTracker`] can't be stored.
    fn peek_next(state: &Self::StorageState, layout: Layout)
        -> Self::LockResult<Option<ByteRange>>;
}

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

    fn resize_container(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError> {
        let layout =
            Layout::from_size_align(state.capacity.load(Ordering::Acquire), state.alignment)?;
        let mut base_addr = state.base.write_named(LockSource::BaseAddress)?;
        let prev_addr = *base_addr;
        *base_addr = unsafe { allocator::realloc(*base_addr, layout, new_capacity) };
        state.capacity.store(new_capacity, Ordering::Release);
        Ok(if *base_addr != prev_addr {
            Some(*base_addr)
        } else {
            None
        })
    }

    #[inline]
    fn deallocate(base: &mut Self::Base, layout: Layout) {
        if let Ok(mut lock) = base.write_named(LockSource::BaseAddress) {
            unsafe { allocator::dealloc(*lock, layout) };
            *lock = null_mut();
        }
    }

    #[inline]
    fn resize_tracker(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        let mut lock = state.tracker.lock_named(LockSource::AllocationTracker)?;
        lock.resize(new_capacity)?;
        Ok(())
    }

    #[inline]
    fn shrink_tracker(state: &mut Self::StorageState) -> Result<Option<usize>, LockingError> {
        let mut lock = state.tracker.lock_named(LockSource::AllocationTracker)?;
        Ok(lock.shrink_to_fit())
    }

    #[inline]
    fn track_next(
        state: &mut Self::StorageState,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        let base = Self::get_base(&state.base)? as usize;
        let mut lock = state.tracker.lock_named(LockSource::AllocationTracker)?;
        lock.take_next(base, layout)
    }

    #[inline]
    fn peek_next(
        state: &Self::StorageState,
        layout: Layout,
    ) -> Result<Option<ByteRange>, LockingError> {
        let lock = state.tracker.lock_named(LockSource::AllocationTracker)?;
        Ok(lock.peek_next(layout))
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

    fn resize_container(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError> {
        let layout = Layout::from_size_align(state.capacity.get(), state.alignment)?;
        let prev_base = state.base.get();
        let new_base = unsafe { allocator::realloc(prev_base, layout, new_capacity) };
        state.base.set(new_base);
        state.capacity.set(new_capacity);
        Ok(if new_base != prev_base {
            Some(new_base)
        } else {
            None
        })
    }

    #[inline]
    fn deallocate(base: &mut Self::Base, layout: Layout) {
        unsafe { allocator::dealloc(base.get(), layout) };
        base.set(null_mut())
    }

    #[inline]
    fn resize_tracker(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        state.tracker.borrow_mut().resize(new_capacity)
    }

    #[inline]
    fn shrink_tracker(state: &mut Self::StorageState) -> Option<usize> {
        state.tracker.borrow_mut().shrink_to_fit()
    }

    #[inline]
    fn track_next(
        state: &mut Self::StorageState,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        let base = state.base.get() as usize;
        let mut tracker = state.tracker.borrow_mut();
        tracker.take_next(base, layout)
    }

    #[inline]
    fn peek_next(state: &Self::StorageState, layout: Layout) -> Option<ByteRange> {
        let tracker = state.tracker.borrow();
        tracker.peek_next(layout)
    }
}

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

    fn resize_container(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError> {
        let layout = Layout::from_size_align(state.capacity, state.alignment)?;
        let prev_base = *state.base;
        state.base = BaseLocation(unsafe { allocator::realloc(prev_base, layout, new_capacity) });
        state.capacity = new_capacity;
        Ok(if *state.base != prev_base {
            Some(*state.base)
        } else {
            None
        })
    }

    #[inline]
    fn deallocate(base: &mut Self::Base, layout: Layout) {
        unsafe {
            allocator::dealloc(*base, layout);
        }
        *base = null_mut();
    }

    #[inline]
    fn resize_tracker(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        state.tracker.resize(new_capacity)
    }

    #[inline]
    fn shrink_tracker(state: &mut Self::StorageState) -> Option<usize> {
        state.tracker.shrink_to_fit()
    }

    #[inline]
    fn track_next(
        state: &mut Self::StorageState,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        let base = *state.base as usize;
        state.tracker.take_next(base, layout)
    }

    #[inline]
    fn peek_next(state: &Self::StorageState, layout: Layout) -> Option<ByteRange> {
        state.tracker.peek_next(layout)
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

    /// Builds a reference for the stored data.
    fn build_ref<T>(
        state: &Self::StorageState,
        addr: *mut T,
        range: ByteRange,
    ) -> Self::ReferenceType<T>;

    /// Marks reference state as no longer being borrowed.
    fn unborrow_ref<T: ?Sized>(_state: &Self::RefState<T>, _kind: BorrowKind) {}
}

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

    fn build_ref<T>(
        state: &Self::StorageState,
        _addr: *mut T,
        range: ByteRange,
    ) -> Self::ReferenceType<T> {
        SyncContiguousEntryRef {
            inner: Arc::new(ReferenceState {
                state: state.clone(),
                range,
                borrow_kind: RwLock::new(()),
                drop_fn: drop_fn::<T>(),
                _phantom: PhantomData,
            }),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
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

    fn build_ref<T>(
        state: &Self::StorageState,
        _addr: *mut T,
        range: ByteRange,
    ) -> Self::ReferenceType<T> {
        ContiguousEntryRef {
            inner: Rc::new(ReferenceState {
                state: state.clone(),
                range,
                borrow_kind: Cell::new(BorrowState::Read(0)),
                drop_fn: drop_fn::<T>(),
                _phantom: PhantomData,
            }),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }

    fn unborrow_ref<T: ?Sized>(state: &Self::RefState<T>, _kind: BorrowKind) {
        let next = match state.borrow_kind.get() {
            BorrowState::Read(count) => BorrowState::Read(count - 1),
            BorrowState::Write => BorrowState::Read(0),
        };
        state.borrow_kind.set(next)
    }
}

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

    fn build_ref<T>(
        _base: &Self::StorageState,
        addr: *mut T,
        _range: ByteRange,
    ) -> Self::ReferenceType<T> {
        addr
    }
}

pub trait StoreDataDetails: StorageDetails {
    unsafe fn push_raw<T>(
        state: &mut Self::StorageState,
        data: *const T,
        layout: Layout,
    ) -> Self::PushResult<T>;

    unsafe fn push_raw_persisted<T>(
        state: &mut Self::StorageState,
        data: *const T,
        layout: Layout,
    ) -> Self::PushResult<T>;

    fn assume_stored<T>(
        state: &Self::StorageState,
        position: usize,
    ) -> Self::LockResult<Self::ReferenceType<T>>;
}

impl StoreDataDetails for ImplConcurrent {
    unsafe fn push_raw<T>(
        state: &mut Self::StorageState,
        data: *const T,
        layout: Layout,
    ) -> Result<SyncContiguousEntryRef<T>, LockingError> {
        let (addr, range) = loop {
            match ImplConcurrent::track_next(state, layout) {
                Ok(taken) => {
                    let found = (taken.0
                        + *state.base.read_named(LockSource::BaseAddress)? as usize)
                        as *mut u8;
                    unsafe { core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size()) }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    let curr_capacity = state.capacity.load(Ordering::Acquire);
                    let new_capacity = curr_capacity
                        .saturating_mul(2)
                        .max(curr_capacity + layout.size());
                    match ImplConcurrent::resize_container(state, new_capacity) {
                        Ok(_) => {
                            match ImplConcurrent::resize_tracker(state, new_capacity) {
                                Ok(_) => {},
                                Err(ContiguousMemoryError::Lock(locking_err)) => return Err(locking_err),
                                Err(_) => unreachable!("unable to grow AllocationTracker"),
                            };
                        }
                        Err(ContiguousMemoryError::Lock(locking_err)) => return Err(locking_err),
                        Err(other) => unreachable!(
                            "reached unexpected error while growing the container to store data: {:?}",
                            other
                        ),
                    };
                }
                Err(ContiguousMemoryError::Lock(locking_err)) => return Err(locking_err),
                Err(other) => unreachable!(
                    "reached unexpected error while looking for next region to store data: {:?}",
                    other
                ),
            }
        };

        Ok(ImplConcurrent::build_ref(state, addr as *mut T, range))
    }

    #[inline(always)]
    unsafe fn push_raw_persisted<T>(
        state: &mut Self::StorageState,
        data: *const T,
        layout: Layout,
    ) -> Self::PushResult<T> {
        match Self::push_raw(state, data, layout) {
            Ok(it) => {
                let result = it.clone();
                core::mem::forget(it.inner);
                Ok(result)
            }
            err => err,
        }
    }

    #[inline(always)]
    fn assume_stored<T>(
        state: &Self::StorageState,
        position: usize,
    ) -> Result<SyncContiguousEntryRef<T>, LockingError> {
        let addr = unsafe {
            state
                .base
                .read_named(LockSource::BaseAddress)?
                .add(position)
        };
        Ok(ImplConcurrent::build_ref(
            state,
            addr as *mut T,
            ByteRange(position, size_of::<T>()),
        ))
    }
}

impl StoreDataDetails for ImplDefault {
    unsafe fn push_raw<T>(
        state: &mut Self::StorageState,
        data: *const T,
        layout: Layout,
    ) -> ContiguousEntryRef<T> {
        let (addr, range) = loop {
            match ImplDefault::track_next(state, layout) {
                Ok(taken) => {
                    let found = (taken.0 + state.base.get() as usize) as *mut u8;
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    let curr_capacity = state.capacity.get();
                    let new_capacity = curr_capacity
                        .saturating_mul(2)
                        .max(curr_capacity + layout.size());
                    match ImplDefault::resize_container(state, new_capacity) {
                        Ok(_) => {
                            ImplDefault::resize_tracker(state, new_capacity).expect("unable to grow AllocationTracker");
                        },
                        Err(err) => unreachable!(
                            "reached unexpected error while growing the container to store data: {:?}",
                            err
                        ),
                    }
                }
                Err(other) => unreachable!(
                    "reached unexpected error while looking for next region to store data: {:?}",
                    other
                ),
            }
        };

        ImplDefault::build_ref(state, addr as *mut T, range)
    }

    #[inline(always)]
    unsafe fn push_raw_persisted<T>(
        state: &mut Self::StorageState,
        data: *const T,
        layout: Layout,
    ) -> Self::PushResult<T> {
        let value = Self::push_raw(state, data, layout);
        let result = value.clone();
        core::mem::forget(value.inner);
        result
    }

    #[inline(always)]
    fn assume_stored<T>(state: &Self::StorageState, position: usize) -> ContiguousEntryRef<T> {
        let addr = unsafe { state.base.get().add(position) };
        ImplDefault::build_ref(state, addr as *mut T, ByteRange(position, size_of::<T>()))
    }
}

impl StoreDataDetails for ImplUnsafe {
    /// Returns a raw pointer (`*mut T`) to the stored value or an error if no
    /// free regions remain
    unsafe fn push_raw<T>(
        state: &mut Self::StorageState,
        data: *const T,
        layout: Layout,
    ) -> Result<*mut T, ContiguousMemoryError> {
        let (addr, range) = match ImplUnsafe::track_next(state, layout) {
            Ok(taken) => {
                let found = (taken.0 + *state.base as usize) as *mut u8;
                unsafe {
                    core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                }

                (found, taken)
            }
            Err(other) => return Err(other),
        };

        Ok(ImplUnsafe::build_ref(state, addr as *mut T, range))
    }

    unsafe fn push_raw_persisted<T>(
        _state: &mut Self::StorageState,
        _data: *const T,
        _layout: Layout,
    ) -> Self::PushResult<T> {
        unimplemented!()
    }

    #[inline(always)]
    fn assume_stored<T>(state: &Self::StorageState, position: usize) -> *mut T {
        let addr = unsafe { state.base.add(position) };
        ImplUnsafe::build_ref(
            state,
            addr as *mut T,
            ByteRange(position, position + size_of::<T>()),
        )
    }
}

/// Trait representing requirements for implementation details of the
/// [`ContiguousMemoryStorage`](crate::ContiguousMemoryStorage).
///
/// This trait is implemented by:
/// - [`ImplDefault`]
/// - [`ImplConcurrent`]
/// - [`ImplUnsafe`]
pub trait ImplDetails: ImplBase + StorageDetails + ReferenceDetails + StoreDataDetails {}
impl<Impl: ImplBase + StorageDetails + ReferenceDetails + StoreDataDetails> ImplDetails for Impl {}
