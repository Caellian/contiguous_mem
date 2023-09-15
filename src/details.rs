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
    alloc::{Layout, LayoutError},
    cell::{Cell, RefCell},
    mem::size_of,
    ptr::null_mut,
};

use core::marker::PhantomData;

#[cfg(feature = "no_std")]
use portable_atomic::{AtomicUsize, Ordering};
#[cfg(not(feature = "no_std"))]
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::{
    error::{ContiguousMemoryError, LockSource, LockingError},
    range::ByteRange,
    refs::{sealed::*, ContiguousEntryRef, SyncContiguousEntryRef},
    tracker::AllocationTracker,
    types::*,
    BaseLocation, ContiguousMemoryState,
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

    /// Indicates whether locks are used for synchronization, allowing the
    /// compiler to easily optimize away branches involving them.
    const USES_LOCKS: bool = false;
}

/// A marker struct representing the behavior specialization that does not
/// require thread-safety. This implementation skips mutexes, making it faster
/// but unsuitable for concurrent usage.
///
/// For example usage of default implementation see: [`ContiguousMemory`](crate::ContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ImplDefault;
impl ImplBase for ImplDefault {
    type StorageState = Rc<ContiguousMemoryState<Self>>;
    type ReferenceType<T: ?Sized> = ContiguousEntryRef<T>;
    type LockResult<T> = T;
}

/// A marker struct representing the behavior specialization for thread-safe
/// operations. This implementation ensures that the container's operations can
/// be used safely in asynchronous contexts, utilizing mutexes to prevent data
/// races.
///
/// For example usage of default implementation see:
/// [`SyncContiguousMemory`](crate::SyncContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ImplConcurrent;
impl ImplBase for ImplConcurrent {
    type StorageState = Arc<ContiguousMemoryState<Self>>;
    type ReferenceType<T: ?Sized> = SyncContiguousEntryRef<T>;
    type LockResult<T> = Result<T, LockingError>;

    const USES_LOCKS: bool = true;
}

/// A marker struct representing the behavior specialization for unsafe
/// implementation. Should be used when the container is guaranteed to outlive
/// any pointers to data contained in represented memory block.
///
/// For example usage of default implementation see:
/// [`UnsafeContiguousMemory`](crate::UnsafeContiguousMemory)
#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ImplUnsafe;
impl ImplBase for ImplUnsafe {
    type StorageState = ContiguousMemoryState<Self>;
    type ReferenceType<T: ?Sized> = *mut T;
    type LockResult<T> = T;
}

/// Implementation details of
/// [`ContiguousMemoryStorage`](ContiguousMemoryStorage).
pub trait StorageDetails: ImplBase {
    /// The type representing the base memory and allocation tracking.
    type Base;

    /// The type representing the allocation tracking mechanism.
    type AllocationTracker;

    /// The type representing [`Layout`] entries with inner mutability.
    type SizeType;

    /// The type representing result of storing data.
    type StoreResult<T>;

    /// Builds a new internal state from provided parameters
    fn build_state(
        base: *mut u8,
        capacity: usize,
        alignment: usize,
    ) -> Result<Self::StorageState, LayoutError>;

    /// Dereferences the inner state smart pointer and returns it by reference.
    fn deref_state(state: &Self::StorageState) -> &ContiguousMemoryState<Self>;

    /// Retrieves the base pointer from the base instance.
    fn get_base(base: &Self::Base) -> Self::LockResult<*mut u8>;

    /// Retrieves the base pointer from the base instance. Non blocking version.
    fn try_get_base(base: &Self::Base) -> Self::LockResult<*mut u8>;

    /// Retrieves the capacity from the state.
    fn get_capacity(capacity: &Self::SizeType) -> usize;

    /// Resizes and reallocates the base memory according to new capacity.
    fn resize_container(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError>;

    /// Deallocates the base memory using layout information.
    fn deallocate(base: &Self::Base, layout: Layout);

    /// Resizes the allocation tracker to the new capacity.
    fn resize_tracker(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError>;

    /// Shrinks tracked area of the allocation tracker to smallest that can fit
    /// currently stored data.
    fn shrink_tracker(state: &mut Self::StorageState) -> Result<Option<usize>, LockingError>;

    /// Finds the next free memory region for given layout in the tracker.
    fn track_next(
        state: &mut Self::StorageState,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError>;

    /// Returns whether a given layout can be stored or returns an error if
    /// [`AllocationTracker`] can't be stored.
    fn peek_next(
        state: &Self::StorageState,
        layout: Layout,
    ) -> Result<Option<ByteRange>, ContiguousMemoryError>;
}

impl StorageDetails for ImplConcurrent {
    type Base = RwLock<*mut u8>;
    type AllocationTracker = Mutex<AllocationTracker>;
    type SizeType = AtomicUsize;
    type StoreResult<T> = Result<Self::ReferenceType<T>, LockingError>;

    fn build_state(
        base: *mut u8,
        capacity: usize,
        alignment: usize,
    ) -> Result<Self::StorageState, LayoutError> {
        let layout = Layout::from_size_align(capacity, alignment)?;

        Ok(Arc::new(ContiguousMemoryState {
            base: BaseLocation(RwLock::new(base)),
            capacity: AtomicUsize::new(layout.size()),
            alignment: layout.align(),
            tracker: Mutex::new(AllocationTracker::new(capacity)),
        }))
    }

    fn deref_state(state: &Self::StorageState) -> &ContiguousMemoryState<Self> {
        &state
    }

    fn get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        base.read_named(LockSource::BaseAddress)
            .map(|result| *result)
    }

    fn try_get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        base.try_read_named(LockSource::BaseAddress)
            .map(|result| *result)
    }

    fn get_capacity(capacity: &Self::SizeType) -> usize {
        capacity.load(Ordering::Acquire)
    }

    fn resize_container(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError> {
        let layout = Layout::from_size_align(Self::get_capacity(&state.capacity), state.alignment)?;
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

    fn deallocate(base: &Self::Base, layout: Layout) {
        if let Ok(mut lock) = base.write_named(LockSource::BaseAddress) {
            unsafe { allocator::dealloc(*lock, layout) };
            *lock = null_mut();
        }
    }

    fn resize_tracker(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        let mut lock = state.tracker.lock_named(LockSource::AllocationTracker)?;
        lock.resize(new_capacity)?;
        Ok(())
    }

    fn shrink_tracker(state: &mut Self::StorageState) -> Result<Option<usize>, LockingError> {
        let mut lock = state.tracker.lock_named(LockSource::AllocationTracker)?;
        Ok(lock.shrink_to_fit())
    }

    fn track_next(
        state: &mut Self::StorageState,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        let base = Self::get_base(&state.base)? as usize;
        let mut lock = state.tracker.lock_named(LockSource::AllocationTracker)?;
        lock.take_next(base, layout)
    }

    fn peek_next(
        state: &Self::StorageState,
        layout: Layout,
    ) -> Result<Option<ByteRange>, ContiguousMemoryError> {
        let lock = state.tracker.lock_named(LockSource::AllocationTracker)?;
        Ok(lock.peek_next(layout))
    }
}

impl StorageDetails for ImplDefault {
    type Base = Cell<*mut u8>;
    type AllocationTracker = RefCell<AllocationTracker>;
    type SizeType = Cell<usize>;
    type StoreResult<T> = ContiguousEntryRef<T>;

    fn build_state(
        base: *mut u8,
        capacity: usize,
        alignment: usize,
    ) -> Result<Self::StorageState, LayoutError> {
        let layout: Layout = Layout::from_size_align(capacity, alignment)?;

        Ok(Rc::new(ContiguousMemoryState {
            base: BaseLocation(Cell::new(base)),
            capacity: Cell::new(layout.size()),
            alignment: layout.align(),
            tracker: RefCell::new(AllocationTracker::new(capacity)),
        }))
    }

    fn deref_state(state: &Self::StorageState) -> &ContiguousMemoryState<Self> {
        &state
    }

    fn get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        base.get()
    }

    fn try_get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        Self::get_base(base)
    }

    fn get_capacity(capacity: &Self::SizeType) -> usize {
        capacity.get()
    }

    fn resize_container(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError> {
        let layout = Layout::from_size_align(Self::get_capacity(&state.capacity), state.alignment)?;
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

    fn deallocate(base: &Self::Base, layout: Layout) {
        unsafe { allocator::dealloc(base.get(), layout) };
        base.set(null_mut())
    }

    fn resize_tracker(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        state.tracker.borrow_mut().resize(new_capacity)
    }

    fn shrink_tracker(state: &mut Self::StorageState) -> Result<Option<usize>, LockingError> {
        Ok(state.tracker.borrow_mut().shrink_to_fit())
    }

    fn track_next(
        state: &mut Self::StorageState,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        let base = Self::get_base(&state.base) as usize;
        let mut tracker = state
            .tracker
            .try_borrow_mut()
            .map_err(|_| ContiguousMemoryError::TrackerInUse)?;
        tracker.take_next(base, layout)
    }

    fn peek_next(
        state: &Self::StorageState,
        layout: Layout,
    ) -> Result<Option<ByteRange>, ContiguousMemoryError> {
        let tracker = state
            .tracker
            .try_borrow()
            .map_err(|_| ContiguousMemoryError::TrackerInUse)?;
        Ok(tracker.peek_next(layout))
    }
}

impl StorageDetails for ImplUnsafe {
    type Base = *mut u8;
    type AllocationTracker = AllocationTracker;
    type SizeType = usize;
    type StoreResult<T> = Result<*mut T, ContiguousMemoryError>;

    fn build_state(
        base: *mut u8,
        capacity: usize,
        alignment: usize,
    ) -> Result<Self::StorageState, LayoutError> {
        let layout = Layout::from_size_align(capacity, alignment)?;
        Ok(ContiguousMemoryState {
            base: BaseLocation(base),
            capacity: layout.size(),
            alignment: layout.align(),
            tracker: AllocationTracker::new(capacity),
        })
    }

    fn deref_state(state: &Self::StorageState) -> &ContiguousMemoryState<Self> {
        &state
    }

    fn get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        *base
    }

    fn try_get_base(base: &Self::Base) -> Self::LockResult<*mut u8> {
        Self::get_base(base)
    }

    fn get_capacity(capacity: &Self::SizeType) -> usize {
        *capacity
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

    fn deallocate(base: &Self::Base, layout: Layout) {
        unsafe {
            allocator::dealloc(*base, layout);
        }
    }

    fn resize_tracker(
        state: &mut Self::StorageState,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        state.tracker.resize(new_capacity)
    }

    fn shrink_tracker(state: &mut Self::StorageState) -> Result<Option<usize>, LockingError> {
        Ok(state.tracker.shrink_to_fit())
    }

    fn track_next(
        state: &mut Self::StorageState,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        let base = Self::get_base(&state.base) as usize;
        state.tracker.take_next(base, layout)
    }

    fn peek_next(
        state: &Self::StorageState,
        layout: Layout,
    ) -> Result<Option<ByteRange>, ContiguousMemoryError> {
        Ok(state.tracker.peek_next(layout))
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
    fn free_region(state: &mut Self::StorageState, range: ByteRange) -> Option<*mut ()>;

    /// Builds a reference for the stored data.
    fn build_ref<T: StoreRequirements>(
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

    fn free_region(state: &mut Self::StorageState, range: ByteRange) -> Option<*mut ()> {
        if let Ok(mut lock) = state.tracker.lock_named(LockSource::AllocationTracker) {
            let _ = lock.release(range);

            if let Ok(base) = state.base.read_named(LockSource::BaseAddress) {
                unsafe { Some(base.add(range.0) as *mut ()) }
            } else {
                None
            }
        } else {
            None
        }
    }

    fn build_ref<T: StoreRequirements>(
        state: &Self::StorageState,
        _addr: *mut T,
        range: ByteRange,
    ) -> Self::ReferenceType<T> {
        SyncContiguousEntryRef {
            inner: Arc::new(ReferenceState {
                state: state.clone(),
                range: range.clone(),
                borrow_kind: RwLock::new(()),
                #[cfg(feature = "ptr_metadata")]
                drop_metadata: static_metadata::<T, dyn HandleDrop>(),
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

    fn free_region(state: &mut Self::StorageState, range: ByteRange) -> Option<*mut ()> {
        if let Ok(mut tracker) = state.tracker.try_borrow_mut() {
            let _ = tracker.release(range);

            let base = state.base.get();
            unsafe { Some(base.add(range.0) as *mut ()) }
        } else {
            None
        }
    }

    fn build_ref<T: StoreRequirements>(
        state: &Self::StorageState,
        _addr: *mut T,
        range: ByteRange,
    ) -> Self::ReferenceType<T> {
        ContiguousEntryRef {
            inner: Rc::new(ReferenceState {
                state: state.clone(),
                range: range.clone(),
                borrow_kind: Cell::new(BorrowState::Read(0)),
                #[cfg(feature = "ptr_metadata")]
                drop_metadata: static_metadata::<T, dyn HandleDrop>(),
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

    fn free_region(state: &mut Self::StorageState, range: ByteRange) -> Option<*mut ()> {
        let _ = state.tracker.release(range);

        unsafe { Some(state.base.add(range.0) as *mut ()) }
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
    unsafe fn push_raw<T: StoreRequirements>(
        state: &mut Self::StorageState,
        data: *mut T,
        layout: Layout,
    ) -> Self::StoreResult<T>;

    fn assume_stored<T: StoreRequirements>(
        state: &Self::StorageState,
        position: usize,
    ) -> Self::LockResult<Self::ReferenceType<T>>;
}

impl StoreDataDetails for ImplConcurrent {
    unsafe fn push_raw<T: StoreRequirements>(
        state: &mut Self::StorageState,
        data: *mut T,
        layout: Layout,
    ) -> Result<SyncContiguousEntryRef<T>, LockingError> {
        let (addr, range) = loop {
            match ImplConcurrent::track_next(state, layout) {
                Ok(taken) => {
                    let found = (taken.0
                        + ImplConcurrent::get_base(&ImplConcurrent::deref_state(state).base)?
                            as usize) as *mut u8;
                    unsafe { core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size()) }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    match ImplConcurrent::resize_container(state, ImplConcurrent::get_capacity(&ImplConcurrent::deref_state(state).capacity) * 2) {
                        Ok(_) => {}
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

    fn assume_stored<T: StoreRequirements>(
        state: &Self::StorageState,
        position: usize,
    ) -> Result<SyncContiguousEntryRef<T>, LockingError> {
        let addr = unsafe {
            ImplConcurrent::get_base(&ImplConcurrent::deref_state(state).base)?.add(position)
        };
        Ok(ImplConcurrent::build_ref(
            state,
            addr as *mut T,
            ByteRange(position, size_of::<T>()),
        ))
    }
}

impl StoreDataDetails for ImplDefault {
    unsafe fn push_raw<T: StoreRequirements>(
        state: &mut Self::StorageState,
        data: *mut T,
        layout: Layout,
    ) -> ContiguousEntryRef<T> {
        let (addr, range) = loop {
            match ImplDefault::track_next(state, layout) {
                Ok(taken) => {
                    let found = (taken.0
                        + ImplDefault::get_base(&ImplDefault::deref_state(state).base) as usize)
                        as *mut u8;
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break (found, taken);
                }
                Err(ContiguousMemoryError::NoStorageLeft) => {
                    match ImplDefault::resize_container(state, ImplDefault::get_capacity(&ImplDefault::deref_state(state).capacity) * 2) {
                        Ok(_) => {},
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

    fn assume_stored<T: StoreRequirements>(
        state: &Self::StorageState,
        position: usize,
    ) -> ContiguousEntryRef<T> {
        let addr =
            unsafe { ImplDefault::get_base(&ImplDefault::deref_state(state).base).add(position) };
        ImplDefault::build_ref(state, addr as *mut T, ByteRange(position, size_of::<T>()))
    }
}

impl StoreDataDetails for ImplUnsafe {
    /// Returns a raw pointer (`*mut T`) to the stored value or
    unsafe fn push_raw<T: StoreRequirements>(
        state: &mut Self::StorageState,
        data: *mut T,
        layout: Layout,
    ) -> Result<*mut T, ContiguousMemoryError> {
        let (addr, range) = loop {
            match ImplUnsafe::track_next(state, layout) {
                Ok(taken) => {
                    let found = (taken.0
                        + ImplUnsafe::get_base(&ImplUnsafe::deref_state(state).base) as usize)
                        as *mut u8;
                    unsafe {
                        core::ptr::copy_nonoverlapping(data as *mut u8, found, layout.size());
                    }
                    break (found, taken);
                }
                Err(other) => return Err(other),
            }
        };

        Ok(ImplUnsafe::build_ref(state, addr as *mut T, range))
    }

    fn assume_stored<T: StoreRequirements>(state: &Self::StorageState, position: usize) -> *mut T {
        let addr =
            unsafe { ImplUnsafe::get_base(&ImplUnsafe::deref_state(state).base).add(position) };
        ImplUnsafe::build_ref(
            state,
            addr as *mut T,
            ByteRange(position, position + size_of::<T>()),
        )
    }
}

/// Trait representing requirements for implementation details of the
/// [`ContiguousMemoryStorage`](ContiguousMemoryStorage).
///
/// This trait is implemented by:
/// - [`ImplDefault`]
/// - [`ImplConcurrent`]
/// - [`ImplUnsafe`]
///
/// As none of the underlying traits can't be implemented, changes to this trait
/// aren't considered breaking and won't affect semver.
pub trait ImplDetails: ImplBase + StorageDetails + ReferenceDetails + StoreDataDetails {}
impl<Impl: ImplBase + StorageDetails + ReferenceDetails + StoreDataDetails> ImplDetails for Impl {}
