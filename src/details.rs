//! Implementation details for behavior specialization marker structs.

use core::{
    alloc::{Layout, LayoutError},
    cell::{Cell, RefCell},
    marker::PhantomData,
    ptr::null_mut,
};

use portable_atomic::AtomicUsize;

use crate::{
    error::{ContiguousMemoryError, LockingError, MutexKind},
    range::ByteRange,
    tracker::AllocationTracker,
    types::*,
    ContiguousMemoryRef, ContiguousMemoryState, ReferenceState, SyncContiguousMemoryRef,
};

/// Implementation details of [`ContiguousMemory`].
pub trait MemoryImpl: Sized {
    /// The type representing reference to internal state
    type State: Clone;

    /// The type representing the base memory and allocation tracking.
    type Base;

    /// The type representing the allocation tracking mechanism.
    type AllocationTracker;

    /// The type representing [`Layout`] entries with inner mutability.
    type SizeType;

    /// The type representing result of accessing data that is locked in async
    /// context
    type LockResult<T>;

    /// Indicates whether locks are used for synchronization.
    const USE_LOCKS: bool = false;

    /// Builds a new internal state from provided parameters
    fn build_state(
        base: *mut u8,
        capacity: usize,
        align: usize,
    ) -> Result<Self::State, LayoutError>;

    fn deref_state(state: &Self::State) -> &ContiguousMemoryState<Self>;

    /// Retrieves the base pointer from the base instance.
    fn get_base(state: &Self::State) -> Self::LockResult<*mut u8>;

    /// Retrieves the capacity from the state.
    fn get_capacity(base: &Self::State) -> usize;

    /// Resizes and reallocates the base memory according to new capacity.
    fn resize(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<*mut u8, ContiguousMemoryError>;

    /// Deallocates the base memory using layout information.
    fn deallocate(base: &Self::Base, layout: Layout);

    /// Resizes the allocation tracker to the new capacity.
    fn resize_tracker(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError>;

    /// Finds the next free memory region for given layout in the tracker.
    fn next_free(
        state: &mut Self::State,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError>;
}

/// A marker struct representing the behavior specialization for thread-safe
/// operations within [`ContiguousMemory`](crate::ContiguousMemory). This
/// implementation ensures that the container's operations can be used safely in
/// asynchronous contexts, utilizing mutexes to prevent data races.
pub struct ImplConcurrent;
impl MemoryImpl for ImplConcurrent {
    type State = Arc<ContiguousMemoryState<Self>>;
    type Base = Mutex<*mut u8>;
    type AllocationTracker = Mutex<AllocationTracker>;
    type SizeType = AtomicUsize;
    type LockResult<T> = Result<T, LockingError>;

    const USE_LOCKS: bool = true;

    #[inline(always)]
    fn build_state(
        base: *mut u8,
        capacity: usize,
        align: usize,
    ) -> Result<Self::State, LayoutError> {
        let layout = Layout::from_size_align(capacity, align)?;

        Ok(Arc::new(ContiguousMemoryState {
            base: Mutex::new(base),
            size: AtomicUsize::new(layout.size()),
            alignment: layout.align(),
            tracker: Mutex::new(AllocationTracker::new(capacity)),
        }))
    }

    #[inline(always)]
    fn deref_state(state: &Self::State) -> &ContiguousMemoryState<Self> {
        &state
    }

    #[inline(always)]
    fn get_base(state: &Self::State) -> Self::LockResult<*mut u8> {
        state
            .base
            .lock_named(MutexKind::BaseAddress)
            .map(|result| *result)
    }

    #[inline(always)]
    fn get_capacity(base: &Self::State) -> usize {
        base.size.load(portable_atomic::Ordering::AcqRel)
    }

    #[inline(always)]
    fn resize(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<*mut u8, ContiguousMemoryError> {
        let layout = Layout::from_size_align(Self::get_capacity(state), state.alignment)?;
        let mut lock = state.base.lock_named(MutexKind::BaseAddress)?;
        *lock = unsafe { alloc::realloc(*lock, layout, new_capacity) };
        state
            .size
            .store(new_capacity, portable_atomic::Ordering::AcqRel);
        Ok(*lock)
    }

    #[inline(always)]
    fn deallocate(base: &Self::Base, layout: Layout) {
        if let Ok(mut lock) = base.lock_named(MutexKind::BaseAddress) {
            unsafe { alloc::dealloc(*lock, layout) };
            *lock = null_mut();
        }
    }

    #[inline(always)]
    fn resize_tracker(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        let mut lock = state.tracker.lock_named(MutexKind::AllocationTracker)?;
        lock.resize(new_capacity)?;
        Ok(())
    }

    #[inline(always)]
    fn next_free(
        state: &mut Self::State,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        let mut lock = state.tracker.lock_named(MutexKind::AllocationTracker)?;
        lock.take_next(layout)
    }
}

/// A marker struct representing the behavior specialization for operations
/// within [`ContiguousMemory`](crate::ContiguousMemory) that do not require
/// thread-safety. This implementation skips mutexes, making it faster but
/// unsuitable for concurrent usage.
pub struct ImplDefault;
impl MemoryImpl for ImplDefault {
    type State = Rc<ContiguousMemoryState<Self>>;
    type Base = Cell<*mut u8>;
    type AllocationTracker = RefCell<AllocationTracker>;
    type SizeType = Cell<usize>;
    type LockResult<T> = T;

    #[inline(always)]
    fn build_state(
        base: *mut u8,
        capacity: usize,
        align: usize,
    ) -> Result<Self::State, LayoutError> {
        let layout: Layout = Layout::from_size_align(capacity, align)?;

        Ok(Rc::new(ContiguousMemoryState {
            base: Cell::new(base),
            size: Cell::new(layout.size()),
            alignment: layout.align(),
            tracker: RefCell::new(AllocationTracker::new(capacity)),
        }))
    }

    #[inline(always)]
    fn deref_state(state: &Self::State) -> &ContiguousMemoryState<Self> {
        &state
    }

    #[inline(always)]
    fn get_base(state: &Self::State) -> Self::LockResult<*mut u8> {
        state.base.get()
    }

    #[inline(always)]
    fn get_capacity(base: &Self::State) -> usize {
        base.size.get()
    }

    #[inline(always)]
    fn resize(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<*mut u8, ContiguousMemoryError> {
        let layout = Layout::from_size_align(state.size.get(), state.alignment)?;
        let value = unsafe { alloc::realloc(state.base.get(), layout, new_capacity) };
        state.base.set(value);
        state.size.set(new_capacity);
        Ok(value)
    }

    #[inline(always)]
    fn deallocate(base: &Self::Base, layout: Layout) {
        unsafe { alloc::dealloc(base.get(), layout) };
        base.set(null_mut())
    }

    #[inline(always)]
    fn resize_tracker(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        state.tracker.borrow_mut().resize(new_capacity)
    }

    #[inline(always)]
    fn next_free(
        state: &mut Self::State,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        state
            .tracker
            .try_borrow_mut()
            .map_err(|_| ContiguousMemoryError::TrackerInUse)?
            .take_next(layout)
    }
}

/// A marker struct representing the behavior specialization for a highly
/// performance-optimized, yet unsafe implementation within
/// [`ContiguousMemory`](crate::ContiguousMemory). This trait is used when the
/// exact required size is known during construction, and when the container is
/// guaranteed to outlive any pointers to data contained in the memory block.
pub struct ImplFixed;
impl MemoryImpl for ImplFixed {
    type State = ContiguousMemoryState<Self>;
    type Base = *mut u8;
    type AllocationTracker = AllocationTracker;
    type SizeType = usize;
    type LockResult<T> = T;

    fn build_state(
        base: *mut u8,
        capacity: usize,
        align: usize,
    ) -> Result<Self::State, LayoutError> {
        let layout = Layout::from_size_align(capacity, align)?;
        Ok(ContiguousMemoryState {
            base,
            size: layout.size(),
            alignment: layout.align(),
            tracker: AllocationTracker::new(capacity),
        })
    }

    #[inline(always)]
    fn deref_state(state: &Self::State) -> &ContiguousMemoryState<Self> {
        &state
    }

    #[inline(always)]
    fn get_base(state: &Self::State) -> Self::LockResult<*mut u8> {
        state.base
    }

    #[inline(always)]
    fn get_capacity(base: &Self::State) -> usize {
        base.size
    }

    #[inline(always)]
    fn resize(
        _state: &mut Self::State,
        _new_capacity: usize,
    ) -> Result<*mut u8, ContiguousMemoryError> {
        unimplemented!("can't reallocate ContiguousMemory with FixedSizeImpl");
    }

    #[inline(always)]
    fn deallocate(base: &Self::Base, layout: Layout) {
        unsafe {
            alloc::dealloc(*base, layout);
        }
    }

    #[inline(always)]
    fn resize_tracker(
        _state: &mut Self::State,
        _new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        Err(ContiguousMemoryError::NoStorageLeft)
    }

    #[inline(always)]
    fn next_free(
        state: &mut Self::State,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        state.tracker.take_next(layout)
    }
}

/// Implementation details of [`ContiguousMemory`] references.
pub trait ReferenceImpl: Sized {
    /// The type representing [`ContiguousMemory`] state of this reference.
    type MemoryState: Clone;

    /// The type representing internal state of the reference.
    type RefState<T: ?Sized>: Clone;

    /// The type handling mutable access exclusion.
    type RefMutLock;

    /// Type of the concurrent mutable access exclusions flag.
    type RefMutGuard<'a>;

    type Type<T>: Clone;

    /// Releases the specified memory range back to the allocation tracker.
    fn release_reference(
        state: &mut Self::MemoryState,
        range: ByteRange,
    ) -> Result<(), ContiguousMemoryError>;

    /// Builds a reference for the stored data.
    fn build_ref<T>(state: &Self::MemoryState, addr: *mut T, range: &ByteRange) -> Self::Type<T>;

    /// Marks reference state as no longer being borrowed.
    fn unborrow_ref<T: ?Sized>(_state: &Self::RefState<T>) {}

    unsafe fn cast<T, R>(from: Self::Type<T>) -> Self::Type<R>;
}

impl ReferenceImpl for ImplConcurrent {
    type MemoryState = <ImplConcurrent as MemoryImpl>::State;
    type RefState<T: ?Sized> = Arc<ReferenceState<Self>>;
    type RefMutLock = Mutex<()>;
    type RefMutGuard<'a> = MutexGuard<'a, ()>;
    type Type<T> = SyncContiguousMemoryRef<T>;

    #[inline(always)]
    fn release_reference(
        state: &mut <Self as MemoryImpl>::State,
        range: ByteRange,
    ) -> Result<(), ContiguousMemoryError> {
        let mut lock = state.tracker.lock_named(MutexKind::AllocationTracker)?;
        lock.release(range)
    }

    #[inline(always)]
    fn build_ref<T>(
        state: &<Self as MemoryImpl>::State,
        _addr: *mut T,
        range: &ByteRange,
    ) -> Self::Type<T> {
        SyncContiguousMemoryRef {
            inner: Arc::new(ReferenceState {
                state: state.clone(),
                range: range.clone(),
                mutable_access: Mutex::new(()),
            }),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }

    unsafe fn cast<T, R>(from: Self::Type<T>) -> Self::Type<R> {
        SyncContiguousMemoryRef {
            inner: from.inner,
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

impl ReferenceImpl for ImplDefault {
    type MemoryState = <ImplDefault as MemoryImpl>::State;
    type RefState<T: ?Sized> = Rc<ReferenceState<Self>>;
    type RefMutGuard<'a> = ();
    type RefMutLock = Cell<bool>;
    type Type<T> = ContiguousMemoryRef<T>;

    #[inline(always)]
    fn release_reference(
        state: &mut <Self as MemoryImpl>::State,
        range: ByteRange,
    ) -> Result<(), ContiguousMemoryError> {
        state
            .tracker
            .try_borrow_mut()
            .map_err(|_| ContiguousMemoryError::TrackerInUse)?
            .release(range)
    }

    #[inline(always)]
    fn build_ref<T>(
        state: &<Self as MemoryImpl>::State,
        _addr: *mut T,
        range: &ByteRange,
    ) -> Self::Type<T> {
        ContiguousMemoryRef {
            inner: Rc::new(ReferenceState {
                state: state.clone(),
                range: range.clone(),
                mutable_access: Cell::new(false),
            }),
            metadata: None,
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }

    fn unborrow_ref<T: ?Sized>(state: &Self::RefState<T>) {
        state.mutable_access.set(false)
    }

    unsafe fn cast<T, R>(from: Self::Type<T>) -> Self::Type<R> {
        ContiguousMemoryRef {
            inner: from.inner,
            metadata: None,
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

impl ReferenceImpl for ImplFixed {
    type MemoryState = <ImplFixed as MemoryImpl>::State;
    type RefState<T: ?Sized> = ();
    type RefMutLock = ();
    type RefMutGuard<'a> = ();
    type Type<T> = *mut T;

    #[inline(always)]
    fn release_reference(
        state: &mut <Self as MemoryImpl>::State,
        range: ByteRange,
    ) -> Result<(), ContiguousMemoryError> {
        state.tracker.release(range)
    }

    #[inline(always)]
    fn build_ref<T>(
        _base: &<Self as MemoryImpl>::State,
        addr: *mut T,
        _range: &ByteRange,
    ) -> Self::Type<T> {
        addr
    }

    unsafe fn cast<T, R>(from: Self::Type<T>) -> Self::Type<R> {
        from as *mut R
    }
}

pub trait ImplDetails: MemoryImpl + ReferenceImpl {}
impl<T: MemoryImpl + ReferenceImpl> ImplDetails for T {}
