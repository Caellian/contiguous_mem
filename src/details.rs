//! Implementation details for behavior specialization marker structs.

use core::{
    alloc::{Layout, LayoutError},
    cell::{Cell, RefCell},
    ptr::null_mut,
};

use core::marker::PhantomData;

use portable_atomic::AtomicUsize;

use crate::{
    error::{ContiguousMemoryError, LockingError, MutexKind},
    range::ByteRange,
    refs::{ContiguousMemoryRef, ReferenceState, SyncContiguousMemoryRef},
    tracker::AllocationTracker,
    types::*,
    ContiguousMemoryState,
};

#[allow(unused_imports)]
use crate::ContiguousMemoryStorage;

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

    /// The type representing result of storing data.
    type StoreResult<T>;

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
    fn resize_container(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError>;

    /// Deallocates the base memory using layout information.
    fn deallocate(base: &Self::Base, layout: Layout);

    /// Resizes the allocation tracker to the new capacity.
    fn resize_tracker(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError>;

    /// Shrinks tracked area of the allocation tracker to smallest that can fit
    /// currently stored data.
    fn shrink_tracker(state: &mut Self::State) -> Result<Option<usize>, LockingError>;

    /// Finds the next free memory region for given layout in the tracker.
    fn next_free(
        state: &mut Self::State,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError>;
}

/// A marker struct representing the behavior specialization for thread-safe
/// operations within [`ContiguousMemory`]. This
/// implementation ensures that the container's operations can be used safely in
/// asynchronous contexts, utilizing mutexes to prevent data races.
pub struct ImplConcurrent;
impl MemoryImpl for ImplConcurrent {
    type State = Arc<ContiguousMemoryState<Self>>;
    type Base = Mutex<*mut u8>;
    type AllocationTracker = Mutex<AllocationTracker>;
    type SizeType = AtomicUsize;
    type StoreResult<T> = Result<SyncContiguousMemoryRef<T>, LockingError>;
    type LockResult<T> = Result<T, LockingError>;

    const USE_LOCKS: bool = true;

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

    fn deref_state(state: &Self::State) -> &ContiguousMemoryState<Self> {
        &state
    }

    fn get_base(state: &Self::State) -> Self::LockResult<*mut u8> {
        state
            .base
            .lock_named(MutexKind::BaseAddress)
            .map(|result| *result)
    }

    fn get_capacity(base: &Self::State) -> usize {
        base.size.load(portable_atomic::Ordering::AcqRel)
    }

    fn resize_container(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError> {
        let layout = Layout::from_size_align(Self::get_capacity(state), state.alignment)?;
        let mut base_addr = state.base.lock_named(MutexKind::BaseAddress)?;
        let prev_addr = *base_addr;
        *base_addr = unsafe { allocator::realloc(*base_addr, layout, new_capacity) };
        state
            .size
            .store(new_capacity, portable_atomic::Ordering::AcqRel);
        Ok(if *base_addr != prev_addr {
            Some(*base_addr)
        } else {
            None
        })
    }

    fn deallocate(base: &Self::Base, layout: Layout) {
        if let Ok(mut lock) = base.lock_named(MutexKind::BaseAddress) {
            unsafe { allocator::dealloc(*lock, layout) };
            *lock = null_mut();
        }
    }

    fn resize_tracker(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        let mut lock = state.tracker.lock_named(MutexKind::AllocationTracker)?;
        lock.resize(new_capacity)?;
        Ok(())
    }

    fn shrink_tracker(state: &mut Self::State) -> Result<Option<usize>, LockingError> {
        let mut lock = state.tracker.lock_named(MutexKind::AllocationTracker)?;
        Ok(lock.shrink_to_fit())
    }

    fn next_free(
        state: &mut Self::State,
        layout: Layout,
    ) -> Result<ByteRange, ContiguousMemoryError> {
        let mut lock = state.tracker.lock_named(MutexKind::AllocationTracker)?;
        lock.take_next(layout)
    }
}

/// A marker struct representing the behavior specialization for operations
/// within [`ContiguousMemory`] that do not require
/// thread-safety. This implementation skips mutexes, making it faster but
/// unsuitable for concurrent usage.
pub struct ImplDefault;
impl MemoryImpl for ImplDefault {
    type State = Rc<ContiguousMemoryState<Self>>;
    type Base = Cell<*mut u8>;
    type AllocationTracker = RefCell<AllocationTracker>;
    type SizeType = Cell<usize>;
    type StoreResult<T> = ContiguousMemoryRef<T>;
    type LockResult<T> = T;

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

    fn deref_state(state: &Self::State) -> &ContiguousMemoryState<Self> {
        &state
    }

    fn get_base(state: &Self::State) -> Self::LockResult<*mut u8> {
        state.base.get()
    }

    fn get_capacity(base: &Self::State) -> usize {
        base.size.get()
    }

    fn resize_container(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError> {
        let layout = Layout::from_size_align(state.size.get(), state.alignment)?;
        let prev_base = state.base.get();
        let new_base = unsafe { allocator::realloc(prev_base, layout, new_capacity) };
        state.base.set(new_base);
        state.size.set(new_capacity);
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
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        state.tracker.borrow_mut().resize(new_capacity)
    }

    fn shrink_tracker(state: &mut Self::State) -> Result<Option<usize>, LockingError> {
        Ok(state.tracker.borrow_mut().shrink_to_fit())
    }

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

/// A marker struct representing the behavior specialization for unsafe
/// implementation. Should be used when the container is guaranteed to outlive
/// any pointers to data contained in represented memory block.
pub struct ImplUnsafe;
impl MemoryImpl for ImplUnsafe {
    type State = ContiguousMemoryState<Self>;
    type Base = *mut u8;
    type AllocationTracker = AllocationTracker;
    type SizeType = usize;
    type StoreResult<T> = Result<*mut T, ContiguousMemoryError>;
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

    fn deref_state(state: &Self::State) -> &ContiguousMemoryState<Self> {
        &state
    }

    fn get_base(state: &Self::State) -> Self::LockResult<*mut u8> {
        state.base
    }

    fn get_capacity(base: &Self::State) -> usize {
        base.size
    }

    fn resize_container(
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<Option<*mut u8>, ContiguousMemoryError> {
        let layout = Layout::from_size_align(state.size, state.alignment)?;
        let prev_base = state.base;
        state.base = unsafe { allocator::realloc(state.base, layout, new_capacity) };
        state.size = new_capacity;
        Ok(if state.base != prev_base {
            Some(state.base)
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
        state: &mut Self::State,
        new_capacity: usize,
    ) -> Result<(), ContiguousMemoryError> {
        state.tracker.resize(new_capacity)
    }

    fn shrink_tracker(state: &mut Self::State) -> Result<Option<usize>, LockingError> {
        Ok(state.tracker.shrink_to_fit())
    }

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

    /// Releases the specified memory region back to the allocation tracker.
    fn free_region(state: &mut Self::MemoryState, range: ByteRange) -> Option<*mut ()>;

    /// Builds a reference for the stored data.
    fn build_ref<T: StoreRequirements>(
        state: &Self::MemoryState,
        addr: *mut T,
        range: &ByteRange,
    ) -> Self::Type<T>;

    /// Marks reference state as no longer being borrowed.
    fn unborrow_ref<T: ?Sized>(_state: &Self::RefState<T>) {}

    unsafe fn cast<T, R>(from: Self::Type<T>) -> Self::Type<R>;
}

impl ReferenceImpl for ImplConcurrent {
    type MemoryState = <ImplConcurrent as MemoryImpl>::State;
    type RefState<T: ?Sized> = Arc<ReferenceState<T, Self>>;
    type RefMutLock = Mutex<()>;
    type RefMutGuard<'a> = MutexGuard<'a, ()>;
    type Type<T> = SyncContiguousMemoryRef<T>;

    fn free_region(state: &mut <Self as MemoryImpl>::State, range: ByteRange) -> Option<*mut ()> {
        if let Ok(mut lock) = state.tracker.lock_named(MutexKind::AllocationTracker) {
            let _ = lock.release(range);

            if let Ok(base) = state.base.lock_named(MutexKind::BaseAddress) {
                unsafe { Some(base.add(range.0) as *mut ()) }
            } else {
                None
            }
        } else {
            None
        }
    }

    fn build_ref<T: StoreRequirements>(
        state: &<Self as MemoryImpl>::State,
        _addr: *mut T,
        range: &ByteRange,
    ) -> Self::Type<T> {
        SyncContiguousMemoryRef {
            inner: Arc::new(ReferenceState {
                state: state.clone(),
                range: range.clone(),
                already_borrowed: Mutex::new(()),
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

    unsafe fn cast<T, R>(from: Self::Type<T>) -> Self::Type<R> {
        SyncContiguousMemoryRef {
            inner: core::mem::transmute(from.inner),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

impl ReferenceImpl for ImplDefault {
    type MemoryState = <ImplDefault as MemoryImpl>::State;
    type RefState<T: ?Sized> = Rc<ReferenceState<T, Self>>;
    type RefMutGuard<'a> = ();
    type RefMutLock = Cell<bool>;
    type Type<T> = ContiguousMemoryRef<T>;

    fn free_region(state: &mut <Self as MemoryImpl>::State, range: ByteRange) -> Option<*mut ()> {
        if let Ok(mut tracker) = state.tracker.try_borrow_mut() {
            let _ = tracker.release(range);

            let base = state.base.get();
            unsafe { Some(base.add(range.0) as *mut ()) }
        } else {
            None
        }
    }

    fn build_ref<T: StoreRequirements>(
        state: &<Self as MemoryImpl>::State,
        _addr: *mut T,
        range: &ByteRange,
    ) -> Self::Type<T> {
        ContiguousMemoryRef {
            inner: Rc::new(ReferenceState {
                state: state.clone(),
                range: range.clone(),
                already_borrowed: Cell::new(false),
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

    fn unborrow_ref<T: ?Sized>(state: &Self::RefState<T>) {
        state.already_borrowed.set(false)
    }

    unsafe fn cast<T, R>(from: Self::Type<T>) -> Self::Type<R> {
        ContiguousMemoryRef {
            inner: core::mem::transmute(from.inner),
            #[cfg(feature = "ptr_metadata")]
            metadata: (),
            #[cfg(not(feature = "ptr_metadata"))]
            _phantom: PhantomData,
        }
    }
}

impl ReferenceImpl for ImplUnsafe {
    type MemoryState = <ImplUnsafe as MemoryImpl>::State;
    type RefState<T: ?Sized> = ();
    type RefMutLock = ();
    type RefMutGuard<'a> = ();
    type Type<T> = *mut T;

    fn free_region(state: &mut <Self as MemoryImpl>::State, range: ByteRange) -> Option<*mut ()> {
        let _ = state.tracker.release(range);

        unsafe { Some(state.base.add(range.0) as *mut ()) }
    }

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
