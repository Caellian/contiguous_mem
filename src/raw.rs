use core::{
    cell::{Cell, RefCell},
    ptr::NonNull,
};

use crate::{error::MemoryError, tracker::AllocationTracker};

use super::*;

#[cfg(all(feature = "no_std"))]
pub use alloc::alloc;
#[cfg(all(not(feature = "no_std")))]
use std::alloc;

#[cfg(feature = "allocator_api")]
use alloc::Allocator;

/// Pointer to allocated slice of memory.
pub type BasePtr = NonNull<[u8]>;
/// Optional [`BasePtr`] value.
///
/// `None` for zero-sized contiguous memory, `Some` otherwise.
pub type BaseAddress = Option<BasePtr>;

pub(crate) const unsafe fn null_base(align: usize) -> BasePtr {
    NonNull::new_unchecked(std::mem::transmute((align as *mut u8, 0usize)))
}

/// Memory manager controls allocation and deallocation of underlying memory
/// used by the container.
///
/// It also manages shrinking/growing of the container.
///
/// [`Layout`] arguments can have the size 0 and that _shouldn't_ cause a panic,
/// implementations of the trait must ensure to return `None` as [`BaseAddress`]
/// appropriately in those cases.
///
/// Default implementation is [`DefaultMemoryManager`].
///
/// If `allocator_api` feature is enabled, this trait is implemented for all
/// [allocators](alloc::Allocator).
pub trait ManageMemory {
    /// Allocates a block of memory with size and alignment specified by
    /// `layout` argument.
    fn allocate(&self, layout: Layout) -> Result<BaseAddress, MemoryError>;

    /// Deallocates a block of memory of provided `layout` at the specified
    /// `address`.
    unsafe fn deallocate(&self, address: BaseAddress, layout: Layout);

    /// Shrinks the container underlying memory from `old_layout` size to
    /// `new_layout`.
    ///
    /// Generally doesn't cause a move, but an implementation can choose to do
    /// so.
    unsafe fn shrink(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError>;

    /// Grows the container underlying memory from `old_layout` size to
    /// `new_layout`.
    unsafe fn grow(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError>;
}

/// Default [memory manager](ManageMemory) that uses the methods exposed by
/// [`alloc`] module.
#[derive(Clone, Copy)]
pub struct DefaultMemoryManager;
impl ManageMemory for DefaultMemoryManager {
    fn allocate(&self, layout: Layout) -> Result<BaseAddress, MemoryError> {
        if layout.size() == 0 {
            Ok(None)
        } else {
            unsafe {
                Ok(Some(NonNull::from(core::slice::from_raw_parts(
                    alloc::alloc(layout),
                    layout.size(),
                ))))
            }
        }
    }

    unsafe fn deallocate(&self, address: BaseAddress, layout: Layout) {
        match address {
            Some(it) => alloc::dealloc(it.as_ptr() as *mut u8, layout),
            None => {}
        }
    }

    unsafe fn shrink(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError> {
        match address {
            Some(it) => Ok(if new_layout.size() > 0 {
                Some(NonNull::from(core::slice::from_raw_parts(
                    alloc::realloc(it.as_ptr() as *mut u8, old_layout, new_layout.size()),
                    new_layout.size(),
                )))
            } else {
                alloc::dealloc(it.as_ptr() as *mut u8, old_layout);
                None
            }),
            None => Ok(None),
        }
    }

    unsafe fn grow(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError> {
        match address {
            Some(it) => Ok(Some(NonNull::from(core::slice::from_raw_parts(
                alloc::realloc(it.as_ptr() as *mut u8, old_layout, new_layout.size()),
                new_layout.size(),
            )))),
            None => Ok({
                if new_layout.size() == 0 {
                    None
                } else {
                    Some(NonNull::from(core::slice::from_raw_parts(
                        alloc::alloc(new_layout),
                        new_layout.size(),
                    )))
                }
            }),
        }
    }
}

#[cfg(feature = "allocator_api")]
impl<A: Allocator> ManageMemory for A {
    fn allocate(&self, layout: Layout) -> Result<BaseAddress, MemoryError> {
        if layout.size() == 0 {
            Ok(None)
        } else {
            Allocator::allocate(self, layout)
                .map(|it| Some(it))
                .map_err(MemoryError::from)
        }
    }

    unsafe fn deallocate(&self, address: BaseAddress, layout: Layout) {
        match address {
            Some(it) => {
                Allocator::deallocate(self, NonNull::new_unchecked(it.as_ptr() as *mut u8), layout)
            }
            None => {}
        }
    }

    unsafe fn shrink(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError> {
        match address {
            Some(it) => {
                if new_layout.size() > 0 {
                    Allocator::shrink(
                        self,
                        NonNull::new_unchecked(it.as_ptr() as *mut u8),
                        old_layout,
                        new_layout,
                    )
                    .map(|it| Some(it))
                    .map_err(MemoryError::from)
                } else {
                    Allocator::deallocate(
                        self,
                        NonNull::new_unchecked(it.as_ptr() as *mut u8),
                        old_layout,
                    );
                    Ok(None)
                }
            }
            None => Ok(None),
        }
    }

    unsafe fn grow(
        &self,
        address: BaseAddress,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<BaseAddress, MemoryError> {
        match address {
            Some(it) => Allocator::grow(
                self,
                NonNull::new_unchecked(it.as_ptr() as *mut u8),
                old_layout,
                new_layout,
            )
            .map(|it| Some(it))
            .map_err(MemoryError::from),
            None => {
                if new_layout.size() == 0 {
                    Ok(None)
                } else {
                    Allocator::allocate(self, new_layout)
                        .map(|it| Some(it))
                        .map_err(MemoryError::from)
                }
            }
        }
    }
}

pub struct MemoryState<Impl: StorageDetails<A>, A: ManageMemory> {
    pub base: BaseLocation<Impl, A>,
    pub capacity: Impl::SizeType,
    pub alignment: usize,
    pub tracker: Impl::AllocationTracker,
    pub alloc: A,
}

impl<Impl: StorageDetails<A>, A: ManageMemory> MemoryState<Impl, A> {
    /// Returns the layout of the managed memory.
    pub fn layout(&self) -> Layout {
        unsafe {
            let capacity = Impl::get_capacity(core::mem::transmute(self));
            Layout::from_size_align_unchecked(capacity, self.alignment)
        }
    }
}

impl MemoryState<ImplDefault, DefaultMemoryManager> {
    pub fn new(layout: Layout) -> Result<Rc<Self>, MemoryError> {
        let base = DefaultMemoryManager.allocate(layout)?;
        Ok(Rc::new(MemoryState {
            base: BaseLocation(Cell::new(base)),
            capacity: Cell::new(layout.size()),
            alignment: layout.align(),
            tracker: RefCell::new(AllocationTracker::new(layout.size())),
            alloc: DefaultMemoryManager,
        }))
    }
}

impl<A: ManageMemory> MemoryState<ImplDefault, A> {
    pub fn new_with_alloc(layout: Layout, alloc: A) -> Result<Rc<Self>, MemoryError> {
        let base = alloc.allocate(layout)?;
        Ok(Rc::new(MemoryState {
            base: BaseLocation(Cell::new(base)),
            capacity: Cell::new(layout.size()),
            alignment: layout.align(),
            tracker: RefCell::new(AllocationTracker::new(layout.size())),
            alloc,
        }))
    }
}

#[cfg(feature = "sync_impl")]
impl MemoryState<ImplConcurrent, DefaultMemoryManager> {
    pub fn new_sync(layout: Layout) -> Result<Arc<Self>, MemoryError> {
        let base = DefaultMemoryManager.allocate(layout)?;
        Ok(Arc::new(MemoryState {
            base: BaseLocation(RwLock::new(base)),
            capacity: AtomicUsize::new(layout.size()),
            alignment: layout.align(),
            tracker: Mutex::new(AllocationTracker::new(layout.size())),
            alloc: DefaultMemoryManager,
        }))
    }
}

impl<A: ManageMemory> MemoryState<ImplConcurrent, A> {
    pub fn new_sync_with_alloc(layout: Layout, alloc: A) -> Result<Arc<Self>, MemoryError> {
        let base = alloc.allocate(layout)?;
        Ok(Arc::new(MemoryState {
            base: BaseLocation(RwLock::new(base)),
            capacity: AtomicUsize::new(layout.size()),
            alignment: layout.align(),
            tracker: Mutex::new(AllocationTracker::new(layout.size())),
            alloc,
        }))
    }
}

#[cfg(feature = "unsafe_impl")]
impl MemoryState<ImplUnsafe, DefaultMemoryManager> {
    pub fn new_unsafe(layout: Layout) -> Result<Self, MemoryError> {
        let base = DefaultMemoryManager.allocate(layout)?;
        Ok(MemoryState {
            base: BaseLocation(base),
            capacity: layout.size(),
            alignment: layout.align(),
            tracker: AllocationTracker::new(layout.size()),
            alloc: DefaultMemoryManager,
        })
    }
}

#[cfg(feature = "unsafe_impl")]
impl<A: ManageMemory> MemoryState<ImplUnsafe, A> {
    pub fn new_unsafe_with_alloc(layout: Layout, alloc: A) -> Result<Self, MemoryError> {
        let base = alloc.allocate(layout)?;
        Ok(MemoryState {
            base: BaseLocation(base),
            capacity: layout.size(),
            alignment: layout.align(),
            tracker: AllocationTracker::new(layout.size()),
            alloc,
        })
    }
}

#[cfg(feature = "unsafe_impl")]
impl<A: ManageMemory + Clone> Clone for MemoryState<ImplUnsafe, A> {
    fn clone(&self) -> Self {
        Self {
            base: self.base,
            capacity: self.capacity,
            alignment: self.alignment,
            tracker: self.tracker.clone(),
            alloc: self.alloc.clone(),
        }
    }
}

impl<A: ManageMemory, Impl: StorageDetails<A>> core::fmt::Debug for MemoryState<Impl, A>
where
    BaseLocation<Impl, A>: core::fmt::Debug,
    Impl::SizeType: core::fmt::Debug,
    Impl::AllocationTracker: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ContiguousMemoryState")
            .field("base", &self.base)
            .field("capacity", &self.capacity)
            .field("alignment", &self.alignment)
            .field("tracker", &self.tracker)
            .finish()
    }
}

impl<Impl: StorageDetails<A>, A: ManageMemory> Drop for MemoryState<Impl, A> {
    fn drop(&mut self) {
        let layout = self.layout();
        unsafe {
            Impl::deallocate(&self.alloc, &mut self.base.0, layout);
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct BaseLocation<Impl: StorageDetails<A>, A: ManageMemory>(pub Impl::Base);

#[cfg(feature = "debug")]
impl<Impl: StorageDetails> core::fmt::Debug for BaseLocation<Impl>
where
    Impl::LockResult<*mut u8>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("BaseLocation")
            .field(&Impl::get_base(&self.0))
            .finish()
    }
}

impl<Impl: ImplDetails<A>, A: ManageMemory> Deref for BaseLocation<Impl, A> {
    type Target = <Impl as StorageDetails<A>>::Base;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(feature = "unsafe_impl")]
impl<A: ManageMemory + Clone> Copy for BaseLocation<ImplUnsafe, A> {}
#[cfg(feature = "sync_impl")]
unsafe impl<Impl: ImplDetails<A>, A: ManageMemory> Send for BaseLocation<Impl, A> where
    Impl: PartialEq<ImplConcurrent>
{
}
#[cfg(feature = "sync_impl")]
unsafe impl<Impl: ImplDetails<A>, A: ManageMemory> Sync for BaseLocation<Impl, A> where
    Impl: PartialEq<ImplConcurrent>
{
}
