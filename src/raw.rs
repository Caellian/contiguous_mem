#![allow(unused)]

use core::{
    cell::{Cell, RefCell},
    ptr::NonNull,
};

use crate::{
    error::MemoryError,
    memory::{DefaultMemoryManager, ManageMemory, SegmentTracker},
};

use super::*;

/// Pointer to allocated slice of memory.
pub type BasePtr = NonNull<[u8]>;
/// Optional [`BasePtr`] value.
///
/// `None` for zero-sized contiguous memory, `Some` otherwise.
pub type BaseAddress = Option<BasePtr>;

pub(crate) const unsafe fn null_base(align: usize) -> BasePtr {
    NonNull::new_unchecked(std::mem::transmute((align as *mut u8, 0usize)))
}

/// Returns a `usize` position of base address or panics if it's `None`.
#[inline]
pub(crate) fn base_addr_position(base: BaseAddress) -> usize {
    base.map(|it| it.as_ptr() as *const u8 as usize)
        .expect("base address missing")
}

#[inline]
pub(crate) fn base_addr_capacity(base: BaseAddress) -> usize {
    base.map(|it| unsafe { it.as_ref().len() })
        .unwrap_or_default()
}

#[inline]
pub(crate) unsafe fn base_addr_layout(base: BaseAddress, align: usize) -> Layout {
    Layout::from_size_align_unchecked(base_addr_capacity(base), align)
}

pub struct MemoryState<Impl: ImplDetails<A>, A: ManageMemory> {
    pub base: BaseLocation<Impl, A>,
    pub alignment: usize,
    pub tracker: Impl::SegmentTracker,
    pub alloc: A,
}

impl<Impl: ImplDetails<A>, A: ManageMemory> MemoryState<Impl, A> {
    /// Returns the layout of the managed memory.
    pub fn layout(&self) -> Layout {
        unsafe { Impl::get_layout(std::mem::transmute(&self.base), self.alignment) }
    }
}

impl MemoryState<ImplDefault, DefaultMemoryManager> {
    pub fn new(layout: Layout) -> Result<Rc<Self>, MemoryError> {
        let base = DefaultMemoryManager.allocate(layout)?;
        Ok(Rc::new(MemoryState {
            base: BaseLocation(Cell::new(base)),
            alignment: layout.align(),
            tracker: RefCell::new(SegmentTracker::new(layout.size())),
            alloc: DefaultMemoryManager,
        }))
    }
}

impl<A: ManageMemory> MemoryState<ImplDefault, A> {
    pub fn new_with_alloc(layout: Layout, alloc: A) -> Result<Rc<Self>, MemoryError> {
        let base = alloc.allocate(layout)?;
        Ok(Rc::new(MemoryState {
            base: BaseLocation(Cell::new(base)),
            alignment: layout.align(),
            tracker: RefCell::new(SegmentTracker::new(layout.size())),
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
            alignment: layout.align(),
            tracker: Mutex::new(SegmentTracker::new(layout.size())),
            alloc: DefaultMemoryManager,
        }))
    }
}

impl<A: ManageMemory> MemoryState<ImplConcurrent, A> {
    pub fn new_sync_with_alloc(layout: Layout, alloc: A) -> Result<Arc<Self>, MemoryError> {
        let base = alloc.allocate(layout)?;
        Ok(Arc::new(MemoryState {
            base: BaseLocation(RwLock::new(base)),
            alignment: layout.align(),
            tracker: Mutex::new(SegmentTracker::new(layout.size())),
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
            alignment: layout.align(),
            tracker: SegmentTracker::new(layout.size()),
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
            alignment: layout.align(),
            tracker: SegmentTracker::new(layout.size()),
            alloc,
        })
    }
}

#[cfg(feature = "unsafe_impl")]
impl<A: ManageMemory + Clone> Clone for MemoryState<ImplUnsafe, A> {
    fn clone(&self) -> Self {
        Self {
            base: self.base,
            alignment: self.alignment,
            tracker: self.tracker.clone(),
            alloc: self.alloc.clone(),
        }
    }
}

impl<A: ManageMemory, Impl: ImplDetails<A>> core::fmt::Debug for MemoryState<Impl, A>
where
    BaseLocation<Impl, A>: core::fmt::Debug,
    Impl::SegmentTracker: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ContiguousMemoryState")
            .field("base", &self.base)
            .field("alignment", &self.alignment)
            .field("tracker", &self.tracker)
            .finish()
    }
}

impl<Impl: ImplDetails<A>, A: ManageMemory> Drop for MemoryState<Impl, A> {
    fn drop(&mut self) {
        let layout = self.layout();
        unsafe {
            Impl::deallocate(&self.alloc, &mut self.base.0, layout);
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct BaseLocation<Impl: ImplDetails<A>, A: ManageMemory>(pub Impl::Base);

#[cfg(feature = "debug")]
impl<Impl: ImplDetails<A>, A: ManageMemory> core::fmt::Debug for BaseLocation<Impl, A>
where
    Impl::LockResult<BaseAddress>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BaseLocation")
            .field("pos", &Impl::get_base(&self.0))
            .field("size", &Impl::get_base(&self.0))
            .finish()
    }
}

impl<Impl: ImplDetails<A>, A: ManageMemory> Deref for BaseLocation<Impl, A> {
    type Target = <Impl as ImplDetails<A>>::Base;

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
