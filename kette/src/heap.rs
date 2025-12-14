#![allow(unused)]
use std::{
    alloc::Layout,
    cell::{RefCell, UnsafeCell},
    collections::HashSet,
    marker::PhantomData,
    mem,
    ptr::NonNull,
    sync::{
        Arc,
        atomic::{AtomicBool, AtomicUsize, Ordering},
    },
};

use bitflags::bitflags;
use parking_lot::{Mutex, RwLock};

use crate::{
    Activation, ActivationObject, Array, Block, ByteArray, ExecutableMap,
    Handle, HeapObject, Message, Method, MethodMap, Quotation, QuotationMap,
    SlotDescriptor, SlotHelper, SlotMap, SlotObject, SlotTags, Strings, Tagged,
    Value, Visitable, map_memory, objects::executable::StackEffect,
};

pub const HANDLE_SET_SIZE: usize = 20;

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum PageType {
    Boxed,
    Unboxed,
}

// TODO: add more control, like growth, gc ratios
// also investigate automatic resizing, dynamic change of rations
// sbcl offers dynamic heap growth, investigate how that works
#[derive(Debug, Default)]
pub struct HeapCreateInfo {
    pub size: usize,
    pub generations: Option<usize>,
    pub generation_size: Option<usize>,
    pub page_size: Option<usize>,
    // rounds to the nearest page
    pub tlab_size: Option<usize>,
    // size of a dirty line, default 512
    pub dirty_line_size: Option<usize>,
    // max slack
    pub max_slack: Option<usize>,
}

// TODO: do minimum, maybe even maximum or other constraints
// some combinations probably don't make sense, or we require some minimums
// for example to get both a bytepage and an object page within the nursery we want at least 2
// pages there
#[derive(Debug)]
pub struct HeapSettings {
    generations: usize,
    // size of a single generation compared to total heap in discrete percent
    generation_size: usize,
    page_size: usize,
    tlab_size: usize,
    dirty_line_size: usize,
    // max allowed slack on a page, if a page reaches lower than this, we might retire it
    // mainly useful for allocations that are almost size of a page or multi pages and reach end of
    // another page, small allocations do not trigger this
    max_slack: usize,
}

impl Default for HeapSettings {
    fn default() -> Self {
        Self {
            generations: 4,
            generation_size: 5,
            page_size: 32768,
            tlab_size: 8192,
            dirty_line_size: 512,
            max_slack: 4096,
        }
    }
}

bitflags! {
    #[derive(Debug, Copy, Clone)]
    pub struct PageFlags: u8 {
        const Used = 1 << 0;
        const Unboxed = 1 << 1;
        const Large = 1 << 2;
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct PageMeta {
    bytes_used: u16,
    offset_first: u16,
    generation: u8,
    flags: PageFlags,
}

#[derive(Debug, Copy, Clone)]
pub struct AllocSearchInfo {
    size: usize,
    ptype: PageType,
    generation: u8,
    allow_split: bool,
}

pub struct AllocationSelection {
    start: usize,
    count: usize,
    first_capacity_page: usize,
}

pub struct AllocationInfo {
    start: NonNull<u8>,
    size: usize,
    page_index: usize,
    large: bool,
    ptype: PageType,
}

#[derive(Debug)]
pub struct Heap {
    inner: Arc<HeapShared>,
    _marker: PhantomData<*const ()>,
}
#[derive(Debug)]
pub struct HeapShared {
    pub start: NonNull<u8>,
    pub end: NonNull<u8>,
    pub settings: HeapSettings,
    pub lock: Mutex<()>,
    pub gc_active: AtomicBool,
    pub epoch: AtomicUsize,
    pub pages: RefCell<Box<[PageMeta]>>,
    pub dirty: UnsafeCell<Box<[u8]>>,
    pub handles: RwLock<HashSet<NonNull<HandleSet>, ahash::RandomState>>,
}

#[derive(Debug)]
pub struct Tlab {
    start: NonNull<u8>,
    end: NonNull<u8>,
    bump: usize,
    size: usize,
}
#[derive(Debug)]
pub struct HeapProxy {
    heap: Arc<HeapShared>,
    epoch: usize,
    boxed_tlab: Tlab,
    unboxed_tlab: Tlab,
    handle_set: Box<HandleSet>,
}

// SAFETY: this is safe
unsafe impl Send for HeapProxy {}
// SAFETY: this is safe
unsafe impl Sync for HeapProxy {}

// SAFETY: this is safe
unsafe impl Send for HeapShared {}
// SAFETY: this is safe
unsafe impl Sync for HeapShared {}

impl Heap {
    pub fn new(info: HeapCreateInfo) -> Self {
        let size = info.size;
        let start = map_memory(size).expect("Allocate Memory for heap");
        // SAFETY: just allocted
        let end_ptr = unsafe { start.as_ptr().add(size) };
        // SAFETY: just allocted
        let end = unsafe { NonNull::new_unchecked(end_ptr) };

        let mut settings = HeapSettings::default();
        info.generations.inspect(|&val| settings.generations = val);
        info.generation_size
            .inspect(|&val| settings.generation_size = val);
        info.page_size.inspect(|&val| settings.page_size = val);
        info.tlab_size.inspect(|&val| settings.tlab_size = val);
        info.dirty_line_size
            .inspect(|&val| settings.dirty_line_size = val);
        info.max_slack.inspect(|&val| settings.max_slack = val);

        let page_count = size / settings.page_size;

        let shared = HeapShared::new(start, end, page_count, settings);
        Self {
            inner: shared,
            _marker: PhantomData,
        }
    }

    pub fn create_proxy(&self) -> HeapProxy {
        let heap = self.inner.clone();
        let epoch = self.inner.epoch.load(Ordering::Relaxed);

        let mut handle_set = Box::new(HandleSet::new());
        // SAFETY: just allocated
        let nonnull = unsafe { NonNull::new_unchecked(handle_set.as_mut()) };
        {
            let mut handles = heap.handles.write();
            handles.insert(nonnull);
        }

        HeapProxy {
            heap,
            epoch,
            boxed_tlab: Tlab::empty(),
            unboxed_tlab: Tlab::empty(),
            handle_set,
        }
    }
}

impl HeapShared {
    pub fn new(
        start: NonNull<u8>,
        end: NonNull<u8>,
        page_count: usize,
        settings: HeapSettings,
    ) -> Arc<Self> {
        let pages = vec![PageMeta::empty(); page_count];
        let pages: Box<[PageMeta]> = Box::from(pages);
        let pages = RefCell::new(pages);

        let dirty_count =
            settings.page_size * page_count / settings.dirty_line_size;
        let dirty = vec![0; dirty_count];
        let dirty: Box<[u8]> = Box::from(dirty);
        let dirty = UnsafeCell::new(dirty);

        let new = Self {
            start,
            end,
            settings,
            epoch: AtomicUsize::new(0),
            gc_active: AtomicBool::new(false),
            lock: Mutex::new(()),
            pages,
            dirty,
            handles: RwLock::new(HashSet::default()),
        };
        Arc::new(new)
    }

    pub fn allocate(&self, info: AllocSearchInfo) -> AllocationInfo {
        let _lock = self.lock.lock();
        if let Some(res) = self.next_fit_find_pages(info) {
            return self.finalize_pages(res, info);
        }

        self.minor_gc();

        if let Some(res) = self.next_fit_find_pages(info) {
            return self.finalize_pages(res, info);
        }
        panic!("VM out of memory")
    }

    fn minor_gc(&self) {
        unimplemented!("TODO: implement minor gc")
    }

    fn major_gc(&self) {
        unimplemented!("TODO: implement major gc")
    }

    fn finalize_pages(
        &self,
        selection: AllocationSelection,
        search: AllocSearchInfo,
    ) -> AllocationInfo {
        let start_index = selection.start;
        let end_index = selection.start + selection.count;

        let mut flags = PageFlags::Used;
        if search.ptype == PageType::Unboxed {
            flags.insert(PageFlags::Unboxed);
        }
        if search.size > self.settings.page_size - self.settings.max_slack {
            flags.insert(PageFlags::Large);
        }
        let total_size = search.size;
        let mut pages = self.pages.borrow_mut();

        let start_ptr: *mut u8;
        // TODO: maybe unify this
        if flags.contains(PageFlags::Large) {
            let mut remaining_size = 0;

            for page_idx in start_index..end_index {
                let bytes_used = self.settings.page_size.min(remaining_size);
                let page = &mut pages[page_idx];
                page.flags = flags;
                page.generation = search.generation;
                page.bytes_used = bytes_used as u16;
                page.offset_first = 0;
                remaining_size -= self.settings.page_size;
                // I am not sure if this can ever fall below 0
            }

            // SAFETY: correctly allocated
            start_ptr = unsafe {
                self.start
                    .as_ptr()
                    .add(start_index * self.settings.page_size)
            };
        } else {
            let old_used = pages[start_index].bytes_used as usize;

            if selection.count == 1 {
                let page = &mut pages[start_index];
                page.bytes_used += total_size as u16;
                page.flags = flags;
                page.generation = search.generation;
                // SAFETY: correctly allocated
                start_ptr = unsafe {
                    self.start
                        .as_ptr()
                        .add(start_index * self.settings.page_size + old_used)
                };
            } else {
                let first_page_fit = self.settings.page_size
                    - pages[start_index].bytes_used as usize;
                let remaining = total_size - first_page_fit;
                pages[start_index].bytes_used = self.settings.page_size as u16;

                let split_page = &mut pages[start_index + 1];
                split_page.bytes_used = remaining as u16;
                split_page.flags = flags;
                split_page.generation = search.generation;
                split_page.offset_first = first_page_fit as u16;
                // SAFETY: correctly allocated
                start_ptr = unsafe {
                    self.start
                        .as_ptr()
                        .add(start_index * self.settings.page_size + old_used)
                };
            }
        }

        // SAFETY: correctly allocated
        let start = unsafe { NonNull::new_unchecked(start_ptr) };

        AllocationInfo {
            start,
            size: search.size,
            page_index: start_index,
            large: search.size > self.settings.page_size,
            ptype: search.ptype,
        }
    }

    // TODO: Right now we don't allow to allocate on large pages
    // this is because right now I feel lazy to get it to work
    // this should be changed
    fn next_fit_find_pages(
        &self,
        search: AllocSearchInfo,
    ) -> Option<AllocationSelection> {
        // big allocations
        if search.size > self.settings.page_size - self.settings.max_slack {
            return self.find_free_pages(search);
        }

        let pages = self.pages.borrow();
        let mut page_idx: Option<usize> = None;
        let mut extend = false;
        // TODO: maybe do two passes, so we don't greedily take a page but prefer used ones
        //       in this case we would remove the third case and make an extra loop for that
        //       that gets called if case1&case2 loop didn't yield a result
        // Two cases:
        // Case 1: same type+gen & page has free memory
        // Case 2: same type+gen & page has some free memory, but page afterwards is free
        // case 3: page is free
        for (idx, page) in pages.iter().enumerate() {
            if page.page_type() == search.ptype
                && !page.is_large()
                && page.generation == search.generation
            {
                // Case 1
                if self.settings.page_size - page.bytes_used as usize
                    >= search.size
                {
                    page_idx = Some(idx);
                    break;
                }

                // Case 2
                if search.allow_split && idx + 1 < pages.len() {
                    let next = &pages[idx + 1];
                    if next.is_free() {
                        page_idx = Some(idx);
                        extend = true;
                        break;
                    }
                }
            }

            // Case 3
            if page.is_free() {
                page_idx = Some(idx);
            }
        }

        page_idx.map(|start| AllocationSelection {
            start,
            count: if extend { 2 } else { 1 },
            first_capacity_page: pages[start].bytes_used as usize,
        })
    }

    fn find_free_pages(
        &self,
        search: AllocSearchInfo,
    ) -> Option<AllocationSelection> {
        // TODO: we don't need size and count, they are bijective here
        let pages = self.pages.borrow();
        let mut size = 0;
        let mut count = 0;
        let mut current_start: Option<usize> = None;
        for (idx, page) in pages.iter().enumerate() {
            if page.is_free() {
                if current_start.is_none() {
                    current_start = Some(idx);
                }
                size += self.settings.page_size;
                count += 1;
            } else {
                size = 0;
                current_start = None;
                count = 0;
            }

            if size >= search.size {
                break;
            }
        }
        if let Some(start) = current_start {
            let res = AllocationSelection {
                start,
                count,
                first_capacity_page: 0,
            };
            return Some(res);
        }

        None
    }

    pub fn register_handle_set(&self, set: &HandleSet) {
        let mut handles = self.handles.write();
        handles.insert(NonNull::from_ref(set));
    }
}

impl HeapProxy {
    fn tlab_alloc(
        &mut self,
        size: usize,
        align: usize,
        ptype: PageType,
    ) -> Option<NonNull<u8>> {
        match ptype {
            PageType::Boxed => self.boxed_tlab.allocate(size, align),
            PageType::Unboxed => self.unboxed_tlab.allocate(size, align),
        }
    }

    fn exchange_tlab(&mut self, ptype: PageType) {
        let size = self.heap.settings.tlab_size;
        let search = AllocSearchInfo {
            size,
            ptype,
            generation: 0,
            allow_split: false,
        };
        let res = self.heap.allocate(search);
        let start = res.start;
        let size = res.size;
        // SAFETY: correctly allocated
        let end_ptr = unsafe { start.as_ptr().add(size) };
        // SAFETY: correctly allocated
        let end = unsafe { NonNull::new_unchecked(end_ptr) };
        let tlab = Tlab {
            start,
            end,
            bump: 0,
            size,
        };

        match ptype {
            PageType::Boxed => self.boxed_tlab = tlab,
            PageType::Unboxed => self.unboxed_tlab = tlab,
        }
    }

    fn maybe_wait_epoch(&mut self) -> bool {
        let heap_epoch = self.heap.epoch.load(Ordering::Relaxed);
        if self.epoch == heap_epoch {
            return false;
        }

        while self.heap.gc_active.load(Ordering::Relaxed) {
            std::hint::spin_loop()
        }

        self.epoch = self.heap.epoch.load(Ordering::Relaxed);
        true
    }

    pub fn allocate_raw(
        &mut self,
        size: usize,
        align: usize,
        ptype: PageType,
    ) -> NonNull<u8> {
        if self.maybe_wait_epoch() {
            self.exchange_tlab(ptype);
        }

        // Fast path: TLAB allocation
        if let Some(allocation) = self.tlab_alloc(size, align, ptype) {
            return allocation;
        }

        debug_assert!(if ptype == PageType::Boxed {
            align.is_multiple_of(8)
        } else {
            true
        });

        // Slow path: Large object or TLAB refresh needed

        // Check if object is too large for TLAB
        if size > self.heap.settings.tlab_size {
            let info = AllocSearchInfo {
                size,
                ptype,
                generation: 0,
                allow_split: true,
            };

            // NOTE: The underlying HeapShared::allocate works on page granularity or gap filling.
            // New pages are always page-aligned (4KB+), which satisfies most object alignments.
            // If the allocator fills a gap in an existing page, strict alignment isn't guaranteed
            // by AllocSearchInfo currently.
            // However, since size > tlab_size, it typically allocates a fresh Large Page
            // or a significant chunk which is usually aligned enough for standard types.
            let res = self.heap.allocate(info);
            return res.start;
        }

        // TLAB exhausted, get a new one
        self.exchange_tlab(ptype);

        // Retry allocation in new TLAB
        self.tlab_alloc(size, align, ptype)
            .expect("Tlab allocation must work after refresh for object smaller than Tlab")
    }

    pub fn allocate_boxed_raw(&mut self, size: usize) -> NonNull<u8> {
        // Boxed objects (pointers) usually require machine word alignment
        self.allocate_raw(size, mem::align_of::<usize>(), PageType::Boxed)
    }

    /// Allocates unboxed raw memory.
    pub fn allocate_unboxed_raw(&mut self, layout: Layout) -> NonNull<u8> {
        self.allocate_raw(layout.size(), layout.align(), PageType::Unboxed)
    }

    /// allocate unitialized bytearray
    /// # Safety
    /// must be initialized afterwards, either zeroed or with data
    pub unsafe fn allocate_bytearray_raw(
        &mut self,
        size: usize,
    ) -> NonNull<ByteArray> {
        // We allocate enough space for the struct header + the data payload
        let total_size = mem::size_of::<ByteArray>() + size;

        // Ensure the ByteArray struct itself is aligned correctly.
        let align = mem::align_of::<ByteArray>();
        let layout = Layout::from_size_align(total_size, align)
            .expect("create valid layout");

        self.allocate_unboxed_raw(layout).cast::<ByteArray>()
    }

    pub fn allocate_bytearray(&mut self, size: usize) -> Tagged<ByteArray> {
        // SAFETY: we ensure correct size
        let mut raw = unsafe { self.allocate_bytearray_raw(size) };
        // SAFETY: just allocated and not null, must exist
        let ba = unsafe { raw.as_mut() };
        // SAFETY: this is safe
        unsafe { (*ba).init_zeroed(size) };
        Tagged::new_ptr(ba)
    }

    pub fn allocate_bytearray_data(
        &mut self,
        data: &[u8],
    ) -> Tagged<ByteArray> {
        let size = data.len();
        // SAFETY: we ensure correct size
        let mut raw = unsafe { self.allocate_bytearray_raw(size) };
        // SAFETY: just created, safe to convert to mutable reference
        let ba = unsafe { raw.as_mut() };
        // SAFETY: this is safe
        unsafe { (*ba).init_data(data) };
        Tagged::new_ptr(ba)
    }

    pub fn allocate_slot_map(
        &mut self,
        slots: &[SlotDescriptor],
    ) -> Tagged<SlotMap> {
        let layout = SlotMap::required_layout(slots.len());
        let mut raw = self.allocate_unboxed_raw(layout).cast::<SlotMap>();
        // SAFETY: just created, safe to convert to mutable reference
        let map = unsafe { raw.as_mut() };

        // SAFETY: this is safe
        unsafe { map.init_with_data(slots) };

        Tagged::new_ptr(map)
    }

    pub fn allocate_slot_map_helper(
        &mut self,
        strings: &Strings,
        slots: &[SlotHelper],
    ) -> Tagged<SlotMap> {
        let slots = slots
            .iter()
            .map(|slot| {
                let interned = strings.get(slot.name, self);
                SlotDescriptor::new(interned.into(), slot.tags, slot.value)
            })
            .collect::<Vec<_>>();

        self.allocate_slot_map(&slots)
    }

    pub fn allocate_slot_object(
        &mut self,
        map: Tagged<SlotMap>,
        data: &[Value],
    ) -> Tagged<SlotObject> {
        // SAFETY: map must be valid here
        let map_ref = unsafe { map.as_ref() };
        let layout =
            SlotObject::required_layout(map_ref.assignable_slots_count());
        debug_assert!(layout.align() == 8);
        let mut raw =
            self.allocate_boxed_raw(layout.size()).cast::<SlotObject>();

        // SAFETY: just created, safe to convert to mutable reference
        let obj = unsafe { raw.as_mut() };
        // SAFETY: this is safe
        unsafe { obj.init_with_data(map, data) };
        Tagged::new_ptr(obj)
    }

    /// name must be interned !
    pub fn allocate_method_map(
        &mut self,
        name: Tagged<ByteArray>,
        code: &Block,
        slots: &[SlotDescriptor],
        effect: Tagged<StackEffect>,
    ) -> Tagged<MethodMap> {
        let layout = MethodMap::required_layout(slots.len());
        let mut raw = self.allocate_unboxed_raw(layout).cast::<MethodMap>();
        // SAFETY: just created, safe to convert to mutable reference
        let map = unsafe { raw.as_mut() };

        // SAFETY: this is safe
        unsafe {
            map.init_with_data(name, effect, code as *const _ as _, slots)
        };

        Tagged::new_ptr(map)
    }

    pub fn allocate_method_object(
        &mut self,
        map: Tagged<MethodMap>,
    ) -> Tagged<Method> {
        // SAFETY: map must be valid here
        let map_ref = unsafe { map.as_ref() };
        let layout = Layout::new::<Method>();
        debug_assert!(layout.align() == 8);
        let mut raw = self.allocate_boxed_raw(layout.size()).cast::<Method>();

        // SAFETY: just created, safe to convert to mutable reference
        let obj = unsafe { raw.as_mut() };
        // SAFETY: this is safe
        unsafe { obj.init(map) };
        Tagged::new_ptr(obj)
    }

    pub fn allocate_message(
        &mut self,
        interned: Tagged<ByteArray>,
    ) -> Tagged<Message> {
        // SAFETY: this is safe
        let mut raw = unsafe {
            self.allocate_boxed_raw(mem::size_of::<Message>())
                .cast::<Message>()
        };

        // SAFETY: just created, safe to convert to mutable reference
        let message = unsafe { raw.as_mut() };
        // SAFETY: this is safe
        unsafe { message.init(interned) };

        Tagged::new_ptr(message)
    }

    pub fn allocate_empty_map(&mut self) -> Tagged<SlotMap> {
        self.allocate_slot_map(&[])
    }

    pub fn allocate_array(&mut self, data: &[Value]) -> Tagged<Array> {
        let mut raw = self.allocate_boxed_raw(data.len()).cast::<Array>();

        // SAFETY: we just create this here
        let array = unsafe { raw.as_mut() };
        // SAFETY: this is safe
        unsafe { array.init_with_data(data) };

        Tagged::new_ptr(array)
    }

    /// # Safety
    /// this is safe but should only be used in conjunction with a quotation object
    pub unsafe fn allocate_quotation_map(
        &mut self,
        code: &Block,
        input: usize,
        output: usize,
    ) -> Tagged<QuotationMap> {
        let layout = QuotationMap::required_layout();
        let mut raw = self.allocate_unboxed_raw(layout).cast::<QuotationMap>();
        // SAFETY: just created, safe to convert to mutable reference
        let map = unsafe { raw.as_mut() };

        // SAFETY: this is safe
        unsafe { map.init(code, input, output) };

        Tagged::new_ptr(map)
    }

    pub fn allocate_quotation(
        &mut self,
        body: Handle<Array>,
        bytecode: &Block,
        input: usize,
        output: usize,
    ) -> Tagged<Quotation> {
        // SAFETY: this is safe
        let map =
            unsafe { self.allocate_quotation_map(bytecode, input, output) };
        let mut raw = self
            .allocate_boxed_raw(mem::size_of::<Quotation>())
            .cast::<Quotation>();
        // SAFETY: we just create this here
        let quot = unsafe { raw.as_mut() };
        // SAFETY: we just create this here
        unsafe { quot.init(body.as_tagged(), map) };
        Tagged::new_ptr(quot)
    }

    /// # Safety
    /// internal function, usage discouraged
    pub unsafe fn allocate_activation_raw(
        &mut self,
        receiver: Handle<Value>,
        map: Handle<ExecutableMap>,
        slots: &[Handle<Value>],
    ) -> Tagged<ActivationObject> {
        let layout = ActivationObject::required_layout(slots.len());
        // SAFETY: is safe
        let mut raw = unsafe {
            self.allocate_raw(layout.size(), layout.align(), PageType::Boxed)
        };
        // SAFETY: just allocated
        let activation = unsafe { raw.cast::<ActivationObject>().as_mut() };
        // SAFETY: allocated with correct size
        unsafe { activation.init(receiver, map, slots) };
        Tagged::new_ptr(activation)
    }

    pub fn allocate_method_activation(
        &mut self,
        receiver: Handle<Value>,
        map: Handle<MethodMap>,
        slots: &[Handle<Value>],
    ) -> Tagged<ActivationObject> {
        // SAFETY: every method map is an executable map
        let map = unsafe { map.cast::<ExecutableMap>() };
        // SAFETY: handles safe, slots must be same size as map wants
        unsafe { self.allocate_activation_raw(receiver, map, slots) }
    }

    pub fn allocate_quotation_activation(
        &mut self,
        quotation: Handle<Quotation>,
        slots: &[Handle<Value>],
    ) -> Tagged<ActivationObject> {
        // SAFETY: every method map is an executable map
        let map = unsafe {
            quotation.map.cast::<ExecutableMap>().promote_to_handle()
        };
        // SAFETY: handles safe, slots must be same size as map wants
        unsafe {
            self.allocate_activation_raw(quotation.as_value_handle(), map, &[])
        }
    }

    pub fn create_proxy(&self) -> HeapProxy {
        let heap = self.heap.clone();
        let epoch = self.heap.epoch.load(Ordering::Relaxed);

        let mut handle_set = Box::new(HandleSet::new());
        // Safety: we just create this here
        let nonnull = unsafe { NonNull::new_unchecked(handle_set.as_mut()) };
        {
            let mut handles = heap.handles.write();
            handles.insert(nonnull);
        }

        HeapProxy {
            heap,
            epoch,
            boxed_tlab: Tlab::empty(),
            unboxed_tlab: Tlab::empty(),
            handle_set,
        }
    }

    pub fn register_handle_set(&self, set: &HandleSet) {
        self.heap.register_handle_set(set);
    }
}

impl Tlab {
    pub fn empty() -> Self {
        Self {
            start: NonNull::dangling(),
            end: NonNull::dangling(),
            size: 0,
            bump: 0,
        }
    }

    pub fn allocate(
        &mut self,
        size: usize,
        align: usize,
    ) -> Option<NonNull<u8>> {
        let start_ptr = self.start.as_ptr();
        // SAFETY: check afterwards
        let current_ptr = unsafe { start_ptr.add(self.bump) };

        let offset = current_ptr.align_offset(align);

        if offset == usize::MAX {
            return None;
        }

        let padded_size = size + offset;

        if self.bump + padded_size <= self.size {
            // SAFETY: checked
            let ptr = unsafe { current_ptr.add(offset) };

            self.bump += padded_size;
            // SAFETY: just created, must be valid
            return Some(unsafe { NonNull::new_unchecked(ptr) });
        }
        None
    }
}

impl PageMeta {
    pub fn empty() -> Self {
        Self {
            flags: PageFlags::empty(),
            offset_first: 0,
            bytes_used: 0,
            generation: 0,
        }
    }

    #[inline]
    fn is_free(&self) -> bool {
        !self.flags.contains(PageFlags::Used)
            && !self.flags.contains(PageFlags::Large)
    }

    #[inline]
    fn is_large(&self) -> bool {
        self.flags.contains(PageFlags::Large)
    }

    #[inline]
    fn page_type(&self) -> PageType {
        if self.flags.contains(PageFlags::Unboxed) {
            PageType::Unboxed
        } else {
            PageType::Boxed
        }
    }

    #[inline]
    fn capacity_tail_bytes(&self, page_size: usize) -> usize {
        let used = self.bytes_used as usize;
        page_size.saturating_sub(used)
    }
}

#[derive(Debug)]
pub struct HandleSet {
    pub prev: Option<NonNull<Self>>,
    pub next: Option<NonNull<Self>>,
    pub bump: usize,
    pub handles: [Value; HANDLE_SET_SIZE],
}

impl Default for HandleSet {
    fn default() -> Self {
        Self::new()
    }
}

impl HandleSet {
    pub fn new() -> Self {
        Self {
            prev: None,
            next: None,
            bump: 0,
            handles: [Value::zero(); HANDLE_SET_SIZE],
        }
    }

    pub fn link_prev(&mut self, prev: &mut Self) {
        assert!(self.prev.is_none(), "Trying to link already linked handles");
        assert!(prev.next.is_none(), "Trying to link already linked handles");

        prev.next = Some(NonNull::new(self).expect("Not null"));
        self.prev = Some(NonNull::new(prev).expect("Non null"));
    }

    pub fn promote<T: HeapObject>(&mut self, tagged: Tagged<T>) -> Handle<T> {
        assert!(self.bump < HANDLE_SET_SIZE, "Handle Set full");
        let value = tagged.as_value();
        self.handles[self.bump] = value;
        self.bump += 1;
        // SAFETY: the GC is made aware of the object
        unsafe { tagged.promote_to_handle() }
    }
}

impl Drop for HeapProxy {
    fn drop(&mut self) {
        assert!(self.handle_set.next.is_none(), "sanity check");
        let mut handles = self.heap.handles.write();
        // SAFETY: must exist
        let nonnull =
            unsafe { NonNull::new_unchecked(self.handle_set.as_mut()) };
        handles.remove(&nonnull);
    }
}

impl Drop for HandleSet {
    fn drop(&mut self) {
        if let Some(_next) = self.next {
            panic!("Handle Set cannot be dropped while other depends on it")
        }
        if let Some(mut prev) = self.prev {
            // SAFETY: handle sets are thread local
            let prev = unsafe { prev.as_mut() };
            prev.next = None
        }
    }
}

impl Visitable for HandleSet {
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        self.handles[0..self.bump]
            .iter()
            .for_each(|&val| visitor.visit(val));

        if let Some(mut next) = self.next {
            // SAFETY: handle sets are thread local
            let next = unsafe { next.as_ref() };
            next.visit_edges(visitor);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Object, Visitable, Visitor};

    use super::*;
    use std::{rc::Rc, sync::Arc};

    fn mk_heap(total_pages: usize, page_size: usize, tlab_size: usize) -> Heap {
        let total_bytes = total_pages * page_size;
        let info = HeapCreateInfo {
            size: total_bytes,
            generations: Some(2),
            generation_size: Some(10),
            page_size: Some(page_size),
            tlab_size: Some(tlab_size),
            dirty_line_size: None,
            max_slack: None, // keep default (4096) unless caller changes settings
        };
        Heap::new(info)
    }

    fn page_flags_contains(
        flags: PageFlags,
        has: &[PageFlags],
        not: &[PageFlags],
    ) -> bool {
        has.iter().all(|f| flags.contains(*f))
            && not.iter().all(|f| !flags.contains(*f))
    }

    #[test]
    fn tlab_bootstrap_sets_page_flags_and_bytes_used() {
        // 8 pages of 32 KiB; tlab = 8 KiB (fits in one page comfortably)
        let page_size = 32 * 1024;
        let tlab_size = 8 * 1024;
        let heap = mk_heap(8, page_size, tlab_size);

        let mut p = heap.create_proxy();

        // First tiny boxed allocation will *bootstrap* a boxed TLAB.
        let _a = p.allocate_boxed_raw(16);

        {
            let pages = p.heap.pages.borrow();
            // Expect first page to be boxed+used, with bytes_used = tlab_size
            let pg0 = pages[0];
            assert!(
                page_flags_contains(
                    pg0.flags,
                    &[PageFlags::Used],
                    &[PageFlags::Unboxed, PageFlags::Large]
                ),
                "first page should be Used (boxed), flags = {:?}",
                pg0.flags
            );
            assert_eq!(
                pg0.bytes_used as usize, tlab_size,
                "boxed TLAB should consume tlab_size bytes in first page"
            );
        }

        let _b =
            p.allocate_unboxed_raw(Layout::from_size_align(24, 8).unwrap());

        {
            let pages = p.heap.pages.borrow();
            // Expect second page (typically) to be unboxed+used, also with tlab_size used.
            // If allocator ever reorders differently, at minimum *one* page must be unboxed
            // with tlab_size used. We'll find it.
            let (idx, pg) = pages
                .iter()
                .enumerate()
                .find(|(_, pg)| {
                    page_flags_contains(
                        pg.flags,
                        &[PageFlags::Used, PageFlags::Unboxed],
                        &[PageFlags::Large],
                    )
                })
                .expect("expected an unboxed TLAB page");
            assert_eq!(
                pg.bytes_used as usize, tlab_size,
                "unboxed TLAB page bytes_used mismatch at page {}",
                idx
            );
        }
    }

    #[test]
    fn page_wrap_split_sets_offset_first_and_bytes_used_correctly() {
        let page_size = 32 * 1024;
        let heap = mk_heap(8, page_size, 8 * 1024);

        // 1) Put 20 KiB on page 0.
        let first = AllocSearchInfo {
            size: 20 * 1024,
            ptype: PageType::Boxed,
            generation: 0,
            allow_split: false,
        };
        let res1 = heap.inner.allocate(first);
        assert_eq!(
            res1.page_index, 0,
            "first small allocation should land on page 0"
        );

        // 2) Request 16 KiB with allow_split: should fill remaining 12 KiB on page 0 and spill 4 KiB into page 1.
        let split_bytes = 16 * 1024;
        let split = AllocSearchInfo {
            size: split_bytes,
            ptype: PageType::Boxed,
            generation: 0,
            allow_split: true,
        };
        let res2 = heap.inner.allocate(split);
        assert_eq!(
            res2.page_index, 0,
            "split allocation should begin on page 0"
        );

        // Verify page accounting
        let pages = heap.inner.pages.borrow();
        let p0 = pages[0];
        let p1 = pages[1];

        // Page 0 should be completely full now
        assert_eq!(
            p0.bytes_used as usize, page_size,
            "page 0 should be filled by the split"
        );
        assert!(page_flags_contains(
            p0.flags,
            &[PageFlags::Used],
            &[PageFlags::Unboxed, PageFlags::Large]
        ));

        // Page 1 should have 'remaining' bytes and offset pointing to where the first object started (the backward offset)
        let first_page_fit = page_size - (20 * 1024);
        let expected_into_p1 = split_bytes - first_page_fit; // 16 KiB - 12 KiB = 4 KiB
        assert_eq!(
            p1.bytes_used as usize, expected_into_p1,
            "page 1 should contain the spillover after the split"
        );
        assert_eq!(
            p1.offset_first as usize, first_page_fit,
            "offset_first must equal how much of the allocation fit on the previous page (backwards offset)"
        );
        assert!(page_flags_contains(
            p1.flags,
            &[PageFlags::Used],
            &[PageFlags::Unboxed, PageFlags::Large]
        ));
    }

    #[test]
    fn tlab_refreshes_when_exhausted_and_bump_resets() {
        let page_size = 32 * 1024;
        let tlab_size = 128; // small to force quick refresh
        let heap = mk_heap(4, page_size, tlab_size);
        let mut p = heap.create_proxy();

        // First boxed TLAB is created on first small alloc.
        let a = p.allocate_boxed_raw(64);
        let bump_after_a = p.boxed_tlab.bump;
        assert_eq!(
            bump_after_a, 64,
            "after first 64B alloc, TLAB bump must be 64"
        );

        // Second alloc won't fit in remaining 64 (we ask for 80).
        let b = p.allocate_boxed_raw(80);
        // A refresh should have happened; the new TLAB's bump should now be 80.
        let bump_after_b = p.boxed_tlab.bump;
        assert_eq!(
            bump_after_b, 80,
            "TLAB bump should reset on refresh and then advance by new size"
        );

        // Pointers should not be equal (likely from different places within page/heap).
        assert_ne!(
            a.as_ptr(),
            b.as_ptr(),
            "post-refresh allocation should yield a different address"
        );

        // Check that the underlying page bytes_used increased by exactly two TLAB chunks
        {
            let pages = p.heap.pages.borrow();
            let pg0 = pages[0];
            assert_eq!(
                pg0.bytes_used as usize,
                tlab_size * 2,
                "two TLAB grabs should consume two chunks from the page"
            );
        }

        // Do the same for unboxed to ensure independent TLABs
        let _u1 =
            p.allocate_unboxed_raw(Layout::from_size_align(32, 1).unwrap());
        assert_eq!(p.unboxed_tlab.bump, 32);
        // skip tlab allocation as this is bigger than the tlab, tlab stays the same
        let _u2 =
            p.allocate_unboxed_raw(Layout::from_size_align(200, 1).unwrap());
        assert_eq!(p.unboxed_tlab.bump, 32);

        // Ensure the unboxed page is marked unboxed
        let pages = p.heap.pages.borrow();
        let (idx, unboxed_pg) = pages
            .iter()
            .enumerate()
            .find(|(_, pg)| {
                page_flags_contains(
                    pg.flags,
                    &[PageFlags::Used, PageFlags::Unboxed],
                    &[],
                )
            })
            .expect("expected an unboxed page after unboxed TLAB usage");
        assert!(
            unboxed_pg.bytes_used as usize >= tlab_size,
            "unboxed page {} should have at least one TLAB chunk",
            idx
        );
    }

    #[test]
    fn multithreaded_allocations_produce_both_boxed_and_unboxed_pages() {
        let page_size = 32 * 1024;
        let tlab_size = 8 * 1024;
        let heap = mk_heap(64, page_size, tlab_size);
        let heap_arc = Arc::new(heap);

        let threads = 8usize;
        let iters = 1000usize;

        use std::collections::HashSet;
        use std::sync::{Arc as SyncArc, Mutex as SyncMutex};
        let seen: SyncArc<SyncMutex<HashSet<usize>>> =
            SyncArc::new(SyncMutex::new(HashSet::new()));

        let mut handles = Vec::new();
        for t in 0..threads {
            let heap_clone = heap_arc.clone();
            let seen_clone = seen.clone();
            let proxy = heap_clone.create_proxy();
            handles.push(std::thread::spawn(move || {
                let mut proxy = proxy;
                for i in 0..iters {
                    let size = 16 + (i % 32);
                    let ptr = if (t + i) % 2 == 0 {
                        proxy.allocate_boxed_raw(size)
                    } else {
                        proxy.allocate_unboxed_raw(Layout::from_size_align(size, 1).unwrap())
                    };
                    let addr = ptr.as_ptr() as usize;
                    let mut set = seen_clone.lock().unwrap();
                    assert!(
                        set.insert(addr),
                        "duplicate pointer detected across threads (addr = {:p})",
                        ptr.as_ptr()
                    );
                }
            }));
        }
        for h in handles {
            h.join().expect("thread panicked");
        }

        let pages = heap_arc.inner.pages.borrow();
        let mut boxed_used_pages = 0usize;
        let mut unboxed_used_pages = 0usize;

        for (idx, pg) in pages.iter().enumerate() {
            if pg.flags.contains(PageFlags::Large) {
                panic!(
                    "unexpected Large page from small TLAB-based allocs (page {})",
                    idx
                );
            }
            if pg.flags.contains(PageFlags::Used) {
                match pg.page_type() {
                    PageType::Boxed => boxed_used_pages += 1,
                    PageType::Unboxed => unboxed_used_pages += 1,
                }
            }
        }

        assert!(
            boxed_used_pages > 0,
            "expected at least one boxed page in use after mixed allocations"
        );
        assert!(
            unboxed_used_pages > 0,
            "expected at least one unboxed page in use after mixed allocations"
        );
    }

    #[derive(Debug)]
    struct TestObj {
        pub x: i64,
    }

    impl Visitable for TestObj {}
    impl Object for TestObj {}
    impl HeapObject for TestObj {}

    fn boxed_obj(x: i64) -> Box<TestObj> {
        Box::new(TestObj { x })
    }

    #[test]
    fn new_handle_set_has_zero_bump_and_no_prev_next() {
        let hs = HandleSet::new();
        assert_eq!(hs.bump, 0);
        assert!(hs.prev.is_none());
        assert!(hs.next.is_none());
    }

    #[test]
    fn linking_prev_and_next_sets_works() {
        let mut first = HandleSet::new();
        let mut second = HandleSet::new();

        second.link_prev(&mut first);

        assert!(first.next.is_some());
        assert!(second.prev.is_some());

        let next_ptr = first.next.unwrap();
        assert_eq!(next_ptr.as_ptr(), &second as *const _ as *mut _);

        let prev_ptr = second.prev.unwrap();
        assert_eq!(prev_ptr.as_ptr(), &mut first as *mut _);
    }

    #[test]
    fn promote_stores_value_and_increments_bump() {
        let mut set = HandleSet::new();

        let mut obj = boxed_obj(123);
        let tagged = Tagged::<TestObj>::new_ptr(&mut *obj);

        let h = set.promote(tagged);

        assert_eq!(set.bump, 1);

        assert_eq!(h.x, 123);
    }

    #[test]
    #[should_panic(expected = "Handle Set full")]
    fn promote_panics_when_full() {
        let mut set = HandleSet::new();

        for idx in 0..HANDLE_SET_SIZE {
            let mut obj = boxed_obj(idx as i64);
            let tagged = Tagged::<TestObj>::new_ptr(obj.as_mut());
            set.promote(tagged);
        }

        let mut extra = boxed_obj(99);
        let extra_tagged = Tagged::<TestObj>::new_ptr(&mut *extra);
        set.promote(extra_tagged);
    }

    #[test]
    #[should_panic(
        expected = "Handle Set cannot be dropped while other depends on it"
    )]
    fn dropping_set_with_next_panics() {
        let mut first = HandleSet::new();
        let mut second = HandleSet::new();
        second.link_prev(&mut first);

        drop(first);
    }

    #[test]
    fn dropping_child_unlinks_from_prev() {
        let mut parent = HandleSet::new();

        {
            let mut child = HandleSet::new();
            child.link_prev(&mut parent);
            assert!(parent.next.is_some());
            drop(child);
        }

        // parent.next must be None again
        assert!(parent.next.is_none());
    }

    #[test]
    fn visitable_handleset_visits_all_handles_including_next() {
        #[derive(Debug)]
        struct CollectVisitor {
            pub visited: Rc<RefCell<Vec<Value>>>,
        }

        impl Visitor for CollectVisitor {
            fn visit(&self, value: Value) {
                self.visited.borrow_mut().push(value);
            }
        }

        let visited = Rc::new(RefCell::new(Vec::new()));
        let visitor = CollectVisitor {
            visited: visited.clone(),
        };

        let mut first = HandleSet::new();
        let mut second = HandleSet::new();
        second.link_prev(&mut first);

        let mut o1 = boxed_obj(1);
        let mut o2 = boxed_obj(2);
        let mut o3 = boxed_obj(3);

        let t1 = Tagged::<TestObj>::new_ptr(&mut *o1);
        let t2 = Tagged::<TestObj>::new_ptr(&mut *o2);
        let t3 = Tagged::<TestObj>::new_ptr(&mut *o3);

        first.promote(t1);
        first.promote(t2);
        second.promote(t3);

        first.visit_edges(&visitor);

        let visited_vals = visited.borrow().clone();

        let expected = vec![t1.as_value(), t2.as_value(), t3.as_value()];

        assert_eq!(
            visited_vals, expected,
            "Visitor did not record expected handle values"
        );
    }
}
