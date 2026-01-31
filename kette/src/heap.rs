//! Immix garbage collector implementation.
//!
//! Uses coarse-grained blocks and fine-grained lines for efficient bump allocation
//! and opportunistic evacuation. Supports parallel GC with barrier synchronization.

use std::{
    alloc::Layout,
    mem,
    ops::Deref,
    ptr::{self, NonNull},
    sync::{
        Arc, Mutex,
        atomic::{AtomicU8, AtomicU32, AtomicUsize, Ordering},
    },
};

use crate::{
    ActivationStack, Allocator, ExecutionState, FLAG_REMEMBERED, Handle,
    HeapValue, OS_PAGE_SIZE, SenseBarrier, Value, Visitable, Visitor, system,
};

/// Configuration for the Immix heap structure.
///
/// Defines the hierarchy of coarse-grained Blocks and fine-grained Lines.
#[derive(Debug)]
pub struct HeapSettings {
    /// Total size of the heap in bytes. Must be a multiple of `block_size`.
    pub heap_size: usize,
    /// Size of a Block (coarse-grained region). Must be a multiple of OS page size (typ. 32KB).
    pub block_size: usize,
    /// Size of a Line (fine-grained marking unit). Must divide `block_size` (typ. 128B).
    pub line_size: usize,
    /// Size of an object before it gets allocated with mmap.
    /// should be at most size of block
    pub large_size: usize,
    /// Memory usage threshold (0.0 - 1.0) relative to heap size to trigger GC.
    pub bytes_before_gc: f64,
    /// Fraction of heap reserved for the nursery (0.0 - 1.0).
    pub nursery_fraction: f64,
    /// Ratio of marked lines (0.0 - 1.0) below which a block is considered "mostly empty"
    /// and recycled during Minor GC. Default 0.10 (10%).
    pub minor_recycle_threshold: f64,
    /// Number of consecutive minor GCs allowed before forcing a major cycle.
    pub max_minor_before_major: u32,
}

impl Default for HeapSettings {
    fn default() -> Self {
        Self {
            heap_size: 536_870_912,       // 512 MB
            block_size: 32_768,           // 32 KB = 2^15
            large_size: 8_176, // 8 KB - (Header + counter) = 2^13 - 16
            line_size: 128,    // 128 Bytes
            bytes_before_gc: 0.05, // 5%
            nursery_fraction: 0.05, // 5%
            minor_recycle_threshold: 0.1, // 10%
            max_minor_before_major: 10,
        }
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GcStatus {
    None = 0,
    MinorRequested = 1,
    MajorRequested = 2,
}

#[derive(Debug)]
pub struct GcState(std::sync::atomic::AtomicU64);

/// Static runtime parameters derived from settings.
#[derive(Debug)]
pub struct RuntimeInfo {
    pub block_count: usize,
    pub line_count: usize,
    pub lines_per_block: usize,
    pub minor_threshold: usize,
    pub major_threshold: usize,
    pub minor_recycle_threshold: usize,
    pub max_minor_before_major: u32,
}

/// Global atomic counters for allocation tracking.
#[derive(Debug)]
pub struct Trackers {
    /// Cursor for acquiring fresh, previously unused blocks.
    pub fresh_block_cursor: AtomicUsize,
    /// Current global epoch used to validate line liveness without clearing bitmaps.
    pub epoch: AtomicU8,
    pub minor_allocated: AtomicUsize,
    pub major_allocated: AtomicUsize,
    pub minor_since_major: AtomicU32,
}

/// Synchronization state for parallel GC rendezvous.
#[derive(Debug)]
pub struct SyncState {
    /// state of the GC, is a packed Atomicu64
    /// (status, generation, threads)
    pub state: GcState,

    /// Single Sense Barrier that lets threads sleep
    /// until the last one arrives and wakes up all
    pub barrier: SenseBarrier,

    /// Thread-local root sets submitted by mutators.
    pub inputs: Mutex<Vec<RootSet>>,
    /// Partitioned work queues for parallel marking.
    pub work_distribution: Mutex<Vec<RootSet>>,
}

impl SyncState {
    fn new() -> Self {
        Self {
            state: GcState::new(),
            barrier: SenseBarrier::new(),
            inputs: Mutex::new(Vec::new()),
            work_distribution: Mutex::new(Vec::new()),
        }
    }
}

/// Block is fully free
pub const BLOCK_FREE: u8 = 0;
/// Block is fragmented but contains enough reusable holes.
pub const BLOCK_RECYCLED: u8 = 1;
/// Block is not reusable (until major GC)
pub const BLOCK_UNAVAILABLE: u8 = 2;
pub const NO_BLOCK: usize = usize::MAX;

/// Metadata header for a coarse-grained memory Block.
#[repr(C)]
#[derive(Debug)]
pub struct Block {
    /// Indicates if the block is Free, Recyclable, or Unavailable.
    pub status: AtomicU8,
    /// Intrusive linked list index for `available` or `full_blocks` lists.
    pub next: AtomicUsize,
}

/// Metadata for large allocations
/// Layout: [ LargeObjectHeader | Object Data ]
#[repr(C)]
pub struct LargeAllocation {
    pub size: usize,
    pub alignment: u32,
    pub rc: AtomicU32,
    /// this is the normal object header, the object lays exactly here
    pub object: [HeapValue; 0],
    // ... normal object data here
}

/// Core shared heap state.
#[derive(Debug)]
pub struct HeapInner {
    pub settings: HeapSettings,
    pub info: RuntimeInfo,
    pub track: Trackers,
    pub sync: SyncState,
    pub large_objects: Mutex<Vec<NonNull<LargeAllocation>>>,
    pub heap_start: *mut u8,
    /// List of recyclable blocks containing reusable holes.
    pub available: AtomicUsize,
    /// List of full blocks to be scanned or swept during GC.
    pub full_blocks: AtomicUsize,
    pub blocks: Box<[Block]>,
    /// Byte-map representing line liveness (1 byte per line).
    pub lines: Box<[AtomicU8]>,
}

// SAFETY: HeapInner uses atomic operations and interior mutability for all shared state.
unsafe impl Send for HeapInner {}
// SAFETY: HeapInner uses atomic operations and interior mutability for all shared state.
unsafe impl Sync for HeapInner {}

#[derive(Debug, Clone)]
pub struct Heap(Arc<HeapInner>);

/// Thread-local allocator.
///
/// Manages bump allocation within the current "hole" (cursor to limit).
#[derive(Debug)]
pub struct HeapProxy {
    pub heap: Heap,
    pub remember: Vec<Handle<HeapValue>>,
    pub state: Option<NonNull<ExecutionState>>,
    pub activations: Option<NonNull<ActivationStack>>,
    /// Extra permanent roots (e.g., SpecialObjects) that must survive GC.
    pub permanent_roots: Vec<Handle<HeapValue>>,
    pub minor_allocated: usize,
    pub epoch: u8,
    pub block_status: u8,
    /// Index of the current active Block.
    pub block: usize,
    /// Current allocation cursor.
    pub bump: *mut u8,
    /// Limit of the current free window (hole end or block end).
    pub end: *mut u8,
}

// SAFETY: HeapProxy contains only Send/Sync types and raw pointers used with proper synchronization.
unsafe impl Send for HeapProxy {}
// SAFETY: HeapProxy contains only Send/Sync types and raw pointers used with proper synchronization.
unsafe impl Sync for HeapProxy {}

#[derive(Debug, Default)]
pub struct RootSet {
    roots: Vec<Handle<HeapValue>>,
    remember: Vec<Handle<HeapValue>>,
}

impl HeapProxy {
    /// Allocates memory.
    /// If the current hole is exhausted, searches for a new hole or requests a new block.
    #[inline(always)]
    pub fn allocate(&mut self, layout: Layout) -> NonNull<u8> {
        if layout.size() >= self.heap.settings.large_size {
            return self.allocate_large(layout);
        }

        // Fast path: Current hole has space.
        if let Some(ptr) = self.allocate_on_block(layout) {
            self.minor_allocated += layout.size();
            return ptr;
        }

        // Slow path handles the rest
        self.allocate_slow(layout)
    }

    // Slowpath of the allocation, gc safepoint and get a new page
    #[cold]
    #[inline(never)]
    fn allocate_slow(&mut self, layout: Layout) -> NonNull<u8> {
        self.safepoint();

        if let Some(ptr) = self.allocate_on_block(layout) {
            self.minor_allocated += layout.size();
            return ptr;
        }

        self.exchange_block();

        if let Some(ptr) = self.allocate_on_block(layout) {
            self.minor_allocated += layout.size();
            return ptr;
        }

        self.execute_gc_with_reason(GcStatus::MajorRequested, true);

        if let Some(ptr) = self.allocate_on_block(layout) {
            self.minor_allocated += layout.size();
            return ptr;
        }

        panic!("out of memory");
    }

    /// Bump allocates within the current window.
    ///
    /// If the window is exhausted and the block is `RECYCLED`, scans for the next hole.
    #[inline]
    pub fn allocate_on_block(&mut self, layout: Layout) -> Option<NonNull<u8>> {
        debug_assert!(layout.align().is_power_of_two());

        loop {
            let cur = self.bump as usize;
            let end = self.end as usize;
            let align = layout.align();
            let size = layout.size();

            let aligned = (cur + (align - 1)) & !(align - 1);
            let new_cur = aligned.checked_add(size)?;

            if new_cur <= end {
                // Successful bump allocation
                self.bump = new_cur as *mut u8;
                // SAFETY: aligned is within the window, so NonNull is safe
                return Some(unsafe {
                    NonNull::new_unchecked(aligned as *mut u8)
                });
            }

            // Window exhausted.
            if self.block_status == BLOCK_FREE {
                // Physical end of block reached.
                return None;
            }

            // Recycled block: Scan for the next hole (skip unavailable lines).
            if self.block_status == BLOCK_RECYCLED {
                self.bump = self.end;
                // SAFETY: safe invariant
                unsafe {
                    if !self.find_next_hole() {
                        // No more holes in this block.
                        return None;
                    }
                }
                // Loop continues with the new hole found.
            } else {
                return None;
            }
        }
    }

    /// Retires the current block and acquires a new one from `available` or `fresh` lists.
    pub fn exchange_block(&mut self) {
        if self.block != NO_BLOCK {
            self.heap.push_full(self.block);
        }

        // Commit local stats
        self.heap
            .track
            .minor_allocated
            .fetch_add(self.minor_allocated, Ordering::AcqRel);
        self.minor_allocated = 0;
        self.epoch = self.heap.track.epoch.load(Ordering::Relaxed);

        let mut attempts = 0;
        loop {
            let new_block_idx = self.heap.request_block();
            if new_block_idx == NO_BLOCK {
                if attempts >= 1 {
                    panic!("OOM: No blocks available after major GC");
                }
                attempts += 1;
                self.execute_gc_with_reason(GcStatus::MajorRequested, false);
                continue;
            }

            self.block = new_block_idx;
            // Safety: index guaranteed valid by request_block logic.
            let status =
                unsafe { self.heap.blocks.get_unchecked(new_block_idx) }
                    .status
                    .load(Ordering::Relaxed);
            self.block_status = status;

            self.bump = std::ptr::null_mut();
            self.end = std::ptr::null_mut();

            // Calculate absolute address
            let block_size = self.heap.settings.block_size;
            let heap_start = self.heap.heap_start;
            // SAFETY: safe invariant
            let block_addr = unsafe { heap_start.add(self.block * block_size) };

            // Initialize alloc window
            if status == BLOCK_FREE {
                self.bump = block_addr;
                // SAFETY: safe invariant
                self.end = unsafe { block_addr.add(block_size) };
            } else if status == BLOCK_RECYCLED {
                // SAFETY: safe invariant
                unsafe {
                    if !self.find_next_hole() {
                        panic!("Recycled block returned with no holes");
                    }
                }
            }

            break;
        }
    }

    /// Handles off-heap allocation via system mmap (Large Object Space).
    #[cold]
    fn allocate_large(&mut self, layout: Layout) -> NonNull<u8> {
        // Calculate total size needed: Header + Object + Alignment padding
        let header_size = mem::size_of::<LargeAllocation>();
        let alignment = layout.align().max(mem::align_of::<LargeAllocation>());

        let raw_size = header_size + layout.size() + alignment;

        let raw_ptr = system::map_memory(raw_size)
            .expect("OOM: Large Object allocation failed")
            .as_ptr();

        let raw = raw_ptr as usize;
        let header = mem::size_of::<LargeAllocation>();
        let align = alignment;

        let payload = (raw + header + (align - 1)) & !(align - 1);
        let alloc = (payload - header) as *mut LargeAllocation;
        let payload_ptr = payload as *mut u8;
        // SAFETY: safe invariant
        unsafe {
            // Initialize Header
            ptr::write(
                alloc,
                LargeAllocation {
                    size: raw_size, // We store the actual mapped size for munmap
                    alignment: alignment as u32,
                    rc: AtomicU32::new(1), // 1 implies new or 1 reference
                    object: [],
                },
            );

            let mut lo_list = self
                .heap
                .large_objects
                .lock()
                .expect("TODO: handle poisioning");
            lo_list.push(NonNull::new_unchecked(alloc));

            // we skip this here
            // self.minor_allocated += raw_size;

            NonNull::new_unchecked(payload_ptr)
        }
    }

    /// get the pointer on the heap this block is pointing to
    /// # Safety
    /// must be initialized correctly
    #[inline(always)]
    unsafe fn current_block_start(&self) -> *mut u8 {
        let block_size = self.heap.settings.block_size;
        // SAFETY: safe if initialized correctly
        unsafe { self.heap.heap_start.add(self.block * block_size) }
    }

    /// get ptr from line
    /// # Safety
    /// must be a valid line idx
    #[inline(always)]
    unsafe fn ptr_from_line(&self, line_idx: usize) -> *mut u8 {
        let line_size = self.heap.settings.line_size;
        // SAFETY: must be a valid line in the heap
        unsafe { self.current_block_start().add(line_idx * line_size) }
    }

    /// get line from pointer
    /// # Safety
    /// must be a valid heap pointer
    #[inline(always)]
    unsafe fn line_from_ptr(&self, ptr: *mut u8) -> usize {
        if ptr.is_null() {
            return 0;
        }
        let offset =
            // SAFETY: caller must take pointer that is inside the heap
            unsafe { ptr.offset_from(self.current_block_start()) as usize };
        offset / self.heap.settings.line_size
    }

    #[inline(always)]
    unsafe fn get_line_status(&self, line_idx: usize) -> u8 {
        let lines_per_block = self.heap.info.lines_per_block;
        let global_idx = (self.block * lines_per_block) + line_idx;
        // SAFETY: caller must make sure this is a valid index
        unsafe { self.heap.lines.get_unchecked(global_idx) }
            .load(Ordering::Relaxed)
    }

    /// Linearly scans the block's line map to find the next contiguous free region (hole).
    /// Scans forward from current position to find the next hole (consecutive free lines).
    /// Uses epoch markers to avoid clearing line mark bitmaps.
    /// Updates `self.bump` (cursor) and `self.end` (limit).
    unsafe fn find_next_hole(&mut self) -> bool {
        let lines_per_block = self.heap.info.lines_per_block;
        // SAFETY: safe invariant
        let start_search_idx = unsafe { self.line_from_ptr(self.bump) };

        // 1. Scan for START of hole (skip live lines, mark >= epoch)
        let mut hole_start = start_search_idx;
        while hole_start < lines_per_block {
            // SAFETY: safe invariant
            if unsafe { self.get_line_status(hole_start) < self.epoch } {
                break;
            }
            hole_start += 1;
        }

        if hole_start >= lines_per_block {
            return false;
        }

        // 2. Scan for END of hole (stop at live line)
        let mut hole_end = hole_start + 1;
        while hole_end < lines_per_block {
            // SAFETY: safe invariant
            if unsafe { self.get_line_status(hole_end) >= self.epoch } {
                break;
            }
            hole_end += 1;
        }

        // SAFETY: safe invariant
        self.bump = unsafe { self.ptr_from_line(hole_start) };
        // SAFETY: safe invariant
        self.end = unsafe { self.ptr_from_line(hole_end) };
        true
    }

    /// Checks if GC is required or already in progress.
    #[inline(never)]
    pub fn safepoint(&mut self) {
        let (status, _gen, _threads, _) =
            self.heap.sync.state.load(Ordering::Relaxed);

        if status != GcStatus::None {
            let roots = self.collect_roots();
            self.heap.rendezvous(false, roots);
            self.exchange_block();
            return;
        }

        let limit = self.heap.info.minor_threshold;
        let global_alloc =
            self.heap.track.minor_allocated.load(Ordering::Relaxed);

        if global_alloc + self.minor_allocated > limit {
            self.execute_gc_with_reason(GcStatus::MinorRequested, true);
            return;
        }

        let major_alloc =
            self.heap.track.major_allocated.load(Ordering::Relaxed);
        if major_alloc > self.heap.info.major_threshold {
            self.execute_gc_with_reason(GcStatus::MajorRequested, true);
            return;
        }

        let minor_since_major =
            self.heap.track.minor_since_major.load(Ordering::Relaxed);
        if minor_since_major >= self.heap.info.max_minor_before_major {
            self.execute_gc_with_reason(GcStatus::MajorRequested, true);
        }
    }

    #[cold]
    fn execute_gc_with_reason(
        &mut self,
        requested: GcStatus,
        reacquire_block: bool,
    ) {
        self.heap
            .track
            .minor_allocated
            .fetch_add(self.minor_allocated, Ordering::Relaxed);
        self.minor_allocated = 0;

        let (is_coord, _status, _gen, _participants) =
            self.heap.sync.state.try_start_gc(requested);

        let roots = self.collect_roots();
        self.heap.rendezvous(is_coord, roots);

        if reacquire_block {
            self.exchange_block();
        }
    }

    #[cfg(test)]
    #[cold]
    fn execute_gc(&mut self) {
        self.execute_gc_with_reason(GcStatus::MinorRequested, true);
    }

    #[inline(always)]
    pub fn write_barrier(
        &mut self,
        source: Handle<HeapValue>,
        _target: Handle<HeapValue>,
    ) {
        // Fast Path: Check flag loosely
        let current_flags = source.header.flags.load(Ordering::Relaxed);
        if (current_flags & FLAG_REMEMBERED) != 0 {
            return;
        }

        // Slow Path: Atomically set flag
        let prev_flags = source
            .header
            .flags
            .fetch_or(FLAG_REMEMBERED, Ordering::Relaxed);
        if (prev_flags & FLAG_REMEMBERED) == 0 {
            self.record_remembered_set(source);
        }
    }

    #[cold]
    pub fn record_remembered_set(&mut self, source: Handle<HeapValue>) {
        self.remember.push(source);
    }

    #[must_use]
    pub fn new(heap: Heap) -> Self {
        heap.sync.state.register_thread();
        let epoch = heap.epoch();

        Self {
            heap,
            remember: Vec::with_capacity(32),
            permanent_roots: Vec::new(),
            minor_allocated: 0,
            epoch,
            state: None,
            activations: None,
            block: NO_BLOCK,
            block_status: BLOCK_FREE,
            bump: ptr::null_mut(),
            end: ptr::null_mut(),
        }
    }

    /// Add permanent roots that must survive all GC cycles.
    /// These are typically SpecialObjects like traits, true/false, etc.
    pub fn add_permanent_roots(&mut self, roots: Vec<Handle<HeapValue>>) {
        self.permanent_roots.extend(roots);
    }

    pub fn init_state(
        &mut self,
        state: &mut ExecutionState,
        activations: &mut ActivationStack,
    ) {
        // Safety: We are just storing pointers. Lifetimes are managed by the VM loop.
        self.state = Some(unsafe { NonNull::new_unchecked(state) });
        // Safety: We are just storing pointers. Lifetimes are managed by the VM loop.
        self.activations = Some(unsafe { NonNull::new_unchecked(activations) });
    }

    fn collect_roots(&mut self) -> RootSet {
        let mut roots = Vec::new();

        // Handle ExecutionState roots
        if let Some(mut state_ptr) = self.state {
            // SAFETY: safe if user guarantees to not move
            let state = unsafe { state_ptr.as_mut() };

            // Stack
            for &value in state.stack() {
                if value.is_fixnum() {
                    continue;
                }
                // SAFETY: checked
                let obj = unsafe { value.as_heap_handle_unchecked() };
                roots.push(obj);
            }

            // Return Stack
            for value in state.return_stack() {
                if value.is_fixnum() {
                    continue;
                }
                // SAFETY: checked
                let obj = unsafe { value.as_heap_handle_unchecked() };
                roots.push(obj);
            }
        }

        // Handle ActivationStack roots
        if let Some(mut acts_ptr) = self.activations {
            // SAFETY: safe if user guarantees to not move
            let activations = unsafe { acts_ptr.as_mut() };
            let activation_roots = activations
                .iter()
                .map(|activation| activation.object.as_heap_value_handle());
            roots.extend(activation_roots);
        }

        // Add permanent roots (SpecialObjects, etc.)
        roots.extend(self.permanent_roots.iter().copied());

        // Take local remembered set
        let remember = mem::take(&mut self.remember);

        RootSet { roots, remember }
    }
}

impl Drop for HeapProxy {
    fn drop(&mut self) {
        use std::sync::atomic::Ordering::Acquire;

        // If GC active, we MUST join as a "ghost" participant (empty roots),
        // because we are still counted in threads.
        loop {
            let (status, _gen, _threads, _) =
                self.heap.sync.state.load(Acquire);
            if status == GcStatus::None {
                break;
            }
            self.heap.rendezvous(false, RootSet::default());
            // After rendezvous returns, either GC ended or another started.
            // Loop until we observe None, then deregister safely.
        }

        // Now no GC is active, safe to deregister (CAS-protected against a concurrent start).
        // If a GC starts concurrently, this CAS will fail because status != None,
        // and we will loop and join above.
        //
        // (We enforce this by doing the CAS ourselves here rather than calling
        // deregister_thread() which asserts status==None.)
        loop {
            let (status, generation, threads, cur) =
                self.heap.sync.state.load(Ordering::Acquire);
            if status != GcStatus::None {
                // GC started between our observation and now → join then retry
                self.heap.rendezvous(false, RootSet::default());
                continue;
            }
            let new_threads =
                threads.checked_sub(1).expect("thread count underflow");
            let next = GcState::pack(GcStatus::None, generation, new_threads);
            if self
                .heap
                .sync
                .state
                .0
                .compare_exchange(
                    cur,
                    next,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                )
                .is_ok()
            {
                break;
            }
        }
    }
}

impl HeapInner {
    pub fn new(settings: HeapSettings) -> Self {
        settings.validate().expect("Invalid Heap Settings");

        let block_size = settings.block_size;
        let heap_size = settings.heap_size;
        let line_size = settings.line_size;
        let num_blocks = heap_size / block_size;
        let lines_per_block = block_size / line_size;
        let total_lines = num_blocks * lines_per_block;

        let heap_start = system::map_memory(heap_size)
            .expect("allocate memory")
            .as_ptr();

        debug_assert!((heap_start as usize).is_multiple_of(OS_PAGE_SIZE));

        // Initialize blocks to free
        let mut blocks = Vec::with_capacity(num_blocks);
        for _ in 0..num_blocks {
            blocks.push(Block {
                status: AtomicU8::new(BLOCK_FREE),
                next: AtomicUsize::new(NO_BLOCK),
            });
        }

        // Initialize lines to 0 (fresh)
        let mut lines = Vec::new();
        lines.resize_with(total_lines, || AtomicU8::new(0));

        let info = RuntimeInfo {
            block_count: num_blocks,
            line_count: total_lines,
            lines_per_block,
            minor_threshold: (heap_size as f64 * settings.nursery_fraction)
                as usize,
            major_threshold: (heap_size as f64 * 0.8) as usize,
            minor_recycle_threshold: (lines_per_block as f64
                * settings.minor_recycle_threshold)
                as usize,
            max_minor_before_major: settings.max_minor_before_major,
        };

        let track = Trackers {
            fresh_block_cursor: AtomicUsize::new(0),
            epoch: AtomicU8::new(1),
            minor_allocated: AtomicUsize::new(0),
            major_allocated: AtomicUsize::new(0),
            minor_since_major: AtomicU32::new(0),
        };

        Self {
            settings,
            info,
            track,
            sync: SyncState::new(),
            large_objects: Mutex::new(Vec::new()),
            heap_start,
            available: AtomicUsize::new(NO_BLOCK),
            full_blocks: AtomicUsize::new(NO_BLOCK),
            blocks: blocks.into_boxed_slice(),
            lines: lines.into_boxed_slice(),
        }
    }

    pub fn epoch(&self) -> u8 {
        self.track.epoch.load(Ordering::Relaxed)
    }

    /// Acquires a block for allocation.
    ///
    /// Prioritizes recycled blocks from `available`, falls back to `fresh_block_cursor`.
    pub fn request_block(&self) -> usize {
        // 1. Try Available List (Recycled)
        if let Some(block) = self.pop_available_block() {
            return block;
        }

        // 2. Try Fresh Cursor
        let total_blocks = self.blocks.len();
        let mut fresh = self.track.fresh_block_cursor.load(Ordering::Relaxed);
        loop {
            if fresh >= total_blocks {
                return NO_BLOCK;
            }
            match self.track.fresh_block_cursor.compare_exchange(
                fresh,
                fresh + 1,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return fresh,
                Err(updated) => fresh = updated,
            }
        }
    }

    pub fn push_full(&self, block_idx: usize) {
        debug_assert_ne!(block_idx, NO_BLOCK);
        let mut head = self.full_blocks.load(Ordering::Relaxed);
        loop {
            // SAFETY: caller must use only valid box indices
            unsafe { self.blocks.get_unchecked(block_idx) }
                .next
                .store(head, Ordering::Relaxed);
            match self.full_blocks.compare_exchange_weak(
                head,
                block_idx,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(new_head) => head = new_head,
            }
        }
    }

    pub fn push_available(&self, block_idx: usize) {
        debug_assert_ne!(block_idx, NO_BLOCK);
        let mut head = self.available.load(Ordering::Relaxed);
        loop {
            // SAFETY: caller must use only valid box indices
            unsafe { self.blocks.get_unchecked(block_idx) }
                .next
                .store(head, Ordering::Relaxed);
            match self.available.compare_exchange_weak(
                head,
                block_idx,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(new_head) => head = new_head,
            }
        }
    }

    pub fn pop_full_block(&self) -> Option<usize> {
        let mut head = self.full_blocks.load(Ordering::Acquire);
        loop {
            if head == NO_BLOCK {
                return None;
            }

            // SAFETY: caller must use only valid box indices
            let next = unsafe { self.blocks.get_unchecked(head) }
                .next
                .load(Ordering::Relaxed);

            match self.full_blocks.compare_exchange_weak(
                head,
                next,
                Ordering::Acquire,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    // Detach the block from the list
                    // SAFETY:  this is safe
                    unsafe { self.blocks.get_unchecked(head) }
                        .next
                        .store(NO_BLOCK, Ordering::Relaxed);
                    return Some(head);
                }
                Err(new_head) => head = new_head,
            }
        }
    }

    pub fn pop_available_block(&self) -> Option<usize> {
        let mut head = self.available.load(Ordering::Relaxed);
        loop {
            if head == NO_BLOCK {
                return None;
            }
            // SAFETY: caller must use only valid box indices
            let next = unsafe { self.blocks.get_unchecked(head) }
                .next
                .load(Ordering::Relaxed);

            match self.available.compare_exchange_weak(
                head,
                next,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    // SAFETY: caller must use only valid box indices
                    unsafe { self.blocks.get_unchecked(head) }
                        .next
                        .store(NO_BLOCK, Ordering::Relaxed);
                    return Some(head);
                }
                Err(new_head) => head = new_head,
            }
        }
    }

    /// Main synchronization barrier for parallel GC.
    /// Implements a 4-phase protocol: submit roots, distribute work, perform GC, wait for completion.
    pub fn rendezvous(&self, is_coordinator: bool, roots: RootSet) {
        use std::sync::atomic::Ordering::Acquire;

        let (status, _generation, participants, _word) =
            self.sync.state.load(Acquire);
        if status == GcStatus::None {
            return;
        }
        let participants = participants as usize;

        // Phase 1: submit roots
        {
            let mut inputs =
                self.sync.inputs.lock().expect("TODO: handle poisioning");
            inputs.push(roots);
        }

        // Barrier 1: everyone arrives (fixed participants)
        self.sync.barrier.wait(participants);

        // Phase 2: coordinator distributes
        if is_coordinator {
            let all_inputs = std::mem::take(
                &mut *self.sync.inputs.lock().expect("TODO: handle poisioning"),
            );
            let roots = all_inputs.into_iter().fold(
                RootSet::default(),
                |mut acc, set| {
                    acc.roots.extend(set.roots);
                    acc.remember.extend(set.remember);
                    acc
                },
            );

            let roots_len = roots.roots.len();
            let remember_len = roots.remember.len();

            let mut roots_iter = roots.roots.into_iter();
            let mut remember_iter = roots.remember.into_iter();

            // distribute in even chunks
            let mut result = Vec::with_capacity(participants);
            for i in 0..participants {
                let roots_count = roots_len / participants
                    + if i < (roots_len % participants) { 1 } else { 0 };
                let remember_count = remember_len / participants
                    + if i < (remember_len % participants) {
                        1
                    } else {
                        0
                    };

                result.push(RootSet {
                    roots: roots_iter.by_ref().take(roots_count).collect(),
                    remember: remember_iter
                        .by_ref()
                        .take(remember_count)
                        .collect(),
                });
            }

            *self
                .sync
                .work_distribution
                .lock()
                .expect("TODO: handle poisioning") = result;
        }

        // Barrier 2: distribution complete
        self.sync.barrier.wait(participants);

        // Phase 3: parallel work
        let my_work = self
            .sync
            .work_distribution
            .lock()
            .expect("TODO: handle poisioning")
            .pop()
            .unwrap_or_default();

        self.execute_parallel_gc_task(
            status,
            my_work,
            participants,
            is_coordinator,
        );

        // Barrier 3: work done
        self.sync.barrier.wait(participants);

        // Coordinator ends GC
        if is_coordinator {
            self.sync.state.finish_gc();
        }

        // Barrier 4: The "Exit Handshake".
        // We MUST wait here. This ensures that NO thread leaves this function
        // until the Coordinator has definitely set the state to None.
        // Without this, a fast worker could leave, see the old 'MinorRequested'
        // status, re-enter rendezvous, and deadlock waiting for a Coordinator
        // that has already left.
        self.sync.barrier.wait(participants);
    }

    pub fn execute_parallel_gc_task(
        &self,
        reason: GcStatus,
        roots: RootSet,
        threads: usize,
        is_coordinator: bool,
    ) {
        match reason {
            GcStatus::MinorRequested => {
                self.minor_gc_marking(roots);
                self.sync.barrier.wait(threads);
                self.minor_gc_sweep();
                if is_coordinator {
                    self.track
                        .minor_since_major
                        .fetch_add(1, Ordering::Relaxed);
                }
            }
            GcStatus::MajorRequested => {
                if is_coordinator {
                    self.advance_epoch();
                }
                self.sync.barrier.wait(threads);
                self.major_gc_marking(roots);
                self.sync.barrier.wait(threads);
                if is_coordinator {
                    self.major_gc_sweep();
                    self.track.minor_since_major.store(0, Ordering::Relaxed);
                }
            }
            _ => {}
        }
    }

    fn minor_gc_marking(&self, roots: RootSet) {
        struct MinorMarkVisitor {
            heap: *const HeapInner,
            queue: *mut Vec<Handle<HeapValue>>,
            epoch: u8,
        }

        impl Visitor for MinorMarkVisitor {
            #[inline(always)]
            fn visit_mut(&mut self, value: Value) {
                // Ignore immediates (integers, etc.)
                if value.is_fixnum() {
                    return;
                }
                debug_assert!(
                    !value.is_header(),
                    "header value encountered in GC visitor"
                );

                // Safety: Validated as not fixnum, assumes valid heap pointer.
                let handle = unsafe { value.as_heap_handle_unchecked() };
                let epoch = self.epoch;

                // FILTER:
                // age == epoch => already marked
                // age == 0 => new, we should mark
                // everything else, we don't care
                if handle
                    .header
                    .age
                    .compare_exchange(
                        0,
                        epoch,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    // SAFETY: this is safe
                    unsafe { (*self.heap).mark_object_line(handle, epoch) };
                    // SAFETY: this is safe
                    unsafe { (*self.queue).push(handle) };
                }
            }
        }

        let RootSet { roots, remember } = roots;

        let mut queue = Vec::new();
        let epoch = self.epoch();

        let mut visitor = MinorMarkVisitor {
            heap: self,
            queue: &mut queue,
            epoch,
        };

        // visit all remember set edges
        for mut obj in remember.iter().copied() {
            obj.visit_edges_mut(&mut visitor);
        }

        // visit all roots
        for obj in roots {
            visitor.visit_mut(obj.into());
        }

        while let Some(mut value) = queue.pop() {
            value.visit_edges_mut(&mut visitor);
        }

        self.clear_remembered_flags(&remember);
    }

    fn major_gc_marking(&self, roots: RootSet) {
        struct MajorMarkVisitor {
            heap: *const HeapInner,
            queue: *mut Vec<Handle<HeapValue>>,
            epoch: u8,
        }

        impl Visitor for MajorMarkVisitor {
            #[inline(always)]
            fn visit_mut(&mut self, value: Value) {
                if value.is_fixnum() {
                    return;
                }
                debug_assert!(
                    !value.is_header(),
                    "header value encountered in GC visitor"
                );

                let handle = unsafe { value.as_heap_handle_unchecked() };

                if handle.header.age.load(Ordering::Relaxed) == self.epoch {
                    return;
                }

                handle.header.age.store(self.epoch, Ordering::Relaxed);
                unsafe { (*self.heap).mark_object_line(handle, self.epoch) };
                unsafe { (*self.queue).push(handle) };
            }
        }

        let RootSet { roots, remember } = roots;
        let mut queue = Vec::new();
        let epoch = self.epoch();
        let mut visitor = MajorMarkVisitor {
            heap: self,
            queue: &mut queue,
            epoch,
        };

        for mut obj in remember.iter().copied() {
            obj.visit_edges_mut(&mut visitor);
        }

        for obj in roots {
            visitor.visit_mut(obj.into());
        }

        while let Some(mut value) = queue.pop() {
            value.visit_edges_mut(&mut visitor);
        }

        self.clear_remembered_flags(&remember);
    }

    fn clear_remembered_flags(&self, objects: &[Handle<HeapValue>]) {
        for obj in objects {
            obj.header
                .flags
                .fetch_and(!FLAG_REMEMBERED, Ordering::Relaxed);
        }
    }

    fn advance_epoch(&self) -> u8 {
        use std::sync::atomic::Ordering::*;
        loop {
            let current = self.track.epoch.load(Relaxed);
            let mut next = current.wrapping_add(1);
            if next == 0 {
                next = 1;
            }
            match self
                .track
                .epoch
                .compare_exchange(current, next, Release, Relaxed)
            {
                Ok(_) => return next,
                Err(_) => continue,
            }
        }
    }

    pub fn minor_gc_sweep(&self) {
        let epoch = self.epoch();
        let lines_per_block = self.info.lines_per_block;
        let recycle_threshold = self.info.minor_recycle_threshold;

        // pop blocks until the list is empty.
        // This distributes the sweeping work across all threads naturally.
        while let Some(block_idx) = self.pop_full_block() {
            let start_line_idx = block_idx * lines_per_block;
            let end_line_idx = start_line_idx + lines_per_block;

            // Count live lines in this block
            let mut marked_lines = 0;

            // We use the raw pointer for performance, avoiding bounds checks in the loop.
            // Safety: Indices are calculated based on fixed block sizes.

            for i in start_line_idx..end_line_idx {
                // In Minor GC, "Live" means strictly equal to the current epoch.
                // 0 = Fresh/Unallocated.
                // Old Epoch = Dead (treated as free by allocator).
                // SAFETY: caller must make sure this is a valid index
                if unsafe { self.lines.get_unchecked(i) }
                    .load(Ordering::Relaxed)
                    == epoch
                {
                    marked_lines += 1;
                }
            }

            if marked_lines > recycle_threshold {
                // Case 1: The block is mostly full.
                // We mark it unavailable and DO NOT return it to the `available` list.
                // It effectively "disappears" from the allocator's view until the
                // next Major GC scans the whole heap.
                // SAFETY: caller must use only valid box indices
                unsafe { self.blocks.get_unchecked(block_idx) }
                    .status
                    .store(BLOCK_UNAVAILABLE, Ordering::Relaxed);
            } else if marked_lines == 0 {
                // Case 2: The block is completely empty.
                // Mark as Free and make available immediately.
                // SAFETY: caller must use only valid box indices
                unsafe { self.blocks.get_unchecked(block_idx) }
                    .status
                    .store(BLOCK_FREE, Ordering::Relaxed);
                self.push_available(block_idx);
            } else {
                // Case 3: The block is fragmented but has space (<= threshold).
                // Mark as Recycled and make available immediately.
                // SAFETY: caller must use only valid box indices
                unsafe { self.blocks.get_unchecked(block_idx) }
                    .status
                    .store(BLOCK_RECYCLED, Ordering::Relaxed);
                self.push_available(block_idx);
            }
        }
    }

    fn major_gc_sweep(&self) {
        let epoch = self.epoch();
        let lines_per_block = self.info.lines_per_block;
        let recycle_threshold = self.info.minor_recycle_threshold;
        let block_size = self.settings.block_size;
        let block_count = self.info.block_count;

        self.available.store(NO_BLOCK, Ordering::Relaxed);
        self.full_blocks.store(NO_BLOCK, Ordering::Relaxed);

        let mut sticky_blocks = 0usize;

        for block_idx in 0..block_count {
            let start_line_idx = block_idx * lines_per_block;
            let end_line_idx = start_line_idx + lines_per_block;

            let mut marked_lines = 0usize;

            for i in start_line_idx..end_line_idx {
                let byte = unsafe { self.lines.get_unchecked(i) }
                    .load(Ordering::Relaxed);
                if byte == epoch {
                    marked_lines += 1;
                } else {
                    unsafe { self.lines.get_unchecked(i) }
                        .store(0, Ordering::Relaxed);
                }
            }

            let block = unsafe { self.blocks.get_unchecked(block_idx) };
            block.next.store(NO_BLOCK, Ordering::Relaxed);

            if marked_lines == 0 {
                block.status.store(BLOCK_FREE, Ordering::Relaxed);
                self.push_available(block_idx);
            } else if marked_lines <= recycle_threshold {
                block.status.store(BLOCK_RECYCLED, Ordering::Relaxed);
                self.push_available(block_idx);
            } else {
                block.status.store(BLOCK_UNAVAILABLE, Ordering::Relaxed);
                sticky_blocks += 1;
            }
        }

        let large_bytes = self.sweep_large_objects(epoch);
        let sticky_bytes = sticky_blocks * block_size;

        self.track
            .major_allocated
            .store(sticky_bytes + large_bytes, Ordering::Relaxed);
    }

    fn sweep_large_objects(&self, epoch: u8) -> usize {
        use std::sync::atomic::Ordering::Relaxed;

        let mut live_bytes = 0usize;
        let mut large_objects =
            self.large_objects.lock().expect("TODO: handle poisioning");

        large_objects.retain(|alloc| {
            let allocation = unsafe { alloc.as_ref() };
            let object_ptr = allocation.object.as_ptr() as *mut HeapValue;
            if object_ptr.is_null() {
                return false;
            }

            let header = unsafe { &(*object_ptr).header };
            if header.age.load(Relaxed) == epoch {
                live_bytes += allocation.size;
                true
            } else {
                let raw = alloc.cast::<u8>();
                system::unmap_memory(raw, allocation.size);
                false
            }
        });

        live_bytes
    }

    /// Calculates the global line index for a pointer within the heap.
    /// Optimized: `(ptr - start) / line_size` is mathematically equivalent to
    /// calculating block indices + offsets, provided `line_size` divides `block_size`.
    #[inline(always)]
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    pub fn line_index_for(&self, ptr: *const u8) -> usize {
        // SAFETY: Caller ensures ptr is within the heap range.
        let heap_offset = unsafe { ptr.offset_from(self.heap_start) } as usize;
        heap_offset / self.settings.line_size
    }

    /// Marks the line corresponding to the object as live with the given epoch.
    #[inline(always)]
    pub fn mark_object_line(&self, obj: Handle<HeapValue>, epoch: u8) {
        let idx = self.line_index_for(obj.as_ptr() as *const u8);
        // SAFETY: this is safe
        unsafe {
            self.lines
                .get_unchecked(idx)
                .store(epoch, Ordering::Relaxed)
        }
    }

    /// Reads the current epoch/status of the line corresponding to the object.
    #[inline(always)]
    pub fn get_object_line_status(&self, obj: Handle<HeapValue>) -> u8 {
        let idx = self.line_index_for(obj.as_ptr() as *const u8);

        // SAFETY: caller must make sure this is a valid index
        unsafe { self.lines.get_unchecked(idx) }.load(Ordering::Relaxed)
    }
}

impl Allocator for HeapProxy {
    fn allocate(&mut self, layout: Layout) -> NonNull<u8> {
        self.allocate(layout)
    }
}

impl Heap {
    #[must_use]
    pub fn new(settings: HeapSettings) -> Self {
        let inner = HeapInner::new(settings);
        Self(Arc::new(inner))
    }

    #[must_use]
    pub fn proxy(&self) -> HeapProxy {
        HeapProxy::new(self.clone())
    }
}

impl Deref for Heap {
    type Target = HeapInner;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl HeapSettings {
    #[inline]
    fn validate(&self) -> Result<(), &'static str> {
        if self.heap_size == 0 || self.block_size == 0 || self.line_size == 0 {
            return Err("Sizes must be > 0");
        }
        if !self.block_size.is_multiple_of(OS_PAGE_SIZE) {
            return Err("block_size must match OS page alignment");
        }
        if !self.heap_size.is_multiple_of(self.block_size) {
            return Err("heap_size must be a multiple of block_size");
        }
        if !self.block_size.is_multiple_of(self.line_size) {
            return Err("line_size must divide block_size");
        }
        if self.block_size > (u16::MAX as usize) {
            return Err("block_size too large for metadata");
        }
        if self.large_size > self.block_size {
            return Err("large size must be smaller or equal to block_size");
        }
        if !(0.0..=1.0).contains(&self.nursery_fraction)
            || !(0.0..=1.0).contains(&self.bytes_before_gc)
            || !(0.0..=1.0).contains(&self.minor_recycle_threshold)
        {
            return Err("Fractions must be between 0.0 and 1.0");
        }
        if self.max_minor_before_major == 0 {
            return Err("max_minor_before_major must be > 0");
        }
        Ok(())
    }
}

impl From<u8> for GcStatus {
    fn from(val: u8) -> Self {
        match val {
            1 => GcStatus::MinorRequested,
            2 => GcStatus::MajorRequested,
            _ => GcStatus::None,
        }
    }
}

impl GcState {
    const STATUS_MASK: u64 = 0b11;
    const GEN_SHIFT: u32 = 2;
    const GEN_MASK: u64 = (1u64 << 30) - 1; // 30 bits
    const THREADS_SHIFT: u32 = 32;

    #[inline(always)]
    fn pack(status: GcStatus, generation: u32, threads: u32) -> u64 {
        debug_assert!((generation as u64) <= Self::GEN_MASK);
        (status as u64)
            | ((generation as u64) << Self::GEN_SHIFT)
            | ((threads as u64) << Self::THREADS_SHIFT)
    }

    #[inline(always)]
    fn unpack(word: u64) -> (GcStatus, u32, u32) {
        let status = match (word & Self::STATUS_MASK) as u8 {
            1 => GcStatus::MinorRequested,
            2 => GcStatus::MajorRequested,
            _ => GcStatus::None,
        };
        let generation = ((word >> Self::GEN_SHIFT) & Self::GEN_MASK) as u32;
        let threads = (word >> Self::THREADS_SHIFT) as u32;
        (status, generation, threads)
    }

    pub fn new() -> Self {
        Self(std::sync::atomic::AtomicU64::new(Self::pack(
            GcStatus::None,
            0,
            0,
        )))
    }

    // status generation threads raw
    #[inline(always)]
    pub fn load(
        &self,
        ord: std::sync::atomic::Ordering,
    ) -> (GcStatus, u32, u32, u64) {
        let w = self.0.load(ord);
        let (s, g, t) = Self::unpack(w);
        (s, g, t, w)
    }

    /// Register a mutator thread. Only allowed when GC is not active.
    pub fn register_thread(&self) {
        use std::sync::atomic::Ordering::*;
        loop {
            let (status, generation, threads, cur) = self.load(Acquire);
            if status != GcStatus::None {
                // Not counted as a participant yet; do NOT join barriers.
                // Just wait until GC ends.
                std::thread::yield_now();
                continue;
            }
            let new_threads =
                threads.checked_add(1).expect("thread count overflow");
            let next = Self::pack(status, generation, new_threads);
            if self.0.compare_exchange(cur, next, AcqRel, Acquire).is_ok() {
                return;
            }
        }
    }

    /// Deregister a mutator thread. Only allowed when GC is not active.
    /// Caller must ensure it has joined during any GC.
    pub fn deregister_thread(&self) {
        use std::sync::atomic::Ordering::*;
        loop {
            let (status, generation, threads, cur) = self.load(Acquire);
            debug_assert_eq!(
                status,
                GcStatus::None,
                "must not deregister during GC"
            );
            let new_threads =
                threads.checked_sub(1).expect("thread count underflow");
            let next = Self::pack(status, generation, new_threads);
            if self.0.compare_exchange(cur, next, AcqRel, Acquire).is_ok() {
                return;
            }
        }
    }

    /// Attempt to start a GC cycle (coordinator election).
    /// Returns (is_coordinator, status, generation, participants)
    pub fn try_start_gc(
        &self,
        requested: GcStatus,
    ) -> (bool, GcStatus, u32, u32) {
        use std::sync::atomic::Ordering::*;
        loop {
            let (status, generation, threads, cur) = self.load(Acquire);
            if status != GcStatus::None {
                // Someone else is running/starting GC
                return (false, status, generation, threads);
            }
            let new_gen = generation.wrapping_add(1) & (Self::GEN_MASK as u32);
            let next = Self::pack(requested, new_gen, threads);
            match self.0.compare_exchange(cur, next, AcqRel, Acquire) {
                Ok(_) => return (true, requested, new_gen, threads),
                Err(_) => continue,
            }
        }
    }

    /// End GC (coordinator only). Leaves generation and threads unchanged.
    pub fn finish_gc(&self) {
        use std::sync::atomic::Ordering::*;
        loop {
            let (status, generation, threads, cur) = self.load(Acquire);
            if status == GcStatus::None {
                return;
            }
            let next = Self::pack(GcStatus::None, generation, threads);
            if self.0.compare_exchange(cur, next, AcqRel, Acquire).is_ok() {
                return;
            }
        }
    }
}

impl Default for GcState {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod gc_tests {
    use crate::{
        ExecutionStateInfo, Header, HeapObject, Object, ObjectKind, ObjectType,
    };

    use super::*;
    use std::sync::Arc;

    // Some test object
    #[repr(C)]
    struct TestObj {
        header: Header,
        payload: [usize; 3], // Some payload
    }

    impl Visitable for TestObj {}
    impl Object for TestObj {}
    impl HeapObject for TestObj {
        const KIND: ObjectKind = ObjectKind::Object;
        const TYPE_BITS: u8 = ObjectType::Array as u8; // Reuse Array type for test
        fn heap_size(&self) -> usize {
            mem::size_of::<Self>()
        }
    }

    fn create_test_settings() -> HeapSettings {
        HeapSettings {
            heap_size: 1024 * 1024, // 1 MB Total
            block_size: 8192,       // 8 KB Blocks
            large_size: 4096 - 16,  // 4 KB
            line_size: 64,          // 64 Byte Lines
            bytes_before_gc: 0.1,   // Trigger GC fast (10% of heap)
            nursery_fraction: 0.1,  // Large nursery for testing
            minor_recycle_threshold: 0.5,
            max_minor_before_major: 3,
        }
    }

    fn create_test_env()
    -> (Heap, HeapProxy, Box<ExecutionState>, Box<ActivationStack>) {
        let settings = create_test_settings();
        let heap_inner = Arc::new(HeapInner::new(settings));
        let heap = Heap(heap_inner.clone());
        let mut proxy = HeapProxy::new(heap.clone());

        let state_info = ExecutionStateInfo {
            stack_size: 1024,
            return_stack_size: 1024,
        };

        // Allocate on the heap immediately via Box::new
        let mut state = Box::new(ExecutionState::new(&state_info));
        let mut acts = Box::new(ActivationStack::default());

        // Link the proxy to the heap memory address
        // &mut *state dereferences the Box to get the mutable struct,
        // but the struct stays at the same heap address.
        proxy.init_state(state.as_mut(), acts.as_mut());

        (heap, proxy, state, acts)
    }

    #[test]
    fn test_allocation_basic() {
        let (_heap, mut proxy, _, _) = create_test_env();

        let layout = Layout::new::<TestObj>();
        let ptr1 = proxy.allocate(layout);

        // Check alignment and pointer validity
        assert_eq!(ptr1.as_ptr() as usize % layout.align(), 0);

        let ptr2 = proxy.allocate(layout);
        assert!(ptr2.as_ptr() as usize > ptr1.as_ptr() as usize);

        // Ensure allocation counted locally
        assert!(proxy.minor_allocated > 0);
    }

    #[test]
    fn test_block_exhaustion_and_switch() {
        let (heap, mut proxy, _state, _activations) = create_test_env();
        let layout = Layout::from_size_align(1024, 8).unwrap(); // 1KB objects

        // 1. Alloc until nearly full
        let _ptr1 = proxy.allocate(layout);
        let initial_block = proxy.block;

        // 2. Alloc enough to force new block (4KB block size, alloc 4x 1KB = full)
        for _ in 0..8 {
            proxy.allocate(layout);
        }

        // 3. Verify we moved to a new block
        assert_ne!(proxy.block, initial_block);

        // 4. Verify old block is in full_blocks list
        let full_head = heap.full_blocks.load(Ordering::Relaxed);
        assert_ne!(full_head, NO_BLOCK);
    }

    #[test]
    fn test_minor_gc_trigger_and_safepoint() {
        let (heap, mut proxy, mut state, _activations) = create_test_env();

        // 1. Create a "Live" object and push to stack
        let layout = Layout::new::<TestObj>();
        let ptr = proxy.allocate(layout);

        // Initialize header so the GC (if it scans linearly) sees a valid object
        let header = unsafe { &mut *(ptr.as_ptr() as *mut Header) };
        *header = Header::new_object(ObjectType::Array);

        let handle = unsafe {
            Handle::<TestObj>::from_ptr(ptr.as_ptr() as *mut TestObj)
        };
        state.push(handle.into()); // Root

        // 2. Allocate garbage until GC triggers
        // Threshold is 10% of 1MB = 100KB.
        // large_size is ~4KB. We allocate 2KB to stay in the nursery (small object path).
        let allocation_size = 2048;
        let small_layout = Layout::from_size_align(allocation_size, 8).unwrap();

        let (_s, start_gen, _, _) = heap.sync.state.load(Ordering::Relaxed);

        // 60 * 2048 = 122,880 bytes > 100,000 bytes (threshold)
        for _ in 0..100 {
            let _garbage = proxy.allocate(small_layout);
        }

        let (_s, end_gen, _, _) = heap.sync.state.load(Ordering::Relaxed);

        // 3. Verify GC Triggered
        assert!(
            end_gen > start_gen,
            "GC should have triggered (generation count increased)"
        );

        // 4. Verify Live Object Marked
        let line_status =
            heap.get_object_line_status(handle.as_heap_value_handle());
        let epoch = heap.epoch();

        assert_eq!(
            line_status, epoch,
            "Live object should be marked with current epoch"
        );
    }

    #[test]
    fn test_garbage_sweeping_same_line() {
        let (heap, mut proxy, mut state, _activations) = create_test_env();
        let layout = Layout::new::<TestObj>();

        // 1. Alloc object A (Live)
        let ptr_a = proxy.allocate(layout);
        // Zero memory to ensure clean state
        unsafe {
            ptr_a.as_ptr().write_bytes(0, layout.size());
        }

        let header_a = unsafe { &mut *(ptr_a.as_ptr() as *mut Header) };
        *header_a = Header::new_object(ObjectType::Array);

        let handle_a = unsafe {
            Handle::<TestObj>::from_ptr(ptr_a.as_ptr() as *mut TestObj)
        };
        state.push(handle_a.into());

        // 2. Alloc object B (Dead - not on stack)
        let ptr_b = proxy.allocate(layout);
        unsafe {
            ptr_b.as_ptr().write_bytes(0, layout.size());
        }

        let header_b = unsafe { &mut *(ptr_b.as_ptr() as *mut Header) };
        *header_b = Header::new_object(ObjectType::Array);

        let handle_b = unsafe {
            Handle::<TestObj>::from_ptr(ptr_b.as_ptr() as *mut TestObj)
        };

        proxy.execute_gc();

        let epoch = heap.epoch();
        let status_a =
            heap.get_object_line_status(handle_a.as_heap_value_handle());
        let status_b =
            heap.get_object_line_status(handle_b.as_heap_value_handle());

        assert_eq!(status_a, epoch, "Root object line must be marked");
        assert_eq!(status_b, epoch, "Dead object line must be marked from a");
        assert_eq!(header_a.age(), 1, "Root object must be marked");
        assert_ne!(header_b.age(), 1, "Dead object must not be marked");
    }

    #[test]
    fn test_garbage_sweeping_new_line() {
        let (heap, mut proxy, mut state, _activations) = create_test_env();
        let layout = Layout::new::<TestObj>();

        let line_size = heap.settings.line_size; // 64 in your test settings

        let ptr_a = proxy.allocate(layout);
        unsafe {
            ptr_a.as_ptr().write_bytes(0, layout.size());
        }
        let header_a = unsafe { &mut *(ptr_a.as_ptr() as *mut Header) };
        *header_a = Header::new_object(ObjectType::Array);
        let handle_a = unsafe {
            Handle::<TestObj>::from_ptr(ptr_a.as_ptr() as *mut TestObj)
        };
        state.push(handle_a.into());

        let padding_layout = Layout::from_size_align(line_size, 8).unwrap();
        proxy.allocate(padding_layout);

        let ptr_b = proxy.allocate(layout);
        unsafe {
            ptr_b.as_ptr().write_bytes(0, layout.size());
        }
        let header_b = unsafe { &mut *(ptr_b.as_ptr() as *mut Header) };
        *header_b = Header::new_object(ObjectType::Array);
        let handle_b = unsafe {
            Handle::<TestObj>::from_ptr(ptr_b.as_ptr() as *mut TestObj)
        };

        proxy.execute_gc();

        let epoch = heap.epoch();
        let status_a =
            heap.get_object_line_status(handle_a.as_heap_value_handle());
        let status_b =
            heap.get_object_line_status(handle_b.as_heap_value_handle());

        assert_eq!(status_a, epoch, "Root object (Line A) must be marked");

        assert_ne!(status_b, epoch, "Dead object (Line B) must not be marked");
        assert_eq!(status_b, 0, "Dead object line should remain 0");
    }

    #[test]
    fn test_sweeping_logic_recycled() {
        let (heap, mut proxy, _state, _activations) = create_test_env();
        let layout = Layout::new::<TestObj>();

        // FIX 1: Lazy init - ensure we have a valid block index to start
        proxy.allocate(layout);
        let dead_block_idx = proxy.block;
        assert_ne!(dead_block_idx, NO_BLOCK);

        // 1. Fill the block
        // We rely on the internal check inside allocate() to switch blocks
        while proxy.block == dead_block_idx {
            proxy.allocate(layout);
        }

        // 2. Trigger GC
        // This will: Sweep dead_block -> Push to Available -> exchange_block() -> Pop from Available
        proxy.execute_gc();

        // 3. Verify status (It should be marked FREE/RECYCLED globally)
        let status = heap.blocks[dead_block_idx].status.load(Ordering::Relaxed);
        assert_eq!(status, BLOCK_FREE, "Empty block should be marked free");

        // 4. Verify Recycling
        // Since it was the only available block, the proxy should have grabbed it immediately.
        // It is NOT in the list, it is in the proxy!
        assert_eq!(
            proxy.block, dead_block_idx,
            "The freed block should have been immediately recycled by the proxy"
        );
    }

    #[test]
    fn test_recycling_multiple_blocks() {
        use std::collections::HashSet;

        let (heap, mut proxy, _state, _activations) = create_test_env();
        let layout = Layout::new::<TestObj>();

        let mut touched_blocks = HashSet::new();

        // 1. Force lazy init and track the first block
        proxy.allocate(layout);
        touched_blocks.insert(proxy.block);
        let mut current_block = proxy.block;

        // We want to fill 3 full blocks. This forces the allocator to move to a 4th block.
        // Total touched blocks = 4.
        let target_flushed_blocks = 3;
        let mut flushes = 0;

        while flushes < target_flushed_blocks {
            proxy.allocate(layout);

            // Detect if the allocator switched blocks
            if proxy.block != current_block {
                flushes += 1;
                current_block = proxy.block;
                touched_blocks.insert(current_block);
            }
        }

        let total_blocks_used = touched_blocks.len();
        assert_eq!(
            total_blocks_used, 4,
            "3 flushed means we must now have 4 blocks used"
        );

        // 3. Trigger GC
        // Logic:
        // 1. Blocks 1, 2, 3 are in `full_blocks`. Sweep frees them -> `available`.
        // 2. Block 4 is in `proxy.block`. It is NOT swept yet.
        // 3. GC ends. `exchange_block` runs.
        // 4. Block 4 pushed to `full_blocks`.
        // 5. Proxy pops Block 1 (or 2 or 3) from `available`.
        proxy.execute_gc();

        assert!(
            touched_blocks.contains(&proxy.block),
            "Proxy should have recycled one of the dirtied blocks"
        );

        let mut available_count = 0;
        let mut head = heap.available.load(Ordering::Relaxed);

        while head != NO_BLOCK {
            if touched_blocks.contains(&head) {
                available_count += 1;
            }
            head = heap.blocks[head].next.load(Ordering::Relaxed);
        }

        // We used 4 blocks.
        // 1 is held by proxy.
        // 1 (the one active during GC) is in `full_blocks` waiting for next cycle.
        // 2 are in `available`.
        assert_eq!(
            available_count,
            total_blocks_used - 2,
            "Expect (Total - Proxy - UnsweptCurrent) blocks in available"
        );
    }

    #[test]
    fn test_multithreaded_stress() {
        use std::sync::{Arc, Barrier};
        use std::thread;

        let settings = HeapSettings {
            heap_size: 20 * 1024 * 1024, // 20 MB Heap
            block_size: 32 * 1024,       // 32 KB Blocks
            large_size: 8 * 1024,        // 8 KB Large Object threshold
            line_size: 128,              // 128 Byte Lines
            bytes_before_gc: 0.05,       // Trigger GC at 5% usage (Aggressive)
            nursery_fraction: 0.1,
            minor_recycle_threshold: 0.2,
            max_minor_before_major: 5,
        };

        let heap_inner = Arc::new(HeapInner::new(settings));
        let heap = Heap(heap_inner.clone());

        let num_threads = 8;
        // Barrier to ensure all threads start hammering the allocator at the same time
        let start_barrier = Arc::new(Barrier::new(num_threads));
        let mut handles = vec![];

        for i in 0..num_threads {
            let heap_ref = heap.clone();
            let barrier = start_barrier.clone();

            handles.push(thread::spawn(move || {
                // Setup Thread-Local VM State
                // We box these to ensure the memory addresses passed to the proxy
                // stay stable and valid for the lifetime of the thread.
                let state_info = ExecutionStateInfo {
                    stack_size: 2048,
                    return_stack_size: 0,
                };
                let mut state = Box::new(ExecutionState::new(&state_info));
                let mut acts = Box::new(ActivationStack::default());

                let mut proxy = HeapProxy::new(heap_ref);
                proxy.init_state(&mut state, &mut acts);

                // Wait for all threads to be ready
                barrier.wait();

                // Stress Loop
                let layout = Layout::from_size_align(128, 8).unwrap();
                let mut local_seed = i as u64 + 1; // Simple seed per thread

                // Simple LCG random number generator
                // Returns values 0..100
                let next_rand = |seed: &mut u64| -> u64 {
                    *seed =
                        seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                    (*seed >> 32) % 100
                };

                for _ in 0..10_000 {
                    let ptr = proxy.allocate(layout);

                    unsafe {
                        // Initialize Header (Vital for GC scanning/marking)
                        let header = &mut *(ptr.as_ptr() as *mut Header);
                        *header = Header::new_object(ObjectType::Array);

                        let roll = next_rand(&mut local_seed);

                        // 5% chance to push to stack (Root creation)
                        if roll < 5 {
                            let h = Handle::<TestObj>::from_ptr(
                                ptr.as_ptr() as *mut TestObj
                            );

                            if state.depth() < 1000 {
                                state.push(h.into());
                            } else {
                                // Stack full: pop one (create garbage) then push new
                                state.pop();
                                state.push(h.into());
                            }
                        }
                        // 5% chance to pop (Garbage creation)
                        else if roll < 10 && state.depth() > 0 {
                            state.pop();
                        }
                    }
                }
            }));
        }

        for h in handles {
            h.join().expect("Thread panicked");
        }

        let (_, generation, _, _) = heap.sync.state.load(Ordering::Relaxed);

        println!("Stress test finished. Total GC Generations: {}", generation);

        assert!(
            generation > 0,
            "Should have triggered at least one GC cycle"
        );
    }

    #[test]
    fn test_major_gc_reclaims_unreachable_blocks() {
        use std::alloc::Layout;

        let (heap, mut proxy, _state, _acts) = create_test_env();
        let layout = Layout::new::<TestObj>();

        proxy.allocate(layout);
        let first_block = proxy.block;

        while proxy.block == first_block {
            let ptr = proxy.allocate(layout);
            unsafe { ptr.as_ptr().write_bytes(0, layout.size()) };
            let header = unsafe { &mut *(ptr.as_ptr() as *mut Header) };
            *header = Header::new_object(ObjectType::Array);
        }

        proxy.execute_gc_with_reason(GcStatus::MajorRequested, true);

        let status = heap.blocks[first_block].status.load(Ordering::Relaxed);
        assert_eq!(
            status, BLOCK_FREE,
            "Major GC should free completely dead block"
        );
    }

    #[test]
    fn test_major_gc_frees_large_objects() {
        use std::alloc::Layout;

        let (heap, mut proxy, _state, _acts) = create_test_env();
        let size = heap.settings.large_size + 512;
        let layout = Layout::from_size_align(size, 16).unwrap();

        let ptr = proxy.allocate(layout);
        unsafe { ptr.as_ptr().write_bytes(0, layout.size()) };
        let header = unsafe { &mut *(ptr.as_ptr() as *mut Header) };
        *header = Header::new_object(ObjectType::Array);

        proxy.execute_gc_with_reason(GcStatus::MajorRequested, true);

        let large_objects =
            heap.large_objects.lock().expect("TODO: handle poisioning");
        assert!(
            large_objects.is_empty(),
            "Major GC should unmap unreachable large allocations"
        );
    }

    #[test]
    fn test_minor_counter_forces_major() {
        use std::alloc::Layout;

        let (heap, mut proxy, mut state, _acts) = create_test_env();
        let layout = Layout::new::<TestObj>();

        let ptr = proxy.allocate(layout);
        unsafe { ptr.as_ptr().write_bytes(0, layout.size()) };
        let header = unsafe { &mut *(ptr.as_ptr() as *mut Header) };
        *header = Header::new_object(ObjectType::Array);
        let handle = unsafe {
            Handle::<TestObj>::from_ptr(ptr.as_ptr() as *mut TestObj)
        };
        state.push(handle.into());

        heap.track
            .minor_since_major
            .store(heap.info.max_minor_before_major, Ordering::Relaxed);

        proxy.safepoint();

        assert_eq!(
            heap.track.minor_since_major.load(Ordering::Relaxed),
            0,
            "Major GC should reset minor counter when forced via threshold"
        );
    }
}
