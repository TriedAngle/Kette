use core::panic;
use std::{
    alloc::Layout,
    ops::{self, Deref},
    ptr::NonNull,
    sync::{
        Arc, Condvar, Mutex, Weak,
        atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering},
    },
};

use crate::{
    AllocationResult, AllocationType, Allocator, HeapSpace, OS_PAGE_SIZE,
    Search,
};

pub const NONE: usize = usize::MAX;

#[repr(C)]
#[derive(Debug)]
pub struct PageMeta {
    /// Current bump cursor for this page (address).
    bump: AtomicUsize,
    /// AllocationType as u8 for atomic access
    kind: AtomicU8,
    /// Lock-free intrusive list link: page index or NONE
    next: AtomicUsize,
}

impl PageMeta {
    #[inline]
    pub fn kind_load(&self) -> AllocationType {
        match self.kind.load(Ordering::Acquire) {
            0b00 => AllocationType::Free,
            0b01 => AllocationType::Boxed,
            0b10 => AllocationType::Unboxed,
            0b11 => AllocationType::Code,
            _ => unreachable!(),
        }
    }

    #[inline]
    pub fn kind_store(&self, k: AllocationType) {
        self.kind.store(k as u8, Ordering::Release);
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct HeapSettings {
    /// Total Heap size, will be able to dynamically grow later, this should be a sane startup.
    /// must be a multiple of page size
    /// defaults to 2^29 bytes = 536.870912 mb
    pub heap_size: usize,
    /// how big a page is, default is 32kb (32768 bytes) (must be multiple of OS page)
    pub page_size: usize,
    /// granularity of dirtying, 128 bytes by default (must fully divide page_size)
    pub line_size: usize,
    /// Dirty-card granularity for the generational remembered set. Default 512 bytes.
    pub dirty_size: usize,
    /// per generation % of total heap to be allocated before GC runs
    pub bytes_before_gc: f64,
    /// Nursery size as a fraction of the total heap (e.g. 0.05 = 5%).
    /// Rounded up to the nearest page during initialization.
    pub nursery_fraction: f64,
    /// size of allocation window a single thread takes from the heap to then thread locally
    /// allocate, default 4kb (4096)
    pub tlab_size: usize,
}

impl Default for HeapSettings {
    fn default() -> Self {
        Self {
            heap_size: 536_870_912,
            page_size: 32_768,
            dirty_size: 512,
            line_size: 128,
            bytes_before_gc: 0.05,
            nursery_fraction: 0.05,
            tlab_size: 4096,
        }
    }
}

#[derive(Debug)]
pub struct Nursery {
    bump: AtomicUsize,
    end: usize,
}

#[derive(Debug)]
pub struct RuntimeInformation {
    /// Total bytes consumed by allocations (payload + padding).
    pub allocated_total: AtomicUsize,
    /// Total padding waste (alignment) across all allocations.
    pub padding_waste_total: AtomicUsize,
    /// Total amount of freed
    pub freed_total: AtomicUsize,
    /// immix total allocation since last gc
    pub allocated_since_last_gc: AtomicUsize,
}

#[derive(Debug)]
pub struct HeapInfo {
    pub page_count: usize,
    pub line_count: usize,
    pub lines_per_page: usize,
    pub dirty_count: usize,
    pub dirty_per_page: usize,
    pub tlab_large_threshold: usize,
    pub bytes_before_major_gc: usize,
}

#[derive(Debug)]
pub struct HeapImpl {
    /// Settings of Heap
    pub settings: HeapSettings,

    pub heap_start: NonNull<u8>,
    pub nursery: Nursery,

    pub immix_start: NonNull<u8>,
    /// Current write-barrier major_epoch. Lines record the last barrier they got dirtied in
    /// starts at 1, 0 means never dirtied
    pub major_epoch: AtomicU8,
    pub minor_epoch: AtomicU8,
    pub running: AtomicBool,
    pub info: HeapInfo,
    pub track: RuntimeInformation,
    pub gc_monitor: Mutex<()>,
    pub gc_cond: Condvar,
    pub proxies: Mutex<Vec<Weak<ProxyState>>>,
    pub heads: [AtomicUsize; 3],
    pub pages: Box<[PageMeta]>,
    pub lines: Box<[AtomicU8]>,
    pub dirty: Box<[AtomicU8]>,
}

// SAFETY: this is threadsafe
unsafe impl Send for HeapImpl {}
// SAFETY: this is threadsafe
unsafe impl Sync for HeapImpl {}

#[derive(Debug, Clone)]
pub struct Heap(Arc<HeapImpl>);

#[derive(Debug)]
pub struct Tlab {
    page_index: usize,
    cur: NonNull<u8>,
    end: NonNull<u8>,
}

pub const MUTATOR_ACTIVE: u8 = 0;
pub const MUTATOR_PARKED: u8 = 1;

#[derive(Debug)]
pub struct ProxyState {
    pub status: AtomicU8,
}

pub struct NoGcGuard<'a> {
    proxy: &'a mut HeapProxy,
}

impl<'a> NoGcGuard<'a> {
    pub fn new(proxy: &'a mut HeapProxy) -> Self {
        proxy.no_gc_count += 1;
        Self { proxy }
    }
}

impl<'a> Drop for NoGcGuard<'a> {
    fn drop(&mut self) {
        self.proxy.no_gc_count -= 1;
    }
}

impl<'a> std::ops::Deref for NoGcGuard<'a> {
    type Target = HeapProxy;
    fn deref(&self) -> &Self::Target {
        self.proxy
    }
}

#[derive(Debug)]
pub struct HeapProxy {
    pub heap: Heap,
    pub state: Arc<ProxyState>,
    pub epoch: u8,
    pub tlab: Option<Tlab>,
    pub no_gc_count: u32,
}

// SAFETY: this is threadsafe
unsafe impl Send for HeapProxy {}
// SAFETY: this is threadsafe
unsafe impl Sync for HeapProxy {}

impl Heap {
    pub fn new(settings: HeapSettings) -> Self {
        let inner = HeapImpl::new(settings);
        Self(Arc::new(inner))
    }

    pub fn proxy(&self) -> HeapProxy {
        HeapProxy::new(self)
    }
}

impl Nursery {
    pub fn new(base: NonNull<u8>, bytes: usize) -> Self {
        let start_addr = base.as_ptr() as usize;
        let end_addr = start_addr + bytes;

        Self {
            bump: AtomicUsize::new(start_addr),
            end: end_addr,
        }
    }

    pub fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
        let size = layout.size();
        let align = layout.align();

        let mut current_addr = self.bump.load(Ordering::Relaxed);
        let end_addr = self.end;

        loop {
            let aligned_addr = current_addr.next_multiple_of(align);

            let new_addr = aligned_addr.checked_add(size)?;

            if new_addr > end_addr {
                return None;
            }

            match self.bump.compare_exchange_weak(
                current_addr,
                new_addr,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    // SAFETY: this was just allocated
                    let ptr = unsafe {
                        NonNull::new_unchecked(aligned_addr as *mut u8)
                    };
                    return Some(ptr);
                }
                Err(updated_current_addr) => {
                    current_addr = updated_current_addr;
                }
            }
        }
    }

    pub fn remaining(&self) -> usize {
        let current = self.bump.load(Ordering::Relaxed);
        self.end.saturating_sub(current)
    }

    pub unsafe fn reset(&mut self, start: NonNull<u8>) {
        self.bump.store(start.as_ptr() as usize, Ordering::Release);
    }
}

impl HeapImpl {
    pub fn new(settings: HeapSettings) -> Self {
        settings
            .validate()
            .unwrap_or_else(|e| panic!("invalid HeapSettings: {e}"));

        let heap_start =
            crate::map_memory(settings.heap_size).unwrap_or_else(|| {
                panic!("mmap failed for heap_size={}", settings.heap_size)
            });

        let nursery_bytes_target = ((settings.heap_size as f64)
            * settings.nursery_fraction)
            .ceil() as usize;

        let nursery_bytes =
            nursery_bytes_target.next_multiple_of(settings.page_size);

        let nursery = Nursery::new(heap_start, nursery_bytes);

        // SAFETY: must be correct, is verified
        let immix_start = unsafe { heap_start.add(nursery_bytes) };

        let immix_bytes = settings.heap_size - nursery_bytes;

        debug_assert!(
            (immix_start.as_ptr() as usize).is_multiple_of(OS_PAGE_SIZE),
            "Sanity Check, start is aligned to page"
        );

        let page_count = immix_bytes / settings.page_size;
        let line_count = immix_bytes / settings.line_size;

        let mut pages = Vec::with_capacity(page_count);
        pages.resize_with(page_count, || PageMeta {
            bump: AtomicUsize::new(0),
            kind: AtomicU8::new(AllocationType::Free as u8),
            next: AtomicUsize::new(NONE),
        });
        let pages: Box<[PageMeta]> = pages.into_boxed_slice();

        let heads = [
            AtomicUsize::new(NONE),
            AtomicUsize::new(NONE),
            AtomicUsize::new(NONE),
        ];

        let mut lines = Vec::with_capacity(line_count);
        lines.resize_with(line_count, || AtomicU8::new(0));
        let lines: Box<[AtomicU8]> = lines.into_boxed_slice();

        let dirty_count = immix_bytes / settings.dirty_size;
        let dirty_per_page = settings.page_size / settings.dirty_size;

        let mut dirty = Vec::with_capacity(dirty_count);
        dirty.resize_with(dirty_count, || AtomicU8::new(0));
        let dirty: Box<[AtomicU8]> = dirty.into_boxed_slice();

        let track = RuntimeInformation {
            allocated_total: AtomicUsize::new(0),
            padding_waste_total: AtomicUsize::new(0),
            freed_total: AtomicUsize::new(0),
            allocated_since_last_gc: AtomicUsize::new(0),
        };

        let bytes_before_major_gc =
            ((immix_bytes as f64) * settings.bytes_before_gc).ceil() as usize;

        let tlab_large_threshold = (settings.tlab_size * 3) / 4;

        let info = HeapInfo {
            page_count,
            line_count,
            lines_per_page: settings.page_size / settings.line_size,
            dirty_count,
            dirty_per_page,
            tlab_large_threshold,
            bytes_before_major_gc,
        };

        HeapImpl {
            settings,
            heap_start,
            nursery,
            immix_start,
            major_epoch: AtomicU8::new(1),
            minor_epoch: AtomicU8::new(1),
            running: AtomicBool::new(false),
            gc_monitor: Mutex::new(()),
            gc_cond: Condvar::new(),
            heads,
            track,
            proxies: Mutex::new(Vec::new()),
            info,
            pages,
            lines,
            dirty,
        }
    }

    pub fn stop_mutators(&self) {
        self.running.store(true, Ordering::SeqCst);

        // 2. Wait for threads to park
        // We spin here because we want to detect the stop ASAP.
        let mut proxies = self.proxies.lock().unwrap();

        proxies.retain(|weak| {
            if let Some(state) = weak.upgrade() {
                let mut spins = 0;
                while state.status.load(Ordering::Acquire) == MUTATOR_ACTIVE {
                    if spins < 100 {
                        std::hint::spin_loop();
                    } else {
                        std::thread::yield_now();
                    }
                    spins += 1;
                }
                true
            } else {
                false
            }
        });
    }

    pub fn start_mutators(&self) {
        // Advance Epoch
        let next = self.minor_epoch.load(Ordering::Relaxed).wrapping_add(1);
        self.minor_epoch.store(next, Ordering::Release);

        self.running.store(false, Ordering::SeqCst);

        let _guard = self.gc_monitor.lock().unwrap();
        self.gc_cond.notify_all();
    }

    #[inline]
    pub fn major_epoch(&self) -> u8 {
        self.major_epoch.load(Ordering::Acquire)
    }

    #[inline]
    pub fn minor_epoch(&self) -> u8 {
        self.minor_epoch.load(Ordering::Acquire)
    }

    #[inline]
    pub fn running(&self) -> bool {
        self.running.load(Ordering::Acquire)
    }

    #[inline]
    fn kind_bucket(kind: AllocationType) -> usize {
        match kind {
            AllocationType::Boxed => 0,
            AllocationType::Unboxed => 1,
            AllocationType::Code => 2,
            AllocationType::Free => unreachable!(),
        }
    }

    #[inline]
    fn page_base_addr(&self, page_index: usize) -> usize {
        debug_assert!(page_index < self.info.page_count, "page_index OOB");
        (self.immix_start.as_ptr() as usize)
            + page_index * self.settings.page_size
    }

    #[inline]
    fn push_front(&self, bucket: usize, page_index: usize) {
        let head = &self.heads[bucket];
        loop {
            let old = head.load(Ordering::Acquire);
            self.pages[page_index].next.store(old, Ordering::Relaxed);
            if head
                .compare_exchange_weak(
                    old,
                    page_index,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                )
                .is_ok()
            {
                return;
            }
            std::hint::spin_loop();
        }
    }

    #[inline]
    fn immix_bytes(&self) -> usize {
        self.info.page_count * self.settings.page_size
    }

    #[inline]
    pub fn line_index_from_ptr(&self, ptr: *const u8) -> usize {
        let base = self.immix_start.as_ptr() as usize;
        let p = ptr as usize;

        debug_assert!(
            p >= base && p < base + self.immix_bytes(),
            "ptr out of heap bounds"
        );

        let offset = p.wrapping_sub(base);
        offset / self.settings.line_size
    }

    #[inline]
    pub fn page_index_from_ptr(&self, ptr: *const u8) -> usize {
        let base = self.immix_start.as_ptr() as usize;
        let p = ptr as usize;

        debug_assert!(
            p >= base && p < base + self.immix_bytes(),
            "ptr out of heap bounds"
        );

        let off = p - base;
        off / self.settings.page_size
    }

    #[inline]
    pub fn line_atomic(
        &self,
        line_index: usize,
    ) -> &std::sync::atomic::AtomicU8 {
        debug_assert!(
            line_index < self.lines.len(),
            "line_index out of bounds"
        );
        // SAFETY: must use correctly bounded index, checked in debug mode
        unsafe { self.lines.get_unchecked(line_index) }
    }

    #[inline]
    pub fn read_line(&self, line_index: usize) -> u8 {
        self.line_atomic(line_index).load(Ordering::Relaxed)
    }

    #[inline]
    pub fn write_line(&self, line_index: usize, value: u8) {
        self.line_atomic(line_index).store(value, Ordering::Relaxed);
    }

    #[inline]
    pub fn line_index_in_page(
        &self,
        page_index: usize,
        line_in_page: usize,
    ) -> usize {
        debug_assert!(
            page_index < self.info.page_count,
            "page_index out of bounds"
        );

        let lpp = self.info.lines_per_page;

        debug_assert!(
            line_in_page < lpp,
            "line_in_page out of page bounds: {} (lines_per_page={})",
            line_in_page,
            lpp
        );

        page_index * lpp + line_in_page
    }

    #[inline]
    pub fn read_page_line(&self, page_index: usize, line_in_page: usize) -> u8 {
        let idx = self.line_index_in_page(page_index, line_in_page);
        self.read_line(idx)
    }

    #[inline]
    pub fn write_page_line(
        &self,
        page_index: usize,
        line_in_page: usize,
        value: u8,
    ) {
        let idx = self.line_index_in_page(page_index, line_in_page);
        self.write_line(idx, value)
    }

    #[inline]
    pub fn line_range_for_page(&self, page_index: usize) -> ops::Range<usize> {
        debug_assert!(
            page_index < self.info.page_count,
            "page_index out of bounds"
        );
        let lpp = self.info.lines_per_page;
        let start = page_index * lpp;
        start..(start + lpp)
    }

    // should call push_front on this afterwards
    // its separated so other threads don't content with the thread that took it.
    // self.push_front(Self::kind_bucket(kind), page_index);
    fn claim_first_free_page(&self, kind: AllocationType) -> Option<usize> {
        let want = kind as u8;

        for page_index in 0..self.info.page_count {
            let p = &self.pages[page_index];

            if p.kind
                .compare_exchange(
                    AllocationType::Free as u8,
                    want,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                )
                .is_ok()
            {
                p.next.store(NONE, Ordering::Relaxed);

                let base = self.page_base_addr(page_index);
                p.bump.store(base, Ordering::Release);

                return Some(page_index);
            }
        }
        None
    }

    #[inline]
    fn maybe_trigger_major_gc(&self) {
        let since = self.track.allocated_since_last_gc.load(Ordering::Relaxed);
        if since >= self.info.bytes_before_major_gc {
            self.major_gc();
        }
    }

    #[inline]
    fn first_occupied_line_in_span(
        &self,
        start_line: usize,
        end_line: usize,
        major_epoch: u8,
    ) -> Option<usize> {
        (start_line..=end_line)
            .find(|&li| self.lines[li].load(Ordering::Acquire) == major_epoch)
    }

    fn try_alloc_in_page(
        &self,
        page_index: usize,
        layout: Layout,
        major_epoch: u8,
    ) -> Option<NonNull<u8>> {
        let size = layout.size();
        let align = layout.align();
        debug_assert!(size != 0);
        debug_assert!(align.is_power_of_two());

        let base = self.page_base_addr(page_index);
        let end = base + self.settings.page_size;

        let page = &self.pages[page_index];

        // Load bump; clamp in case it's 0 / stale.
        let mut current = page.bump.load(Ordering::Acquire);
        if current < base {
            current = base;
        }

        loop {
            if current >= end {
                return None;
            }

            let aligned = current.next_multiple_of(align);
            let next = aligned.checked_add(size)?;
            if next > end {
                return None;
            }

            // Check line occupancy for reserved span [current, next).
            let scan_start = current;
            let scan_end_inclusive = next - 1;

            let start_line = self.line_index_from_ptr(scan_start as *const u8);
            let end_line =
                self.line_index_from_ptr(scan_end_inclusive as *const u8);

            if let Some(occ) = self.first_occupied_line_in_span(
                start_line,
                end_line,
                major_epoch,
            ) {
                // jump past the occupied line and retry
                let after_occ = (self.immix_start.as_ptr() as usize)
                    + (occ + 1) * self.settings.line_size;

                current = current.max(after_occ);

                // catch up to current bump if contention advanced it
                let bump_now = page.bump.load(Ordering::Acquire);
                if bump_now > current {
                    current = bump_now;
                }
                continue;
            }

            // Try to claim [current, next) by bumping.
            match page.bump.compare_exchange_weak(
                current,
                next,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    // Mark lines as occupied in this major_epoch.
                    for li in start_line..=end_line {
                        self.lines[li].store(major_epoch, Ordering::Release);
                    }

                    // SAFETY: claimed
                    return Some(unsafe {
                        NonNull::new_unchecked(aligned as *mut u8)
                    });
                }
                Err(updated) => {
                    // Contention: reload and retry
                    current = updated;
                    if current < base {
                        current = base;
                    }
                }
            }
        }
    }

    pub fn allocate_raw(&self, s: Search) -> AllocationResult {
        match s.space {
            HeapSpace::Nursery => {
                if let Some(alloc) = self.nursery.allocate(s.layout) {
                    return AllocationResult {
                        ptr: alloc,
                        page_index: 0,
                    };
                }

                self.minor_gc();

                if let Some(alloc) = self.nursery.allocate(s.layout) {
                    return AllocationResult {
                        ptr: alloc,
                        page_index: 0,
                    };
                }

                panic!("nursery: out of memory after minor GC");
            }

            HeapSpace::Immix => {
                debug_assert!(s.kind != AllocationType::Free);

                let major_epoch = self.major_epoch();
                let bucket = Self::kind_bucket(s.kind);

                // Try existing pages in this kind bucket.
                // TODO: maybe accellerate this search
                let mut idx = self.heads[bucket].load(Ordering::Acquire);
                while idx != NONE {
                    if let Some(ptr) =
                        self.try_alloc_in_page(idx, s.layout, major_epoch)
                    {
                        return AllocationResult {
                            ptr,
                            page_index: idx,
                        };
                    }
                    idx = self.pages[idx].next.load(Ordering::Acquire);
                }

                self.maybe_trigger_major_gc();

                // No fit: claim a new free page.
                if let Some(new_page) = self.claim_first_free_page(s.kind) {
                    if let Some(ptr) =
                        self.try_alloc_in_page(new_page, s.layout, major_epoch)
                    {
                        return AllocationResult {
                            ptr,
                            page_index: new_page,
                        };
                    }

                    self.push_front(bucket, new_page);
                }

                panic!("immix: out of memory (no free pages)");
            }
        }
    }

    /// this write barrier dirties if the destion is in a boxed immix page
    /// keeps src_obj_addr if internal code changes later
    #[inline]
    pub fn write_barrier(&self, dst_slot_addr: *mut u8) {
        let dst = dst_slot_addr as usize;

        let immix_base = self.immix_start.as_ptr() as usize;
        let immix_end = immix_base + self.immix_bytes();

        if dst < immix_base || dst >= immix_end {
            return;
        }

        let page_index = (dst - immix_base) / self.settings.page_size;

        if self.pages[page_index].kind_load() != AllocationType::Boxed {
            return;
        }

        let dirty_index = (dst - immix_base) / self.settings.dirty_size;

        let e = self.minor_epoch.load(Ordering::Relaxed);
        self.dirty[dirty_index].store(e, Ordering::Relaxed);
    }

    /// Major GC (full-heap / immix collection). Stub for now.
    pub fn major_gc(&self) {
        unimplemented!("major_gc")
    }

    /// Minor GC (nursery collection). Stub for now.
    pub fn minor_gc(&self) {
        unimplemented!("minor_gc")
    }

    fn register_proxy_state(&self, state: &Arc<ProxyState>) {
        let mut v = self.proxies.lock().unwrap();
        v.push(Arc::downgrade(state));
    }
}

impl ProxyState {
    pub fn new() -> Self {
        Self {
            status: AtomicU8::new(MUTATOR_ACTIVE),
        }
    }
}

impl HeapProxy {
    fn new(heap: &Heap) -> Self {
        let heap = heap.clone();
        let epoch = heap.minor_epoch();
        let state = Arc::new(ProxyState::new());
        heap.register_proxy_state(&state);

        Self {
            heap,
            epoch,
            tlab: None,
            state,
            no_gc_count: 0,
        }
    }

    pub fn proxy(&self) -> HeapProxy {
        Self::new(&self.heap)
    }

    fn refill_tlab(&mut self) {
        let tlab_size = self.heap.settings.tlab_size;

        let res = self.heap.allocate(Search::new_size_align(
            tlab_size,
            16,
            AllocationType::Free,
            HeapSpace::Nursery,
        ));

        let start = res.ptr;
        // SAFETY: just allocated
        let end_ptr = unsafe { start.as_ptr().add(tlab_size) };
        // SAFETY: valid pointer end
        let end = unsafe { NonNull::new_unchecked(end_ptr) };

        self.tlab = Some(Tlab {
            page_index: res.page_index,
            cur: start,
            end,
        });
    }

    pub fn enter_no_gc_scope(&mut self) -> NoGcGuard<'_> {
        NoGcGuard { proxy: self }
    }

    #[inline(never)]
    fn enter_safepoint(&mut self) {
        self.state.status.store(MUTATOR_PARKED, Ordering::Release);

        if self.heap.running() {
            // Acquire the monitor lock
            let mut guard = self.heap.gc_monitor.lock().unwrap();

            // Wait while GC is running.
            // Using Condvar::wait handles the OS-level sleep/wake.
            while self.heap.running() {
                guard = self.heap.gc_cond.wait(guard).unwrap();
            }
        }

        // 3. We are back. Mark Active.
        self.state.status.store(MUTATOR_ACTIVE, Ordering::Release);

        // 4. Update local epoch and invalidate TLAB
        // The GC might have moved objects, or we are in a new phase.
        self.epoch = self.heap.minor_epoch();
        self.tlab = None;
    }

    #[inline]
    pub fn safepoint_poll(&mut self) {
        // If we are in a NoGC scope, we CANNOT stop.
        debug_assert!(self.no_gc_count == 0, "NoGcScope is not a safepoint");

        if self.heap.running.load(Ordering::Relaxed) {
            self.enter_safepoint();
        }
    }

    /// Call this before a blocking but gc safe code
    pub fn enter_blocking_region(&mut self) {
        debug_assert!(
            self.no_gc_count == 0,
            "cannot park mutator while in NoGcScope"
        );
        self.state.status.store(MUTATOR_PARKED, Ordering::Release);
    }

    /// Call this immediately at the end of the gc safe code
    pub fn exit_blocking_region(&mut self) {
        // Declare intent to be ACTIVE first.
        self.state.status.store(MUTATOR_ACTIVE, Ordering::SeqCst);

        // CHECK: Did a GC start while we were waking up?
        if self.heap.running.load(Ordering::SeqCst) {
            // ROLLEBACK: A GC is running, and we just marked ourselves Active.
            // The GC might be waiting for us now. We must park and wait.
            self.state.status.store(MUTATOR_PARKED, Ordering::Release);

            let mut guard = self.heap.gc_monitor.lock().unwrap();
            while self.heap.running.load(Ordering::Relaxed) {
                guard = self.heap.gc_cond.wait(guard).unwrap();
            }

            // Now the GC is finished. We can safely be Active.
            self.state.status.store(MUTATOR_ACTIVE, Ordering::Release);
        }

        //  Check if we need to dump the TLAB
        let global_epoch = self.heap.minor_epoch.load(Ordering::Relaxed);
        if global_epoch != self.epoch {
            self.epoch = global_epoch;
            self.tlab = None;
        }
    }

    pub fn allocate_raw(&mut self, s: Search) -> AllocationResult {
        if s.space == HeapSpace::Nursery {
            if let Some(ref mut tlab) = self.tlab {
                if let Some(ptr) = tlab.try_alloc(s.layout) {
                    return AllocationResult {
                        page_index: tlab.page_index,
                        ptr,
                    };
                }
            }
        }

        // Poll for GC
        self.safepoint_poll();

        // Large/Immix objects
        let is_large = s.layout.size() >= self.heap.info.tlab_large_threshold;
        if s.space != HeapSpace::Nursery || is_large {
            return self.heap.allocate(s);
        }

        self.refill_tlab();

        // Retry Allocation
        let tlab = unsafe { self.tlab.as_mut().unwrap_unchecked() };

        if let Some(ptr) = tlab.try_alloc(s.layout) {
            return AllocationResult {
                page_index: tlab.page_index,
                ptr,
            };
        }

        panic!("OOM: Failed to allocate even after TLAB refill");
    }
}

impl Tlab {
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.cur == self.end
    }

    #[inline]
    pub fn remaining(&self) -> usize {
        (self.end.as_ptr() as usize).saturating_sub(self.cur.as_ptr() as usize)
    }

    /// bump-allocate `size` with `align` inside this tlab
    #[inline]
    fn try_alloc(&mut self, layout: Layout) -> Option<NonNull<u8>> {
        let size = layout.size();
        let align = layout.align();
        debug_assert!(align.is_power_of_two());
        debug_assert!(size != 0);

        let cur = self.cur.as_ptr() as usize;
        let aligned = (cur + (align - 1)) & !(align - 1);
        let next = aligned.checked_add(size)?;

        if next <= self.end.as_ptr() as usize {
            // SAFETY: next is within tlab range
            self.cur = unsafe { NonNull::new_unchecked(next as *mut u8) };
            // SAFETY: this is the allocated value
            Some(unsafe { NonNull::new_unchecked(aligned as *mut u8) })
        } else {
            None
        }
    }
}

impl HeapSettings {
    #[inline]
    fn validate(&self) -> Result<(), &'static str> {
        if self.heap_size == 0 {
            return Err("heap_size must be > 0");
        }
        if self.page_size == 0 {
            return Err("page_size must be > 0");
        }
        if self.line_size == 0 {
            return Err("line_size must be > 0");
        }

        if !self.page_size.is_multiple_of(OS_PAGE_SIZE) {
            return Err(
                "page_size must be a multiple of OS page size (PAGE_SIZE)",
            );
        }

        if self.dirty_size == 0 {
            return Err("dirty_size must be > 0");
        }
        if !self.page_size.is_multiple_of(self.dirty_size) {
            return Err("dirty_size must fully divide page_size");
        }

        if !self.heap_size.is_multiple_of(self.page_size) {
            return Err("heap_size must be a multiple of page_size");
        }
        if !self.heap_size.is_multiple_of(self.line_size) {
            return Err("heap_size must be a multiple of line_size");
        }
        if !self.page_size.is_multiple_of(self.line_size) {
            return Err("line_size must fully divide page_size");
        }

        if self.page_size > (u16::MAX as usize) {
            return Err(
                "page_size must be <= u16::MAX because PageMeta.used is u16",
            );
        }

        if self.tlab_size == 0 {
            return Err("tlab_size must be > 0");
        }
        if self.tlab_size > self.page_size {
            return Err("tlab_size should not exceed page_size");
        }

        if !(0.0..=1.0).contains(&self.nursery_fraction) {
            return Err("nursery_fraction must be in [0.0, 1.0]");
        }

        if !(0.0..=1.0).contains(&self.bytes_before_gc) {
            return Err("bytes_before_gc must be in [0.0, 1.0]");
        }

        Ok(())
    }
}

impl Allocator for Heap {
    fn allocate(&mut self, search: Search) -> AllocationResult {
        self.allocate_raw(search)
    }
}

impl Allocator for HeapProxy {
    fn allocate(&mut self, search: Search) -> AllocationResult {
        self.allocate_raw(search)
    }
}

impl Deref for Heap {
    type Target = HeapImpl;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// Optional but very useful: automatic unmap on drop.
impl Drop for HeapImpl {
    fn drop(&mut self) {
        crate::unmap_memory(self.heap_start, self.settings.heap_size);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_default() {
        let heap = HeapImpl::new(HeapSettings::default());
        let _ = heap;
    }
}
