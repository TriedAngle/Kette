use core::panic;
use std::{
    ops::{self, Deref},
    ptr::{self, NonNull},
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, AtomicU8, Ordering},
    },
};

use crate::{
    AllocationResult, AllocationType, Allocator, HeapObject, HeapSpace,
    OS_PAGE_SIZE, Search,
};

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct PageMeta {
    start: NonNull<u8>,
    used: u16,
    space: HeapSpace,
    kind: AllocationType,
    /// The next page of the same type and age, used for faster allocation
    next: Option<usize>,
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
    /// per generation % of total heap to be allocated before GC runs
    pub bytes_before_gc: f64,
    /// Nursery size as a fraction of the total heap (e.g. 0.05 = 5%).
    /// Rounded up to the nearest full page during initialization.
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
            line_size: 128,
            bytes_before_gc: 0.05,
            nursery_fraction: 0.05,
            tlab_size: 4096,
        }
    }
}

#[derive(Debug)]
pub struct RuntimeInformation {
    /// Total bytes consumed by allocations (payload + padding).
    pub allocated_total: usize,
    /// Total padding waste (alignment) across all allocations.
    pub padding_waste_total: usize,

    pub freed_total: usize,

    /// immix total allocation since last gc
    pub allocated_since_last_gc: usize,
}

#[derive(Debug)]
pub struct HeapState {
    pub track: RuntimeInformation,
    /// Start pointer of the heap
    /// Heads of pages, indexed by (space x type)
    pub heads: Box<[Option<usize>]>,
    pub pages: Box<[PageMeta]>,
}

#[derive(Debug)]
pub struct HeapInfo {
    pub page_count: usize,
    pub line_count: usize,
    pub lines_per_page: usize,
    pub nursery_page_count: usize,
}

#[derive(Debug)]
pub struct HeapImpl {
    /// Settings of Heap
    pub settings: HeapSettings,
    /// Runtime information used to know when to GC or total information
    pub start: NonNull<u8>,
    /// Current write-barrier epoch. Lines record the last barrier they got dirtied in
    /// starts at 1, 0 means never dirtied
    pub epoch: AtomicU8,
    pub running: AtomicBool,
    pub info: HeapInfo,
    pub state: Mutex<HeapState>,
    pub lines: Box<[AtomicU8]>,
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

#[derive(Debug)]
pub struct HeapProxy {
    pub heap: Heap,
    pub epoch: u8,
    pub tlabs: [Option<Tlab>; 3],
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

impl HeapImpl {
    pub fn new(settings: HeapSettings) -> Self {
        settings
            .validate()
            .unwrap_or_else(|e| panic!("invalid HeapSettings: {e}"));

        let start =
            crate::map_memory(settings.heap_size).unwrap_or_else(|| {
                panic!("mmap failed for heap_size={}", settings.heap_size)
            });

        let page_count = settings.heap_size / settings.page_size;
        let line_count = settings.heap_size / settings.line_size;

        let nursery_bytes_target = ((settings.heap_size as f64)
            * settings.nursery_fraction)
            .ceil() as usize;
        let mut nursery_page_count = (nursery_bytes_target
            .saturating_add(settings.page_size - 1))
            / settings.page_size;
        if nursery_page_count > page_count {
            nursery_page_count = page_count;
        }

        let mut pages = Vec::with_capacity(page_count);
        for i in 0..page_count {
            let page_start_ptr =
                // SAFETY: checked, must be valid
                unsafe { start.as_ptr().add(i * settings.page_size) };
            // SAFETY: we are just allocating
            let page_start = unsafe { NonNull::new_unchecked(page_start_ptr) };

            pages.push(PageMeta {
                start: page_start,
                used: 0,
                space: if i < nursery_page_count {
                    HeapSpace::Nursery
                } else {
                    HeapSpace::Immix
                },
                kind: AllocationType::Free,
                next: None,
            });
        }

        let pages: Box<[PageMeta]> = pages.into_boxed_slice();

        let mut lines = Vec::with_capacity(line_count);
        lines.resize_with(line_count, || AtomicU8::new(0));
        let lines: Box<[AtomicU8]> = lines.into_boxed_slice();

        let track = RuntimeInformation {
            allocated_total: 0,
            padding_waste_total: 0,
            freed_total: 0,
            allocated_since_last_gc: 0,
        };

        let heads: Box<[Option<usize>]> =
            vec![None; HeapSpace::COUNT * 3].into_boxed_slice();

        let state = HeapState {
            heads,
            track,
            pages,
        };

        let info = HeapInfo {
            page_count,
            line_count,
            lines_per_page: settings.page_size / settings.line_size,
            nursery_page_count,
        };

        let state = Mutex::new(state);

        HeapImpl {
            settings,
            start,
            epoch: AtomicU8::new(1),
            running: AtomicBool::new(false),
            state,
            info,
            lines,
        }
    }

    #[inline]
    fn kind_bucket(kind: AllocationType) -> Option<usize> {
        match kind {
            AllocationType::Boxed => Some(0),
            AllocationType::Unboxed => Some(1),
            AllocationType::Code => Some(2),
            AllocationType::Free => None,
        }
    }

    #[inline]
    fn bucket_index(&self, kind: AllocationType, space: HeapSpace) -> usize {
        let k = Self::kind_bucket(kind).expect("Free has no allocation bucket");
        (space as usize) * 3 + k
    }

    #[inline]
    fn bucket_push_front(&self, state: &mut HeapState, page_index: usize) {
        let kind = state.pages[page_index].kind;
        let space = state.pages[page_index].space;
        let b = self.bucket_index(kind, space);

        let old_head = state.heads[b];
        state.pages[page_index].next = old_head;
        state.heads[b] = Some(page_index);
    }

    /// Compute (padding, total_consumed, aligned_ptr) for allocating `size` with `align`
    /// at current `used` inside `page_index`. Returns None if it doesn't fit.
    #[inline]
    fn compute_fit(
        &self,
        state: &HeapState,
        page_index: usize,
        size: usize,
        align: usize,
    ) -> Option<(usize, usize, NonNull<u8>)> {
        let page = &state.pages[page_index];
        let used = page.used as usize;

        let base = page.start.as_ptr() as usize;
        let cur = base + used;

        // align must be power-of-two
        let aligned = (cur + (align - 1)) & !(align - 1);
        let padding = aligned - cur;

        let total = padding + size;
        if used + total > self.settings.page_size {
            return None;
        }

        // SAFETY: checked for space, this must be valid
        let ptr = unsafe { NonNull::new_unchecked(aligned as *mut u8) };
        Some((padding, total, ptr))
    }

    #[inline]
    pub fn line_index_from_ptr(&self, ptr: *const u8) -> usize {
        let base = self.start.as_ptr() as usize;
        let p = ptr as usize;

        debug_assert!(
            p >= base && p < base + self.settings.heap_size,
            "ptr out of heap bounds"
        );

        let offset = p.wrapping_sub(base);
        offset / self.settings.line_size
    }

    #[inline]
    pub fn page_index_from_ptr(&self, ptr: *const u8) -> usize {
        let base = self.start.as_ptr() as usize;
        let p = ptr as usize;

        debug_assert!(
            p >= base && p < base + self.settings.heap_size,
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

    /// Allocate using a Search request. Best-fit within (kind,space) bucket;
    /// otherwise claim a Free page in the requested space.
    pub fn allocate_raw(&self, s: Search) -> AllocationResult {
        debug_assert!(
            s.kind != AllocationType::Free,
            "cannot allocate with AllocationType::Free"
        );
        debug_assert!(s.size != 0, "cannot allocate zero sized objects");
        debug_assert!(
            s.align.is_power_of_two(),
            "align must be non-zero power of two, got {}",
            s.align
        );

        if s.size > self.settings.page_size {
            panic!(
                "allocation size {} > page_size {}. TODO: handle large / multi page allocations",
                s.size, self.settings.page_size
            );
        }

        let mut state = match self.state.lock() {
            Ok(state) => state,
            Err(_e) => panic!("TODO: handle mutex poisoning"),
        };

        // First pass: best-fit within bucket list (kind, space)
        let bucket = self.bucket_index(s.kind, s.space);
        let mut cur = state.heads[bucket];

        // (page_index, remainder, padding, total_consumed, ptr)
        let mut best: Option<(usize, usize, usize, usize, NonNull<u8>)> = None;

        while let Some(i) = cur {
            // Sanity Check: list should be homogeneous
            debug_assert!(state.pages[i].kind == s.kind);
            debug_assert!(state.pages[i].space == s.space);

            if let Some((padding, total, ptr)) =
                self.compute_fit(&state, i, s.size, s.align)
            {
                let used = state.pages[i].used as usize;
                let remainder = self.settings.page_size - (used + total);

                match best {
                    None => best = Some((i, remainder, padding, total, ptr)),
                    Some((_bi, bremainder, _bpad, _btotal, _bptr)) => {
                        // smallest remainder wins; ties keep earlier (newer) page since we traverse newest-first
                        if remainder < bremainder {
                            best = Some((i, remainder, padding, total, ptr));
                        }
                    }
                }
            }

            cur = state.pages[i].next;
        }

        if let Some((page_index, _rem, padding, total, ptr)) = best {
            // consume space
            let new_used = (state.pages[page_index].used as usize) + total;
            debug_assert!(new_used <= self.settings.page_size);
            state.pages[page_index].used = new_used as u16;

            // bookkeeping (consumption-based)
            state.track.allocated_total += total;
            state.track.padding_waste_total += padding;

            return AllocationResult { page_index, ptr };
        }

        // Second Pass: claim a Free page in the requested space
        for i in 0..state.pages.len() {
            if state.pages[i].kind == AllocationType::Free
                && state.pages[i].space == s.space
            {
                state.pages[i].kind = s.kind;
                state.pages[i].used = 0;
                state.pages[i].next = None;

                self.bucket_push_front(&mut state, i);

                // SAFETY: page is free, must have space
                let (padding, total, ptr) = unsafe {
                    self.compute_fit(&state, i, s.size, s.align)
                        .unwrap_unchecked()
                };

                let new_used = total;
                debug_assert!(new_used <= self.settings.page_size);
                state.pages[i].used = new_used as u16;

                state.track.allocated_total += total;
                state.track.padding_waste_total += padding;

                return AllocationResult { page_index: i, ptr };
            }
        }

        panic!("out of memory: no suitable page found in requested space");
    }

    #[inline]
    pub fn epoch(&self) -> u8 {
        self.epoch.load(Ordering::Acquire)
    }

    #[inline]
    pub fn running(&self) -> bool {
        self.running.load(Ordering::Acquire)
    }

    #[inline]
    pub fn bump_epoch(&self) -> u8 {
        // wrapping is fine; if you want to avoid 0, add a check.
        self.epoch.fetch_add(1, Ordering::Relaxed).wrapping_add(1)
    }

    /// Finds the boxed object header address containing `ptr` by scanning backwards.
    /// Returns (object_start_ptr, object_heap_size).
    /// # Panics
    /// Panics if it can't find a header inside the containing page.
    #[inline]
    fn find_boxed_object_start_and_size(
        &self,
        state: &HeapState,
        ptr_in_obj: *const u8,
    ) -> (*const u8, usize) {
        let page_index = self.page_index_from_ptr(ptr_in_obj);
        debug_assert!(
            state.pages[page_index].kind == AllocationType::Boxed,
            "boxed write barrier used on non-boxed page"
        );

        let page_base = state.pages[page_index].start.as_ptr() as usize;
        let page_end = page_base + self.settings.page_size;

        // Scan backwards in u64 steps. Align down to 8 so reads are well-defined.
        let mut p = (ptr_in_obj as usize) & !7usize;

        // Clamp to page range (in case caller gave a weird ptr)
        if p < page_base {
            p = page_base;
        }
        if p >= page_end {
            p = page_end - 8;
        }

        while p >= page_base {
            // SAFETY: p is within [page_base, page_end) and we move in 8-byte steps.
            let word = unsafe { ptr::read(p as *const u64) };

            // Header tag: low two bits are 1 (0b11)
            if (word & 0b11) == 0b11 {
                let obj_start = p as *const u8;

                // SAFETY: By convention, the object begins with a Header.
                let obj = unsafe { &*(obj_start as *const crate::HeapValue) };
                let size = obj.heap_size();

                debug_assert!(size > 0, "object size must be > 0");
                debug_assert!(
                    size <= self.settings.page_size,
                    "object size {} exceeds page_size {}",
                    size,
                    self.settings.page_size
                );
                debug_assert!(
                    (obj_start as usize) + size <= page_end,
                    "object crosses page boundary (start={:#x}, size={}, page_end={:#x})",
                    obj_start as usize,
                    size,
                    page_end
                );

                return (obj_start, size);
            }

            if p == page_base {
                break;
            }
            p -= 8;
        }

        panic!("write_barrier(Boxed): could not find object header in page");
    }

    /// Boxed write barrier:
    /// - finds the containing object header by scanning backwards for the 0b11 tag
    /// - uses get_heap_size() to mark all lines spanned by the object with current epoch
    #[inline]
    pub fn write_barrier(&self, ptr: *const u8) {
        let state = match self.state.lock() {
            Ok(state) => state,
            Err(_e) => panic!("TODO: implement mutex poisening handling"),
        };
        debug_assert!(
            state.pages[self.page_index_from_ptr(ptr)].kind
                == AllocationType::Boxed,
            "write_barrier called for non-boxed page"
        );

        let (obj_start, obj_size) =
            self.find_boxed_object_start_and_size(&state, ptr);
        // SAFETY: this must exist by our definition of objects
        let obj_end_inclusive = unsafe { obj_start.add(obj_size - 1) };

        let epoch = self.epoch.load(Ordering::Relaxed);

        let first_line = self.line_index_from_ptr(obj_start);
        let last_line = self.line_index_from_ptr(obj_end_inclusive);

        for li in first_line..=last_line {
            self.line_atomic(li).store(epoch, Ordering::Relaxed);
        }
    }
}

impl HeapProxy {
    fn new(heap: &Heap) -> Self {
        let heap = heap.clone();
        let epoch = heap.epoch();
        Self {
            heap,
            epoch,
            tlabs: [None, None, None],
        }
    }

    pub fn proxy(&self) -> HeapProxy {
        Self::new(&self.heap)
    }

    #[inline]
    fn kind_index(kind: AllocationType) -> Option<usize> {
        match kind {
            AllocationType::Boxed => Some(0),
            AllocationType::Unboxed => Some(1),
            AllocationType::Code => Some(2),
            AllocationType::Free => None,
        }
    }

    #[inline]
    fn sync(&mut self) {
        // Fast reads, no heap lock.
        let running = self.heap.running();
        let epoch = self.heap.epoch();

        if !running && epoch == self.epoch {
            return;
        }

        // Wait until GC finishes.
        while self.heap.running() {
            std::thread::yield_now();
        }

        self.epoch = self.heap.epoch();
        self.tlabs = [None, None, None];
    }

    #[inline]
    fn tlab_threshold(&self) -> usize {
        // 75% of tlab_size
        // (avoid floats; exact integer math)
        let tlab_size = self.heap.settings.tlab_size;
        (tlab_size * 3) / 4
    }

    fn refill_tlab(&mut self, kind: AllocationType) {
        let Some(k) = Self::kind_index(kind) else {
            panic!("cannot refill TLAB for Free pages");
        };

        // Allocate a fresh tlab chunk from the real heap (gen0).
        // Important: we call sync_with_gc before allocating.
        let tlab_size = self.heap.settings.tlab_size;

        let res = self.heap.allocate(Search::new(
            tlab_size,
            16, // tlab chunk alignment; objects will align inside
            kind,
            HeapSpace::Nursery,
        ));

        let start = res.ptr;
        // SAFETY: just allocated
        let end_ptr = unsafe { start.as_ptr().add(tlab_size) };
        // SAFETY: valid pointer end
        let end = unsafe { NonNull::new_unchecked(end_ptr) };

        self.tlabs[k] = Some(Tlab {
            page_index: res.page_index,
            cur: start,
            end,
        });
    }

    pub fn allocate_raw(&mut self, s: Search) -> AllocationResult {
        debug_assert!(s.kind != AllocationType::Free);
        debug_assert!(s.size != 0);
        debug_assert!(s.align.is_power_of_two());

        // Always synchronize with GC before doing anything.
        self.sync();

        // TLABs are Nursery Only
        if s.space != HeapSpace::Nursery {
            return self.heap.allocate(s);
        }

        // Skip TLAB if request is "large" relative to the tlab.
        let threshold = self.tlab_threshold();

        if s.size >= threshold {
            return self.heap.allocate(s);
        }

        let Some(k) = Self::kind_index(s.kind) else {
            panic!("Invalid kind {:?}", s.kind)
        };

        // Try existing tlab first.
        if let Some(ref mut tlab) = self.tlabs[k]
            && let Some(ptr) = tlab.try_alloc(s.size, s.align)
        {
            return AllocationResult {
                page_index: tlab.page_index,
                ptr,
            };
        }

        self.refill_tlab(s.kind);

        // SAFETY: we just refilled
        let tlab = unsafe { self.tlabs[k].as_mut().unwrap_unchecked() };

        if let Some(ptr) = tlab.try_alloc(s.size, s.align) {
            return AllocationResult {
                page_index: tlab.page_index,
                ptr,
            };
        }

        panic!("Failed to Allocate")
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
    fn try_alloc(&mut self, size: usize, align: usize) -> Option<NonNull<u8>> {
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
        crate::unmap_memory(self.start, self.settings.heap_size);
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
