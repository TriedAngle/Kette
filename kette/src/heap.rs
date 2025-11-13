#![allow(unused)]
use std::{
    cell::{RefCell, UnsafeCell},
    marker::PhantomData,
    ptr::NonNull,
    sync::{
        Arc,
        atomic::{AtomicBool, AtomicUsize, Ordering},
    },
};

use bitflags::bitflags;
use parking_lot::Mutex;

use crate::map_memory;

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
    _marker: PhantomData<*const ()>,
}
#[derive(Debug)]
pub struct TLAB {
    start: NonNull<u8>,
    end: NonNull<u8>,
    bump: usize,
    size: usize,
}
#[derive(Debug)]
pub struct HeapProxy {
    heap: Arc<HeapShared>,
    epoch: usize,
    boxed_tlab: TLAB,
    unboxed_tlab: TLAB,
}

unsafe impl Send for HeapProxy {}
unsafe impl Sync for HeapProxy {}

impl Heap {
    pub fn new(info: HeapCreateInfo) -> Self {
        let size = info.size;
        let start = map_memory(size).unwrap();
        let end_ptr = unsafe { start.as_ptr().add(size) };
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
            _marker: PhantomData::default(),
        }
    }

    pub fn create_proxy(&self) -> HeapProxy {
        let heap = self.inner.clone();
        let epoch = self.inner.epoch.load(Ordering::Relaxed);
        let proxy = HeapProxy {
            heap,
            epoch,
            boxed_tlab: TLAB::empty(),
            unboxed_tlab: TLAB::empty(),
        };
        proxy
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

        let dirty_count = settings.page_size * page_count / settings.dirty_line_size;
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
            _marker: PhantomData::default(),
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
                start_ptr = unsafe {
                    self.start
                        .as_ptr()
                        .add(start_index * self.settings.page_size + old_used)
                };
            } else {
                let first_page_fit =
                    self.settings.page_size - pages[start_index].bytes_used as usize;
                let remaining = total_size - first_page_fit;
                pages[start_index].bytes_used = self.settings.page_size as u16;

                let split_page = &mut pages[start_index + 1];
                split_page.bytes_used = remaining as u16;
                split_page.flags = flags;
                split_page.generation = search.generation;
                split_page.offset_first = first_page_fit as u16;
                start_ptr = unsafe {
                    self.start
                        .as_ptr()
                        .add(start_index * self.settings.page_size + old_used)
                };
            }
        }

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
    fn next_fit_find_pages(&self, search: AllocSearchInfo) -> Option<AllocationSelection> {
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
                if self.settings.page_size - page.bytes_used as usize >= search.size {
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

    fn find_free_pages(&self, search: AllocSearchInfo) -> Option<AllocationSelection> {
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
}

impl HeapProxy {
    fn tlab_alloc(&mut self, size: usize, ptype: PageType) -> Option<NonNull<u8>> {
        match ptype {
            PageType::Boxed => self.boxed_tlab.allocate(size),
            PageType::Unboxed => self.unboxed_tlab.allocate(size),
        }
    }

    fn exchange_tlab(&mut self, ptype: PageType) {
        let size = self.heap.settings.tlab_size;
        let search = AllocSearchInfo {
            size,
            ptype: ptype,
            generation: 0,
            allow_split: false,
        };
        let res = self.heap.allocate(search);
        let start = res.start;
        let size = res.size;
        let end_ptr = unsafe { start.as_ptr().add(size) };
        let end = unsafe { NonNull::new_unchecked(end_ptr) };
        let tlab = TLAB {
            start,
            end,
            bump: 0,
            size: size,
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
        return true;
    }

    pub fn allocate_raw(&mut self, size: usize, ptype: PageType) -> NonNull<u8> {
        if self.maybe_wait_epoch() {
            self.exchange_tlab(ptype);
        }

        if size > self.heap.settings.tlab_size {
            let info = AllocSearchInfo {
                size,
                ptype,
                generation: 0,
                allow_split: true,
            };
            let res = self.heap.allocate(info);
            return res.start;
        }

        if let Some(allocation) = self.tlab_alloc(size, ptype) {
            return allocation;
        }

        self.exchange_tlab(ptype);

        self.tlab_alloc(size, ptype)
            .expect("Tlab allocation must work")
    }

    pub fn allocate_boxed_raw(&mut self, size: usize) -> NonNull<u8> {
        self.allocate_raw(size, PageType::Boxed)
    }

    pub fn allocate_unboxed_raw(&mut self, size: usize) -> NonNull<u8> {
        // TODO: implement alignment if necessary
        self.allocate_raw(size, PageType::Unboxed)
    }

    pub fn create_proxy(&self) -> HeapProxy {
        let heap = self.heap.clone();
        let epoch = self.heap.epoch.load(Ordering::Relaxed);
        let proxy = HeapProxy {
            heap,
            epoch,
            boxed_tlab: TLAB::empty(),
            unboxed_tlab: TLAB::empty(),
        };
        proxy
    }
}

impl TLAB {
    pub fn empty() -> Self {
        Self {
            start: NonNull::dangling(),
            end: NonNull::dangling(),
            size: 0,
            bump: 0,
        }
    }

    pub fn allocate(&mut self, size: usize) -> Option<NonNull<u8>> {
        if self.bump + size <= self.size {
            let ptr = unsafe { self.start.as_ptr().add(self.bump) };
            self.bump += size;
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
        !self.flags.contains(PageFlags::Used) && !self.flags.contains(PageFlags::Large)
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
        if used >= page_size {
            0
        } else {
            page_size - used
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

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

    fn page_flags_contains(flags: PageFlags, has: &[PageFlags], not: &[PageFlags]) -> bool {
        has.iter().all(|f| flags.contains(*f)) && not.iter().all(|f| !flags.contains(*f))
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

        let _b = p.allocate_unboxed_raw(24);

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
        let _u1 = p.allocate_unboxed_raw(32);
        assert_eq!(p.unboxed_tlab.bump, 32);
        // skip tlab allocation as this is bigger than the tlab, tlab stays the same
        let _u2 = p.allocate_unboxed_raw(200);
        assert_eq!(p.unboxed_tlab.bump, 32);

        // Ensure the unboxed page is marked unboxed
        let pages = p.heap.pages.borrow();
        let (idx, unboxed_pg) = pages
            .iter()
            .enumerate()
            .find(|(_, pg)| {
                page_flags_contains(pg.flags, &[PageFlags::Used, PageFlags::Unboxed], &[])
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
        let seen: SyncArc<SyncMutex<HashSet<usize>>> = SyncArc::new(SyncMutex::new(HashSet::new()));

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
                        proxy.allocate_unboxed_raw(size)
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
}
