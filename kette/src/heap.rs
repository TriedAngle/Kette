// heap.rs - simple single-threaded mark & sweep GC using an mmap-backed heap.
// Notes:
// - ByteArray objects are not allocated on this heap (ignored in GC for now).
// - We keep it very simple: bump-pointer allocation + a free-list rebuilt on
//   every sweep. No coalescing (yet).
// - Headers already include a MARK bit; we only use that bit for GC.
// - Large allocations (bigger than LARGE_THRESHOLD bytes) are backed by their
//   own anonymous mmap and tracked in `large_allocs`.

#![allow(dead_code)]
use std::ptr::{self, NonNull};

use crate::visitor::MarkVisitor;
use crate::{
    Array, ArrayMap, ByteArray, Object, ObjectKind, ObjectType, SlotMap, SlotObject, TaggedU64,
    TaggedUsize, TaggedValue, ValueTag, Visitor,
};

#[cfg(unix)]
mod sys {
    use core::ffi::c_void;

    pub const PROT_NONE: i32 = 0x0;
    pub const PROT_READ: i32 = 0x1;
    pub const PROT_WRITE: i32 = 0x2;
    pub const PROT_EXEC: i32 = 0x4;

    pub const MAP_FILE: i32 = 0x0;
    pub const MAP_SHARED: i32 = 0x01;
    pub const MAP_PRIVATE: i32 = 0x02;

    #[cfg(target_os = "linux")]
    pub const MAP_ANON: i32 = 0x20;
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    pub const MAP_ANON: i32 = 0x1000;

    pub const MAP_FAILED: isize = -1;

    unsafe extern "C" {
        pub fn mmap(
            addr: *mut c_void,
            length: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: isize,
        ) -> *mut c_void;

        pub fn munmap(addr: *mut c_void, length: usize) -> i32;
    }

    #[inline]
    pub unsafe fn anonymous_mmap(len: usize) -> *mut u8 {
        let p = unsafe {
            mmap(
                core::ptr::null_mut(),
                len,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANON,
                -1,
                0,
            )
        };
        if (p as isize) == MAP_FAILED {
            core::ptr::null_mut()
        } else {
            p as *mut u8
        }
    }

    #[inline]
    pub unsafe fn anonymous_munmap(ptr: *mut u8, len: usize) {
        let _ = unsafe { munmap(ptr.cast(), len) };
    }
}

#[inline(always)]
fn align_up(x: usize, a: usize) -> usize {
    debug_assert!(a.is_power_of_two());
    (x + (a - 1)) & !(a - 1)
}

#[derive(Debug, Clone, Copy)]
struct FreeBlock {
    off: usize,
    len: usize,
}

#[derive(Debug)]
struct LargeAlloc {
    ptr: NonNull<Object>,
    size: usize,
    mmap_len: usize,
}

pub struct Heap {
    base: NonNull<u8>,
    len: usize,
    top: usize,
    free: Vec<FreeBlock>,
    large_allocs: Vec<LargeAlloc>,
    large_threshold: usize,
}

impl Heap {
    /// Create a new heap with `bytes` capacity (mmap-backed).
    pub fn new(bytes: usize) -> Option<Self> {
        unsafe {
            let p = sys::anonymous_mmap(bytes);
            NonNull::new(p).map(|nn| Self {
                base: nn,
                len: bytes,
                top: 0,
                free: Vec::new(),
                large_allocs: Vec::new(),
                large_threshold: 1 << 20,
            })
        }
    }

    pub fn zeroed() -> Self {
        Self {
            base: NonNull::dangling(),
            top: 0,
            len: 0,
            free: Vec::new(),
            large_threshold: 0,
            large_allocs: Vec::new(),
        }
    }

    /// Set the size threshold for off-heap "large" allocations.
    pub fn set_large_threshold(&mut self, bytes: usize) {
        self.large_threshold = bytes;
    }

    /// Total capacity of the main heap (bytes).
    #[inline]
    pub fn capacity(&self) -> usize {
        self.len
    }

    /// Bytes currently bumped (not counting free-list blocks).
    #[inline]
    pub fn high_water(&self) -> usize {
        self.top
    }

    /// Allocate a SlotMap on the heap.
    pub fn alloc_slot_map(&mut self, assignable_slots: usize) -> Option<NonNull<SlotMap>> {
        let layout_size = size_of::<SlotMap>();
        let p = self.alloc_raw(layout_size, align_of::<SlotMap>())?;
        unsafe {
            let sm_ptr = p.cast::<SlotMap>();
            // Construct in place.
            let sm_val = SlotMap::new(TaggedU64::from(assignable_slots as u64));
            ptr::write(sm_ptr.as_ptr(), sm_val);
            Some(sm_ptr)
        }
    }

    /// Allocate an ArrayMap on the heap.
    pub fn alloc_array_map(&mut self, len: usize) -> Option<NonNull<ArrayMap>> {
        let layout_size = size_of::<ArrayMap>();
        let p = self.alloc_raw(layout_size, align_of::<ArrayMap>())?;
        unsafe {
            let am_ptr = p.cast::<ArrayMap>();
            let am_val = ArrayMap::new(TaggedUsize::from(len));
            ptr::write(am_ptr.as_ptr(), am_val);
            Some(am_ptr)
        }
    }

    /// Allocate a SlotObject with given `map` and initial `slots`.
    pub fn alloc_slot_object(
        &mut self,
        map: NonNull<SlotMap>,
        slots: &[TaggedValue],
    ) -> Option<NonNull<SlotObject>> {
        // Use the map's slot count to size the object.
        let n = unsafe { map.as_ref().assignable_slots_count() };
        if slots.len() > n {
            // Strict: refuse to build a mismatched object.
            return None;
        }

        let bytes = size_of::<SlotObject>() + n * size_of::<TaggedValue>();
        if bytes >= self.large_threshold {
            return self.alloc_large_slot_object(map, slots);
        }

        let p = self.alloc_raw(bytes, align_of::<SlotObject>())?;
        unsafe {
            let so_ptr = p.cast::<SlotObject>();
            SlotObject::init(so_ptr, map);
            let so = so_ptr.as_ptr();
            // Write all n slots.
            for (i, v) in slots.iter().copied().enumerate() {
                (*so).set_slot_unchecked(i, v);
            }
            Some(so_ptr)
        }
    }

    /// Allocate an Array whose length is dictated by its ArrayMap.
    /// The number of runtime values MUST equal the map's declared length.
    pub fn alloc_array(
        &mut self,
        map: NonNull<ArrayMap>,
        values: &[TaggedValue],
    ) -> Option<NonNull<Array>> {
        // Use the map's declared array length.
        let n = unsafe { map.as_ref().size() };
        if values.len() > n {
            // Strict: refuse to build a mismatched array.
            return None;
        }

        let bytes = size_of::<Array>() + n * size_of::<TaggedValue>();
        if bytes >= self.large_threshold {
            return self.alloc_large_array(map, values);
        }

        let p = self.alloc_raw(bytes, align_of::<Array>())?;
        unsafe {
            let a_ptr = p.cast::<Array>();
            Array::init(a_ptr, map);
            let a = a_ptr.as_ptr();
            for (i, v) in values.iter().copied().enumerate() {
                (*a).set_unchecked(i, v);
            }
            Some(a_ptr)
        }
    }

    /// Perform a full GC given a flat root set.
    /// Returns total bytes reclaimed on both the main heap and large mmaps.
    pub fn collect(&mut self, roots: &mut [TaggedValue]) -> usize {
        // ---- Mark ----
        {
            let mut mv = MarkVisitor {};
            for v in roots.iter().copied() {
                mv.visit(v);
            }
            // drop mv before sweeping (mutable borrow)
        }
        // ---- Sweep ----
        let mut freed = 0usize;

        // Rebuild free-list from scratch.
        self.free.clear();

        // Sweep the main heap by scanning tagged words for headers.
        let mut off = 0usize;
        while off + size_of::<u64>() <= self.top {
            let word_ptr = unsafe { self.base.as_ptr().add(off) as *mut u64 };
            let word = unsafe { *word_ptr };
            if (word & 0b11) == (ValueTag::Header as u64) {
                let mut obj_ptr = unsafe { NonNull::new_unchecked(word_ptr.cast::<Object>()) };
                let size = unsafe { self.object_size_bytes(obj_ptr) };
                let obj_ref = unsafe { obj_ptr.as_mut() };
                let header = &mut obj_ref.header;
                if header.is_marked() {
                    // Live: unmark for next cycle.
                    header.unmark();
                } else {
                    // Dead: reclaim this region.
                    self.free.push(FreeBlock { off, len: size });
                    freed += size;
                }
                // Skip to the next object area.
                off = off.saturating_add(align_up(size, size_of::<u64>()));
            } else {
                // Not a header: advance one word.
                off += size_of::<u64>();
            }
        }

        // Sweep large mmaps.
        // Keep only live ones; unmap the rest.
        let mut i = 0usize;
        while i < self.large_allocs.len() {
            // SAFETY: each LargeAlloc.ptr points to the start of an object header
            let obj = self.large_allocs[i].ptr;
            let header = unsafe { &mut obj.as_ptr().cast::<Object>().as_mut().unwrap().header };
            if header.is_marked() {
                header.unmark();
                i += 1;
            } else {
                let la = self.large_allocs.remove(i);
                unsafe { sys::anonymous_munmap(la.ptr.as_ptr().cast::<u8>(), la.mmap_len) };
                freed += la.size;
            }
        }

        freed
    }

    /// Allocate raw bytes within the main heap using a simple free-list + bump.
    fn alloc_raw(&mut self, size: usize, align: usize) -> Option<NonNull<u8>> {
        // Try the free-list first (first-fit with alignment fixup).
        let mut idx = 0usize;
        while idx < self.free.len() {
            let fb = self.free[idx];
            let start = align_up(self.base.as_ptr() as usize + fb.off, align);
            let aligned_off = start - self.base.as_ptr() as usize;
            let end = aligned_off + size;
            if end <= fb.off + fb.len {
                // We can carve out here.
                // Remove the block and push back the leftovers (at most 2).
                self.free.remove(idx);
                // Left prefix (if any)
                if aligned_off > fb.off {
                    self.free.push(FreeBlock {
                        off: fb.off,
                        len: aligned_off - fb.off,
                    });
                }
                // Right suffix (if any)
                if end < fb.off + fb.len {
                    self.free.push(FreeBlock {
                        off: end,
                        len: (fb.off + fb.len) - end,
                    });
                }
                return Some(unsafe {
                    NonNull::new_unchecked(self.base.as_ptr().add(aligned_off))
                });
            } else {
                idx += 1;
            }
        }

        // Fallback to bump allocation.
        let aligned_top = align_up(self.top + (self.base.as_ptr() as usize), align)
            - (self.base.as_ptr() as usize);
        let new_top = aligned_top.checked_add(size)?;
        if new_top > self.len {
            return None;
        }
        let p = unsafe { NonNull::new_unchecked(self.base.as_ptr().add(aligned_top)) };
        self.top = new_top;
        Some(p)
    }

    /// Compute object size in bytes from its header (object or map).
    unsafe fn object_size_bytes(&self, obj: NonNull<Object>) -> usize {
        let oref = obj.as_ptr();
        let hdr = unsafe { (*oref).header };
        match hdr.kind() {
            ObjectKind::Map => match hdr.map_type().expect("invalid map header") {
                crate::MapType::Slot => size_of::<SlotMap>(),
                crate::MapType::Array => size_of::<ArrayMap>(),
            },
            ObjectKind::Object => {
                match hdr.object_type().expect("invalid object header") {
                    ObjectType::Slot => {
                        let so = unsafe { &*(oref as *const SlotObject) };
                        let n = so.assignable_slots();
                        size_of::<SlotObject>() + n * size_of::<TaggedValue>()
                    }
                    ObjectType::Array => {
                        let a = unsafe { &*(oref as *const Array) };
                        let n = a.len();
                        size_of::<Array>() + n * size_of::<TaggedValue>()
                    }
                    ObjectType::ByteArray => {
                        // Not on this heap; treat as just a header to avoid UB.
                        size_of::<ByteArray>()
                    }
                    ObjectType::Max => size_of::<u64>(), // conservative
                }
            }
        }
    }

    // ---- Large off-heap helpers ----

    fn alloc_large_slot_object(
        &mut self,
        map: NonNull<SlotMap>,
        slots: &[TaggedValue],
    ) -> Option<NonNull<SlotObject>> {
        let bytes = size_of::<SlotObject>() + slots.len() * size_of::<TaggedValue>();
        unsafe {
            let p = sys::anonymous_mmap(bytes);
            let nn = NonNull::new(p)?;
            let so_ptr = nn.cast::<SlotObject>();
            SlotObject::init(so_ptr, map);
            for (i, v) in slots.iter().copied().enumerate() {
                so_ptr.as_ptr().as_mut().unwrap().set_slot_unchecked(i, v);
            }
            self.large_allocs.push(LargeAlloc {
                ptr: so_ptr.cast::<Object>(),
                size: bytes,
                mmap_len: bytes, // already exact size; ok for munmap
            });
            Some(so_ptr)
        }
    }

    fn alloc_large_array(
        &mut self,
        map: NonNull<ArrayMap>,
        values: &[TaggedValue],
    ) -> Option<NonNull<Array>> {
        let bytes = size_of::<Array>() + values.len() * size_of::<TaggedValue>();
        unsafe {
            let p = sys::anonymous_mmap(bytes);
            let nn = NonNull::new(p)?;
            let a_ptr = nn.cast::<Array>();
            Array::init(a_ptr, map);
            for (i, v) in values.iter().copied().enumerate() {
                a_ptr.as_ptr().as_mut().unwrap().set_unchecked(i, v);
            }
            self.large_allocs.push(LargeAlloc {
                ptr: a_ptr.cast::<Object>(),
                size: bytes,
                mmap_len: bytes,
            });
            Some(a_ptr)
        }
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        // Unmap large allocations
        for la in self.large_allocs.drain(..) {
            unsafe { sys::anonymous_munmap(la.ptr.as_ptr().cast::<u8>(), la.mmap_len) };
        }
        // Unmap the main heap
        unsafe { sys::anonymous_munmap(self.base.as_ptr(), self.len) };
    }
}

#[cfg(test)]
mod tests {
    use crate::TaggedPtr;

    use super::*;
    use std::ptr::NonNull;

    // --- Helpers -------------------------------------------------------------

    #[inline]
    fn tv_obj(o: NonNull<Object>) -> TaggedValue {
        TaggedPtr::<Object>::from_nonnull(o).into()
    }

    #[inline]
    fn tv_slot_map(m: NonNull<SlotMap>) -> TaggedValue {
        TaggedPtr::<SlotMap>::from_nonnull(m).into()
    }

    #[inline]
    fn tv_array_map(m: NonNull<ArrayMap>) -> TaggedValue {
        TaggedPtr::<ArrayMap>::from_nonnull(m).into()
    }

    #[inline]
    fn tv_array(a: NonNull<Array>) -> TaggedValue {
        TaggedPtr::<Array>::from_nonnull(a).into()
    }

    fn make_heap() -> Heap {
        // small heap is fine; we also exercise large allocs off-heap
        let mut h = Heap::new(1024 * 64).expect("mmap heap");
        // use a normal threshold by default, individual tests may override
        h.set_large_threshold(1 << 20);
        h
    }

    // Build a simple object graph:
    //   obj --slot0--> arr
    // Maps are passed in and MUST be rooted by the caller.
    fn make_object_pointing_to_array(
        heap: &mut Heap,
        smap: NonNull<SlotMap>,
        amap: NonNull<ArrayMap>,
    ) -> (NonNull<SlotObject>, NonNull<Array>) {
        let arr = heap.alloc_array(amap, &[]).expect("array allocation");
        let slots = [tv_array(arr)];
        let obj = heap
            .alloc_slot_object(smap, &slots)
            .expect("object allocation");
        (obj, arr)
    }

    // --- Tests ---------------------------------------------------------------

    #[test]
    fn mark_keeps_reachable_objects_when_maps_are_rooted() {
        let mut heap = make_heap();

        // Create maps (must be in roots!)
        let smap = heap.alloc_slot_map(1).expect("slot map");
        let amap = heap.alloc_array_map(0).expect("array map");

        // An object with one slot pointing to an array.
        let (obj, _arr) = make_object_pointing_to_array(&mut heap, smap, amap);

        let top_before = heap.high_water();

        // Roots: both maps AND the object (visitor doesn't walk maps from objects)
        let mut roots = [tv_slot_map(smap), tv_array_map(amap), tv_obj(obj.cast())];

        // Nothing should be freed; also live objects should be unmarked after sweep
        let freed = heap.collect(&mut roots);
        assert_eq!(freed, 0, "GC freed live objects unexpectedly");

        // No allocations happened, high water unchanged.
        assert_eq!(
            heap.high_water(),
            top_before,
            "high water should not move during a no-op collection"
        );
    }

    #[test]
    fn sweeping_frees_unreachable_and_reuses_free_list() {
        let mut heap = make_heap();

        // Root maps only; object/array will be unreachable and must die.
        let smap = heap.alloc_slot_map(1).expect("slot map");
        let amap = heap.alloc_array_map(0).expect("array map");

        let (obj, _arr) = make_object_pointing_to_array(&mut heap, smap, amap);

        // Record the address of the object to later check hole reuse.
        let obj_addr = obj.as_ptr() as usize;

        // Snapshot bump top before GC (for later reuse check)
        let top_before = heap.high_water();

        // Only maps are rooted (as instructed), graph (obj->arr) is not.
        let mut roots = [tv_slot_map(smap), tv_array_map(amap)];
        let freed = heap.collect(&mut roots);
        assert!(
            freed > 0,
            "collector should have reclaimed unreachable object+array"
        );

        // Now allocate a same-shaped object; it should reuse the freed hole
        // (free-list first-fit) and *not* bump the top.
        let (obj2, _arr2) = make_object_pointing_to_array(&mut heap, smap, amap);
        assert_eq!(
            heap.high_water(),
            top_before,
            "allocation should reuse free block instead of bumping"
        );
        assert_eq!(
            obj2.as_ptr() as usize,
            obj_addr,
            "free-list should hand back the same freed slot (first-fit)"
        );
    }

    #[test]
    fn collecting_twice_is_idempotent_when_nothing_changes() {
        let mut heap = make_heap();

        // Live graph (all rooted).
        let smap = heap.alloc_slot_map(1).expect("slot map");
        let amap = heap.alloc_array_map(0).expect("array map");
        let (obj, _arr) = make_object_pointing_to_array(&mut heap, smap, amap);

        let mut roots = [tv_slot_map(smap), tv_array_map(amap), tv_obj(obj.cast())];

        // First pass
        let freed1 = heap.collect(&mut roots);
        assert_eq!(freed1, 0);

        // Second pass
        let freed2 = heap.collect(&mut roots);
        assert_eq!(freed2, 0, "back-to-back GC should free nothing");
    }

    #[test]
    fn cyclic_unreachable_objects_are_collected_when_maps_are_rooted() {
        let mut heap = make_heap();

        let smap = heap.alloc_slot_map(1).expect("slot map");
        let amap = heap.alloc_array_map(0).expect("array map");

        let slots_dummy = [tv_array_map(amap)]; // temporary to allocate shape
        let o1 = heap.alloc_slot_object(smap, &slots_dummy).expect("o1");
        let o2 = heap.alloc_slot_object(smap, &slots_dummy).expect("o2");

        unsafe {
            // o1.slot0 = o2
            o1.as_ptr()
                .as_mut()
                .unwrap()
                .set_slot_unchecked(0, tv_obj(o2.cast()));
            // o2.slot0 = o1
            o2.as_ptr()
                .as_mut()
                .unwrap()
                .set_slot_unchecked(0, tv_obj(o1.cast()));
        }

        let top_before = heap.high_water();

        let mut roots = [tv_slot_map(smap), tv_array_map(amap)];
        let freed = heap.collect(&mut roots);
        assert!(
            freed > 0,
            "cycle without a root must be collected by mark & sweep"
        );

        let _o3 = heap.alloc_slot_object(smap, &slots_dummy).expect("o3");
        assert_eq!(
            heap.high_water(),
            top_before,
            "after freeing the cycle, subsequent allocation should reuse free space"
        );
    }

    #[test]
    fn large_allocation_off_heap_is_unmapped_when_unreachable() {
        let mut heap = make_heap();

        heap.set_large_threshold(128);

        let smap = heap.alloc_slot_map(1).expect("slot map");
        let amap = heap.alloc_array_map(256).expect("array map");

        let big_len = 256usize; // 256 * size_of<TaggedValue> + header >> 128
        let values = vec![tv_slot_map(smap); big_len]; // arbitrary tagged values
        let big_arr = heap
            .alloc_array(amap, &values)
            .expect("large array off-heap");

        let obj_live_slots = [tv_array(big_arr)];
        let obj_live = heap
            .alloc_slot_object(smap, &obj_live_slots)
            .expect("small object");

        let mut roots_live = [
            tv_slot_map(smap),
            tv_array_map(amap),
            tv_obj(obj_live.cast()),
        ];
        let freed_live = heap.collect(&mut roots_live);
        assert_eq!(freed_live, 0, "live large object should not be freed");

        let _replace_obj = heap
            .alloc_slot_object(smap, &[])
            .expect("replacement small object");
        let mut roots_dead = [tv_slot_map(smap), tv_array_map(amap)];
        let freed_dead = heap.collect(&mut roots_dead);

        let expect_min = size_of::<Array>() + big_len * size_of::<TaggedValue>();
        assert!(
            freed_dead >= expect_min,
            "expected to reclaim >= {} bytes, actually freed {}",
            expect_min,
            freed_dead
        );
    }

    #[test]
    fn free_list_split_prefix_and_suffix_are_preserved() {
        let mut heap = make_heap();

        let smap = heap.alloc_slot_map(2).expect("slot map");
        let amap = heap.alloc_array_map(2).expect("array map");

        let a = heap.alloc_slot_object(smap, &[]).expect("A");
        let _b = heap.alloc_slot_object(smap, &[]).expect("B");
        let c = heap.alloc_slot_object(smap, &[]).expect("C");

        let top_after_abc = heap.high_water();

        let mut roots = [
            tv_slot_map(smap),
            tv_array_map(amap),
            tv_obj(a.cast()),
            tv_obj(c.cast()),
        ];
        let freed = heap.collect(&mut roots);
        assert!(freed > 0, "B should have been reclaimed");

        let _d = heap.alloc_slot_object(smap, &[]).expect("D");
        assert_eq!(
            heap.high_water(),
            top_after_abc,
            "allocating into middle free block should not bump top"
        );

        let _e = heap.alloc_slot_object(smap, &[]).expect("E");
    }
}
