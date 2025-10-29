use std::alloc::{self, Layout};
use std::cell::RefCell;
use std::collections::HashSet;
use std::mem;
use std::ptr::NonNull;

use crate::{
    Array, ArrayMap, GenericObject, Object, SlotDescriptor, SlotMap, SlotObject, TaggedPtr,
    TaggedValue, View, Visitable, Visitor,
};

pub struct Heap {}

impl Heap {
    pub fn zeroed() -> Self {
        Self {}
    }
}

pub struct AllocationToken<'heap> {
    bytes: &'heap mut [u8],
    used: usize,
}

impl<'heap> AllocationToken<'heap> {
    pub fn new(start: NonNull<u8>, size: usize) -> Self {
        let bytes = unsafe { std::slice::from_raw_parts_mut(start.as_ptr(), size) };
        Self { bytes, used: 0 }
    }

    fn current(&mut self) -> *mut u8 {
        let ptr = self.bytes.as_mut_ptr();
        unsafe { ptr.add(self.used) }
    }

    pub fn allocate_raw(&mut self, size: usize) -> NonNull<u8> {
        assert!(self.bytes.len() - self.used >= size);
        let current = self.current();
        self.used += size;
        unsafe { NonNull::new(current).unwrap_unchecked() }
    }

    pub fn allocate<T: Object>(&mut self) -> View<T> {
        let size = mem::size_of::<T>();
        View::new(self.allocate_raw(size).cast())
    }
}

impl<'heap> Drop for AllocationToken<'heap> {
    fn drop(&mut self) {
        assert!(self.used == self.bytes.len())
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct GarbageCollectionStats {
    /// count of objects
    freed_objects: usize,
    /// bytes of freed objecs
    freed: usize,
    /// count of survived objects
    survived_objects: usize,
}

/// All allocators expect the layout to include the header !
/// so internally allocators can use pointers to Header or GenericObject
pub trait Allocator: Visitable {
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>>;
    fn free(&self, ptr: NonNull<u8>);
    fn free_if<F>(&self, f: F)
    where
        F: FnMut(&NonNull<GenericObject>) -> bool;
}

pub trait GarbageCollector {
    fn allocate_raw(&self, layout: Layout) -> NonNull<u8>;
    #[inline]
    fn allocate(&self, layout: Layout) -> AllocationToken<'_> {
        let raw = self.allocate_raw(layout);
        let token = AllocationToken::new(raw, layout.size());
        token
    }
    /// while technically safe, the returned value is unsafe to use and should directly be populated with data
    /// so the unsafe is here to discourage the usage
    #[inline]
    unsafe fn allocate_raw_slot_map(&self, total_slots: usize) -> View<SlotMap> {
        let map_head = Layout::new::<SlotMap>();
        let map_slots = Layout::array::<SlotDescriptor>(total_slots).unwrap();
        let (layout, _) = map_head.extend(map_slots).unwrap();
        let map: NonNull<SlotMap> = self.allocate_raw(layout).cast();
        View::new(map)
    }

    /// TODO: assignable slots should be inferred by going through slots
    fn allocate_slot_map(
        &self,
        assignable_slots: usize,
        slots: &[SlotDescriptor],
    ) -> View<SlotMap> {
        let total_slots = slots.len();
        let mut map = unsafe { self.allocate_raw_slot_map(total_slots) };
        let map_slots_ptr = map.slots.as_mut_ptr();
        unsafe { map.init(assignable_slots, total_slots) };
        unsafe { std::ptr::copy_nonoverlapping(slots.as_ptr(), map_slots_ptr, total_slots) };
        map
    }

    #[inline]
    unsafe fn allocate_raw_slot_object(&self, slot_count: usize) -> View<SlotObject> {
        let head = Layout::new::<SlotObject>();
        let slots = Layout::array::<TaggedValue>(slot_count).unwrap();
        let (layout, _) = head.extend(slots).unwrap();
        let obj: NonNull<SlotObject> = self.allocate_raw(layout).cast();
        View::new(obj)
    }

    fn allocate_slot_object_from_map(
        &self,
        map: View<SlotMap>,
        values: &[TaggedValue],
    ) -> View<SlotObject> {
        let slot_count = map.assignable_slots.into();
        assert!(
            slot_count == values.len(),
            "slots must match object slot count"
        );
        let mut obj = unsafe { self.allocate_raw_slot_object(slot_count) };
        let slots_ptr = obj.slots.as_mut_ptr();
        unsafe { obj.init(map.into()) };
        unsafe {
            std::ptr::copy_nonoverlapping(values.as_ptr(), slots_ptr, slot_count);
        }
        obj
    }

    fn allocate_array_map(&self, size: usize) -> View<ArrayMap> {
        let layout = Layout::new::<ArrayMap>();
        let raw: NonNull<ArrayMap> = self.allocate_raw(layout).cast();
        let mut map = View::new(raw);
        unsafe { map.init(size) };
        map
    }

    #[inline]
    unsafe fn allocate_raw_array(&self, size: usize) -> View<Array> {
        let head = Layout::new::<SlotObject>();
        let items = Layout::array::<TaggedValue>(size).unwrap();
        let (layout, _) = head.extend(items).unwrap();
        let array: NonNull<Array> = self.allocate_raw(layout).cast();
        View::new(array)
    }

    /// This is unsafe because we didn't initialize the fields yet.
    /// this array would be safe to write, but reading from unwritten fields could be arbitrary.
    #[inline]
    unsafe fn allocate_unsafe_array(&self, map: View<ArrayMap>) -> View<Array> {
        let size: usize = map.size.into();
        let mut array = unsafe { self.allocate_raw_array(size) };
        unsafe { array.init(map.into()) };
        array
    }

    fn allocate_filled_array(&self, map: View<ArrayMap>, value: TaggedValue) -> View<Array> {
        let mut array = unsafe { self.allocate_unsafe_array(map) };
        array.fields_mut().fill(value);
        array
    }

    fn allocate_array(&self, map: View<ArrayMap>, values: &[TaggedValue]) -> View<Array> {
        let mut array = unsafe { self.allocate_unsafe_array(map) };
        assert!(array.len() == values.len());
        unsafe {
            std::ptr::copy_nonoverlapping(values.as_ptr(), array.fields.as_mut_ptr(), values.len())
        };
        array
    }

    fn force_collect(&self) -> GarbageCollectionStats;
    fn add_root(&self, object: TaggedPtr<GenericObject>);
    fn remove_root(&self, object: TaggedPtr<GenericObject>);
}

pub struct RustAllocator {
    allocations: RefCell<HashSet<NonNull<GenericObject>, ahash::RandomState>>,
}

impl RustAllocator {
    pub fn new() -> Self {
        Self {
            allocations: RefCell::new(HashSet::default()),
        }
    }

    fn dealloc(obj: NonNull<GenericObject>) {
        let size = unsafe { (*obj.as_ptr()).heap_size() };
        let layout = unsafe { Layout::from_size_align_unchecked(size, 8) };
        unsafe { alloc::dealloc(obj.as_ptr() as _, layout) };
    }
}

impl Visitable for RustAllocator {
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        let allocations = self.allocations.borrow_mut();
        allocations
            .iter()
            .map(|&a| TaggedValue::from(TaggedPtr::from_nonnull(a)))
            .for_each(|value| visitor.visit(value));
    }
    fn visit_edges_mut(&mut self, _visitor: &mut impl Visitor) {
        unreachable!("this shouldn't exist")
    }
}

impl Allocator for RustAllocator {
    fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
        let raw = unsafe { alloc::alloc(layout) };
        if raw.is_null() {
            return None;
        }
        let res = NonNull::new(raw.cast()).unwrap();
        let mut allocations = self.allocations.borrow_mut();
        allocations.insert(res);
        unsafe { Some(NonNull::new(raw).unwrap_unchecked()) }
    }

    fn free(&self, ptr: NonNull<u8>) {
        let obj = ptr.cast();
        let mut allocations = self.allocations.borrow_mut();
        allocations.remove(&obj);
        Self::dealloc(obj);
    }

    fn free_if<F>(&self, f: F)
    where
        F: FnMut(&NonNull<GenericObject>) -> bool,
    {
        let mut allocations = self.allocations.borrow_mut();
        allocations.extract_if(f).for_each(|obj| Self::dealloc(obj));
        allocations.shrink_to_fit();
    }
}

pub struct HandleSet {}

pub struct MarkAndSweepGCImpl<A: Allocator> {
    allocator: A,
    roots: HashSet<TaggedPtr<GenericObject>, ahash::RandomState>,
    /// ignored for now, optimization for later.
    #[allow(unused)]
    handles: Option<NonNull<HandleSet>>,
}

pub struct MarkAndSweepGC<A: Allocator> {
    inner: RefCell<MarkAndSweepGCImpl<A>>,
}

impl<A: Allocator> MarkAndSweepGCImpl<A> {
    fn new(allocator: A) -> Self {
        Self {
            allocator,
            roots: HashSet::default(),
            handles: None,
        }
    }

    fn collect(&mut self) -> GarbageCollectionStats {
        struct MarkVisitor<'a> {
            queue: &'a mut Vec<TaggedPtr<GenericObject>>,
        }
        impl<'a> Visitor for MarkVisitor<'a> {
            fn visit_mut(&mut self, value: TaggedValue) {
                let Some(obj) = value.as_reference::<GenericObject>() else {
                    return;
                };
                let ptr = obj.as_mut_ptr();
                if unsafe { (*ptr).header.is_marked() } {
                    return;
                }
                unsafe { (*ptr).header.mark() };
                self.queue.push(obj);
            }
        }

        let mut stats = GarbageCollectionStats {
            freed: 0,
            survived_objects: 0,
            freed_objects: 0,
        };

        let mut queue = Vec::<TaggedPtr<GenericObject>>::new();
        queue.extend(&self.roots);

        let mut marker = MarkVisitor { queue: &mut queue };
        for &root in &self.roots {
            marker.visit_mut(root.into());
        }
        println!("queue: {:?}", queue);

        while let Some(mut object) = queue.pop() {
            let mut marker = MarkVisitor { queue: &mut queue };
            object.visit_edges_mut(&mut marker);
        }

        self.allocator.free_if(|obj| {
            let ptr = obj.as_ptr();
            if unsafe { (*ptr).header.is_marked() } {
                stats.survived_objects += 1;
                unsafe { (*ptr).header.unmark() };
                return false;
            }

            stats.freed_objects += 1;
            stats.freed += unsafe { (*ptr).heap_size() };

            true
        });
        stats
    }

    fn allocate_raw(&mut self, layout: Layout) -> NonNull<u8> {
        let Some(allocation) = self.allocator.allocate(layout) else {
            self.collect();
            let Some(allocation) = self.allocator.allocate(layout) else {
                panic!("No Space in Heap");
            };
            return allocation;
        };
        allocation
    }

    fn add_root(&mut self, object: TaggedPtr<GenericObject>) {
        self.roots.insert(object);
    }

    fn remove_root(&mut self, object: TaggedPtr<GenericObject>) {
        self.roots.remove(&object);
    }
}

impl<A: Allocator> MarkAndSweepGC<A> {
    pub fn new(allocator: A) -> Self {
        let inner = MarkAndSweepGCImpl::new(allocator);
        Self {
            inner: RefCell::new(inner),
        }
    }
}

impl<A: Allocator> GarbageCollector for MarkAndSweepGC<A> {
    fn allocate_raw(&self, layout: Layout) -> NonNull<u8> {
        self.inner.borrow_mut().allocate_raw(layout)
    }
    fn force_collect(&self) -> GarbageCollectionStats {
        self.inner.borrow_mut().collect()
    }
    fn add_root(&self, object: TaggedPtr<GenericObject>) {
        self.inner.borrow_mut().add_root(object);
    }
    fn remove_root(&self, object: TaggedPtr<GenericObject>) {
        self.inner.borrow_mut().remove_root(object);
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    fn new_gc() -> MarkAndSweepGC<RustAllocator> {
        MarkAndSweepGC::new(RustAllocator::new())
    }

    fn alloc_empty_slot_map<G: GarbageCollector>(gc: &G) -> View<SlotMap> {
        gc.allocate_slot_map(0, &[])
    }
    fn alloc_empty_slot_object<G: GarbageCollector>(
        gc: &G,
        map: View<SlotMap>,
    ) -> View<SlotObject> {
        gc.allocate_slot_object_from_map(map, &[])
    }

    fn alloc_empty_array<G: GarbageCollector>(gc: &G) -> (View<ArrayMap>, View<Array>) {
        let amap = gc.allocate_array_map(0);
        let array = unsafe { gc.allocate_unsafe_array(amap) };
        (amap, array)
    }

    fn alloc_empty_byte_array<G: GarbageCollector>(gc: &G) -> View<ByteArray> {
        let layout = std::alloc::Layout::new::<ByteArray>();
        let raw: std::ptr::NonNull<ByteArray> = gc.allocate_raw(layout).cast();
        let mut ba = View::new(raw);
        // Initialize as an ObjectType::ByteArray with default flags/data.
        ba.header = Header::encode_object(ObjectType::ByteArray, 0, HeaderFlags::empty(), 0);
        ba
    }

    fn as_generic_object<T>(v: View<T>) -> TaggedPtr<GenericObject> {
        let tp: TaggedPtr<T> = v.into();
        unsafe { tp.cast() }
    }

    #[test]
    fn collect_without_roots_frees_everything() {
        let gc = new_gc();

        // Allocate a mix of objects
        let slot_map = alloc_empty_slot_map(&gc);
        let _slot_obj = alloc_empty_slot_object(&gc, slot_map);

        let (_amap, _arr) = alloc_empty_array(&gc);
        let (_amap2, _arr2) = alloc_empty_array(&gc);

        // Nothing is rooted, so everything should be freed.
        let stats = gc.force_collect();
        assert_eq!(
            stats.survived_objects, 0,
            "no roots => nothing should survive"
        );
        assert!(
            stats.freed_objects >= 5,
            "we allocated at least 5 distinct objects"
        );
        assert!(stats.freed > 0, "freed byte counter should be positive");
    }

    #[test]
    fn rooted_object_survives_others_are_freed() {
        let gc = new_gc();

        // Two independent objects: root only one of them.
        let slot_map = alloc_empty_slot_map(&gc);
        let rooted = alloc_empty_slot_object(&gc, slot_map);

        let slot_map2 = alloc_empty_slot_map(&gc);
        let _unrooted = alloc_empty_slot_object(&gc, slot_map2);

        // Add root for the first one.
        gc.add_root(as_generic_object(rooted));

        let stats = gc.force_collect();
        assert_eq!(
            stats.survived_objects, 2,
            "rooted object survives; its SlotMap survives too"
        );
        assert_eq!(
            stats.freed_objects, 2,
            "unrooted object and its SlotMap are freed"
        );
    }

    #[test]
    fn add_then_remove_root_changes_liveness() {
        let gc = new_gc();

        let sm = alloc_empty_slot_map(&gc);
        let obj = alloc_empty_slot_object(&gc, sm);

        // First GC with the object rooted: it should survive.
        gc.add_root(as_generic_object(obj));
        let stats1 = gc.force_collect();
        assert_eq!(
            stats1.survived_objects, 2,
            "rooted object and its SlotMap should survive"
        );
        assert_eq!(stats1.freed_objects, 0, "nothing unrooted was allocated");

        // Remove root, allocate a small extra object (to keep allocator set non-empty).
        gc.remove_root(as_generic_object(obj));
        let (_amap, _arr) = alloc_empty_array(&gc);

        // Now the previously-rooted pair should be freed; the new array pair survives if not rooted?
        // We did not root the array, so after this collection: the old pair is freed,
        // and the new array + its map are also freed (no roots at all).
        let stats2 = gc.force_collect();
        assert!(
            stats2.freed_objects >= 2,
            "the previously rooted {obj:?}, {sm:?} should now be freed"
        );
        assert_eq!(
            stats2.survived_objects, 0,
            "no roots => nothing should survive"
        );
    }

    #[test]
    fn surviving_objects_are_unmarked_after_sweep() {
        let gc = new_gc();

        let sm = alloc_empty_slot_map(&gc);
        let obj = alloc_empty_slot_object(&gc, sm);

        // Root it so it survives the sweep.
        let obj_root = as_generic_object(obj);
        gc.add_root(obj_root);

        // Run GC
        let _ = gc.force_collect();

        // After sweep, survivors must be unmarked for the next cycle.
        // SAFETY: obj_root points to a live object (we just collected with it rooted).
        let gptr = obj_root.as_mut_ptr();
        let header = unsafe { &(*gptr).header };
        assert!(!header.is_marked(), "survivor must be unmarked after sweep");
    }

    #[test]
    fn array_and_arraymap_can_be_allocated_and_collected() {
        let gc = new_gc();

        // Allocate an ArrayMap + Array (size 0).
        let (_amap, arr) = alloc_empty_array(&gc);

        // If we root the array, both it and its map survive.
        gc.add_root(as_generic_object(arr));
        let stats1 = gc.force_collect();
        assert_eq!(
            stats1.survived_objects, 2,
            "rooted array and its ArrayMap should survive"
        );
        assert_eq!(stats1.freed_objects, 0);

        // Drop the root and collect again; both should now be freed.
        gc.remove_root(as_generic_object(arr));
        let stats2 = gc.force_collect();
        assert!(
            stats2.freed_objects >= 2,
            "array and its map should be freed when unrooted"
        );
        assert_eq!(stats2.survived_objects, 0);

        // Make sure we can still allocate after freeing
        let new_map = alloc_empty_slot_map(&gc);
        let _new_obj = alloc_empty_slot_object(&gc, new_map); // using the old map View is fine; it was a copy
        let stats3 = gc.force_collect();
        // We didn't root the new pair; they should be freed too.
        assert!(stats3.freed_objects >= 2);
        assert_eq!(stats3.survived_objects, 0);
    }

    #[test]
    fn arrays_and_slot_objects_with_values_are_tracked_transitively() {
        let gc = new_gc();

        // --- leaf objects the container values will point to ---
        let leaf_a = alloc_empty_byte_array(&gc);
        let leaf_b = alloc_empty_byte_array(&gc);

        // Helper: TaggedValue reference from a View<T>.
        fn ref_value<T>(v: View<T>) -> TaggedValue {
            let tp: TaggedPtr<T> = v.into();
            tp.into()
        }

        // --- an Array with 2 fields pointing to the leaves ---
        let amap2 = gc.allocate_array_map(2);
        let arr_vals = [ref_value(leaf_a), ref_value(leaf_b)];
        let arr = gc.allocate_array(amap2, &arr_vals);

        // --- a SlotObject with 2 slots: [arr, leaf_b] ---
        // We need a SlotMap with 2 assignable slots. Use the raw allocator to avoid having to
        // provide real SlotDescriptors (they aren't used by GC marking anyways).
        let sm2 = {
            let mut sm = unsafe { gc.allocate_raw_slot_map(2) };
            unsafe { sm.init(2, 2) };
            sm
        };
        let obj_vals = [ref_value(arr), ref_value(leaf_b)];
        let obj = gc.allocate_slot_object_from_map(sm2, &obj_vals);

        // Root ONLY the slot object. Transitively, it should keep: obj, its SlotMap, arr, arr's ArrayMap, and both leaves.
        gc.add_root(as_generic_object(obj));
        let s1 = gc.force_collect();
        assert!(
            s1.survived_objects >= 6,
            "rooted SlotObject should keep itself, its SlotMap, the Array, its ArrayMap, and both leaves alive"
        );
        assert_eq!(
            s1.freed_objects, 0,
            "nothing should be freed while obj is the sole root"
        );

        // Now unroot the SlotObject, but root the Array.
        gc.remove_root(as_generic_object(obj));
        gc.add_root(as_generic_object(arr));

        let s2 = gc.force_collect();
        // The SlotObject + its SlotMap should now be freed; Array + ArrayMap + 2 leaves survive.
        assert!(
            s2.survived_objects >= 4,
            "rooted Array should keep itself, its ArrayMap, and both leaves alive"
        );
        assert!(
            s2.freed_objects >= 2,
            "the SlotObject and its SlotMap should now be freed"
        );

        // Finally, unroot everything and ensure it all goes away.
        gc.remove_root(as_generic_object(arr));
        let s3 = gc.force_collect();
        assert_eq!(
            s3.survived_objects, 0,
            "with no roots, nothing should survive"
        );
        assert!(
            s3.freed_objects >= 4,
            "Array, ArrayMap, and the two leaves should be freed"
        );
    }
}
