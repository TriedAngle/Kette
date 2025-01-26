use std::{alloc, collections::HashSet, ptr};

use crate::object::{Array, ByteArray, HEADER_TAG, MARK_BIT, Map, Object, ObjectHeader, ObjectRef};

const BUMP_CHUNK_SIZE: usize = 64 * 1024;
const SMALL_OBJECT_MAX_SIZE: usize = 64;
const MIN_OBJECT_SIZE: usize = 8;

struct BumpChunk {
    start: *mut u8,
    current: *mut u8,
    end: *mut u8,
}

impl BumpChunk {
    unsafe fn new() -> Self {
        let layout = unsafe { alloc::Layout::from_size_align_unchecked(BUMP_CHUNK_SIZE, 8) };
        let ptr = unsafe { alloc::alloc(layout) };
        Self {
            start: ptr,
            current: ptr,
            end: unsafe { ptr.add(BUMP_CHUNK_SIZE) },
        }
    }

    fn remaining_space(&self) -> usize {
        unsafe { self.end.offset_from(self.current) as usize }
    }

    fn contains_address(&self, addr: *mut u8) -> bool {
        self.start <= addr && addr < self.end
    }

    unsafe fn scan_live_objects(&self) -> usize {
        let mut live_count = 0;
        let mut current = self.start as *mut u64;
        while current < self.end as *mut u64 {
            let value = unsafe { *current };
            if (value & 0b11) == HEADER_TAG {
                if value & MARK_BIT != 0 {
                    live_count += 1;
                }
            }
            current = unsafe { current.add(1) };
        }
        live_count
    }
}

struct BumpAllocator {
    chunks: Vec<BumpChunk>,
    current_chunk_idx: usize,
}

struct LargeAllocator {
    objects: Vec<ptr::NonNull<Object>>,
}

pub struct GarbageCollector {
    bump: BumpAllocator,
    large: LargeAllocator,
    roots: HashSet<*mut Object>,
    total_allocated: usize,
    threshold: usize,
}

impl BumpAllocator {
    fn new() -> Self {
        Self {
            chunks: vec![unsafe { BumpChunk::new() }],
            current_chunk_idx: 0,
        }
    }

    unsafe fn allocate(&mut self, size: usize) -> *mut u8 {
        debug_assert!(size <= SMALL_OBJECT_MAX_SIZE);
        debug_assert!(size >= MIN_OBJECT_SIZE);
        let aligned_size = (size + 7) & !7;

        if self.chunks[self.current_chunk_idx].remaining_space() < aligned_size {
            let mut found = false;
            for (idx, chunk) in self.chunks.iter().enumerate() {
                if chunk.remaining_space() >= aligned_size {
                    self.current_chunk_idx = idx;
                    found = true;
                    break;
                }
            }

            if !found {
                unsafe {
                    self.chunks.push(BumpChunk::new());
                }

                self.current_chunk_idx = self.chunks.len() - 1;
            }
        }

        let chunk = &mut self.chunks[self.current_chunk_idx];
        let result = chunk.current;
        chunk.current = unsafe { chunk.current.add(aligned_size) };
        result
    }

    unsafe fn collect_empty_chunks(&mut self) {
        let mut i = 0;
        while i < self.chunks.len() {
            let live_count = unsafe { self.chunks[i].scan_live_objects() };

            if live_count == 0 {
                let layout =
                    unsafe { alloc::Layout::from_size_align_unchecked(BUMP_CHUNK_SIZE, 8) };
                unsafe { alloc::dealloc(self.chunks[i].start, layout) };

                self.chunks.swap_remove(i);

                if i <= self.current_chunk_idx {
                    self.current_chunk_idx = self.current_chunk_idx.saturating_sub(1);
                }
            } else {
                i += 1;
            }
        }

        if self.chunks.is_empty() {
            self.chunks.push(unsafe { BumpChunk::new() });
            self.current_chunk_idx = 0;
        }
    }
}

impl LargeAllocator {
    fn new() -> Self {
        Self {
            objects: Vec::new(),
        }
    }

    unsafe fn allocate(&mut self, size: usize) -> *mut Object {
        let layout = unsafe { alloc::Layout::from_size_align_unchecked(size, 8) };
        let ptr = unsafe { alloc::alloc(layout) as *mut Object };
        unsafe {
            self.objects.push(ptr::NonNull::new_unchecked(ptr));
        }
        ptr
    }

    unsafe fn deallocate(&mut self, ptr: *mut Object) {
        let map = unsafe { (*ptr).get_map() };
        let size = (*map).object_size;
        let layout = unsafe { alloc::Layout::from_size_align_unchecked(size, 8) };
        unsafe { alloc::dealloc(ptr as *mut u8, layout) };
    }
}

impl GarbageCollector {
    pub fn new() -> Self {
        Self {
            bump: BumpAllocator::new(),
            large: LargeAllocator::new(),
            roots: HashSet::new(),
            total_allocated: 0,
            threshold: 1024 * 1024, // 1MB initial threshold
        }
    }

    pub unsafe fn allocate(&mut self, map: *mut Map) -> *mut Object {
        let size = unsafe { (*map).object_size };

        self.total_allocated += size;
        if self.total_allocated > self.threshold {
            unsafe { self.collect() };
            self.threshold = self.total_allocated * 2;
        }

        let ptr = if size <= SMALL_OBJECT_MAX_SIZE {
            unsafe { self.bump.allocate(size) as *mut Object }
        } else {
            unsafe { self.large.allocate(size) }
        };

        unsafe { (*ptr).header = ObjectHeader::new(map) };

        let slots = unsafe { (ptr as *mut u8).add(std::mem::size_of::<Object>()) };
        unsafe { std::ptr::write_bytes(slots, 0, size - std::mem::size_of::<Object>()) };

        ptr
    }

    pub unsafe fn allocate_array(&mut self, map: *mut Map, length: usize) -> *mut Array {
        let size = Array::required_size(length);

        self.total_allocated += size;
        if self.total_allocated > self.threshold {
            unsafe { self.collect() };
            self.threshold = self.total_allocated * 2;
        }

        let ptr = if size <= SMALL_OBJECT_MAX_SIZE {
            unsafe { self.bump.allocate(size) as *mut Array }
        } else {
            unsafe { self.large.allocate(size) as *mut Array }
        };

        unsafe { (*ptr).header.map = (map as u64) | HEADER_TAG };
        unsafe { (*ptr).size = length };

        let elements = unsafe { (ptr as *mut u8).add(std::mem::size_of::<Array>()) };
        unsafe { std::ptr::write_bytes(elements, 0, length * std::mem::size_of::<ObjectRef>()) };

        ptr
    }

    pub unsafe fn allocate_bytearray(&mut self, map: *mut Map, length: usize) -> *mut ByteArray {
        let size = ByteArray::required_size(length);

        self.total_allocated += size;
        if self.total_allocated > self.threshold {
            unsafe { self.collect() };
            self.threshold = self.total_allocated * 2;
        }

        let ptr = if size <= SMALL_OBJECT_MAX_SIZE {
            unsafe { self.bump.allocate(size) as *mut ByteArray }
        } else {
            unsafe { self.large.allocate(size) as *mut ByteArray }
        };

        unsafe { (*ptr).header.map = (map as u64) | HEADER_TAG };
        unsafe { (*ptr).size = length };

        let elements = unsafe { (ptr as *mut u8).add(std::mem::size_of::<ByteArray>()) };
        unsafe { std::ptr::write_bytes(elements, 0, length) };

        ptr
    }

    pub unsafe fn allocate_map(
        &mut self,
        name: ObjectRef,
        slot_count: usize,
        object_size: usize,
        default: Option<ObjectRef>,
    ) -> *mut Map {
        let map_size = std::mem::size_of::<Map>();

        self.total_allocated += map_size;
        if self.total_allocated > self.threshold {
            unsafe { self.collect() };
            self.threshold = self.total_allocated * 2;
        }

        let ptr = unsafe { self.large.allocate(map_size) as *mut Map };

        unsafe {
            (*ptr).header.map = (Object::map_map_ref().as_ptr_unchecked() as u64) | HEADER_TAG
        };
        unsafe { (*ptr).object_size = object_size };
        unsafe { (*ptr).slot_count = slot_count };
        unsafe { (*ptr).name = name };
        unsafe {
            (*ptr).default = if let Some(default) = default {
                default
            } else {
                Object::false_ref()
            }
        };

        let slots_array = unsafe { self.allocate_array(ptr, slot_count) };
        unsafe { (*ptr).slots = ObjectRef::from_ptr(slots_array as *mut Object) };

        ptr
    }

    pub fn add_root(&mut self, obj: *mut Object) {
        self.roots.insert(obj);
    }

    pub fn remove_root(&mut self, obj: *mut Object) {
        self.roots.remove(&obj);
    }

    pub unsafe fn collect(&mut self) {
        unsafe { self.mark() };

        unsafe { self.sweep() };

        unsafe { self.bump.collect_empty_chunks() };

        self.total_allocated = unsafe { self.calculate_live_size() };
    }

    // TODO: add support for arrays and maps
    // for this we first need a way to "check"
    // if something is an array or a map
    // map map should encode what fields map has
    // array we need special object map
    unsafe fn mark(&mut self) {
        let mut work_list = Vec::new();

        for &root in &self.roots {
            unsafe { self.mark_object(root, &mut work_list) };
        }

        while let Some(obj) = work_list.pop() {
            let map = unsafe { (*obj).get_map() };

            let slot_count = (*map).slot_count;
            for i in 0..slot_count {
                if let Some(value) = unsafe { (*obj).get_slot_value(i) } {
                    if !value.is_int() {
                        if let Some(ptr) = value.as_ptr() {
                            unsafe { self.mark_object(ptr, &mut work_list) };
                        }
                    }
                }
            }

            if (*map).header.map & HEADER_TAG == HEADER_TAG {
                if let Some(slots_ptr) = (*map).slots.as_ptr() {
                    unsafe { self.mark_object(slots_ptr, &mut work_list) };
                }
                // Mark any other metadata objects the map references
                if let Some(name_ptr) = (*map).name.as_ptr() {
                    unsafe { self.mark_object(name_ptr, &mut work_list) };
                }
            }
        }
    }

    unsafe fn mark_object(&self, obj: *mut Object, work_list: &mut Vec<*mut Object>) {
        if obj == Object::false_ref().as_ptr().unwrap()
            || obj == Object::true_ref().as_ptr().unwrap()
        {
            return;
        }
        let header_ptr = unsafe { &mut (*obj).header };
        if header_ptr.map & MARK_BIT == 0 {
            header_ptr.map |= MARK_BIT;
            work_list.push(obj);
        }
    }

    unsafe fn sweep(&mut self) {
        let mut i = 0;
        while i < self.large.objects.len() {
            let obj = self.large.objects[i].as_ptr();

            if unsafe { (*obj).header.map & MARK_BIT } == 0 {
                unsafe { self.large.deallocate(obj) };
                self.large.objects.swap_remove(i);
            } else {
                unsafe { (*obj).header.map &= !MARK_BIT };
                i += 1;
            }
        }
    }

    unsafe fn calculate_live_size(&self) -> usize {
        let mut total = 0;

        for obj in &self.large.objects {
            let map = unsafe { (*obj.as_ptr()).get_map() };
            total += (*map).object_size;
        }

        for chunk in &self.bump.chunks {
            total += unsafe { chunk.scan_live_objects() };
        }

        total
    }
}

#[cfg(test)]
mod tests {
    use crate::object::{Map, ObjectHeader, Slot};

    use super::*;

    #[test]
    fn test_chunk_scanning() {
        unsafe {
            let mut chunk = BumpChunk::new();
            let layout = alloc::Layout::from_size_align(32, 8).unwrap();

            let obj1 = chunk.current as *mut ObjectHeader;
            chunk.current = chunk.current.add(layout.size());
            *obj1 = ObjectHeader::new(0x1000 as *mut Map);

            let obj2 = chunk.current as *mut ObjectHeader;
            chunk.current = chunk.current.add(layout.size());
            *obj2 = ObjectHeader::new(0x2000 as *mut Map);

            assert_eq!(
                chunk.scan_live_objects(),
                0,
                "Should start with no marked objects"
            );

            (*obj1).set_mark();
            assert_eq!(
                chunk.scan_live_objects(),
                1,
                "Should find one marked object"
            );

            (*obj2).set_mark();
            assert_eq!(
                chunk.scan_live_objects(),
                2,
                "Should find two marked objects"
            );

            (*obj1).clear_mark();
            (*obj2).clear_mark();
            assert_eq!(
                chunk.scan_live_objects(),
                0,
                "Should end with no marked objects"
            );
        }
    }

    #[test]
    fn test_allocation_and_collection() {
        let mut gc = GarbageCollector::new();

        unsafe {
            let map = gc.allocate_map(Object::false_ref(), 2, 32, None);

            let mut objects = Vec::new();
            for _ in 0..100 {
                objects.push(gc.allocate(map));
            }

            for obj in objects.iter().take(10) {
                gc.add_root(*obj);
            }

            gc.collect();

            for &root in gc.roots.iter() {
                assert_eq!(
                    (*root).get_map() as *const _,
                    map,
                    "Root object should survive collection"
                );
            }
        }
    }

    #[test]
    fn test_map_allocation() {
        let mut gc = GarbageCollector::new();

        unsafe {
            let map = gc.allocate_map(Object::false_ref(), 3, 48, None);

            assert_eq!((*map).slot_count, 3);
            assert_eq!((*map).object_size, 48);

            let slots = (*map).slots();
            assert_eq!(slots.size, 3);

            let slot_map = gc.allocate_map(Object::false_ref(), 5, std::mem::size_of::<Slot>(), None);
            let slot = gc.allocate(slot_map) as *mut Slot;
            (*map).set_slot(ObjectRef::from_ptr(slot as *mut Object), 0);

            // TODO: uncomment this after fix of gc mark for map & arrays
            // gc.collect();

            assert_eq!((*map).slot_count, 3);
            assert_eq!(slots.size, 3);
            // assert_eq!(
            //     (*map).get_slot(0),
            //     Some(ObjectRef::from_ptr(slot as *mut Object))
            // );
        }
    }

    #[test]
    fn test_bytearray_allocation() {
        let mut gc = GarbageCollector::new();

        unsafe {
            let bytearray_map = gc.allocate_map(Object::false_ref(), 0, 0, None);
            let bytearray = gc.allocate_bytearray(bytearray_map, 100);

            (*bytearray).set_element(0, b'H');
            (*bytearray).set_element(1, b'i');

            gc.collect();

            assert_eq!((*bytearray).get_element(0), Some(b'H'));
            assert_eq!((*bytearray).get_element(1), Some(b'i'));
        }
    }
}
