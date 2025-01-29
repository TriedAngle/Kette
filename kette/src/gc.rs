use std::{
    alloc,
    collections::{HashMap, HashSet},
    ptr, usize,
};

use crate::{
    bignum::BigNum,
    object::{
        Array, ByteArray, Float, Map, Object, ObjectHeader, ObjectRef, Quotation, Slot,
        SpecialObjects, Word,
    },
};

const SMALL_OBJECT_MAX_SIZE: usize = 64;
const BUMP_CHUNK_SIZE: usize = 64 * 1024; // 64KB chunks
const MIN_OBJECT_ALIGNMENT: usize = 8;
const ALLOCATION_METADATA_SIZE: usize = std::mem::size_of::<usize>();

pub struct AllocatorStats {
    pub chunk_count: usize,
    pub total_allocated: usize,
    pub total_objects: usize,
    pub live_objects: usize,
}

struct Chunk {
    start: *mut u8,
    current: *mut u8,
    end: *mut u8,

    object_count: usize,
    live_count: usize,
}

impl Chunk {
    unsafe fn new() -> Self {
        let layout =
            alloc::Layout::from_size_align_unchecked(BUMP_CHUNK_SIZE, MIN_OBJECT_ALIGNMENT);
        let ptr = alloc::alloc(layout);

        Self {
            start: ptr,
            current: ptr,
            end: ptr.add(BUMP_CHUNK_SIZE),
            object_count: 0,
            live_count: 0,
        }
    }

    fn remaining_space(&self) -> usize {
        unsafe { self.end.offset_from(self.current) as usize }
    }

    fn contains_address(&self, addr: *mut u8) -> bool {
        addr >= self.start && addr < self.end
    }

    unsafe fn allocate(&mut self, size: usize) -> Option<*mut u8> {
        let total_size = size + ALLOCATION_METADATA_SIZE;
        let aligned_size = (total_size + MIN_OBJECT_ALIGNMENT - 1) & !(MIN_OBJECT_ALIGNMENT - 1);

        if self.remaining_space() < aligned_size {
            return None;
        }

        *(self.current as *mut usize) = size;
        let object_start = self.current.add(ALLOCATION_METADATA_SIZE);

        self.current = self.current.add(aligned_size);
        self.object_count += 1;

        Some(object_start)
    }

    unsafe fn for_each_object<F>(&self, mut f: F)
    where
        F: FnMut(*mut ObjectHeader),
    {
        let mut current = self.start;

        while current < self.current {
            let size = *(current as *mut usize);
            let object = current.add(ALLOCATION_METADATA_SIZE) as *mut ObjectHeader;

            f(object);

            let total_size = size + ALLOCATION_METADATA_SIZE;
            let aligned_size =
                (total_size + MIN_OBJECT_ALIGNMENT - 1) & !(MIN_OBJECT_ALIGNMENT - 1);
            current = current.add(aligned_size);
        }
    }

    unsafe fn scan_live_objects(&mut self) -> usize {
        self.live_count = 0;
        let mut live_count = 0;

        self.for_each_object(|obj| {
            if (*obj).is_marked() {
                live_count += 1;
                (*obj).clear_mark();
            }
        });
        self.live_count = live_count;
        live_count
    }
}

pub struct BumpAllocator {
    chunks: Vec<Chunk>,
    current_chunk_idx: usize,
    total_allocated: usize,
    alive_objects: usize,
}

impl BumpAllocator {
    pub fn new() -> Self {
        Self {
            chunks: vec![unsafe { Chunk::new() }],
            current_chunk_idx: 0,
            total_allocated: 0,
            alive_objects: 0,
        }
    }

    pub unsafe fn allocate(&mut self, size: usize) -> *mut u8 {
        debug_assert!(size >= MIN_OBJECT_ALIGNMENT);

        if let Some(ptr) = self.chunks[self.current_chunk_idx].allocate(size) {
            self.total_allocated += size;
            return ptr;
        }

        for (idx, chunk) in self.chunks.iter_mut().enumerate() {
            if let Some(ptr) = chunk.allocate(size) {
                self.current_chunk_idx = idx;
                self.total_allocated += size;
                return ptr;
            }
        }

        self.chunks.push(unsafe { Chunk::new() });
        self.current_chunk_idx = self.chunks.len() - 1;

        let ptr = self.chunks[self.current_chunk_idx]
            .allocate(size)
            .expect("New chunk should have space");

        self.total_allocated += size;
        ptr
    }

    pub fn contains_address(&self, addr: *mut u8) -> bool {
        self.chunks.iter().any(|chunk| chunk.contains_address(addr))
    }

    pub unsafe fn sweep(&mut self) {
        self.total_allocated = 0;
        self.alive_objects = 0;
        let mut i = 0;
        while i < self.chunks.len() {
            let live_count = unsafe { self.chunks[i].scan_live_objects() };
            self.alive_objects += live_count;
            if live_count == 0 {
                self.chunks.swap_remove(i);

                if i <= self.current_chunk_idx {
                    self.current_chunk_idx = self.current_chunk_idx.saturating_sub(1);
                }
            } else {
                i += 1;
            }
        }

        if self.chunks.is_empty() {
            self.chunks.push(unsafe { Chunk::new() });
            self.current_chunk_idx = 0;
        }
    }

    pub fn stats(&self) -> AllocatorStats {
        let mut total_objects = 0;
        let mut live_objects = 0;

        for chunk in &self.chunks {
            total_objects += chunk.object_count;
            live_objects += chunk.live_count;
        }

        AllocatorStats {
            chunk_count: self.chunks.len(),
            total_allocated: self.total_allocated,
            total_objects,
            live_objects,
        }
    }
}

pub struct LargeAllocator {
    objects: Vec<ptr::NonNull<Object>>,
}

impl LargeAllocator {
    fn new() -> Self {
        Self {
            objects: Vec::new(),
        }
    }

    pub unsafe fn allocate(&mut self, size: usize) -> *mut Object {
        let layout = unsafe { alloc::Layout::from_size_align_unchecked(size, 8) };
        let ptr = unsafe { alloc::alloc(layout) as *mut Object };
        unsafe {
            self.objects.push(ptr::NonNull::new_unchecked(ptr));
        }
        ptr
    }

    pub unsafe fn deallocate(&mut self, ptr: *mut Object) {
        let map = unsafe { (*ptr).get_map() };
        let size = (*map).object_size;
        let layout = unsafe {
            alloc::Layout::from_size_align_unchecked(size.as_int_unchecked() as usize, 8)
        };
        unsafe { alloc::dealloc(ptr as *mut u8, layout) };
    }
}

pub struct GarbageCollector {
    pub bump: BumpAllocator,
    pub large: LargeAllocator,
    pub roots: HashSet<ObjectRef>,
    pub total_allocated: usize,
    pub threshold: usize,
    pub specials: SpecialObjects,
}

impl GarbageCollector {
    pub fn new() -> Self {
        Self {
            bump: BumpAllocator::new(),
            large: LargeAllocator::new(),
            roots: HashSet::new(),
            total_allocated: 0,
            threshold: 1024 * 1024, // 1MB initial threshold
            specials: SpecialObjects::new(),
        }
    }

    pub unsafe fn allocate(&mut self, map: *mut Map) -> *mut Object {
        let size = unsafe { (*map).object_size.as_int_unchecked() as usize };

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

    pub unsafe fn allocate_array(&mut self, length: usize) -> *mut Array {
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

        unsafe {
            (*ptr).header = ObjectHeader::new(self.specials.get_array_map());
            (*ptr).size = ObjectRef::from_int(length as i64);
        }

        let elements = unsafe { (ptr as *mut u8).add(std::mem::size_of::<Array>()) };
        unsafe { std::ptr::write_bytes(elements, 0, length * std::mem::size_of::<ObjectRef>()) };

        ptr
    }

    pub unsafe fn allocate_bytearray(&mut self, length: usize) -> *mut ByteArray {
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

        unsafe {
            (*ptr).header = ObjectHeader::new(self.specials.get_bytearray_map());
            (*ptr).size = length;
        }

        let elements = unsafe { (ptr as *mut u8).add(std::mem::size_of::<ByteArray>()) };
        unsafe { std::ptr::write_bytes(elements, 0, length) };

        ptr
    }

    pub unsafe fn allocate_string(&mut self, s: &str) -> *mut ByteArray {
        let ptr = unsafe { self.allocate_bytearray(s.len()) };
        unsafe { (*ptr).set_from_str(s) };
        ptr
    }

    unsafe fn allocate_slot(
        &mut self,
        name: ObjectRef,
        kind: ObjectRef,
        index: ObjectRef, // integer
    ) -> *mut Slot {
        let slot = unsafe { self.allocate(self.specials.get_slot_map()) as *mut Slot };
        unsafe { (*slot).name = name };
        unsafe { (*slot).kind = kind };
        unsafe { (*slot).index = index };
        unsafe { (*slot).ty = SpecialObjects::get_false() };
        unsafe { (*slot).guard = SpecialObjects::get_false() };
        slot
    }

    pub unsafe fn allocate_map(
        &mut self,
        name: ObjectRef,
        init_slot_capacity: usize,
        object_size: usize,
        default: ObjectRef,
    ) -> *mut Map {
        let map_size = std::mem::size_of::<Map>();

        self.total_allocated += map_size;
        if self.total_allocated > self.threshold {
            unsafe { self.collect() };
            self.threshold = self.total_allocated * 2;
        }

        let ptr = unsafe { self.large.allocate(map_size) as *mut Map };

        unsafe {
            (*ptr).header = ObjectHeader::new(self.specials.get_map_map());
        };
        unsafe { (*ptr).object_size = ObjectRef::from_int(object_size as i64) };
        unsafe { (*ptr).slot_count = ObjectRef::from_int(0) };
        unsafe { (*ptr).name = name };
        unsafe { (*ptr).default = default };

        let slots_array = unsafe { self.allocate_array(init_slot_capacity) };
        unsafe { (*ptr).slots = ObjectRef::from_array_ptr(slots_array) };

        ptr
    }

    pub unsafe fn allocate_quotation(&mut self, size: Option<usize>) -> *mut Quotation {
        let ptr = self.allocate(self.specials.get_quotation_map()) as *mut Quotation;

        (*ptr).body = ObjectRef::null();
        (*ptr).stack_effect = ObjectRef::null();
        (*ptr).compiled = ObjectRef::null();

        if let Some(size) = size {
            let body = unsafe { self.allocate_array(size) };
            unsafe { (*ptr).body = ObjectRef::from_array_ptr(body) };
        }

        ptr
    }

    pub unsafe fn allocate_word(&mut self, size: Option<usize>, flags: bool) -> *mut Word {
        let ptr = self.allocate(self.specials.get_word_map()) as *mut Word;

        let body = self.allocate_quotation(size);
        (*ptr).body = ObjectRef::from_quotation_ptr(body);

        if flags {
            let flags = self.allocate_array(4);
            (*ptr).flags = ObjectRef::from_array_ptr(flags);
        }
        (*ptr).stack_effect = ObjectRef::null();

        ptr
    }

    pub unsafe fn allocate_float(&mut self, value: f64) -> *mut Float {
        let ptr = self.allocate(self.specials.get_float_map()) as *mut Float;

        unsafe { (*ptr).float = value }
        ptr
    }

    pub unsafe fn allocate_bignum(&mut self, num_size: u64, negative: bool) -> *mut BigNum {
        let size = BigNum::required_size(num_size as usize);

        self.total_allocated += size;
        if self.total_allocated > self.threshold {
            unsafe { self.collect() };
            self.threshold = self.total_allocated * 2;
        }

        let ptr = if size <= SMALL_OBJECT_MAX_SIZE {
            unsafe { self.bump.allocate(size) as *mut BigNum }
        } else {
            unsafe { self.large.allocate(size) as *mut BigNum }
        };

        unsafe { std::ptr::write_bytes(ptr as *mut u8, 0, size) };

        unsafe {
            (*ptr).header = ObjectHeader::new(self.specials.get_bignum_map());
            (*ptr).meta = BigNum::encode_meta(num_size as u64, negative);
        }
        ptr
    }

    pub fn add_root_object(&mut self, obj: *mut Object) {
        let object = ObjectRef::from_ptr(obj);
        self.add_root(object);
    }
    pub fn add_root(&mut self, obj: ObjectRef) {
        self.roots.insert(obj);
    }

    pub fn remove_root(&mut self, obj: ObjectRef) {
        self.roots.remove(&obj);
    }

    pub unsafe fn collect(&mut self) {
        unsafe { self.mark() };

        unsafe { self.sweep() };

        self.total_allocated = unsafe { self.calculate_live_size() };
    }

    unsafe fn mark(&mut self) {
        let mut work_list = Vec::new();

        for &root in &self.roots {
            unsafe { self.mark_object(root, &mut work_list) };
        }

        while let Some(obj) = work_list.pop() {
            let object = unsafe { obj.as_ptr_unchecked() };
            let map = unsafe { (*object).get_map() };

            let slot_count = unsafe { map.slot_count.as_int_unchecked() as usize };
            for i in 0..slot_count {
                if let Some(slot) = (*map).get_slot(i) {
                    let slot = unsafe { slot.as_ptr_unchecked() as *mut Slot };
                    let kind = unsafe { (*slot).kind };
                    if kind == SpecialObjects::get_slot_kind_data() {
                        let idx = unsafe { (*slot).index.as_int_unchecked() as usize };
                        let value = unsafe { (*object).get_slot_value(idx) };

                        if let Some(value) = value {
                            unsafe { self.mark_object(value, &mut work_list) };
                        }
                    }
                } else {
                    panic!("slot doesn't exist??");
                }
            }
        }
    }

    unsafe fn mark_object(&self, obj: ObjectRef, work_list: &mut Vec<ObjectRef>) {
        if obj.is_false() || obj.is_int() {
            return;
        }

        let object = unsafe { obj.as_ptr_unchecked() };
        let header = unsafe { &mut (*object).header };

        if !header.is_marked() {
            header.set_mark();

            let map_ptr = header.map();
            if !map_ptr.is_null() {
                let map_ref = ObjectRef::from_map(map_ptr);
                if map_ptr as *mut Object != object && !map_ref.is_false() {
                    unsafe { self.mark_object(map_ref, work_list) };
                    return;
                }
            }
            if obj.as_bytearray_ptr().is_some()
                || map_ptr == self.specials.bytearray_map.as_map_ptr()
            {
                return;
            }
            if obj.as_bignum_ptr().is_some() || map_ptr == self.specials.bignum_map.as_map_ptr() {
                return;
            }

            if let Some(array) = obj.as_array_ptr() {
                self.mark_array(array, work_list);
            }

            if map_ptr == self.specials.array_map.as_map_ptr() {
                let array = obj.as_ptr_unchecked() as *mut Array;
                self.mark_array(array, work_list);
                return;
            }

            work_list.push(obj);
        }
    }

    unsafe fn mark_array(&self, array: *mut Array, work_list: &mut Vec<ObjectRef>) {
        let size = unsafe { (*array).size.as_int_unchecked() as usize };

        for i in 0..size {
            let element = unsafe { (*array).get_element_unsafe(i) };
            unsafe { self.mark_object(element, work_list) };
        }
    }

    unsafe fn sweep(&mut self) {
        let mut i = 0;
        while i < self.large.objects.len() {
            let obj = self.large.objects[i].as_ptr();

            if unsafe { !(*obj).header.is_marked() } {
                unsafe { self.large.deallocate(obj) };
                self.large.objects.swap_remove(i);
            } else {
                unsafe {
                    (*obj).header.clear_mark();
                };
                i += 1;
            }
        }

        unsafe { self.bump.sweep() };
    }

    unsafe fn calculate_live_size(&self) -> usize {
        let mut total = 0;
        total += self.large.objects.len();
        total += self.bump.alive_objects;

        total
    }
}

impl GarbageCollector {
    pub unsafe fn deep_clone(&mut self, obj: ObjectRef, levels: usize) -> ObjectRef {
        let mut cache = std::collections::HashMap::new();
        self.deep_clone_with_cache(obj, &mut cache, 0, levels)
    }

    unsafe fn deep_clone_with_cache(
        &mut self,
        obj: ObjectRef,
        cache: &mut HashMap<*mut Object, ObjectRef>,
        current_level: usize,
        levels: usize,
    ) -> ObjectRef {
        if current_level > levels && current_level == 0 {
            return obj;
        }
        if obj.is_int() || obj.is_false() {
            return obj;
        }

        let obj_ptr = obj.as_ptr_unchecked();

        if let Some(&cloned) = cache.get(&obj_ptr) {
            return cloned;
        }

        if let Some(array) = obj.as_array_ptr() {
            let size = (*array).size.as_int_unchecked() as usize;
            let new_array = self.allocate_array(size);

            cache.insert(obj_ptr, ObjectRef::from_array_ptr(new_array));

            if !(*array).size.is_int() {
                (*new_array).size =
                    self.deep_clone_with_cache((*array).size, cache, current_level + 1, levels);
            } else {
                (*new_array).size = (*array).size;
            }

            for i in 0..size {
                let elem = (*array).get_element_unsafe(i);
                let cloned_elem =
                    self.deep_clone_with_cache(elem, cache, current_level + 1, levels);
                (*new_array).set_element_unsafe(i, cloned_elem);
            }

            return ObjectRef::from_array_ptr(new_array);
        }

        if let Some(bytearray) = obj.as_bytearray_ptr() {
            let size = (*bytearray).size;
            let new_bytearray = self.allocate_bytearray(size);

            let src = (bytearray as *const u8).add(std::mem::size_of::<ByteArray>());
            let dst = (new_bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            std::ptr::copy_nonoverlapping(src, dst, size);

            return ObjectRef::from_bytearray_ptr(new_bytearray);
        }

        if let Some(float) = obj.as_float_ptr() {
            let new_float = self.allocate((*float).header.map()) as *mut Float;
            (*new_float).float = (*float).float;
            return ObjectRef::from_float_ptr(new_float);
        }

        let map = (*obj_ptr).get_map_mut();
        let slot_count = map.slot_count.as_int_unchecked() as usize;

        let new_obj = self.allocate(map);

        cache.insert(obj_ptr, ObjectRef::from_ptr(new_obj));

        for i in 0..slot_count {
            if let Some(slot_ref) = map.get_slot(i) {
                let slot = slot_ref.as_ptr_unchecked() as *const Slot;
                if (*slot).is_data_slot() {
                    let idx = (*slot).index.as_int_unchecked() as usize;
                    let value = (*obj_ptr).get_slot_value(idx).unwrap();
                    let cloned_value =
                        self.deep_clone_with_cache(value, cache, current_level + 1, levels);
                    (*new_obj).set_slot_value(idx, cloned_value);
                }
            }
        }

        ObjectRef::from_ptr(new_obj)
    }
}

impl GarbageCollector {
    pub fn init_special_objects(&mut self) {
        unsafe {
            let map_map = self.allocate_map(
                ObjectRef::null(),
                5,
                std::mem::size_of::<Map>(),
                ObjectRef::null(),
            );
            (*map_map).header = ObjectHeader::new(map_map);
            self.specials.map_map = ObjectRef::from_map(map_map);

            let bytearray_map_name =
                ObjectRef::from_bytearray_ptr(self.allocate_string("ByteArray"));
            let bytearray_map = self.allocate_map(
                bytearray_map_name,
                1,
                std::mem::size_of::<ByteArray>(),
                ObjectRef::null(),
            );
            (*bytearray_map_name.as_bytearray_ptr().unwrap()).header =
                ObjectHeader::new(bytearray_map);
            (*bytearray_map).header = ObjectHeader::new(map_map);
            self.specials.bytearray_map = ObjectRef::from_map(bytearray_map);

            let map_map_name = self.allocate_string("Map");
            (*map_map).name = ObjectRef::from_bytearray_ptr(map_map_name);

            let array_map_name = ObjectRef::from_bytearray_ptr(self.allocate_string("Array"));
            let array_map = self.allocate_map(
                array_map_name,
                1,
                std::mem::size_of::<Array>(),
                ObjectRef::null(),
            );
            (*array_map).header = ObjectHeader::new(map_map);
            self.specials.array_map = ObjectRef::from_map(array_map);

            (*(*map_map).slots.as_array_ptr().unwrap()).header = ObjectHeader::new(array_map);

            let slot_map_name = ObjectRef::from_bytearray_ptr(self.allocate_string("Slot"));
            let slot_map = self.allocate_map(
                slot_map_name,
                5,
                std::mem::size_of::<Slot>(),
                ObjectRef::null(),
            );
            self.specials.slot_map = ObjectRef::from_map(slot_map);
            (*slot_map).header = ObjectHeader::new(map_map);

            let name_name = ObjectRef::from_bytearray_ptr(self.allocate_string("name"));
            let object_size_name =
                ObjectRef::from_bytearray_ptr(self.allocate_string("object_size"));
            let slot_count_name = ObjectRef::from_bytearray_ptr(self.allocate_string("slot_count"));
            let slots_name = ObjectRef::from_bytearray_ptr(self.allocate_string("slots"));
            let default_name = ObjectRef::from_bytearray_ptr(self.allocate_string("default"));
            let size_name = ObjectRef::from_bytearray_ptr(self.allocate_string("size"));

            let slot_type_name = ObjectRef::from_bytearray_ptr(self.allocate_string("type"));
            let slot_index_name = ObjectRef::from_bytearray_ptr(self.allocate_string("index"));
            let slot_kind_name = ObjectRef::from_bytearray_ptr(self.allocate_string("kind"));
            let slot_guard_name = ObjectRef::from_bytearray_ptr(self.allocate_string("guard"));

            let map_name_slot = self.allocate_slot(
                name_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );
            let map_object_size_slot = self.allocate_slot(
                object_size_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(1),
            );
            let map_slot_count_slot = self.allocate_slot(
                slot_count_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(2),
            );
            let map_slots_slot = self.allocate_slot(
                slots_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(3),
            );
            let map_default_slot = self.allocate_slot(
                default_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(4),
            );

            (*map_map).slot_count = ObjectRef::from_int(5);
            let map_slots = (*map_map).slots.as_array_ptr().unwrap();
            (*map_slots).set_element(0, ObjectRef::from_ptr(map_name_slot as *mut Object));
            (*map_slots).set_element(1, ObjectRef::from_ptr(map_object_size_slot as *mut Object));
            (*map_slots).set_element(2, ObjectRef::from_ptr(map_slot_count_slot as *mut Object));
            (*map_slots).set_element(3, ObjectRef::from_ptr(map_slots_slot as *mut Object));
            (*map_slots).set_element(4, ObjectRef::from_ptr(map_default_slot as *mut Object));

            let array_size_slot = self.allocate_slot(
                size_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );
            let bytearray_size_slot = self.allocate_slot(
                size_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );

            (*array_map).slot_count = ObjectRef::from_int(1);
            (*bytearray_map).slot_count = ObjectRef::from_int(1);
            let array_slots = (*array_map).slots.as_array_ptr().unwrap();
            (*array_slots).set_element(0, ObjectRef::from_ptr(array_size_slot as *mut Object));
            let bytearray_slots = (*bytearray_map).slots.as_array_ptr().unwrap();
            (*bytearray_slots)
                .set_element(0, ObjectRef::from_ptr(bytearray_size_slot as *mut Object));

            let slot_name_slot = self.allocate_slot(
                name_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );
            let slot_type_slot = self.allocate_slot(
                slot_type_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(1),
            );
            let slot_index_slot = self.allocate_slot(
                slot_index_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(2),
            );
            let slot_kind_slot = self.allocate_slot(
                slot_kind_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(3),
            );
            let slot_guard_slot = self.allocate_slot(
                slot_guard_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(4),
            );

            (*slot_map).slot_count = ObjectRef::from_int(5);
            let slot_slots = (*slot_map).slots.as_array_ptr().unwrap();
            (*slot_slots).set_element(0, ObjectRef::from_ptr(slot_name_slot as *mut Object));
            (*slot_slots).set_element(1, ObjectRef::from_ptr(slot_type_slot as *mut Object));
            (*slot_slots).set_element(2, ObjectRef::from_ptr(slot_index_slot as *mut Object));
            (*slot_slots).set_element(3, ObjectRef::from_ptr(slot_kind_slot as *mut Object));
            (*slot_slots).set_element(4, ObjectRef::from_ptr(slot_guard_slot as *mut Object));

            let slot_map_name = ObjectRef::from_bytearray_ptr(self.allocate_string("True"));
            let true_map = self.allocate_map(
                slot_map_name,
                5,
                std::mem::size_of::<Object>(),
                ObjectRef::null(),
            );

            let true_object = self.allocate(true_map);
            (*true_map).default = ObjectRef::from_ptr(true_object);
            self.specials.true_object = ObjectRef::from_ptr(true_object);

            let float_map_name = ObjectRef::from_bytearray_ptr(self.allocate_string("Float"));
            let float_map = self.allocate_map(
                float_map_name,
                5,
                std::mem::size_of::<Float>(),
                ObjectRef::null(),
            );
            self.specials.float_map = ObjectRef::from_map(float_map);

            let bignum_map_name = ObjectRef::from_bytearray_ptr(self.allocate_string("ByteArray"));
            let bignum_map = self.allocate_map(
                bignum_map_name,
                1,
                std::mem::size_of::<BigNum>(),
                ObjectRef::null(),
            );
            self.specials.bignum_map = ObjectRef::from_map(bignum_map);

            let quotation_map_name =
                ObjectRef::from_bytearray_ptr(self.allocate_string("Quotation"));
            let quotation_map = self.allocate_map(
                quotation_map_name,
                3, // body, stack_effect, compiled
                std::mem::size_of::<Quotation>(),
                ObjectRef::null(),
            );
            (*quotation_map).header = ObjectHeader::new(map_map);
            self.specials.quotation_map = ObjectRef::from_map(quotation_map);

            let body_name = ObjectRef::from_bytearray_ptr(self.allocate_string("body"));
            let stack_effect_name =
                ObjectRef::from_bytearray_ptr(self.allocate_string("stack-effect"));
            let compiled_name = ObjectRef::from_bytearray_ptr(self.allocate_string("compiled"));

            let quotation_body_slot = self.allocate_slot(
                body_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );
            let quotation_stack_effect_slot = self.allocate_slot(
                stack_effect_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(1),
            );
            let quotation_compiled_slot = self.allocate_slot(
                compiled_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(2),
            );

            (*quotation_map).slot_count = ObjectRef::from_int(3);
            let quotation_slots = (*quotation_map).slots.as_array_ptr().unwrap();
            (*quotation_slots)
                .set_element(0, ObjectRef::from_ptr(quotation_body_slot as *mut Object));
            (*quotation_slots).set_element(
                1,
                ObjectRef::from_ptr(quotation_stack_effect_slot as *mut Object),
            );
            (*quotation_slots).set_element(
                2,
                ObjectRef::from_ptr(quotation_compiled_slot as *mut Object),
            );

            let word_map_name = ObjectRef::from_bytearray_ptr(self.allocate_string("Word"));
            let word_map = self.allocate_map(
                word_map_name,
                4, // name, body (Quotation), stack_effect, flags
                std::mem::size_of::<Word>(),
                ObjectRef::null(),
            );
            (*word_map).header = ObjectHeader::new(map_map);
            self.specials.word_map = ObjectRef::from_map(word_map);

            let word_name_slot_name = ObjectRef::from_bytearray_ptr(self.allocate_string("name"));
            let word_body_slot_name = ObjectRef::from_bytearray_ptr(self.allocate_string("body"));
            let word_stack_effect_slot_name =
                ObjectRef::from_bytearray_ptr(self.allocate_string("stack-effect"));
            let word_flags_slot_name = ObjectRef::from_bytearray_ptr(self.allocate_string("flags"));

            let word_name_slot = self.allocate_slot(
                word_name_slot_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );
            let word_body_slot = self.allocate_slot(
                word_body_slot_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(1),
            );
            let word_stack_effect_slot = self.allocate_slot(
                word_stack_effect_slot_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(2),
            );
            let word_flags_slot = self.allocate_slot(
                word_flags_slot_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(3),
            );

            (*word_map).slot_count = ObjectRef::from_int(4);
            let word_slots = (*word_map).slots.as_array_ptr().unwrap();
            (*word_slots).set_element(0, ObjectRef::from_ptr(word_name_slot as *mut Object));
            (*word_slots).set_element(1, ObjectRef::from_ptr(word_body_slot as *mut Object));
            (*word_slots).set_element(
                2,
                ObjectRef::from_ptr(word_stack_effect_slot as *mut Object),
            );
            (*word_slots).set_element(3, ObjectRef::from_ptr(word_flags_slot as *mut Object));

            self.add_root_object(map_map as *mut Object);
            self.add_root_object(array_map as *mut Object);
            self.add_root_object(bytearray_map as *mut Object);
            self.add_root_object(slot_map as *mut Object);
            self.add_root_object(true_map as *mut Object);
            self.add_root_object(true_object);
            self.add_root_object(float_map as *mut Object);
            self.add_root_object(bignum_map as *mut Object);
            self.add_root_object(quotation_map as *mut Object);
            self.add_root_object(word_map as *mut Object);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::object::{Map, ObjectHeader, ObjectType};

    use super::*;

    #[test]
    fn test_special_objects_initialization() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            assert!(!gc.specials.map_map.is_int(), "Map map should be a pointer");

            let map_map_ptr = gc.specials.get_map_map();
            assert_eq!((*map_map_ptr).header.map(), map_map_ptr as *mut Map);

            gc.collect();

            assert!(SpecialObjects::get_false() == ObjectRef::null());
            assert_eq!(gc.specials.get_map_map(), map_map_ptr);
        }
    }

    #[test]
    fn test_special_maps_names() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let map_map = gc.specials.get_map_map();
            let array_map = gc.specials.get_array_map();
            let bytearray_map = gc.specials.get_bytearray_map();

            assert_eq!(
                (*map_map)
                    .name
                    .as_bytearray_ptr()
                    .and_then(|p| (*p).as_str()),
                Some("Map")
            );
            assert_eq!(
                (*array_map)
                    .name
                    .as_bytearray_ptr()
                    .and_then(|p| (*p).as_str()),
                Some("Array")
            );
            assert_eq!(
                (*bytearray_map)
                    .name
                    .as_bytearray_ptr()
                    .and_then(|p| (*p).as_str()),
                Some("ByteArray")
            );

            assert_eq!((*map_map).header.map() as *const _, map_map);
            assert_eq!((*array_map).header.map() as *const _, map_map);
            assert_eq!((*bytearray_map).header.map() as *const _, map_map);
        }
    }

    #[test]
    fn test_bytearray_allocation() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let bytearray = gc.allocate_bytearray(100);

            (*bytearray).set_element(0, b'H');
            (*bytearray).set_element(1, b'i');

            gc.collect();

            assert_eq!((*bytearray).get_element(0), Some(b'H'));
            assert_eq!((*bytearray).get_element(1), Some(b'i'));
        }
    }

    #[test]
    fn test_string_allocation() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let test_str = "Hello, World!";
            let bytearray = gc.allocate_string(test_str);

            assert_eq!((*bytearray).size, test_str.len());
            assert_eq!((*bytearray).as_str(), Some(test_str));
        }
    }

    #[test]
    fn test_array_allocation() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let array = gc.allocate_array(5);
            assert_eq!((*array).size.as_int_unchecked() as usize, 5);

            let int_value = ObjectRef::from_int(42);
            (*array).set_element(0, int_value);
            assert_eq!((*array).get_element(0), Some(int_value));
        }
    }

    #[test]
    fn test_chunk_scanning() {
        unsafe {
            let mut chunk = Chunk::new();

            let obj1 =
                chunk.allocate(32).expect("First allocation should succeed") as *mut ObjectHeader;
            let obj2 = chunk
                .allocate(32)
                .expect("Second allocation should succeed")
                as *mut ObjectHeader;

            *obj1 = ObjectHeader::new(0x1000 as *mut Map);
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

            (*obj1).set_mark();
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
        gc.init_special_objects();

        unsafe {
            let name = gc.allocate_string("TestObject");
            let slot1 = gc.allocate_slot(
                SpecialObjects::get_false(),
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );
            let slot2 = gc.allocate_slot(
                SpecialObjects::get_false(),
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(1),
            );
            let map = gc.allocate_map(
                ObjectRef::from_ptr(name as _),
                2,
                32,
                SpecialObjects::get_false(),
            );

            (*map).slot_count = ObjectRef::from_int(2);
            (*map).set_slot(ObjectRef::from_ptr(slot1 as _), 0);
            (*map).set_slot(ObjectRef::from_ptr(slot2 as _), 1);

            let mut our_roots = Vec::new();

            let mut objects = Vec::new();
            for _ in 0..100 {
                objects.push(gc.allocate(map));
            }

            gc.add_root_object(map as *mut _);

            for obj in objects.iter().take(10) {
                gc.add_root_object(*obj);
                our_roots.push(*obj);
            }

            gc.collect();

            for &root in our_roots.iter() {
                assert_eq!(
                    (*root).get_map() as *const _,
                    map,
                    "Root object should survive collection"
                );
            }

            assert!(
                gc.roots.contains(&ObjectRef::from_ptr(map as *mut _)),
                "Map should survive collection"
            );
        }
    }

    #[test]
    fn test_map_allocation() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let map = gc.allocate_map(
                SpecialObjects::get_false(),
                3,
                48,
                SpecialObjects::get_false(),
            );

            assert_eq!((*map).slot_count.as_int_unchecked(), 0);
            assert_eq!((*map).object_size.as_int_unchecked(), 48);

            let slots = (*map).slots();
            assert_eq!(slots.size.as_int_unchecked(), 3);

            let slot_map = gc.allocate_map(
                SpecialObjects::get_false(),
                5,
                std::mem::size_of::<Slot>(),
                SpecialObjects::get_false(),
            );
            let slot = gc.allocate(slot_map) as *mut Slot;
            (*map).set_slot(ObjectRef::from_ptr(slot as *mut Object), 0);
            (*map).slot_count = ObjectRef::from_int(1);

            assert_eq!((*map).slot_count.as_int_unchecked(), 1);
            assert_eq!(
                (*map).get_slot(0),
                Some(ObjectRef::from_ptr(slot as *mut Object))
            );
        }
    }

    #[test]
    fn test_gc_map_marking() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let map = gc.allocate_map(
                ObjectRef::null(),
                5,
                std::mem::size_of::<Map>(),
                ObjectRef::null(),
            );

            let mapp = ObjectRef::from_ptr(map as *mut _);
            assert_eq!(map as *mut _, mapp.as_ptr_unchecked());
            gc.add_root_object(map as *mut Object);

            let map_ptr = map as *mut Map;
            let map_map_ptr = (*map).header.map();

            gc.collect();

            assert_eq!(map_map_ptr, (*map_ptr).header.map());
        }
    }

    #[test]
    fn test_gc_map_map_marking() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let map_map = gc.specials.get_map_map();
            let initial_map_map_ptr = map_map;

            let old_slot_count = (*map_map).slot_count;
            let old_object_size = (*map_map).object_size;

            gc.collect();

            let map_map_after = gc.specials.get_map_map();
            assert_eq!(
                map_map_after, initial_map_map_ptr,
                "map_map should survive collection"
            );
            assert_eq!(
                (*map_map_after).header.map(),
                map_map_after,
                "map_map should still point to itself"
            );

            assert_eq!(
                (*map_map_after).slot_count,
                old_slot_count,
                "slot_count should survive"
            );
            assert_eq!(
                (*map_map_after).object_size,
                old_object_size,
                "object_size should survive"
            );
        }
    }

    #[test]
    fn test_gc_array_marking() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let array = gc.allocate_array(5);
            let obj = gc.allocate((*array).header.map());

            (*array).set_element(0, ObjectRef::from_ptr(obj));
            (*array).set_element(1, ObjectRef::from_int(42));
            (*array).set_element(2, SpecialObjects::get_false());

            gc.add_root_object(array as *mut Object);

            gc.collect();

            assert!((*array).get_element(0).unwrap().as_ptr().is_some());
            assert_eq!((*array).get_element(1).unwrap().as_int(), Some(42));
            assert!((*array).get_element(2).unwrap().is_false());
        }
    }

    #[test]
    fn test_gc_slot_marking() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let map = gc.allocate_map(
                ObjectRef::null(),
                2,
                std::mem::size_of::<Object>() + std::mem::size_of::<ObjectRef>(),
                ObjectRef::null(),
            );

            let slot = gc.allocate_slot(
                ObjectRef::null(),
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );

            (*map).set_slot(ObjectRef::from_ptr(slot as *mut Object), 0);
            (*map).slot_count = ObjectRef::from_int(1);

            gc.add_root_object(map as *mut Object);

            gc.collect();

            assert!((*map).get_slot(0).unwrap().as_ptr().is_some());
        }
    }

    #[test]
    fn test_gc_cyclic_references() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let obj_map = gc.allocate_map(
                ObjectRef::null(),
                1, // slot capacity
                std::mem::size_of::<Object>() + std::mem::size_of::<ObjectRef>(),
                ObjectRef::null(),
            );
            gc.add_root_object(obj_map as *mut Object);

            let slot_name = gc.allocate_string("next");
            let slot = gc.allocate_slot(
                ObjectRef::from_bytearray_ptr(slot_name),
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );

            (*obj_map).set_slot(ObjectRef::from_ptr(slot as *mut Object), 0);
            (*obj_map).slot_count = ObjectRef::from_int(1);

            let obj1 = gc.allocate(obj_map);
            let obj2 = gc.allocate(obj_map);
            let obj3 = gc.allocate(obj_map);

            (*obj1).set_slot_value(0, ObjectRef::from_ptr(obj2));
            (*obj2).set_slot_value(0, ObjectRef::from_ptr(obj3));
            (*obj3).set_slot_value(0, ObjectRef::from_ptr(obj1));

            gc.add_root_object(obj1);

            let initial_size = gc.total_allocated;
            gc.collect();

            let slot_value1 = (*obj1).get_slot_value(0).unwrap();
            assert!(slot_value1.as_ptr().is_some(), "obj2 should be alive");

            let obj2_ptr = slot_value1.as_ptr_unchecked();
            let slot_value2 = (*obj2_ptr).get_slot_value(0).unwrap();
            assert!(slot_value2.as_ptr().is_some(), "obj3 should be alive");

            let obj3_ptr = slot_value2.as_ptr_unchecked();
            let slot_value3 = (*obj3_ptr).get_slot_value(0).unwrap();
            assert!(
                slot_value3.as_ptr().is_some(),
                "Reference back to obj1 should be alive"
            );

            gc.remove_root(ObjectRef::from_ptr(obj1));

            let new_root = gc.allocate(obj_map);
            gc.add_root_object(new_root);

            gc.collect();

            assert!(
                gc.total_allocated < initial_size,
                "Memory usage should decrease after collecting cycle"
            );

            (*new_root).set_slot_value(0, ObjectRef::from_int(42));
            let value = (*new_root).get_slot_value(0).unwrap();
            assert_eq!(
                value,
                ObjectRef::from_int(42),
                "New root should be usable after collection"
            );
        }
    }

    #[test]
    fn test_gc_large_object_allocation() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let large_size = 1024 * 1024; // 1MB
            let large_array = gc.allocate_array(large_size / std::mem::size_of::<ObjectRef>());

            for i in 0..10 {
                (*large_array).set_element(i, ObjectRef::from_int(i as i64));
            }

            gc.add_root_object(large_array as *mut Object);

            gc.collect();

            for i in 0..10 {
                assert_eq!(
                    (*large_array).get_element(i),
                    Some(ObjectRef::from_int(i as i64)),
                    "Array data should survive collection"
                );
            }
        }
    }

    #[test]
    fn test_object_type_tagging() {
        unsafe {
            let mut gc = GarbageCollector::new();
            gc.init_special_objects();

            let array = gc.allocate_array(5);
            let array_ref = ObjectRef::from_array_ptr(array);
            assert_eq!(array_ref.get_type(), Some(ObjectType::Array));

            let bytearray = gc.allocate_bytearray(10);
            let bytearray_ref = ObjectRef::from_bytearray_ptr(bytearray);
            assert_eq!(bytearray_ref.get_type(), Some(ObjectType::ByteArray));

            gc.add_root_object(array as *mut Object);
            gc.add_root_object(bytearray as *mut Object);
            gc.collect();

            let array_ref2 = ObjectRef::from_array_ptr(array);
            let bytearray_ref2 = ObjectRef::from_bytearray_ptr(bytearray);

            assert_eq!(array_ref2.get_type(), Some(ObjectType::Array));
            assert_eq!(bytearray_ref2.get_type(), Some(ObjectType::ByteArray));
        }
    }

    #[test]
    fn test_clone_simple_object() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let map_name = ObjectRef::from_bytearray_ptr(gc.allocate_string("Test Type"));
            let slot_name = ObjectRef::from_bytearray_ptr(gc.allocate_string("value"));

            let map = gc.allocate_map(
                map_name,
                1,
                std::mem::size_of::<Object>() + std::mem::size_of::<ObjectRef>(),
                ObjectRef::null(),
            );
            let slot = gc.allocate_slot(
                slot_name,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );

            (*map).set_slot(ObjectRef::from_ptr(slot as *mut Object), 0);
            (*map).slot_count = ObjectRef::from_int(1);

            let obj = gc.allocate(map);
            let value = ObjectRef::from_int(42);
            (*obj).set_slot_value(0, value);
            assert_eq!((*obj).get_slot_value(0), Some(ObjectRef::from_int(42)));

            let cloned = gc.deep_clone(ObjectRef::from_ptr(obj), 0);

            assert!(cloned.as_ptr().is_some());
            let cloned_obj = cloned.as_ptr_unchecked();
            assert_eq!(
                (*cloned_obj).get_slot_value(0),
                Some(ObjectRef::from_int(42))
            );
            assert_ne!(cloned_obj, obj);
        }
    }

    #[test]
    fn test_clone_array() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let array = gc.allocate_array(3);
            (*array).set_element(0, ObjectRef::from_int(1));
            (*array).set_element(1, ObjectRef::from_int(2));
            (*array).set_element(2, ObjectRef::from_int(3));

            let cloned = gc.deep_clone(ObjectRef::from_array_ptr(array), 0);

            assert!(cloned.as_array_ptr().is_some());
            let cloned_array = cloned.as_array_ptr().unwrap();
            assert_ne!(cloned_array, array);

            assert_eq!((*cloned_array).get_element(0), Some(ObjectRef::from_int(1)));
            assert_eq!((*cloned_array).get_element(1), Some(ObjectRef::from_int(2)));
            assert_eq!((*cloned_array).get_element(2), Some(ObjectRef::from_int(3)));
        }
    }

    #[test]
    fn test_clone_bytearray() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let original = gc.allocate_string("Hello, World!");
            let cloned = gc.deep_clone(ObjectRef::from_bytearray_ptr(original), 0);

            assert!(cloned.as_bytearray_ptr().is_some());
            let cloned_ba = cloned.as_bytearray_ptr().unwrap();
            assert_ne!(cloned_ba, original);

            assert_eq!((*cloned_ba).as_str(), Some("Hello, World!"));
        }
    }

    #[test]
    fn test_clone_cyclic_references() {
        let mut gc = GarbageCollector::new();
        gc.init_special_objects();

        unsafe {
            let map = gc.allocate_map(
                ObjectRef::null(),
                1,
                std::mem::size_of::<Object>() + std::mem::size_of::<ObjectRef>(),
                ObjectRef::null(),
            );

            let slot_name = gc.allocate_string("next");
            let slot_name_ref = ObjectRef::from_bytearray_ptr(slot_name);

            let slot = gc.allocate_slot(
                slot_name_ref,
                SpecialObjects::get_slot_kind_data(),
                ObjectRef::from_int(0),
            );

            (*map).set_slot(ObjectRef::from_ptr(slot as *mut Object), 0);
            (*map).slot_count = ObjectRef::from_int(1);

            let obj1 = gc.allocate(map);
            let obj2 = gc.allocate(map);
            let obj3 = gc.allocate(map);

            (*obj1).set_slot_value(0, ObjectRef::from_ptr(obj2));
            (*obj2).set_slot_value(0, ObjectRef::from_ptr(obj3));
            (*obj3).set_slot_value(0, ObjectRef::from_ptr(obj1));

            let cloned1 = gc.deep_clone(ObjectRef::from_ptr(obj1), 0);
            let cloned1_ptr = cloned1.as_ptr_unchecked();

            let cloned2 = (*cloned1_ptr).get_slot_value(0).unwrap();
            let cloned2_ptr = cloned2.as_ptr_unchecked();
            let cloned3 = (*cloned2_ptr).get_slot_value(0).unwrap();
            let cloned3_ptr = cloned3.as_ptr_unchecked();
            let back_to_cloned1 = (*cloned3_ptr).get_slot_value(0).unwrap();

            assert_eq!(back_to_cloned1.as_ptr_unchecked(), cloned1_ptr);
            assert_ne!(cloned1_ptr, obj1);
            assert_ne!(cloned2_ptr, obj2);
            assert_ne!(cloned3_ptr, obj3);
        }
    }
}
