use std::alloc::{Layout, alloc, dealloc};
use std::collections::HashMap;
use std::mem;
use std::str;

use crate::{
    Array, ByteArray, Map, Object, ObjectHeader, SLOT_CONST_DATA, SLOT_DATA,
    Slot, Tagged,
};

pub struct SpecialObjects {
    pub map_map: Tagged,
    pub object_map: Tagged,
    pub false_map: Tagged,
    pub fixnum_map: Tagged,
    pub array_map: Tagged,
    pub bytearray_map: Tagged,
    pub slot_map: Tagged,
    pub quotation_map: Tagged,
    pub word_map: Tagged,

    pub primitive_tag: Tagged,
    pub parser_tag: Tagged,
}

impl SpecialObjects {
    pub fn new() -> Self {
        SpecialObjects {
            map_map: Tagged::null(),
            object_map: Tagged::null(),
            false_map: Tagged::null(),
            fixnum_map: Tagged::null(),
            array_map: Tagged::null(),
            bytearray_map: Tagged::null(),
            slot_map: Tagged::null(),
            quotation_map: Tagged::null(),
            word_map: Tagged::null(),

            primitive_tag: Tagged::null(),
            parser_tag: Tagged::null(),
        }
    }
}

pub struct GarbageCollector {
    allocations: HashMap<*mut u8, (usize, Layout)>,
    pub specials: SpecialObjects,
    roots: Vec<Tagged>,
}

impl GarbageCollector {
    pub fn new() -> Self {
        let mut gc = GarbageCollector {
            allocations: HashMap::new(),
            specials: SpecialObjects::new(),
            roots: Vec::new(),
        };

        unsafe {
            gc.initialize_special_objects();
        }

        gc
    }

    pub fn clone(&mut self, obj: Tagged) -> Tagged {
        if obj.is_int() || obj == Tagged::null() {
            return obj;
        }

        let obj_ptr = obj.to_ptr();
        let map_ptr = unsafe { (*obj_ptr).header.get_map() };
        let map_tagged = Tagged::from_ptr(map_ptr as *mut Object);

        if map_tagged == self.specials.bytearray_map {
            let bytearray_ptr = obj_ptr as *mut ByteArray;
            let size = unsafe { (*bytearray_ptr).len() };

            let clone = self.allocate_bytearray(size);
            let clone_ptr = clone.to_ptr() as *mut ByteArray;

            for i in 0..size {
                let byte = unsafe { (*bytearray_ptr).get_byte(i) };
                unsafe { (*clone_ptr).set_byte(i, byte) };
            }

            return clone;
        }

        if map_tagged == self.specials.array_map {
            let array_ptr = obj_ptr as *mut Array;
            let size = unsafe { (*array_ptr).len() };

            let clone = self.allocate_array(size);
            let clone_ptr = clone.to_ptr() as *mut Array;

            for i in 0..size {
                let elem = unsafe { (*array_ptr).get(i) };
                unsafe { (*clone_ptr).set(i, elem) };
            }

            return clone;
        }

        let clone = self.allocate_object(map_tagged);
        let clone_ptr = clone.to_ptr();

        unsafe {
            let data_slots = (*map_ptr).data_slots.to_int() as usize;

            for i in 0..data_slots {
                let value = (*obj_ptr).get_slot(i);
                (*clone_ptr).set_slot(i, value);
            }
        }

        clone
    }

    fn mark(&self) {
        for root in &self.roots {
            self.mark_object(*root);
        }
    }

    fn mark_object(&self, tagged: Tagged) {
        if tagged.is_int() || tagged == Tagged::null() {
            return;
        }

        let obj_ptr = tagged.to_ptr();

        unsafe {
            if (*obj_ptr).header.is_marked() {
                return;
            }

            (*obj_ptr).header.mark();

            let map_ptr = (*obj_ptr).header.get_map();
            self.mark_object(Tagged::from_ptr(map_ptr as *mut Object));

            if map_ptr as *mut Object == self.specials.bytearray_map.to_ptr() {
                return;
            }

            if map_ptr as *mut Object == self.specials.array_map.to_ptr() {
                let array_ptr = obj_ptr as *mut Array;
                let size = (*array_ptr).len();

                for i in 0..size {
                    let elem = (*array_ptr).get(i);
                    self.mark_object(elem);
                }
                return;
            }

            let data_slots = (*map_ptr).data_slots.to_int() as usize;
            for i in 0..data_slots {
                let value = (*obj_ptr).get_slot(i);
                self.mark_object(value);
            }
        }
    }

    fn sweep(&mut self) {
        let mut to_free = Vec::new();

        for (&ptr, &(_size, layout)) in &self.allocations {
            let obj_ptr = ptr as *mut Object;

            unsafe {
                if !(*obj_ptr).header.is_marked() {
                    to_free.push((ptr, layout));
                } else {
                    (*obj_ptr).header.unmark();
                }
            }
        }

        for (ptr, layout) in to_free {
            unsafe {
                dealloc(ptr, layout);
            }
            self.allocations.remove(&ptr);
        }
    }

    pub fn collect_garbage(&mut self) {
        self.mark();
        self.sweep();
    }

    unsafe fn initialize_special_objects(&mut self) {
        let map_map_ptr = self.raw_allocate::<Map>(mem::size_of::<Map>());
        self.specials.map_map = Tagged::from_ptr(map_map_ptr as *mut Object);

        let object_map_ptr = self.raw_allocate::<Map>(mem::size_of::<Map>());
        self.specials.object_map =
            Tagged::from_ptr(object_map_ptr as *mut Object);

        let false_map_ptr = self.raw_allocate::<Map>(mem::size_of::<Map>());
        self.specials.false_map =
            Tagged::from_ptr(false_map_ptr as *mut Object);

        let fixnum_map_ptr = self.raw_allocate::<Map>(mem::size_of::<Map>());
        self.specials.fixnum_map =
            Tagged::from_ptr(fixnum_map_ptr as *mut Object);

        let array_map_ptr = self.raw_allocate::<Map>(mem::size_of::<Map>());
        self.specials.array_map =
            Tagged::from_ptr(array_map_ptr as *mut Object);

        let bytearray_map_ptr = self.raw_allocate::<Map>(mem::size_of::<Map>());
        self.specials.bytearray_map =
            Tagged::from_ptr(bytearray_map_ptr as *mut Object);

        unsafe {
            (*map_map_ptr).header = ObjectHeader::new(map_map_ptr);
            (*map_map_ptr).data_slots = Tagged::from_int(4);
        }

        unsafe {
            (*object_map_ptr).header = ObjectHeader::new(map_map_ptr);
            (*object_map_ptr).data_slots = Tagged::from_int(0);
        }

        unsafe {
            (*false_map_ptr).header = ObjectHeader::new(map_map_ptr);
            (*false_map_ptr).data_slots = Tagged::from_int(0);
        }

        unsafe {
            (*fixnum_map_ptr).header = ObjectHeader::new(map_map_ptr);
            (*fixnum_map_ptr).data_slots = Tagged::from_int(0);
        }

        unsafe {
            (*array_map_ptr).header = ObjectHeader::new(map_map_ptr);
            (*array_map_ptr).data_slots = Tagged::from_int(0);
        }

        unsafe {
            (*bytearray_map_ptr).header = ObjectHeader::new(map_map_ptr);
            (*bytearray_map_ptr).data_slots = Tagged::from_int(0);
        }

        let slot_map = self.create_map(
            "Slot",
            &[
                ("name", SLOT_CONST_DATA, Tagged::from_int(0)),
                ("kind", SLOT_CONST_DATA, Tagged::from_int(1)),
                ("value", SLOT_CONST_DATA, Tagged::from_int(2)),
            ],
        );
        self.specials.slot_map = slot_map;

        let quotation_map = self.create_map(
            "Quotation",
            &[
                ("effect", SLOT_CONST_DATA, Tagged::from_int(0)),
                ("body", SLOT_CONST_DATA, Tagged::from_int(1)),
            ],
        );
        self.specials.quotation_map = quotation_map;

        let word_map = self.create_map(
            "Word",
            &[
                ("name", SLOT_CONST_DATA, Tagged::from_int(0)),
                ("effect", SLOT_CONST_DATA, Tagged::from_int(1)),
                ("tags", SLOT_CONST_DATA, Tagged::from_int(2)),
                ("body", SLOT_CONST_DATA, Tagged::from_int(3)),
            ],
        );
        self.specials.word_map = word_map;

        self.specials.primitive_tag =
            self.allocate_object(self.specials.object_map);
        self.specials.parser_tag =
            self.allocate_object(self.specials.object_map);

        self.add_root(self.specials.map_map);
        self.add_root(self.specials.object_map);
        self.add_root(self.specials.false_map);
        self.add_root(self.specials.fixnum_map);
        self.add_root(self.specials.array_map);
        self.add_root(self.specials.bytearray_map);
        self.add_root(self.specials.slot_map);
        self.add_root(self.specials.quotation_map);
        self.add_root(self.specials.word_map);
        self.add_root(self.specials.primitive_tag);
        self.add_root(self.specials.parser_tag);
    }

    fn raw_allocate<T>(&mut self, size: usize) -> *mut T {
        let layout =
            Layout::from_size_align(size, mem::align_of::<T>()).unwrap();
        let ptr = unsafe { alloc(layout) };

        unsafe {
            std::ptr::write_bytes(ptr, 0, size);
        }

        self.allocations.insert(ptr, (size, layout));

        ptr as *mut T
    }

    pub fn add_root(&mut self, obj: Tagged) {
        if !obj.is_int() && obj != Tagged::null() {
            self.roots.push(obj);
        }
    }

    pub fn remove_root(&mut self, obj: Tagged) {
        self.roots.retain(|&root| root != obj);
    }

    pub fn allocate_object(&mut self, map: Tagged) -> Tagged {
        let map_ptr = map.to_ptr() as *mut Map;

        let data_slots = unsafe { (*map_ptr).data_slots.to_int() as usize };

        let base_size = mem::size_of::<Object>();
        let slots_size = data_slots * mem::size_of::<Tagged>();
        let total_size = base_size + slots_size;

        let layout =
            Layout::from_size_align(total_size, mem::align_of::<Object>())
                .unwrap();

        let ptr = unsafe { alloc(layout) };

        unsafe {
            std::ptr::write_bytes(ptr, 0, total_size);
        }

        let obj = ptr as *mut Object;
        unsafe {
            (*obj).header = ObjectHeader::new(map_ptr);
        }

        self.allocations.insert(ptr, (total_size, layout));

        Tagged::from_ptr(obj)
    }

    pub fn allocate_slot(
        &mut self,
        name: Tagged,
        kind: Tagged,
        value: Tagged,
    ) -> Tagged {
        let size = mem::size_of::<Slot>();
        let layout =
            Layout::from_size_align(size, mem::align_of::<Slot>()).unwrap();

        let ptr = unsafe { alloc(layout) };

        unsafe {
            std::ptr::write_bytes(ptr, 0, size);
        }

        let slot = ptr as *mut Slot;
        unsafe {
            (*slot).header =
                ObjectHeader::new(self.specials.slot_map.to_ptr() as *mut Map);
            (*slot).name = name;
            (*slot).kind = kind;
            (*slot).value = value;
        }

        self.allocations.insert(ptr, (size, layout));

        Tagged::from_ptr(slot as *mut Object)
    }

    pub fn allocate_map(
        &mut self,
        name: Tagged,
        slots: Tagged,
        slot_count: usize,
    ) -> Tagged {
        let size = mem::size_of::<Map>();
        let layout =
            Layout::from_size_align(size, mem::align_of::<Map>()).unwrap();

        let ptr = unsafe { alloc(layout) };

        unsafe {
            std::ptr::write_bytes(ptr, 0, size);
        }

        let data_slots = self.calculate_data_slots(slots, slot_count);

        let map = ptr as *mut Map;
        unsafe {
            (*map).header = ObjectHeader::new(
                self.specials.object_map.to_ptr() as *mut Map,
            );
            (*map).name = name;
            (*map).slots = slots;
            (*map).slot_count = Tagged::from_int(slot_count as i64);
            (*map).data_slots = Tagged::from_int(data_slots as i64);
        }

        self.allocations.insert(ptr, (size, layout));

        Tagged::from_ptr(map as *mut Object)
    }

    fn calculate_data_slots(&self, slots: Tagged, slot_count: usize) -> usize {
        let mut data_count = 0;

        if slots != Tagged::null() && slot_count > 0 {
            let slots_ptr = slots.to_ptr() as *mut Array;

            for i in 0..slot_count {
                let slot_tagged = unsafe { (*slots_ptr).get(i) };
                let slot_ptr = slot_tagged.to_ptr() as *mut Slot;

                let kind = unsafe { (*slot_ptr).kind.to_int() };
                if kind == SLOT_CONST_DATA || kind == SLOT_DATA {
                    data_count += 1;
                }
            }
        }

        data_count
    }

    pub fn create_map(
        &mut self,
        name: &str,
        slots: &[(&str, i64, Tagged)],
    ) -> Tagged {
        let name_tagged = self.allocate_string(name);

        let slots_tagged = self.allocate_array(slots.len());
        let slots_ptr = slots_tagged.to_ptr() as *mut Array;

        for (i, (slot_name, kind, value)) in slots.iter().enumerate() {
            let slot_name_tagged = self.allocate_string(slot_name);
            let kind_tagged = Tagged::from_int(*kind);

            let slot_tagged =
                self.allocate_slot(slot_name_tagged, kind_tagged, *value);

            unsafe {
                (*slots_ptr).set(i, slot_tagged);
            }
        }

        self.allocate_map(name_tagged, slots_tagged, slots.len())
    }

    pub fn push_slot(
        &mut self,
        map: Tagged,
        slot_name: &str,
        kind: i64,
        value: Tagged,
    ) -> bool {
        let map_ptr = map.to_ptr() as *mut Map;

        unsafe {
            let slots = (*map_ptr).slots;
            let slot_count = (*map_ptr).slot_count.to_int() as usize;

            if slots == Tagged::null() {
                let new_slots = self.allocate_array(1);
                let new_slot_name = self.allocate_string(slot_name);
                let new_slot = self.allocate_slot(
                    new_slot_name,
                    Tagged::from_int(kind),
                    value,
                );

                let new_slots_ptr = new_slots.to_ptr() as *mut Array;
                (*new_slots_ptr).set(0, new_slot);

                (*map_ptr).slots = new_slots;
                (*map_ptr).slot_count = Tagged::from_int(1);

                if kind == SLOT_CONST_DATA || kind == SLOT_DATA {
                    (*map_ptr).data_slots = Tagged::from_int(1);
                } else {
                    (*map_ptr).data_slots = Tagged::from_int(0);
                }

                return true;
            }

            let mut slots_ptr = slots.to_ptr() as *mut Array;
            let slots_len = (*slots_ptr).len();

            if slot_count >= slots_len {
                let new_capacity = std::cmp::max(1, slots_len * 2);
                let new_slots = self.allocate_array(new_capacity);
                let new_slots_ptr = new_slots.to_ptr() as *mut Array;

                for i in 0..slot_count {
                    let slot = (*slots_ptr).get(i);
                    (*new_slots_ptr).set(i, slot);
                }

                (*map_ptr).slots = new_slots;
                slots_ptr = new_slots_ptr;
            }

            let new_slot_name = self.allocate_string(slot_name);
            let new_slot = self.allocate_slot(
                new_slot_name,
                Tagged::from_int(kind),
                value,
            );

            (*slots_ptr).set(slot_count, new_slot);
            (*map_ptr).slot_count = Tagged::from_int((slot_count + 1) as i64);

            if kind == SLOT_CONST_DATA || kind == SLOT_DATA {
                let current_data_slots =
                    (*map_ptr).data_slots.to_int() as usize;
                (*map_ptr).data_slots =
                    Tagged::from_int((current_data_slots + 1) as i64);
            }
        }

        true
    }

    pub fn remove_slot(&mut self, map: Tagged, slot_name: &str) -> bool {
        let map_ptr = map.to_ptr() as *mut Map;

        unsafe {
            let slots = (*map_ptr).slots;
            let slot_count = (*map_ptr).slot_count.to_int() as usize;

            if slots == Tagged::null() || slot_count == 0 {
                return false;
            }

            let slots_ptr = slots.to_ptr() as *mut Array;
            let mut found_idx = None;
            let mut was_data_slot = false;

            for i in 0..slot_count {
                let slot_tagged = (*slots_ptr).get(i);
                let slot_ptr = slot_tagged.to_ptr() as *mut Slot;

                let name_tagged = (*slot_ptr).name;
                let name_ptr = name_tagged.to_ptr() as *mut ByteArray;
                let slot_name_str = (*name_ptr).as_str();

                if slot_name_str == slot_name {
                    found_idx = Some(i);
                    let kind = (*slot_ptr).kind.to_int();
                    was_data_slot =
                        kind == SLOT_CONST_DATA || kind == SLOT_DATA;
                    break;
                }
            }

            if let Some(idx) = found_idx {
                for i in idx..(slot_count - 1) {
                    let next_slot = (*slots_ptr).get(i + 1);
                    (*slots_ptr).set(i, next_slot);
                }

                (*map_ptr).slot_count =
                    Tagged::from_int((slot_count - 1) as i64);

                if was_data_slot {
                    let current_data_slots =
                        (*map_ptr).data_slots.to_int() as usize;
                    (*map_ptr).data_slots =
                        Tagged::from_int((current_data_slots - 1) as i64);
                }

                return true;
            }
        }

        false
    }

    pub fn allocate_array(&mut self, size: usize) -> Tagged {
        let elem_size = mem::size_of::<Tagged>();
        let base_size = mem::size_of::<Array>();
        let total_size = base_size + (size * elem_size);

        let layout =
            Layout::from_size_align(total_size, mem::align_of::<Array>())
                .unwrap();

        let ptr = unsafe { alloc(layout) };

        unsafe {
            std::ptr::write_bytes(ptr, 0, total_size);
        }

        let array = ptr as *mut Array;
        unsafe {
            (*array).header =
                ObjectHeader::new(self.specials.array_map.to_ptr() as *mut Map);
            (*array).size = Tagged::from_int(size as i64);
        }

        self.allocations.insert(ptr, (total_size, layout));

        Tagged::from_ptr(array as *mut Object)
    }

    pub fn allocate_bytearray(&mut self, size: usize) -> Tagged {
        let base_size = mem::size_of::<ByteArray>();
        let total_size = base_size + size;
        let layout =
            Layout::from_size_align(total_size, mem::align_of::<ByteArray>())
                .unwrap();

        let ptr = unsafe { alloc(layout) };

        unsafe {
            std::ptr::write_bytes(ptr, 0, total_size);
        }

        let bytearray = ptr as *mut ByteArray;
        unsafe {
            (*bytearray).header = ObjectHeader::new(
                self.specials.bytearray_map.to_ptr() as *mut Map,
            );
            (*bytearray).size = Tagged::from_int(size as i64);
        }

        self.allocations.insert(ptr, (total_size, layout));

        Tagged::from_ptr(bytearray as *mut Object)
    }

    pub fn allocate_string(&mut self, s: &str) -> Tagged {
        let bytes = s.as_bytes();
        let bytearray = self.allocate_bytearray(bytes.len() + 1);

        let bytearray_ptr = bytearray.to_ptr() as *mut ByteArray;

        for (i, &byte) in bytes.iter().enumerate() {
            unsafe {
                (*bytearray_ptr).set_byte(i, byte);
            }
        }

        unsafe {
            (*bytearray_ptr).set_byte(bytes.len(), 0);
        }

        bytearray
    }

    pub fn resize_array(&mut self, array: Tagged, new_size: usize) -> Tagged {
        if array.is_int() || array == Tagged::null() {
            return self.allocate_array(new_size);
        }

        let array_ptr = array.to_ptr();
        let map_ptr = unsafe { (*array_ptr).header.get_map() };
        let map_tagged = Tagged::from_ptr(map_ptr as *mut Object);

        if map_tagged != self.specials.array_map {
            return self.allocate_array(new_size);
        }

        let array_ptr = array_ptr as *mut Array;
        let old_size = unsafe { (*array_ptr).len() };

        let new_array = self.allocate_array(new_size);
        let new_array_ptr = new_array.to_ptr() as *mut Array;

        let copy_size = std::cmp::min(old_size, new_size);
        for i in 0..copy_size {
            let value = unsafe { (*array_ptr).get(i) };
            unsafe { (*new_array_ptr).set(i, value) };
        }

        new_array
    }

    pub fn resize_bytearray(
        &mut self,
        bytearray: Tagged,
        new_size: usize,
    ) -> Tagged {
        if bytearray.is_int() || bytearray == Tagged::null() {
            return self.allocate_bytearray(new_size);
        }

        let ba_ptr = bytearray.to_ptr();
        let map_ptr = unsafe { (*ba_ptr).header.get_map() };
        let map_tagged = Tagged::from_ptr(map_ptr as *mut Object);

        if map_tagged != self.specials.bytearray_map {
            return self.allocate_bytearray(new_size);
        }

        let ba_ptr = ba_ptr as *mut ByteArray;
        let old_size = unsafe { (*ba_ptr).len() };

        let new_ba = self.allocate_bytearray(new_size);
        let new_ba_ptr = new_ba.to_ptr() as *mut ByteArray;

        let copy_size = std::cmp::min(old_size, new_size);
        for i in 0..copy_size {
            let byte = unsafe { (*ba_ptr).get_byte(i) };
            unsafe { (*new_ba_ptr).set_byte(i, byte) };
        }

        new_ba
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Array, ByteArray, GarbageCollector, Map, Object, SLOT_CONST_DATA, Slot,
        Tagged,
    };

    #[test]
    fn test_initialize_special_objects() {
        let gc = GarbageCollector::new();

        assert_ne!(gc.specials.map_map, Tagged::null());
        assert_ne!(gc.specials.object_map, Tagged::null());
        assert_ne!(gc.specials.false_map, Tagged::null());
        assert_ne!(gc.specials.fixnum_map, Tagged::null());
        assert_ne!(gc.specials.array_map, Tagged::null());
        assert_ne!(gc.specials.bytearray_map, Tagged::null());

        let map_map_ptr = gc.specials.map_map.to_ptr() as *mut Map;
        unsafe { assert_eq!((*map_map_ptr).header.get_map(), map_map_ptr) }
    }

    #[test]
    fn test_allocate_object() {
        let mut gc = GarbageCollector::new();

        let name = gc.allocate_string("TestObject");
        let slots = gc.allocate_array(0);
        let map = gc.allocate_map(name, slots, 0);

        let obj = gc.allocate_object(map);

        unsafe {
            let obj_map = (*obj.to_ptr()).header.get_map();
            assert_eq!(obj_map as *mut Object, map.to_ptr());
        }
    }

    #[test]
    fn test_allocate_string() {
        let mut gc = GarbageCollector::new();

        let test_str = "Hello, World!";
        let string_obj = gc.allocate_string(test_str);

        unsafe {
            let map = (*string_obj.to_ptr()).header.get_map();
            assert_eq!(map as *mut Object, gc.specials.bytearray_map.to_ptr());

            let bytearray = string_obj.to_ptr() as *mut ByteArray;
            let size = (*bytearray).len();
            assert_eq!(size, test_str.len() + 1);

            let str_from_bytes = (*bytearray).as_str();
            assert_eq!(str_from_bytes, test_str);
        }
    }

    #[test]
    fn test_allocate_array() {
        let mut gc = GarbageCollector::new();

        let array = gc.allocate_array(5);

        unsafe {
            let map = (*array.to_ptr()).header.get_map();
            assert_eq!(map as *mut Object, gc.specials.array_map.to_ptr());

            let array_ptr = array.to_ptr() as *mut Array;
            assert_eq!((*array_ptr).len(), 5);

            for i in 0..5 {
                assert_eq!((*array_ptr).get(i), Tagged::null());
            }
        }
    }

    #[test]
    fn test_array_operations() {
        let mut gc = GarbageCollector::new();

        let array = gc.allocate_array(3);
        let val1 = Tagged::from_int(42);
        let val2 = Tagged::from_int(100);
        let val3 = gc.allocate_string("test");

        unsafe {
            let array_ptr = array.to_ptr() as *mut Array;
            (*array_ptr).set(0, val1);
            (*array_ptr).set(1, val2);
            (*array_ptr).set(2, val3);

            assert_eq!((*array_ptr).get(0), val1);
            assert_eq!((*array_ptr).get(1), val2);
            assert_eq!((*array_ptr).get(2), val3);

            let mut elements = Vec::new();
            for item in (*array_ptr).iter() {
                elements.push(item);
            }

            assert_eq!(elements.len(), 3);
            assert_eq!(elements[0], val1);
            assert_eq!(elements[1], val2);
            assert_eq!(elements[2], val3);
        }
    }

    #[test]
    fn test_resize_array() {
        let mut gc = GarbageCollector::new();

        let array = gc.allocate_array(3);
        unsafe {
            let array_ptr = array.to_ptr() as *mut Array;
            (*array_ptr).set(0, Tagged::from_int(1));
            (*array_ptr).set(1, Tagged::from_int(2));
            (*array_ptr).set(2, Tagged::from_int(3));
        }

        let larger = gc.resize_array(array, 5);
        unsafe {
            let larger_ptr = larger.to_ptr() as *mut Array;
            assert_eq!((*larger_ptr).len(), 5);

            assert_eq!((*larger_ptr).get(0).to_int(), 1);
            assert_eq!((*larger_ptr).get(1).to_int(), 2);
            assert_eq!((*larger_ptr).get(2).to_int(), 3);

            assert_eq!((*larger_ptr).get(3), Tagged::null());
            assert_eq!((*larger_ptr).get(4), Tagged::null());
        }

        let smaller = gc.resize_array(array, 2);
        unsafe {
            let smaller_ptr = smaller.to_ptr() as *mut Array;
            assert_eq!((*smaller_ptr).len(), 2);

            assert_eq!((*smaller_ptr).get(0).to_int(), 1);
            assert_eq!((*smaller_ptr).get(1).to_int(), 2);
        }
    }

    #[test]
    fn test_bytearray_operations() {
        let mut gc = GarbageCollector::new();

        let bytearray = gc.allocate_bytearray(5);

        unsafe {
            let ba_ptr = bytearray.to_ptr() as *mut ByteArray;

            (*ba_ptr).set_byte(0, b'T');
            (*ba_ptr).set_byte(1, b'E');
            (*ba_ptr).set_byte(2, b'S');
            (*ba_ptr).set_byte(3, b'T');
            (*ba_ptr).set_byte(4, b'\0');

            assert_eq!((*ba_ptr).get_byte(0), b'T');
            assert_eq!((*ba_ptr).get_byte(1), b'E');
            assert_eq!((*ba_ptr).get_byte(2), b'S');
            assert_eq!((*ba_ptr).get_byte(3), b'T');
            assert_eq!((*ba_ptr).get_byte(4), b'\0');

            assert_eq!((*ba_ptr).as_str(), "TEST");
        }
    }

    #[test]
    fn test_resize_bytearray() {
        let mut gc = GarbageCollector::new();

        let ba = gc.allocate_bytearray(4);
        unsafe {
            let ba_ptr = ba.to_ptr() as *mut ByteArray;
            (*ba_ptr).set_byte(0, b'T');
            (*ba_ptr).set_byte(1, b'E');
            (*ba_ptr).set_byte(2, b'S');
            (*ba_ptr).set_byte(3, b'T');
        }

        let larger = gc.resize_bytearray(ba, 6);
        unsafe {
            let larger_ptr = larger.to_ptr() as *mut ByteArray;
            assert_eq!((*larger_ptr).len(), 6);

            assert_eq!((*larger_ptr).get_byte(0), b'T');
            assert_eq!((*larger_ptr).get_byte(1), b'E');
            assert_eq!((*larger_ptr).get_byte(2), b'S');
            assert_eq!((*larger_ptr).get_byte(3), b'T');

            assert_eq!((*larger_ptr).get_byte(4), 0);
            assert_eq!((*larger_ptr).get_byte(5), 0);
        }

        let smaller = gc.resize_bytearray(ba, 2);
        unsafe {
            let smaller_ptr = smaller.to_ptr() as *mut ByteArray;
            assert_eq!((*smaller_ptr).len(), 2);

            assert_eq!((*smaller_ptr).get_byte(0), b'T');
            assert_eq!((*smaller_ptr).get_byte(1), b'E');
        }
    }

    #[test]
    fn test_map_and_slots() {
        let mut gc = GarbageCollector::new();

        let name = gc.allocate_string("Person");

        let slots_array = gc.allocate_array(2);

        let name_slot_name = gc.allocate_string("name");
        let name_slot_kind = Tagged::from_int(0);
        let name_slot_value = Tagged::from_int(0);
        let name_slot =
            gc.allocate_slot(name_slot_name, name_slot_kind, name_slot_value);

        let age_slot_name = gc.allocate_string("age");
        let age_slot_kind = Tagged::from_int(0);
        let age_slot_value = Tagged::from_int(1);
        let age_slot =
            gc.allocate_slot(age_slot_name, age_slot_kind, age_slot_value);

        unsafe {
            let slots_ptr = slots_array.to_ptr() as *mut Array;
            (*slots_ptr).set(0, name_slot);
            (*slots_ptr).set(1, age_slot);
        }

        let map = gc.allocate_map(name, slots_array, 2);

        unsafe {
            let map_ptr = map.to_ptr() as *mut Map;

            assert_eq!((*map_ptr).data_slots.to_int(), 2);
            assert_eq!((*map_ptr).slot_count.to_int(), 2);

            let name_ptr = (*map_ptr).name.to_ptr() as *mut ByteArray;
            assert_eq!((*name_ptr).as_str(), "Person");
        }

        let obj = gc.allocate_object(map);

        unsafe {
            let obj_ptr = obj.to_ptr();

            let name_value = gc.allocate_string("John");
            (*obj_ptr).set_slot(0, name_value);

            let age_value = Tagged::from_int(30);
            (*obj_ptr).set_slot(1, age_value);

            let name_slot_value = (*obj_ptr).get_slot(0);
            let name_slot_ptr = name_slot_value.to_ptr() as *mut ByteArray;
            assert_eq!((*name_slot_ptr).as_str(), "John");

            let age_slot_value = (*obj_ptr).get_slot(1);
            assert_eq!(age_slot_value.to_int(), 30);
        }
    }

    #[test]
    fn test_create_map_helper() {
        let mut gc = GarbageCollector::new();

        let person_map = gc.create_map(
            "Person",
            &[
                ("name", 0, Tagged::from_int(0)),
                ("age", 0, Tagged::from_int(1)),
            ],
        );

        unsafe {
            let map_ptr = person_map.to_ptr() as *mut Map;

            assert_eq!((*map_ptr).data_slots.to_int(), 2);
            assert_eq!((*map_ptr).slot_count.to_int(), 2);

            let name_ptr = (*map_ptr).name.to_ptr() as *mut ByteArray;
            assert_eq!((*name_ptr).as_str(), "Person");

            let slots = (*map_ptr).slots;
            let slots_ptr = slots.to_ptr() as *mut Array;

            let name_slot = (*slots_ptr).get(0);
            let name_slot_ptr = name_slot.to_ptr() as *mut Slot;
            let name_slot_name = (*name_slot_ptr).name;
            let name_slot_name_ptr = name_slot_name.to_ptr() as *mut ByteArray;
            assert_eq!((*name_slot_name_ptr).as_str(), "name");

            let age_slot = (*slots_ptr).get(1);
            let age_slot_ptr = age_slot.to_ptr() as *mut Slot;
            let age_slot_name = (*age_slot_ptr).name;
            let age_slot_name_ptr = age_slot_name.to_ptr() as *mut ByteArray;
            assert_eq!((*age_slot_name_ptr).as_str(), "age");
        }
    }

    #[test]
    fn test_push_slot() {
        let mut gc = GarbageCollector::new();

        let person_map = gc.create_map("Person", &[]);

        gc.push_slot(person_map, "name", 0, Tagged::from_int(0));
        gc.push_slot(person_map, "age", 0, Tagged::from_int(1));

        unsafe {
            let map_ptr = person_map.to_ptr() as *mut Map;

            assert_eq!((*map_ptr).data_slots.to_int(), 2);
            assert_eq!((*map_ptr).slot_count.to_int(), 2);

            let slots = (*map_ptr).slots;
            let slots_ptr = slots.to_ptr() as *mut Array;

            let name_slot = (*slots_ptr).get(0);
            let name_slot_ptr = name_slot.to_ptr() as *mut Slot;
            let name_slot_name = (*name_slot_ptr).name;
            let name_slot_name_ptr = name_slot_name.to_ptr() as *mut ByteArray;
            assert_eq!((*name_slot_name_ptr).as_str(), "name");

            let age_slot = (*slots_ptr).get(1);
            let age_slot_ptr = age_slot.to_ptr() as *mut Slot;
            let age_slot_name = (*age_slot_ptr).name;
            let age_slot_name_ptr = age_slot_name.to_ptr() as *mut ByteArray;
            assert_eq!((*age_slot_name_ptr).as_str(), "age");
        }

        gc.push_slot(person_map, "get_name", 2, Tagged::null());

        unsafe {
            let map_ptr = person_map.to_ptr() as *mut Map;
            assert_eq!((*map_ptr).data_slots.to_int(), 2);
            assert_eq!((*map_ptr).slot_count.to_int(), 3);
        }
    }

    #[test]
    fn test_remove_slot() {
        let mut gc = GarbageCollector::new();

        let person_map = gc.create_map(
            "Person",
            &[
                ("name", 0, Tagged::from_int(0)),
                ("age", 0, Tagged::from_int(1)),
                ("address", 0, Tagged::from_int(2)),
            ],
        );

        let result = gc.remove_slot(person_map, "age");
        assert!(result);

        unsafe {
            let map_ptr = person_map.to_ptr() as *mut Map;

            assert_eq!((*map_ptr).data_slots.to_int(), 2);
            assert_eq!((*map_ptr).slot_count.to_int(), 2);

            let slots = (*map_ptr).slots;
            let slots_ptr = slots.to_ptr() as *mut Array;

            let name_slot = (*slots_ptr).get(0);
            let name_slot_ptr = name_slot.to_ptr() as *mut Slot;
            let name_slot_name = (*name_slot_ptr).name;
            let name_slot_name_ptr = name_slot_name.to_ptr() as *mut ByteArray;
            assert_eq!((*name_slot_name_ptr).as_str(), "name");

            let addr_slot = (*slots_ptr).get(1);
            let addr_slot_ptr = addr_slot.to_ptr() as *mut Slot;
            let addr_slot_name = (*addr_slot_ptr).name;
            let addr_slot_name_ptr = addr_slot_name.to_ptr() as *mut ByteArray;
            assert_eq!((*addr_slot_name_ptr).as_str(), "address");
        }

        let result = gc.remove_slot(person_map, "non_existent");
        assert!(!result);
    }

    #[test]
    fn test_clone() {
        let mut gc = GarbageCollector::new();

        let original_str = gc.allocate_string("Test String");
        let clone_str = gc.clone(original_str);

        assert_ne!(original_str.to_ptr(), clone_str.to_ptr());
        unsafe {
            let orig_ptr = original_str.to_ptr() as *mut ByteArray;
            let clone_ptr = clone_str.to_ptr() as *mut ByteArray;

            assert_eq!((*orig_ptr).as_str(), (*clone_ptr).as_str());
        }

        let original_array = gc.allocate_array(3);
        unsafe {
            let array_ptr = original_array.to_ptr() as *mut Array;
            (*array_ptr).set(0, Tagged::from_int(1));
            (*array_ptr).set(1, Tagged::from_int(2));
            (*array_ptr).set(2, Tagged::from_int(3));
        }

        let clone_array = gc.clone(original_array);

        assert_ne!(original_array.to_ptr(), clone_array.to_ptr());
        unsafe {
            let orig_ptr = original_array.to_ptr() as *mut Array;
            let clone_ptr = clone_array.to_ptr() as *mut Array;

            assert_eq!((*orig_ptr).len(), (*clone_ptr).len());
            for i in 0..3 {
                assert_eq!((*orig_ptr).get(i), (*clone_ptr).get(i));
            }
        }

        let person_map = gc.create_map(
            "Person",
            &[
                ("name", SLOT_CONST_DATA, Tagged::from_int(0)),
                ("age", SLOT_CONST_DATA, Tagged::from_int(1)),
            ],
        );

        let original_person = gc.allocate_object(person_map);
        unsafe {
            let obj_ptr = original_person.to_ptr();
            (*obj_ptr).set_slot(0, gc.allocate_string("John"));
            (*obj_ptr).set_slot(1, Tagged::from_int(30));
        }

        let clone_person = gc.clone(original_person);

        assert_ne!(original_person.to_ptr(), clone_person.to_ptr());
        unsafe {
            let orig_ptr = original_person.to_ptr();
            let clone_ptr = clone_person.to_ptr();

            assert_eq!(
                (*orig_ptr).header.get_map(),
                (*clone_ptr).header.get_map()
            );

            let name_slot_orig = (*orig_ptr).get_slot(0);
            let name_slot_clone = (*clone_ptr).get_slot(0);
            let name_orig_ptr = name_slot_orig.to_ptr() as *mut ByteArray;
            let name_clone_ptr = name_slot_clone.to_ptr() as *mut ByteArray;

            assert_eq!((*name_orig_ptr).as_str(), (*name_clone_ptr).as_str());

            let age_slot_orig = (*orig_ptr).get_slot(1);
            let age_slot_clone = (*clone_ptr).get_slot(1);

            assert_eq!(age_slot_orig.to_int(), age_slot_clone.to_int());
        }
    }

    #[test]
    fn test_garbage_collection() {
        let mut gc = GarbageCollector::new();

        println!("test0");
        let _temp1 = gc.allocate_string("Temporary 1");
        println!("test1");
        let _temp2 = gc.allocate_array(10);
        println!("test2");

        let keep = gc.allocate_string("Keep me");
        println!("test3");
        gc.add_root(keep);
        println!("test4");

        gc.collect_garbage();
        println!("test5");

        unsafe {
            let keep_ptr = keep.to_ptr() as *mut ByteArray;
            assert_eq!((*keep_ptr).as_str(), "Keep me");
        }
        println!("test1");

        let alloc_count_before = gc.allocations.len();

        let _new1 = gc.allocate_string("New 1");
        let _new2 = gc.allocate_string("New 2");

        gc.collect_garbage();

        assert!(gc.allocations.len() > 0);
        assert!(gc.allocations.len() < alloc_count_before + 2);
    }
}
