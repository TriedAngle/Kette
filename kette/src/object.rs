use std::fmt;

pub const TAG_MASK: u64 = 0x1;
pub const TAG_OBJECT: u64 = 0x1;
pub const TAG_INT: u64 = 0x0;
pub const HEADER_TAG: u64 = 0b11;
pub const MARK_BIT: u64 = 1 << 2;
pub const HEADER_FULL_TAG: u64 = 0b111;
pub const MAP_MASK: u64 = !HEADER_FULL_TAG;

const fn empty_object() -> Object {
    Object {
        header: ObjectHeader::null(),
    }
}

pub static mut SPECIAL_OBJECTS: [Object; 7] = [
    empty_object(), // 0 = f
    empty_object(), // 1 = t
    empty_object(), // 2 = map map
    empty_object(), // 3 = parent_slot
    empty_object(), // 4 = trait_slot
    empty_object(), // 5 = data_slot
    empty_object(), // 6 = method_slot
];

fn get_special_object(index: usize) -> ObjectRef {
    unsafe { ObjectRef::from_ptr(&mut SPECIAL_OBJECTS[index]) }
}

#[repr(C)]
pub struct ObjectHeader {
    pub map: u64,
}

impl ObjectHeader {
    pub const fn null() -> Self {
        Self { map: 0 }
    }

    pub fn new(map: *mut Map) -> Self {
        let ptr_bits = map as u64 & MAP_MASK;
        Self {
            map: ptr_bits | HEADER_TAG,
        }
    }

    pub fn new_u64(value: u64) -> Self {
        let ptr_bits = value & MAP_MASK;
        Self {
            map: ptr_bits | HEADER_TAG,
        }
    }

    pub fn map(&self) -> *mut Map {
        (self.map & MAP_MASK) as *mut Map
    }

    pub fn is_marked(&self) -> bool {
        self.map & MARK_BIT != 0
    }

    pub fn set_mark(&mut self) {
        self.map |= MARK_BIT;
    }

    pub fn clear_mark(&mut self) {
        self.map &= !MARK_BIT;
    }
}

// ObjectHeader:
// [63: mark bit][62-2: map pointer][1-0: header tag (11)]
#[repr(C)]
pub struct Object {
    pub header: ObjectHeader,
}

impl Object {
    pub fn get_map(&self) -> &Map {
        unsafe { &*self.header.map() }
    }

    pub fn get_map_mut(&mut self) -> &mut Map {
        unsafe { &mut *self.header.map() }
    }

    pub fn false_ref() -> ObjectRef {
        get_special_object(0)
    }

    pub fn true_ref() -> ObjectRef {
        get_special_object(1)
    }

    pub fn map_map_ref() -> ObjectRef {
        get_special_object(2)
    }

    pub fn parent_kind_ref() -> ObjectRef {
        get_special_object(3)
    }

    pub fn trait_kind_ref() -> ObjectRef {
        get_special_object(4)
    }

    pub fn data_kind_ref() -> ObjectRef {
        get_special_object(5)
    }

    pub fn method_kind_ref() -> ObjectRef {
        get_special_object(6)
    }

    pub unsafe fn get_slot_value(&self, index: usize) -> Option<ObjectRef> {
        unsafe {
            let values = (self as *const Self).add(1) as *const ObjectRef;
            Some(*values.add(index))
        }
    }

    pub unsafe fn set_slot_value(&mut self, index: usize, value: ObjectRef) {
        unsafe {
            let values = (self as *mut Self).add(1) as *mut ObjectRef;
            *values.add(index) = value;
        }
    }

    pub fn lookup_slot_value(&self, name: &ByteArray) -> Option<ObjectRef> {
        let map = self.get_map();
        map.lookup_slot(name, None)
            .and_then(|(slot, _)| unsafe { self.get_slot_value(slot.index) })
    }

    pub fn set_slot_value_by_name(&mut self, name: &ByteArray, value: ObjectRef) -> bool {
        let map = self.get_map();
        if let Some((slot, _)) = map.lookup_slot(name, None) {
            unsafe {
                self.set_slot_value(slot.index, value);
            }
            true
        } else {
            false
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, PartialEq)]
pub struct ObjectRef(u64);

impl ObjectRef {
    pub fn from_ptr(ptr: *mut Object) -> Self {
        debug_assert!((ptr as u64 & TAG_MASK) == 0);
        Self(ptr as u64 | TAG_OBJECT)
    }

    pub fn from_int(value: i64) -> Self {
        Self(value as u64)
    }

    pub fn from_int_checked(value: i64) -> Option<Self> {
        if (value as u64 & TAG_MASK) != 0 {
            return None;
        }
        Some(Self(value as u64))
    }

    pub fn is_int(&self) -> bool {
        self.0 & TAG_MASK == TAG_INT
    }

    pub fn inner(&self) -> u64 {
        self.0
    }

    pub fn as_int(&self) -> Option<i64> {
        if self.is_int() {
            Some(self.0 as i64)
        } else {
            None
        }
    }

    pub fn as_ptr(&self) -> Option<*mut Object> {
        if !self.is_int() {
            Some((self.0 & !TAG_MASK) as *mut Object)
        } else {
            None
        }
    }

    pub unsafe fn as_int_unchecked(&self) -> i64 {
        self.0 as i64
    }

    pub unsafe fn as_ptr_unchecked(&self) -> *mut Object {
        (self.0 & !TAG_MASK) as *mut Object
    }
}

#[repr(C)]
pub struct Array {
    pub header: ObjectHeader,
    pub size: usize,
    // [ObjectRef; length] elements follow here
}

impl Array {
    pub fn required_size(n: usize) -> usize {
        let base_size = std::mem::size_of::<Array>();
        let elements_size = n * std::mem::size_of::<ObjectRef>();
        let total = base_size + elements_size;
        (total + 7) & !7
    }

    pub fn get_element(&self, index: usize) -> Option<ObjectRef> {
        if index >= self.size {
            return None;
        }

        unsafe { Some(self.get_element_unsafe(index)) }
    }

    pub fn set_element(&self, index: usize, value: ObjectRef) -> bool {
        if index >= self.size {
            return false;
        }
        unsafe {
            self.set_element_unsafe(index, value);
        }
        true
    }

    pub unsafe fn get_element_unsafe(&self, index: usize) -> ObjectRef {
        unsafe {
            let elements = (self as *const Self).add(1) as *const ObjectRef;
            *elements.add(index)
        }
    }

    pub unsafe fn set_element_unsafe(&self, index: usize, value: ObjectRef) {
        unsafe {
            let elements = (self as *const Self).add(1) as *mut ObjectRef;
            *elements.add(index) = value;
        }
    }
}

#[repr(C)]
pub struct ByteArray {
    pub header: ObjectHeader,
    pub size: usize,
    // [u8; length] elements follow here
}

impl ByteArray {
    pub fn required_size(n: usize) -> usize {
        let base_size = std::mem::size_of::<ByteArray>(); // Header + length
        let total = base_size + n;
        (total + 7) & !7
    }

    pub fn get_element(&self, index: usize) -> Option<u8> {
        if index >= self.size {
            return None;
        }

        unsafe { Some(self.get_element_unsafe(index)) }
    }

    pub fn set_element(&self, index: usize, value: u8) -> bool {
        if index >= self.size {
            return false;
        }
        unsafe {
            self.set_element_unsafe(index, value);
        }
        true
    }

    pub unsafe fn get_element_unsafe(&self, index: usize) -> u8 {
        unsafe {
            let elements = (self as *const Self).add(1) as *const u8;
            *elements.add(index)
        }
    }

    pub unsafe fn set_element_unsafe(&self, index: usize, value: u8) {
        unsafe {
            let elements = (self as *const Self).add(1) as *mut u8;
            *elements.add(index) = value;
        }
    }

    pub fn equal(&self, other: &ByteArray) -> bool {
        if self.size != other.size {
            return false;
        }

        unsafe {
            let self_bytes = (self as *const Self).add(1) as *const u8;
            let other_bytes = (other as *const ByteArray).add(1) as *const u8;

            for offset in 0..self.size {
                if *self_bytes.add(offset) != *other_bytes.add(offset) {
                    return false;
                }
            }
        }
        true
    }

    pub unsafe fn set_from_str(&mut self, s: &str) {
        debug_assert!(self.size >= s.len(), "ByteArray too small for string");
        let bytes = s.as_bytes();
        unsafe {
            let elements = (self as *mut Self).add(1) as *mut u8;
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), elements, s.len());
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        unsafe {
            let bytes =
                std::slice::from_raw_parts((self as *const Self).add(1) as *const u8, self.size);
            std::str::from_utf8(bytes).ok()
        }
    }
}

#[repr(C)]
pub struct Slot {
    pub header: ObjectHeader,
    pub name: ObjectRef, // ByteArray
    pub ty: ObjectRef,
    pub index: usize,
    pub kind: ObjectRef,
    pub guard: ObjectRef,
}

impl Slot {
    pub fn get_name(&self) -> Option<&ByteArray> {
        unsafe { self.name.as_ptr().map(|ptr| &*(ptr as *const ByteArray)) }
    }

    pub fn is_parent_slot(&self) -> bool {
        self.kind.inner() == Object::parent_kind_ref().inner()
    }

    pub fn is_trait_slot(&self) -> bool {
        self.kind.inner() == Object::trait_kind_ref().inner()
    }

    pub fn is_data_slot(&self) -> bool {
        self.kind.inner() == Object::data_kind_ref().inner()
    }
}

#[repr(C)]
pub struct Map {
    pub header: ObjectHeader,
    pub name: ObjectRef, // ByteArray
    pub object_size: usize,
    pub slot_count: usize,
    pub slots: ObjectRef, // Array
    pub default: ObjectRef,
}

impl Map {
    pub fn name(&self) -> *mut ByteArray {
        self.name.as_ptr().map(|ptr| ptr as *mut _).unwrap()
    }

    pub fn slots(&self) -> &Array {
        unsafe { &*(self.slots.as_ptr_unchecked() as *mut _ as *const _) }
    }

    pub fn get_parent_slots(&self) -> Vec<&Slot> {
        let mut parent_slots = Vec::new();

        for i in 0..self.slot_count {
            if let Some(slot_ref) = self.get_slot(i) {
                unsafe {
                    let slot = &*(slot_ref.as_ptr_unchecked() as *const Slot);
                    if slot.is_parent_slot() {
                        parent_slots.push(slot);
                    }
                }
            }
        }
        parent_slots
    }

    pub fn get_trait_slots(&self) -> Vec<&Slot> {
        let mut trait_slots = Vec::new();

        for i in 0..self.slot_count {
            if let Some(slot_ref) = self.get_slot(i) {
                unsafe {
                    let slot = &*(slot_ref.as_ptr_unchecked() as *const Slot);
                    if slot.is_trait_slot() {
                        trait_slots.push(slot);
                    }
                }
            }
        }
        trait_slots
    }

    pub fn lookup_slot(&self, name: &ByteArray, kind: Option<ObjectRef>) -> Option<(&Slot, usize)> {
        if let Some(index) = self.get_slot_index(name) {
            if let Some(slot_ref) = self.get_slot(index) {
                unsafe {
                    let slot = &*(slot_ref.as_ptr_unchecked() as *const Slot);
                    if kind.map_or(true, |k| slot.kind.inner() == k.inner()) {
                        return Some((slot, index));
                    }
                }
            }
        }

        for parent_slot in self.get_parent_slots() {
            unsafe {
                let parent_obj = &*(parent_slot.ty.as_ptr_unchecked());
                let parent_map = &*(parent_obj.header.map());
                if let Some((slot, idx)) = parent_map.lookup_slot(name, kind) {
                    return Some((slot, idx));
                }
            }
        }

        None
    }

    pub fn get_slot_index(&self, name: &ByteArray) -> Option<usize> {
        for i in 0..self.slot_count {
            if let Some(slot_ref) = self.get_slot(i) {
                unsafe {
                    let slot = &*(slot_ref.as_ptr_unchecked() as *const Slot);
                    if let Some(slot_name) = slot.get_name() {
                        if slot_name.equal(name) {
                            return Some(i);
                        }
                    }
                }
            }
        }
        None
    }

    pub fn get_slot(&self, index: usize) -> Option<ObjectRef> {
        let slots = self.slots();
        slots.get_element(index)
    }

    pub fn set_slot(&self, slot: ObjectRef, index: usize) -> bool {
        let slots = self.slots();
        slots.set_element(index, slot)
    }
}

impl fmt::Debug for ObjectRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_int() {
            write!(f, "Fixnum({})", unsafe { self.as_int_unchecked() })
        } else {
            let ptr = unsafe { self.as_ptr_unchecked() };
            let inner = self.inner();

            if inner == Object::true_ref().inner() {
                write!(f, "t")
            } else if inner == Object::false_ref().inner() {
                write!(f, "f")
            } else {
                write!(f, "OBJ({:#x})", ptr as usize)
            }
        }
    }
}

impl fmt::Debug for Map {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = unsafe {
            if let Some(ptr) = self.name.as_ptr() {
                let byte_array = &*(ptr as *const ByteArray);
                byte_array
            } else {
                return write!(f, "Map {{ name: <invalid>, ... }}");
            }
        };

        let slots = self.slots();
        let mut slot_debug = f.debug_struct("Map");
        slot_debug
            .field("name", &name)
            .field("object_size", &self.object_size)
            .field("slot_count", &self.slot_count);

        let mut formatted_slots = Vec::new();
        for i in 0..self.slot_count {
            if let Some(slot_ref) = slots.get_element(i) {
                unsafe {
                    if let Some(ptr) = slot_ref.as_ptr() {
                        let slot = &*(ptr as *const Slot);
                        formatted_slots.push(slot);
                    }
                }
            }
        }
        slot_debug.field("slots", &formatted_slots);
        slot_debug.field("default", &self.default);
        slot_debug.finish()
    }
}

impl fmt::Debug for ByteArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut bytes = Vec::with_capacity(self.size);
        for i in 0..self.size {
            if let Some(byte) = self.get_element(i) {
                bytes.push(byte);
            }
        }

        match std::str::from_utf8(&bytes) {
            Ok(s) => write!(f, "ByteArray({:?})", s),
            Err(_) => write!(f, "ByteArray(bytes: {:?})", bytes),
        }
    }
}

impl fmt::Debug for Array {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries((0..self.size).filter_map(|i| self.get_element(i)))
            .finish()
    }
}

impl fmt::Debug for Slot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = unsafe {
            if let Some(ptr) = self.name.as_ptr() {
                Some(&*(ptr as *const ByteArray))
            } else {
                None
            }
        };

        let kind_str = if self.is_parent_slot() {
            "parent"
        } else if self.is_trait_slot() {
            "trait"
        } else if self.is_data_slot() {
            "data"
        } else {
            "unknown"
        };

        f.debug_struct("Slot")
            .field("name", &name)
            .field("type", &self.ty)
            .field("index", &self.index)
            .field("kind", &kind_str)
            .field("guard", &self.guard)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::{Layout, alloc};

    #[test]
    fn test_integer_encoding() {
        let positive = 42i64;
        let pos_ref = ObjectRef::from_int(positive);
        assert!(pos_ref.is_int());
        assert_eq!(pos_ref.as_int(), Some(positive));
        assert_eq!(pos_ref.as_ptr(), None);

        let negative = -42i64;
        let neg_ref = ObjectRef::from_int(negative);
        assert!(neg_ref.is_int());
        assert_eq!(neg_ref.as_int(), Some(negative));
        assert_eq!(neg_ref.as_ptr(), None);

        let large = i64::MAX;
        let large_ref = ObjectRef::from_int_checked(large);
        assert!(large_ref.is_none());

        let min = i64::MIN;
        let min_ref = ObjectRef::from_int_checked(min);
        assert!(min_ref.is_some());
    }

    #[test]
    fn test_pointer_encoding() {
        let dummy_addr = 0x1000u64 as *mut Object;
        let ptr_ref = ObjectRef::from_ptr(dummy_addr);

        assert!(!ptr_ref.is_int());
        assert_eq!(ptr_ref.as_ptr(), Some(dummy_addr));
        assert_eq!(ptr_ref.as_int(), None);
    }

    unsafe fn create_test_array(length: usize) -> *mut Array {
        let size = Array::required_size(length);
        let align = std::mem::align_of::<Array>();
        let layout = Layout::from_size_align(size, align).unwrap();

        unsafe {
            let ptr = alloc(layout) as *mut Array;
            (*ptr).size = length;
            ptr
        }
    }

    unsafe fn create_test_bytearray(length: usize) -> *mut ByteArray {
        let size = ByteArray::required_size(length);
        let align = std::mem::align_of::<ByteArray>();
        let layout = Layout::from_size_align(size, align).unwrap();

        unsafe {
            let ptr = alloc(layout) as *mut ByteArray;
            (*ptr).size = length;
            ptr
        }
    }

    #[test]
    fn test_array_operations() {
        unsafe {
            let array = create_test_array(5);
            let array_ref = &*array;

            let obj1 = ObjectRef::from_int(42);
            let obj2 = ObjectRef::from_int(-17);

            assert!(array_ref.set_element(0, obj1));
            assert!(array_ref.set_element(1, obj2));

            assert_eq!(array_ref.get_element(0), Some(obj1));
            assert_eq!(array_ref.get_element(1), Some(obj2));

            assert!(!array_ref.set_element(5, obj1));
            assert_eq!(array_ref.get_element(5), None);

            let obj3 = ObjectRef::from_int(100);
            assert!(array_ref.set_element(0, obj3));
            assert_eq!(array_ref.get_element(0), Some(obj3));
        }
    }

    #[test]
    fn test_bytearray_operations() {
        unsafe {
            let bytearray = create_test_bytearray(10);
            let bytearray_ref = &*bytearray;

            assert!(bytearray_ref.set_element(0, 42));
            assert!(bytearray_ref.set_element(1, 255));
            assert!(bytearray_ref.set_element(9, 128));

            assert_eq!(bytearray_ref.get_element(0), Some(42));
            assert_eq!(bytearray_ref.get_element(1), Some(255));
            assert_eq!(bytearray_ref.get_element(9), Some(128));

            assert!(!bytearray_ref.set_element(10, 1));
            assert_eq!(bytearray_ref.get_element(10), None);

            assert!(bytearray_ref.set_element(0, 99));
            assert_eq!(bytearray_ref.get_element(0), Some(99));
        }
    }

    #[test]
    fn test_bytearray_equal() {
        unsafe {
            let ba1 = create_test_bytearray(3);
            let ba2 = create_test_bytearray(3);
            let ba3 = create_test_bytearray(4);

            (*ba1).set_element(0, b'a');
            (*ba1).set_element(1, b'b');
            (*ba1).set_element(2, b'c');

            (*ba2).set_element(0, b'a');
            (*ba2).set_element(1, b'b');
            (*ba2).set_element(2, b'c');

            (*ba3).set_element(0, b'a');
            (*ba3).set_element(1, b'b');
            (*ba3).set_element(2, b'c');
            (*ba3).set_element(3, b'd');

            assert!((*ba1).equal(&*ba2));
            assert!(!(*ba1).equal(&*ba3));
        }
    }
    #[test]
    fn test_header() {
        let dummy_map = unsafe { create_test_map(1, 1) };
        unsafe { (*dummy_map).header = ObjectHeader::new_u64(0x1000) };
        let header = unsafe { &mut (*dummy_map).header };

        assert_eq!(
            header.map & 0b11,
            HEADER_TAG,
            "Header tag bits should be set"
        );
        assert_eq!(
            header.map(),
            0x1000 as *mut _,
            "Should recover original value"
        );

        assert!(!header.is_marked(), "New header should not be marked");
        header.set_mark();
        assert!(header.is_marked(), "Header should be marked after set_mark");
        assert_eq!(header.map & MARK_BIT, MARK_BIT, "Mark bit should be set");
        header.clear_mark();
        assert!(
            !header.is_marked(),
            "Header should not be marked after clear_mark"
        );

        let ptr_bits = header.map & MAP_MASK;
        header.set_mark();
        assert_eq!(
            header.map & MAP_MASK,
            ptr_bits,
            "Pointer bits should be preserved when marking"
        );
        header.clear_mark();
        assert_eq!(
            header.map & MAP_MASK,
            ptr_bits,
            "Pointer bits should be preserved when clearing mark"
        );
    }

    unsafe fn create_test_object(map: *mut Map) -> *mut Object {
        let align = std::mem::align_of::<Object>();
        unsafe {
            let size = (*map).object_size;
            let layout = Layout::from_size_align(size, align).unwrap();
            let obj = alloc(layout) as *mut Object;
            (*obj).header = ObjectHeader::new(map);
            obj
        }
    }

    unsafe fn create_test_map(slot_count: usize, object_slots: usize) -> *mut Map {
        let align = std::mem::align_of::<Map>();
        let size = std::mem::size_of::<Map>();
        let layout = Layout::from_size_align(size, align).unwrap();

        unsafe {
            let map = alloc(layout) as *mut Map;

            (*map).header = ObjectHeader::new(Object::map_map_ref().as_ptr_unchecked() as *mut _);
            (*map).name = Object::false_ref();
            (*map).object_size =
                std::mem::size_of::<Object>() + (object_slots * std::mem::size_of::<ObjectRef>());
            (*map).slot_count = slot_count;
            (*map).default = Object::false_ref();

            let slots_array = create_test_array(slot_count);
            (*map).slots = ObjectRef::from_ptr(slots_array as *mut Object);

            map
        }
    }

    unsafe fn create_test_slot(name: &[u8], kind: ObjectRef) -> *mut Slot {
        let align = std::mem::align_of::<Slot>();
        let size = std::mem::size_of::<Slot>();
        let layout = Layout::from_size_align(size, align).unwrap();

        unsafe {
            let slot = alloc(layout) as *mut Slot;

            (*slot).header = ObjectHeader::null();

            let name_array = create_test_bytearray(name.len());
            for (i, &byte) in name.iter().enumerate() {
                (*name_array).set_element(i, byte);
            }

            (*slot).name = ObjectRef::from_ptr(name_array as *mut Object);
            (*slot).kind = kind;
            (*slot).ty = Object::false_ref();
            (*slot).index = 0;
            (*slot).guard = Object::false_ref();

            slot
        }
    }

    #[test]
    fn test_object_slots() {
        unsafe {
            let parent_map = create_test_map(1, 1);
            let parent_obj = create_test_object(parent_map);
            (*parent_obj).header = ObjectHeader::new(parent_map);

            let x_name = create_test_bytearray(1);
            (*x_name).set_from_str("x");

            let x_slot = create_test_slot(b"x", Object::data_kind_ref());
            (*x_slot).ty = ObjectRef::from_int(42);
            (*x_slot).index = 0;
            (*parent_map).set_slot(ObjectRef::from_ptr(x_slot as *mut Object), 0);

            (*parent_obj).set_slot_value(0, ObjectRef::from_int(100));

            let child_map = create_test_map(2, 2);
            let child_obj = create_test_object(child_map);
            (*child_obj).header = ObjectHeader::new(child_map);

            let y_slot = create_test_slot(b"y", Object::data_kind_ref());
            (*y_slot).index = 1;

            let parent_slot = create_test_slot(b"parent", Object::parent_kind_ref());
            (*parent_slot).ty = ObjectRef::from_ptr(parent_obj);

            (*child_map).set_slot(ObjectRef::from_ptr(y_slot as _), 0);
            (*child_map).set_slot(ObjectRef::from_ptr(parent_slot as _), 1);

            (*child_obj).set_slot_value(1, ObjectRef::from_int(200));
            (*child_obj).set_slot_value(0, ObjectRef::from_int(100));

            let x_lookup = create_test_bytearray(1);
            (*x_lookup).set_from_str("x");
            let y_lookup = create_test_bytearray(1);
            (*y_lookup).set_from_str("y");

            let y_value = (*child_obj).lookup_slot_value(&*y_lookup);
            assert_eq!(y_value, Some(ObjectRef::from_int(200)), "y value mismatch");

            let x_value = (*child_obj).lookup_slot_value(&*x_lookup);
            assert_eq!(x_value, Some(ObjectRef::from_int(100)), "x value mismatch");

            (*child_obj).set_slot_value_by_name(&*y_lookup, ObjectRef::from_int(300));
            let new_y_value = (*child_obj).lookup_slot_value(&*y_lookup);
            assert_eq!(
                new_y_value,
                Some(ObjectRef::from_int(300)),
                "updated y value mismatch"
            );
        }
    }
}
