use std::{collections::VecDeque, mem};

use crate::{ParseStackFn, StackFn};

pub const TAG_INT: u64 = 0b1;
pub const TAG_MASK_FULL: u64 = 0b11;
pub const TAG_OBJECT: u64 = 0b00;
pub const TAG_HEADER: u64 = 0b10;

pub const MARK_BIT: u64 = 0b100; // 3rd bit for mark
pub const MAP_SHIFT: u64 = 8; // Map pointer starts after 8th bit

pub const SLOT_CONST_DATA: i64 = 0;
pub const SLOT_DATA: i64 = 1;
pub const SLOT_METHOD: i64 = 2;
pub const SLOT_DYNAMIC: i64 = 3;
pub const SLOT_PARENT: i64 = 4;

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Tagged(u64);

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjectHeader(u64);

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Object {
    pub header: ObjectHeader,
    // Elements are stored directly after the size field in memory
}

// Slot kinds:
// const data: 0
// data: 1
// method: 2
// parent: 3
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Slot {
    pub header: ObjectHeader,
    pub name: Tagged,  // ByteArray
    pub kind: Tagged,  // Fixnum
    pub value: Tagged, // depends on kind
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Map {
    pub header: ObjectHeader,
    pub name: Tagged,       // ByteArray
    pub data_slots: Tagged, // Fixnum,
    pub slot_count: Tagged, // Fixnum,
    pub slots: Tagged,      // Array
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Array {
    pub header: ObjectHeader,
    pub size: Tagged,
    // Elements are stored directly after the size field in memory
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ByteArray {
    pub header: ObjectHeader,
    pub size: Tagged,
    // Elements are stored directly after the size field in memory
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Quotation {
    pub header: ObjectHeader,
    pub effect: Tagged, // effect
    pub body: Tagged,   // array
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Word {
    pub header: ObjectHeader,
    pub name: Tagged,   // bytearray
    pub effect: Tagged, // effect
    pub tags: Tagged,   // array
    pub body: Tagged,   // quotation
}

impl Tagged {
    pub const fn null() -> Self {
        Self(0)
    }

    pub const fn ffalse() -> Self {
        Self::null()
    }

    pub fn from_ptr(ptr: *mut Object) -> Self {
        debug_assert!(ptr as u64 & TAG_MASK_FULL == 0);
        Self(ptr as u64)
    }

    pub fn from_int(value: i64) -> Self {
        debug_assert!(
            value <= (i64::MAX >> 1) && value >= (i64::MIN >> 1),
            "Integer value outside of taggable range"
        );
        let shifted = value << 1;
        let transmuted: u64 = unsafe { mem::transmute(shifted) };
        Self(transmuted | TAG_INT)
    }

    pub fn from_fn(fun: StackFn) -> Tagged {
        let val: i64 = unsafe { mem::transmute(fun) };
        Self::from_int(val)
    }

    pub fn from_parse_fn(fun: ParseStackFn) -> Tagged {
        let val: i64 = unsafe { mem::transmute(fun) };
        Self::from_int(val)
    }

    pub fn to_ptr(self) -> *mut Object {
        debug_assert!(self.0 & TAG_MASK_FULL == TAG_OBJECT);
        self.0 as *mut Object
    }

    pub fn to_int(self) -> i64 {
        debug_assert!(self.0 & TAG_INT == TAG_INT, "Not an integer value");
        let transmuted: i64 = unsafe { mem::transmute(self.0) };
        let value = transmuted >> 1;
        value
    }

    pub fn to_fn(self) -> StackFn {
        let val = self.to_int();
        let fun: StackFn = unsafe { mem::transmute(val) };
        fun
    }

    pub fn to_parse_fn(self) -> ParseStackFn {
        let val = self.to_int();
        let fun: ParseStackFn = unsafe { mem::transmute(val) };
        fun
    }

    pub fn is_int(&self) -> bool {
        (self.0 & TAG_INT) == TAG_INT
    }

    pub fn is_false(&self) -> bool {
        *self == Self::ffalse()
    }
}

impl Object {
    pub unsafe fn get_slot(&self, idx: usize) -> Tagged {
        let ptr = (self as *const Self).cast::<u8>();
        let offset =
            mem::size_of::<ObjectHeader>() + idx * mem::size_of::<Tagged>();

        let slot_ptr = unsafe { ptr.add(offset).cast::<Tagged>() };
        unsafe { *slot_ptr }
    }

    pub unsafe fn set_slot(&mut self, idx: usize, value: Tagged) {
        let ptr = (self as *mut Self).cast::<u8>();
        let offset =
            mem::size_of::<ObjectHeader>() + idx * mem::size_of::<Tagged>();
        let slot_ptr = unsafe { ptr.add(offset).cast::<Tagged>() };
        unsafe {
            *slot_ptr = value;
        }
    }
}

impl ObjectHeader {
    pub fn new(map_ptr: *mut Map) -> Self {
        let header_value = TAG_HEADER | ((map_ptr as u64) << MAP_SHIFT);
        Self(header_value)
    }

    pub fn mark(&mut self) {
        self.0 |= MARK_BIT;
    }

    pub fn unmark(&mut self) {
        self.0 &= !MARK_BIT;
    }

    pub fn is_marked(&self) -> bool {
        (self.0 & MARK_BIT) != 0
    }

    pub fn get_map(&self) -> *mut Map {
        (self.0 >> MAP_SHIFT) as *mut Map
    }
}

impl Array {
    pub fn len(&self) -> usize {
        self.size.to_int() as usize
    }

    pub fn data_ptr(&mut self) -> *mut Tagged {
        let ptr = (self as *mut Self).cast::<u8>();
        let offset = mem::size_of::<ObjectHeader>() + mem::size_of::<Tagged>();
        let data_ptr = unsafe { ptr.add(offset).cast::<Tagged>() };
        data_ptr
    }

    pub unsafe fn get(&self, idx: usize) -> Tagged {
        debug_assert!(idx < self.len(), "Index out of bounds");
        let ptr = (self as *const Self).cast::<u8>();
        let offset =
            mem::size_of::<ObjectHeader>() + mem::size_of::<Tagged>() + idx * 8;
        let element_ptr = unsafe { ptr.add(offset).cast::<Tagged>() };
        unsafe { *element_ptr }
    }

    pub unsafe fn set(&mut self, idx: usize, value: Tagged) {
        debug_assert!(idx < self.len(), "Index out of bounds");
        let ptr = (self as *mut Self).cast::<u8>();
        let offset =
            mem::size_of::<ObjectHeader>() + mem::size_of::<Tagged>() + idx * 8;
        let element_ptr = unsafe { ptr.add(offset).cast::<Tagged>() };
        unsafe {
            *element_ptr = value;
        }
    }

    pub unsafe fn iter<'a>(&'a self) -> ArrayIterator<'a> {
        ArrayIterator {
            array: self,
            current: 0,
            end: self.len(),
        }
    }
}

impl ByteArray {
    pub fn len(&self) -> usize {
        self.size.to_int() as usize
    }

    pub unsafe fn get_byte(&self, idx: usize) -> u8 {
        debug_assert!(idx < self.len(), "Index out of bounds");
        let ptr = (self as *const Self).cast::<u8>();
        let offset =
            mem::size_of::<ObjectHeader>() + mem::size_of::<Tagged>() + idx;
        let byte_ptr = unsafe { ptr.add(offset) };
        unsafe { *byte_ptr }
    }

    pub unsafe fn set_byte(&mut self, idx: usize, value: u8) {
        debug_assert!(idx < self.len(), "Index out of bounds");
        let ptr = (self as *mut Self).cast::<u8>();
        let offset =
            mem::size_of::<ObjectHeader>() + mem::size_of::<Tagged>() + idx;
        let byte_ptr = unsafe { ptr.add(offset) };
        unsafe {
            *byte_ptr = value;
        }
    }

    pub unsafe fn as_str<'a>(&'a self) -> &'a str {
        let ptr = (self as *const Self).cast::<u8>();
        let offset = mem::size_of::<ObjectHeader>() + mem::size_of::<Tagged>();
        let byte_ptr = unsafe { ptr.add(offset) };
        let bytes =
            unsafe { std::slice::from_raw_parts(byte_ptr, self.len() - 1) };
        unsafe { std::str::from_utf8_unchecked(bytes) }
    }
}

pub struct ArrayIterator<'a> {
    array: &'a Array,
    current: usize,
    end: usize,
}

impl<'a> Iterator for ArrayIterator<'a> {
    type Item = Tagged;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.end {
            let value = unsafe { self.array.get(self.current) };
            self.current += 1;
            Some(value)
        } else {
            None
        }
    }
}

impl Map {
    pub unsafe fn get_slot_ptr(&self, idx: usize) -> *mut Slot {
        debug_assert!(
            idx < self.slot_count.to_int() as usize,
            "Slot index out of bounds"
        );

        if self.slots == Tagged::null() {
            return std::ptr::null_mut();
        }

        let slots_ptr = self.slots.to_ptr() as *mut Array;
        let slot_tagged = unsafe { (*slots_ptr).get(idx) };

        slot_tagged.to_ptr() as *mut Slot
    }

    pub unsafe fn slot_ptrs<'a>(&self) -> &'a [*mut Slot] {
        if self.slots == Tagged::null() {
            return &[];
        }

        let slot_count = self.slot_count.to_int() as usize;
        if slot_count == 0 {
            return &[];
        }

        let slots_ptr = self.slots.to_ptr() as *mut Array;
        let first_slot_tagged = unsafe { (*slots_ptr).get(0) };
        let first_slot_ptr = first_slot_tagged.to_ptr() as *mut Slot;

        unsafe {
            std::slice::from_raw_parts(
                &first_slot_ptr as *const *mut Slot,
                slot_count,
            )
        }
    }

    pub unsafe fn iter_slots<'a>(&'a self) -> MapSlotIterator<'a> {
        MapSlotIterator {
            map: self,
            current: 0,
            end: self.slot_count.to_int() as usize,
        }
    }

    unsafe fn get_slot_name(slot_ptr: *const Slot) -> &'static str {
        let name_tagged = unsafe { (*slot_ptr).name };
        let name_ptr = name_tagged.to_ptr() as *const ByteArray;
        unsafe { (*name_ptr).as_str() }
    }

    unsafe fn is_slot_match(
        slot_ptr: *const Slot,
        name: &str,
        kind: Option<i64>,
    ) -> bool {
        let slot_name = unsafe { Self::get_slot_name(slot_ptr) };
        slot_name == name
            && (kind.is_none()
                || unsafe { (*slot_ptr).kind.to_int() == kind.unwrap() })
    }

    unsafe fn find_slot_in_map(
        map_ptr: *const Map,
        name: &str,
        kind: Option<i64>,
    ) -> Option<*mut Slot> {
        let slot_count = unsafe { (*map_ptr).slot_count.to_int() as usize };

        if unsafe { (*map_ptr).slots == Tagged::null() } || slot_count == 0 {
            return None;
        }

        let slots_ptr = unsafe { (*map_ptr).slots.to_ptr() as *mut Array };

        for i in 0..slot_count {
            let slot_tagged = unsafe { (*slots_ptr).get(i) };
            let slot_ptr = slot_tagged.to_ptr() as *mut Slot;

            if unsafe { Self::is_slot_match(slot_ptr, name, kind) } {
                return Some(slot_ptr);
            }
        }

        None
    }

    unsafe fn get_parent_map_from_slot(
        parent_slot: *const Slot,
    ) -> Option<*mut Map> {
        let parent_tagged = unsafe { (*parent_slot).value };
        if parent_tagged != Tagged::null() {
            Some(parent_tagged.to_ptr() as *mut Map)
        } else {
            None
        }
    }

    pub fn find_slot(
        &self,
        name: &str,
        kind: Option<i64>,
    ) -> Option<*mut Slot> {
        if let Some(slot_ptr) =
            unsafe { Self::find_slot_in_map(self, name, kind) }
        {
            return Some(slot_ptr);
        }

        unsafe { self.find_in_parents(name, kind) }
    }

    pub fn find_super(
        &self,
        name: &str,
        kind: Option<i64>,
    ) -> Option<*mut Slot> {
        unsafe { self.find_in_parents(name, kind) }
    }

    unsafe fn find_in_parents(
        &self,
        name: &str,
        kind: Option<i64>,
    ) -> Option<*mut Slot> {
        let parent_slots = unsafe { self.get_parent_slots() };
        if parent_slots.is_empty() {
            return None;
        }

        let mut queue = VecDeque::new();

        for parent_slot in parent_slots {
            if let Some(parent_map) =
                unsafe { Self::get_parent_map_from_slot(parent_slot) }
            {
                queue.push_back(parent_map);
            }
        }

        while let Some(parent_map) = queue.pop_front() {
            if let Some(slot_ptr) =
                unsafe { Self::find_slot_in_map(parent_map, name, kind) }
            {
                return Some(slot_ptr);
            }

            for parent_slot in unsafe { (*parent_map).get_parent_slots() } {
                if let Some(parent_map) =
                    unsafe { Self::get_parent_map_from_slot(parent_slot) }
                {
                    queue.push_back(parent_map);
                }
            }
        }

        None
    }

    unsafe fn get_parent_slots(&self) -> Vec<*mut Slot> {
        let mut parent_slots = Vec::new();
        let slot_count = self.slot_count.to_int() as usize;

        if self.slots == Tagged::null() || slot_count == 0 {
            return parent_slots;
        }

        let slots_ptr = self.slots.to_ptr() as *mut Array;

        for i in 0..slot_count {
            let slot_tagged = unsafe { (*slots_ptr).get(i) };
            let slot_ptr = slot_tagged.to_ptr() as *mut Slot;

            if unsafe { (*slot_ptr).kind.to_int() == SLOT_PARENT } {
                parent_slots.push(slot_ptr);
            }
        }

        parent_slots
    }
}

pub struct MapSlotIterator<'a> {
    map: &'a Map,
    current: usize,
    end: usize,
}

impl<'a> Iterator for MapSlotIterator<'a> {
    type Item = *mut Slot;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.end {
            let slot_ptr = unsafe { self.map.get_slot_ptr(self.current) };
            self.current += 1;
            Some(slot_ptr)
        } else {
            None
        }
    }
}

impl Quotation {
    pub unsafe fn iter_body<'a>(&'a self) -> ArrayIterator<'a> {
        let body_array = self.body.to_ptr() as *const Array;
        unsafe { (*body_array).iter() }
    }
}

impl Word {
    pub unsafe fn iter_body<'a>(&'a self) -> ArrayIterator<'a> {
        let quotation = self.body.to_ptr() as *const Quotation;
        let body_array = unsafe { (*quotation).body.to_ptr() as *const Array };
        unsafe { (*body_array).iter() }
    }

    pub unsafe fn has_tag(&self, tag: Tagged) -> bool {
        if self.tags == Tagged::null() {
            return false;
        }

        let tags_array = self.tags.to_ptr() as *const Array;
        let tags_len = unsafe { (*tags_array).len() };

        for i in 0..tags_len {
            let current_tag = unsafe { (*tags_array).get(i) };
            if current_tag == tag {
                return true;
            }
        }

        false
    }
}

impl std::fmt::Debug for Tagged {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_int() {
            write!(f, "{}", self.to_int())
        } else if *self == Self::ffalse() {
            write!(f, "f")
        } else if self.0 & TAG_MASK_FULL == TAG_OBJECT {
            let obj_ptr = self.to_ptr();
            unsafe {
                let header = &(*obj_ptr).header;
                let map_ptr = header.get_map();

                let name_tagged = (*map_ptr).name;
                if name_tagged == Tagged::null() {
                    write!(f, "<unnamed>")
                } else {
                    let name_ptr = name_tagged.to_ptr() as *const ByteArray;
                    let name = (*name_ptr).as_str();
                    write!(f, "{{{}}}", name)
                }
            }
        } else {
            write!(f, "<invalid>")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tagged_int_conversion() {
        let value = 42;
        let tagged = Tagged::from_int(value);

        assert_eq!(tagged.0 & TAG_INT, TAG_INT);

        assert_eq!(tagged.to_int(), value);

        let value = 0;
        let tagged = Tagged::from_int(value);
        assert_eq!(tagged.to_int(), value);

        let value = -42;
        let tagged = Tagged::from_int(value);
        assert_eq!(tagged.to_int(), value);

        let value = i64::MAX >> 1;
        let tagged = Tagged::from_int(value);
        assert_eq!(tagged.to_int(), value);

        let value = i64::MIN >> 1;
        let tagged = Tagged::from_int(value);
        assert_eq!(tagged.to_int(), value);
    }

    #[test]
    fn test_tagged_is_int() {
        let int_tagged = Tagged::from_int(42);
        assert!(
            int_tagged.is_int(),
            "Tagged value should be detected as an integer"
        );

        let null_tagged = Tagged::null();
        assert!(
            !null_tagged.is_int(),
            "Null tagged should not be detected as an integer"
        );
    }

    #[test]
    fn test_tagged_bit_patterns() {
        let tagged = Tagged::from_int(42);
        assert_eq!(tagged.0 & 0x1, 0x1);

        assert_eq!(tagged.0, 85); // 42 * 2 + 1 = 85

        let tagged = Tagged::from_int(-42);
        let expected = ((-42 as i64) << 1) as u64 | 0x1;
        assert_eq!(tagged.0, expected);
    }

    #[test]
    #[should_panic(expected = "Not an integer value")]
    fn test_to_int_on_non_int() {
        Tagged::null().to_int();
    }
}
