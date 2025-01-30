use std::{fmt, marker::PhantomData, mem};

use crate::bignum::BigNum;

// Basic type tag (LSB)
pub const TAG_MASK: u64 = 0x1;
pub const TAG_INT: u64 = 0x1; // Integers have LSB = 1
pub const TAG_OBJECT: u64 = 0x0; // Pointers have LSB = 0

// Lower 3 bits patterns
pub const ALIGN_MASK: u64 = 0x7; // 111
pub const HEADER_TAG: u64 = 0x2; // 010
pub const MARK_BIT: u64 = 0x4; // 100

// Object type tags in upper bits (bits 63-60, giving us 16 possible types)
pub const TYPE_SHIFT: u64 = 60;
pub const TYPE_BITS: u64 = 0xF; // 4 bits for type
pub const TYPE_MASK: u64 = TYPE_BITS << TYPE_SHIFT;

pub const FALSE_VALUE: u64 = 0;

#[repr(u64)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectType {
    Normal = 0,
    Array = 1,
    ByteArray = 2,
    Float = 3,
    BigNum = 4,
    Alien = 5,
    Box = 6,
    Quotation = 7,
    Word = 8,
    // 9-15 available for future use
}

impl From<u64> for ObjectType {
    fn from(value: u64) -> Self {
        unsafe { mem::transmute(value) }
    }
}

pub const MAP_MASK: u64 = !(TYPE_MASK | ALIGN_MASK);

#[repr(C)]
pub struct ObjectHeader {
    pub map: u64,
}

impl ObjectHeader {
    pub const fn null() -> Self {
        Self {
            map: 0 | HEADER_TAG,
        }
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

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjectRef(u64);

impl ObjectRef {
    pub const fn null() -> Self {
        Self(FALSE_VALUE)
    }

    pub fn from_ptr(ptr: *mut Object) -> Self {
        debug_assert!((ptr as u64 & ALIGN_MASK) == 0);
        Self(ptr as u64)
    }

    pub fn from_int(value: i64) -> Self {
        unsafe { Self((mem::transmute::<_, u64>(value) << 1) | TAG_INT) }
    }

    pub fn from_int_checked(value: i64) -> Option<Self> {
        if value > (i64::MAX >> 1) || value < (i64::MIN >> 1) {
            return None;
        }
        Some(Self::from_int(value))
    }

    pub fn from_map(ptr: *mut Map) -> Self {
        debug_assert!((ptr as u64 & ALIGN_MASK) == 0);
        Self(ptr as u64)
    }

    pub fn from_typed_ptr(ptr: *mut Object, obj_type: ObjectType) -> Self {
        debug_assert!((ptr as u64 & ALIGN_MASK) == 0);
        Self((ptr as u64) | ((obj_type as u64) << TYPE_SHIFT))
    }

    pub fn from_array_ptr(ptr: *mut Array) -> Self {
        Self::from_typed_ptr(ptr as *mut Object, ObjectType::Array)
    }

    pub fn from_bytearray_ptr(ptr: *mut ByteArray) -> Self {
        Self::from_typed_ptr(ptr as *mut Object, ObjectType::ByteArray)
    }

    pub fn from_float_ptr(ptr: *mut Float) -> Self {
        Self::from_typed_ptr(ptr as *mut Object, ObjectType::Float)
    }

    pub fn from_bignum_ptr(ptr: *mut BigNum) -> Self {
        Self::from_typed_ptr(ptr as *mut Object, ObjectType::BigNum)
    }

    pub fn from_alien_ptr(ptr: *mut Alien) -> Self {
        Self::from_typed_ptr(ptr as *mut Object, ObjectType::Alien)
    }

    pub fn from_box_ptr(ptr: *mut BoxObject) -> Self {
        Self::from_typed_ptr(ptr as *mut Object, ObjectType::Box)
    }

    pub fn from_quotation_ptr(ptr: *mut Quotation) -> Self {
        Self::from_typed_ptr(ptr as *mut Object, ObjectType::Quotation)
    }

    pub fn from_word_ptr(ptr: *mut Word) -> Self {
        Self::from_typed_ptr(ptr as *mut Object, ObjectType::Word)
    }

    pub fn is_int(&self) -> bool {
        self.0 & TAG_MASK == TAG_INT
    }

    pub fn is_header(&self) -> bool {
        (self.0 & ALIGN_MASK) == HEADER_TAG
    }

    pub fn as_map_ptr(&self) -> *mut Map {
        (self.0 & MAP_MASK) as *mut Map
    }

    pub fn get_type(&self) -> Option<ObjectType> {
        if self.is_int() || self.is_false() || self.is_header() {
            return None;
        }
        let type_bits = (self.0 & TYPE_MASK) >> TYPE_SHIFT;
        match type_bits {
            0 => Some(ObjectType::Normal),
            1 => Some(ObjectType::Array),
            2 => Some(ObjectType::ByteArray),
            3 => Some(ObjectType::Float),
            4 => Some(ObjectType::BigNum),
            5 => Some(ObjectType::Alien),
            6 => Some(ObjectType::Box),
            7 => Some(ObjectType::Quotation),
            8 => Some(ObjectType::Word),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        if self.is_int() {
            Some(unsafe { mem::transmute::<_, i64>(self.0) >> 1 })
        } else {
            None
        }
    }

    pub unsafe fn as_int_unchecked(&self) -> i64 {
        unsafe { mem::transmute::<_, i64>(self.0) >> 1 }
    }

    pub fn is_false(&self) -> bool {
        self.0 == FALSE_VALUE
    }

    pub fn as_ptr(&self) -> Option<*mut Object> {
        if self.is_false() || self.is_int() || self.is_header() {
            None
        } else {
            Some((self.0 & MAP_MASK) as *mut Object)
        }
    }

    // TODO: make unchecked variants
    pub fn as_array_ptr(&self) -> Option<*mut Array> {
        if self.get_type() == Some(ObjectType::Array) {
            Some((self.0 & MAP_MASK) as *mut Array)
        } else {
            None
        }
    }

    pub fn as_bytearray_ptr(&self) -> Option<*mut ByteArray> {
        if self.get_type() == Some(ObjectType::ByteArray) {
            Some((self.0 & MAP_MASK) as *mut ByteArray)
        } else {
            None
        }
    }

    pub fn as_float_ptr(&self) -> Option<*mut Float> {
        if self.get_type() == Some(ObjectType::Float) {
            Some((self.0 & MAP_MASK) as *mut Float)
        } else {
            None
        }
    }

    pub fn as_bignum_ptr(&self) -> Option<*mut BigNum> {
        if self.get_type() == Some(ObjectType::BigNum) {
            Some((self.0 & MAP_MASK) as *mut BigNum)
        } else {
            None
        }
    }

    pub fn as_alien_ptr(&self) -> Option<*mut Alien> {
        if self.get_type() == Some(ObjectType::Alien) {
            Some((self.0 & MAP_MASK) as *mut Alien)
        } else {
            None
        }
    }

    pub fn as_box_ptr(&self) -> Option<*mut BoxObject> {
        if self.get_type() == Some(ObjectType::Box) {
            Some((self.0 & MAP_MASK) as *mut BoxObject)
        } else {
            None
        }
    }

    pub fn as_quotation_ptr(&self) -> Option<*mut Quotation> {
        if self.get_type() == Some(ObjectType::Quotation) {
            Some((self.0 & MAP_MASK) as *mut Quotation)
        } else {
            None
        }
    }

    pub fn as_word_ptr(&self) -> Option<*mut Word> {
        if self.get_type() == Some(ObjectType::Word) {
            Some((self.0 & MAP_MASK) as *mut Word)
        } else {
            None
        }
    }

    pub unsafe fn as_ptr_unchecked(&self) -> *mut Object {
        (self.0 & MAP_MASK) as *mut Object
    }

    pub unsafe fn as_array_ptr_unchecked(&self) -> *mut Array {
        (self.0 & MAP_MASK) as *mut Array
    }

    pub unsafe fn as_bytearray_ptr_unchecked(&self) -> *mut ByteArray {
        (self.0 & MAP_MASK) as *mut ByteArray
    }
}

pub struct SpecialObjects {
    pub map_map: ObjectRef,
    pub array_map: ObjectRef,
    pub bytearray_map: ObjectRef,
    pub slot_map: ObjectRef,
    pub box_map: ObjectRef,
    pub quotation_map: ObjectRef,
    pub word_map: ObjectRef,
    pub float_map: ObjectRef,
    pub bignum_map: ObjectRef,

    pub true_object: ObjectRef,
}

impl SpecialObjects {
    pub fn new() -> Self {
        Self {
            map_map: ObjectRef::null(),
            array_map: ObjectRef::null(),
            bytearray_map: ObjectRef::null(),
            slot_map: ObjectRef::null(),
            box_map: ObjectRef::null(),
            quotation_map: ObjectRef::null(),
            word_map: ObjectRef::null(),
            float_map: ObjectRef::null(),
            bignum_map: ObjectRef::null(),

            true_object: ObjectRef::null(),
        }
    }

    pub fn get_false() -> ObjectRef {
        ObjectRef::null()
    }

    pub fn get_slot_kind_data() -> ObjectRef {
        ObjectRef::from_int(0)
    }

    pub fn get_slot_kind_method() -> ObjectRef {
        ObjectRef::from_int(1)
    }

    pub fn get_slot_kind_parent() -> ObjectRef {
        ObjectRef::from_int(2)
    }

    pub fn get_slot_kind_trait() -> ObjectRef {
        ObjectRef::from_int(3)
    }

    // TODO: make these objects
    pub fn word_primitive() -> ObjectRef {
        ObjectRef::from_int(0)
    }

    pub fn word_parser() -> ObjectRef {
        ObjectRef::from_int(1)
    }

    pub fn word_inline() -> ObjectRef {
        ObjectRef::from_int(2)
    }

    pub fn word_recursive() -> ObjectRef {
        ObjectRef::from_int(3)
    }

    pub fn get_map_map(&self) -> *mut Map {
        unsafe { self.map_map.as_ptr_unchecked() as *mut _ }
    }

    pub fn get_array_map(&self) -> *mut Map {
        unsafe { self.array_map.as_ptr_unchecked() as *mut _ }
    }

    pub fn get_bytearray_map(&self) -> *mut Map {
        unsafe { self.bytearray_map.as_ptr_unchecked() as *mut _ }
    }

    pub fn get_slot_map(&self) -> *mut Map {
        unsafe { self.slot_map.as_ptr_unchecked() as *mut _ }
    }

    pub fn get_word_map(&self) -> *mut Map {
        unsafe { self.word_map.as_ptr_unchecked() as *mut _ }
    }

    pub fn get_box_map(&self) -> *mut Map {
        unsafe { self.box_map.as_ptr_unchecked() as *mut _ }
    }

    pub fn get_quotation_map(&self) -> *mut Map {
        unsafe { self.quotation_map.as_ptr_unchecked() as *mut _ }
    }

    pub fn get_float_map(&self) -> *mut Map {
        unsafe { self.float_map.as_ptr_unchecked() as *mut _ }
    }

    pub fn get_bignum_map(&self) -> *mut Map {
        unsafe { self.bignum_map.as_ptr_unchecked() as *mut _ }
    }
}

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

    pub fn get_map_ptr(&self) -> *mut Map {
        self.header.map()
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
        map.lookup_slot(name, None).and_then(|(slot, _)| unsafe {
            self.get_slot_value(slot.index.as_int_unchecked() as usize)
        })
    }

    pub fn set_slot_value_by_name(&mut self, name: &ByteArray, value: ObjectRef) -> bool {
        let map = self.get_map();
        if let Some((slot, _)) = map.lookup_slot(name, None) {
            unsafe {
                self.set_slot_value(slot.index.as_int_unchecked() as usize, value);
            }
            true
        } else {
            false
        }
    }
}

#[repr(C)]
pub struct Float {
    pub header: ObjectHeader,
    pub float: f64,
}

#[repr(C)]
pub struct Alien {
    pub header: ObjectHeader,
}

#[repr(C)]
pub struct BoxObject {
    pub header: ObjectHeader,
    pub boxed: ObjectRef,
}

#[repr(C)]
pub struct Array {
    pub header: ObjectHeader,
    pub size: ObjectRef, // int
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
        let size = unsafe { self.size.as_int_unchecked() as usize };
        if index >= size {
            return None;
        }

        unsafe { Some(self.get_element_unsafe(index)) }
    }

    pub fn set_element(&self, index: usize, value: ObjectRef) -> bool {
        let size = unsafe { self.size.as_int_unchecked() as usize };
        if index >= size {
            return false;
        }
        unsafe {
            self.set_element_unsafe(index, value);
        }
        true
    }

    pub fn data_ptr_mut(&mut self) -> *mut ObjectRef {
        unsafe { (self as *mut Self).add(1) as *mut _ }
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

pub struct ArrayIterator<'a> {
    array: &'a Array,
    current_index: usize,
    _phantom: PhantomData<&'a ()>,
}

impl<'a> ArrayIterator<'a> {
    pub fn new(array: &'a Array) -> Self {
        Self {
            array,
            current_index: 0,
            _phantom: PhantomData,
        }
    }
}

impl<'a> Iterator for ArrayIterator<'a> {
    type Item = ObjectRef;

    fn next(&mut self) -> Option<Self::Item> {
        let size = unsafe { self.array.size.as_int_unchecked() } as usize;
        if self.current_index >= size {
            return None;
        }

        let element = self.array.get_element(self.current_index);
        self.current_index += 1;
        element
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = unsafe { self.array.size.as_int_unchecked() } as usize;
        let remaining = size.saturating_sub(self.current_index);
        (remaining, Some(remaining))
    }
}

// Add iterator functionality to Array
impl Array {
    pub fn iter(&self) -> ArrayIterator<'_> {
        ArrayIterator::new(self)
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

    pub unsafe fn as_bytes(&self) -> &[u8] {
        let ptr = (self as *const Self).add(1) as *const u8;
        std::slice::from_raw_parts(ptr, self.size)
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
            let base_ptr = self as *const Self as *const u8 as *mut u8;
            let elements = base_ptr.add(std::mem::size_of::<ByteArray>());
            // let elements = (self as *mut Self).add(1) as *mut u8;
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
    pub index: ObjectRef,
    pub kind: ObjectRef,
    pub guard: ObjectRef,
}

impl Slot {
    pub fn get_name(&self) -> Option<&ByteArray> {
        self.name.as_bytearray_ptr().map(|ptr| unsafe { &*ptr })
    }

    pub fn is_data_slot(&self) -> bool {
        self.kind == SpecialObjects::get_slot_kind_data()
    }

    pub fn is_method_slot(&self) -> bool {
        self.kind == SpecialObjects::get_slot_kind_method()
    }

    pub fn is_parent_slot(&self) -> bool {
        self.kind == SpecialObjects::get_slot_kind_parent()
    }

    pub fn is_trait_slot(&self) -> bool {
        self.kind == SpecialObjects::get_slot_kind_trait()
    }
}

#[repr(C)]
pub struct Map {
    pub header: ObjectHeader,
    pub name: ObjectRef,        // ByteArray
    pub object_size: ObjectRef, // integer
    pub slot_count: ObjectRef,  // integer
    pub slots: ObjectRef,       // Array
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

        let slot_count = unsafe { self.slot_count.as_int_unchecked() } as usize;
        for i in 0..slot_count {
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

        let slot_count = unsafe { self.slot_count.as_int_unchecked() } as usize;
        for i in 0..slot_count {
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
                    if kind.map_or(true, |k| slot.kind == k) {
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
        let slot_count = unsafe { self.slot_count.as_int_unchecked() } as usize;
        for i in 0..slot_count {
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

#[repr(C)]
pub struct Quotation {
    pub header: ObjectHeader,
    pub body: ObjectRef, // Array
    // inferred stack effect
    pub stack_effect: ObjectRef, // Array
    pub compiled: ObjectRef,     // ptr
}

#[repr(C)]
pub struct Word {
    pub header: ObjectHeader,
    pub name: ObjectRef, // ByteArray
    pub body: ObjectRef, // Quotation
    // declared stack effect
    pub stack_effect: ObjectRef, // Array
    pub flags: ObjectRef,        // Array
}

impl fmt::Debug for ObjectRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_int() {
            write!(f, "Int({})", unsafe { self.as_int_unchecked() })
        } else if self.is_header() {
            write!(f, "Header({:#x})", self.0 & MAP_MASK)
        } else if *self == SpecialObjects::get_false() {
            write!(f, "f")
        } else {
            let type_name = match self.get_type() {
                Some(ObjectType::Normal) => "Object",
                Some(ObjectType::Array) => "Array",
                Some(ObjectType::ByteArray) => {
                    return write!(f, "ByteArray: {:?}", unsafe {
                        &*self.as_bytearray_ptr_unchecked()
                    })
                }
                Some(ObjectType::Float) => "Float",
                Some(ObjectType::BigNum) => "BigNum",
                Some(ObjectType::Alien) => "Alien",
                Some(ObjectType::Box) => "Box",
                Some(ObjectType::Quotation) => "Quotation",
                Some(ObjectType::Word) => "Word",
                None => "Invalid",
            };
            write!(f, "{}({:#x})", type_name, self.0 & MAP_MASK)
        }
    }
}

impl fmt::Debug for Map {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut slot_debug = f.debug_struct("Map");

        if self.name.is_false() {
            slot_debug.field("name", &ObjectRef::null());
        } else {
            unsafe {
                if let Some(ptr) = self.name.as_ptr() {
                    let byte_array = &*(ptr as *const ByteArray);
                    if let Some(s) = byte_array.as_str() {
                        slot_debug.field("name", &s);
                    } else {
                        slot_debug.field("name", &"<invalid utf8>");
                    }
                } else {
                    slot_debug.field("name", &"<invalid>");
                }
            }
        };

        let slots = self.slots();
        slot_debug
            .field("object_size", &self.object_size)
            .field("slot_count", &self.slot_count);
        let mut formatted_slots = Vec::new();
        let slot_count = unsafe { self.slot_count.as_int_unchecked() } as usize;
        for i in 0..slot_count {
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
        let size = unsafe { self.size.as_int_unchecked() as usize };
        f.debug_list()
            .entries((0..size).filter_map(|i| self.get_element(i)))
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

impl From<*mut Array> for ObjectRef {
    fn from(value: *mut Array) -> Self {
        Self::from_array_ptr(value)
    }
}

impl From<*mut ByteArray> for ObjectRef {
    fn from(value: *mut ByteArray) -> Self {
        Self::from_bytearray_ptr(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::{alloc, Layout};

    unsafe fn create_test_object(map: *mut Map) -> *mut Object {
        let align = std::mem::align_of::<Object>();
        unsafe {
            let size = (*map).object_size.as_int_unchecked() as usize;
            let layout = Layout::from_size_align(size, align).unwrap();
            let obj = alloc(layout) as *mut Object;
            (*obj).header = ObjectHeader::new(map);
            obj
        }
    }

    unsafe fn create_test_array(length: usize) -> *mut Array {
        let size = Array::required_size(length);
        let align = std::mem::align_of::<Array>();
        let layout = Layout::from_size_align(size, align).unwrap();

        unsafe {
            let ptr = alloc(layout) as *mut Array;
            (*ptr).size = ObjectRef::from_int(length as i64);
            (*ptr).header = ObjectHeader::null();
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
            (*ptr).header = ObjectHeader::null();
            ptr
        }
    }

    unsafe fn create_test_map(slot_count: usize, object_slots: usize) -> *mut Map {
        let align = std::mem::align_of::<Map>();
        let size = std::mem::size_of::<Map>();
        let layout = Layout::from_size_align(size, align).unwrap();

        let slot_count_obj = ObjectRef::from_int(slot_count as i64);
        let object_size_bytes =
            std::mem::size_of::<Object>() + (object_slots * std::mem::size_of::<ObjectRef>());

        unsafe {
            let map = alloc(layout) as *mut Map;
            (*map).header = ObjectHeader::null();
            (*map).name = ObjectRef::null();
            (*map).object_size = ObjectRef::from_int(object_size_bytes as i64);
            (*map).slot_count = slot_count_obj;
            (*map).default = ObjectRef::null();

            let slots_array = create_test_array(slot_count);
            (*map).slots = ObjectRef::from_array_ptr(slots_array);

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

            (*slot).name = ObjectRef::from_bytearray_ptr(name_array);
            (*slot).kind = kind;
            (*slot).ty = ObjectRef::null();
            (*slot).index = ObjectRef::from_int(0);
            (*slot).guard = ObjectRef::null();

            slot
        }
    }

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
        assert!(min_ref.is_none());
    }

    #[test]
    fn test_pointer_encoding() {
        let dummy_addr = 0x1000u64 as *mut Object;
        let ptr_ref = ObjectRef::from_ptr(dummy_addr);

        assert!(!ptr_ref.is_int());
        assert_eq!(ptr_ref.as_ptr(), Some(dummy_addr));
        assert_eq!(ptr_ref.as_int(), None);
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
        let header = ObjectHeader::new_u64(0x1000);

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
        let mut header = header;
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

    #[test]
    fn test_object_slots() {
        unsafe {
            let parent_map = create_test_map(1, 1);
            let parent_obj = create_test_object(parent_map);
            (*parent_obj).header = ObjectHeader::new(parent_map);

            let x_slot = create_test_slot(b"x", ObjectRef::from_int(0));
            (*x_slot).ty = ObjectRef::from_int(42);
            (*x_slot).index = ObjectRef::from_int(0);
            (*parent_map).set_slot(ObjectRef::from_ptr(x_slot as *mut Object), 0);
            (*parent_map).slot_count = ObjectRef::from_int(1);

            (*parent_obj).set_slot_value(0, ObjectRef::from_int(100));

            let child_map = create_test_map(2, 2);
            let child_obj = create_test_object(child_map);
            (*child_obj).header = ObjectHeader::new(child_map);

            let y_slot = create_test_slot(b"y", ObjectRef::from_int(0));
            (*y_slot).index = ObjectRef::from_int(1);

            let parent_slot = create_test_slot(b"parent", ObjectRef::from_int(2));
            (*parent_slot).ty = ObjectRef::from_ptr(parent_obj);

            (*child_map).set_slot(ObjectRef::from_ptr(y_slot as *mut Object), 0);
            (*child_map).set_slot(ObjectRef::from_ptr(parent_slot as *mut Object), 1);
            (*child_map).slot_count = ObjectRef::from_int(2);

            (*child_obj).set_slot_value(0, ObjectRef::from_int(100));
            (*child_obj).set_slot_value(1, ObjectRef::from_int(200));

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

    #[test]
    fn test_array_iterator() {
        unsafe {
            let array = create_test_array(3);
            let array_ref = &*array;

            array_ref.set_element(0, ObjectRef::from_int(1));
            array_ref.set_element(1, ObjectRef::from_int(2));
            array_ref.set_element(2, ObjectRef::from_int(3));

            let mut values = Vec::new();
            for obj_ref in array_ref.iter() {
                values.push(obj_ref.as_int().unwrap());
            }

            assert_eq!(values, vec![1, 2, 3]);

            let mut iter = array_ref.iter();
            assert_eq!(iter.size_hint(), (3, Some(3)));
            iter.next();
            assert_eq!(iter.size_hint(), (2, Some(2)));
            iter.next();
            assert_eq!(iter.size_hint(), (1, Some(1)));
            iter.next();
            assert_eq!(iter.size_hint(), (0, Some(0)));
        }
    }

    #[test]
    fn test_as_bytes() {
        let size = 5;
        let required_size = ByteArray::required_size(size);
        let mut memory = vec![0u8; required_size];

        let bytearray = memory.as_mut_ptr() as *mut ByteArray;
        unsafe {
            (*bytearray).size = size;

            for i in 0..size {
                (*bytearray).set_element(i, (i + 1) as u8);
            }

            let bytes = (*bytearray).as_bytes();
            assert_eq!(bytes.len(), size);
            for i in 0..size {
                assert_eq!(bytes[i], (i + 1) as u8);
            }
        }
    }
}
