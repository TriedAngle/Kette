use std::{mem, ptr, slice};

pub struct SpecialObjects {
    pub map_map: *mut Map,
    pub slot_map: *mut Map,
    pub word_map: *mut Map,
    pub quotation_map: *mut Map,
    pub fixnum_map: *mut Map,
    pub fixfloat_map: *mut Map,
    pub box_map: *mut Map,
    pub array_map: *mut Map,
    pub bytearray_map: *mut Map,
    pub alien_map: *mut Map,
    pub context_map: *mut Map,

    pub false_object: *mut Object,
    pub true_object: *mut Object,

    pub input: *mut ByteArrayObject,
    pub input_offset: *mut FixnumObject,
}

impl Default for SpecialObjects {
    fn default() -> Self {
        Self {
            map_map: ptr::null_mut(),
            slot_map: ptr::null_mut(),
            word_map: ptr::null_mut(),
            quotation_map: ptr::null_mut(),
            fixnum_map: ptr::null_mut(),
            fixfloat_map: ptr::null_mut(),
            box_map: ptr::null_mut(),
            array_map: ptr::null_mut(),
            bytearray_map: ptr::null_mut(),
            alien_map: ptr::null_mut(),
            context_map: ptr::null_mut(),
            false_object: ptr::null_mut(),
            true_object: ptr::null_mut(),

            input: ptr::null_mut(),
            input_offset: ptr::null_mut(),
        }
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct ObjectHeader {
    pub meta: usize,
    pub map: ObjectRef,
}

#[repr(C)]
#[derive(Debug)]
pub struct Object {
    header: ObjectHeader,
}

impl Object {
    pub const fn required_size(map: &Map) -> usize {
        map.object_size * 8
    }

    pub fn set_map(&mut self, map: *mut Map) {
        self.header.map = ObjectRef::new(map as *mut Object);
    }
    pub unsafe fn get_field(&mut self, index: usize) -> ObjectRef {
        let self_ptr = self as *mut Self;
        let fields_ptr = self_ptr.add(1) as *mut ObjectRef;
        *fields_ptr.add(index)
    }
    pub unsafe fn set_field(&mut self, index: usize, value: ObjectRef) {
        let self_ptr = self as *mut Self;
        let fields_ptr = self_ptr.add(1) as *mut ObjectRef;
        let field = fields_ptr.add(index);
        *field = value;
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjectRef(pub *mut Object);

impl ObjectRef {
    pub unsafe fn get_field(&self, index: usize) -> ObjectRef {
        let ptr = self.0 as *mut u8;
        let start = ptr.add(mem::size_of::<ObjectHeader>());
        let data = start as *mut ObjectRef;
        let offset = data.add(index);
        *offset
    }

    pub unsafe fn set_field(&self, index: usize, value: ObjectRef) {
        let ptr = self.0 as *mut u8;
        let start = ptr.add(mem::size_of::<ObjectHeader>());
        let data = start as *mut ObjectRef;

        let offset = data.add(index);
        *offset = value;
    }

    pub const fn new(ptr: *mut Object) -> Self {
        Self(ptr)
    }

    pub const fn from_usize(value: usize) -> Self {
        Self::new(value as *mut Object)
    }

    pub const fn from_map(map: *mut Map) -> Self {
        Self::new(map as *mut Object)
    }

    pub const fn from_word(word: *mut WordObject) -> Self {
        Self::new(word as *mut Object)
    }

    pub fn from_fn(fun: unsafe fn(vm: *mut crate::VM)) -> Self {
        Self(unsafe { mem::transmute(fun) })
    }

    pub fn as_usize(self) -> usize {
        self.0 as usize
    }

    pub fn as_isize(self) -> isize {
        unsafe { mem::transmute(self.0) }
    }

    pub const fn null() -> Self {
        ObjectRef(ptr::null_mut())
    }

    pub fn is_null(&self) -> bool {
        self.0.is_null()
    }

    pub fn get_map(&self) -> *const Map {
        unsafe { (*self.0).header.map.0 as *const Map }
    }

    pub fn get_map_mut(&self) -> *mut Map {
        unsafe { (*self.0).header.map.0 as *mut Map }
    }

    pub const fn as_map(&self) -> *const Map {
        self.0 as *const Map
    }

    pub const fn as_map_mut(&self) -> *mut Map {
        self.0 as *mut Map
    }

    pub const fn as_box(&self) -> *const BoxObject {
        self.0 as *const BoxObject
    }

    pub const fn as_box_mut(&self) -> *mut BoxObject {
        self.0 as *mut BoxObject
    }

    pub const fn as_byte_array(&self) -> *const ByteArrayObject {
        self.0 as *const ByteArrayObject
    }

    pub const fn as_byte_array_mut(&self) -> *mut ByteArrayObject {
        self.0 as *mut ByteArrayObject
    }

    pub const fn as_array(&self) -> *const ArrayObject {
        self.0 as *const ArrayObject
    }

    pub const fn as_array_mut(&self) -> *mut ArrayObject {
        self.0 as *mut ArrayObject
    }

    pub const fn object_mut(&self) -> *mut Object {
        self.0
    }

    pub const fn as_fixnum(&self) -> *const FixnumObject {
        self.0 as *const FixnumObject
    }

    pub const fn as_fixnum_mut(&self) -> *mut FixnumObject {
        self.0 as *mut FixnumObject
    }

    pub const fn as_fixfloat(&self) -> *const FixfloatObject {
        self.0 as *const FixfloatObject
    }

    pub const fn as_fixfloat_mut(&self) -> *mut FixfloatObject {
        self.0 as *mut FixfloatObject
    }

    pub const fn as_word(&self) -> *const WordObject {
        self.0 as *const WordObject
    }

    pub const fn as_word_mut(&self) -> *mut WordObject {
        self.0 as *mut WordObject
    }

    pub const fn as_quotation(&self) -> *const QuotationObject {
        self.0 as *const QuotationObject
    }

    pub const fn as_quotation_mut(&self) -> *mut QuotationObject {
        self.0 as *mut QuotationObject
    }

    pub const fn as_slot(&self) -> *const SlotObject {
        self.0 as *const SlotObject
    }

    pub const fn as_slot_mut(&self) -> *mut SlotObject {
        self.0 as *mut SlotObject
    }

    pub unsafe fn array_data(&self) -> *mut ObjectRef {
        let ptr = self.0 as *mut u8;
        let data = ptr.add(mem::size_of::<ArrayObject>());
        data as *mut ObjectRef
    }

    pub unsafe fn get_array_at(&self, index: usize) -> ObjectRef {
        let ptr = self.0 as *mut u8;
        let start = ptr.add(mem::size_of::<ArrayObject>());
        let data = start as *mut ObjectRef;
        let offset = data.add(index);
        *offset
    }

    pub unsafe fn set_array_at(&self, index: usize, value: ObjectRef) {
        let ptr = self.0 as *mut u8;
        let start = ptr.add(mem::size_of::<ArrayObject>());
        let data = start as *mut ObjectRef;
        let offset = data.add(index);
        *offset = value;
    }

    pub unsafe fn array_data_len(&self) -> usize {
        let ptr = self.0 as *const u8;
        let data = ptr.add(mem::size_of::<ObjectHeader>());
        *(data as *const usize)
    }

    pub unsafe fn bytearray_data(&self) -> *mut u8 {
        let ptr = self.0 as *mut u8;
        let data = ptr.add(mem::size_of::<ByteArrayObject>());
        data as *mut u8
    }

    pub unsafe fn bytearray_data_len(&self) -> usize {
        let ptr = self.0 as *const u8;
        let data = ptr.add(mem::size_of::<ObjectHeader>());
        *(data as *const usize)
    }

    pub unsafe fn bytearray_is_eq(&self, other: ObjectRef) -> bool {
        let self_ptr = self.bytearray_data();
        let other_ptr = other.bytearray_data();
        let self_len = self.bytearray_data_len();
        let other_len = other.bytearray_data_len();

        if self_len != other_len {
            return false;
        }
        let self_slice = slice::from_raw_parts(self_ptr, self_len);
        let other_slice = slice::from_raw_parts(other_ptr, other_len);
        self_slice == other_slice
    }

    pub unsafe fn bytearray_is_eq_rust(&self, other: &str) -> bool {
        let self_ptr = self.bytearray_data();
        let self_len = self.bytearray_data_len();

        if self_len != other.len() {
            return false;
        }
        let self_slice = slice::from_raw_parts(self_ptr, self_len);
        self_slice == other.as_bytes()
    }

    pub unsafe fn bytearray_as_str(&self) -> &str {
        let data = self.bytearray_data();
        let data_len = self.bytearray_data_len();
        let length = (0..data_len)
            .find(|&i| *data.add(i) == 0)
            .unwrap_or(data_len);

        let data_slice = slice::from_raw_parts(data, length);
        std::str::from_utf8(data_slice).unwrap()
    }

    pub unsafe fn map_slots(&self) -> &[SlotObject] {
        let ptr = self.0 as *mut Map;

        let data = (*ptr).slots.array_data() as *const SlotObject;
        let len = (*ptr).slots.array_data_len();
        let slice = slice::from_raw_parts(data, len);
        slice
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct FixnumObject {
    pub header: ObjectHeader,
    pub value: isize,
}

#[repr(C)]
#[derive(Debug)]
pub struct FixfloatObject {
    pub header: ObjectHeader,
    pub value: f64,
}

#[repr(C)]
#[derive(Debug)]
pub struct ArrayObject {
    pub header: ObjectHeader,
    pub size: usize, // array capacity
                     // data here
}

#[repr(C)]
#[derive(Debug)]
pub struct ByteArrayObject {
    pub header: ObjectHeader,
    pub capacity: usize, // size of data
                         // data here
}

impl ByteArrayObject {}

#[repr(C)]
#[derive(Debug)]
pub struct BoxObject {
    pub header: ObjectHeader,
    pub boxed: ObjectRef,
}

#[repr(C)]
#[derive(Debug)]
pub struct AlienObject {
    pub header: ObjectHeader,
    pub base: usize,
    pub offset: usize,
    pub expired: usize,
}

#[repr(C)]
#[derive(Debug)]
pub struct QuotationObject {
    pub header: ObjectHeader,
    pub body: ObjectRef, // array
    pub effect: ObjectRef,
    pub entry: ObjectRef,
}

impl QuotationObject {
    pub unsafe fn body(&self) -> &[ObjectRef] {
        let data = self.body.array_data();
        let len = self.body.array_data_len();
        slice::from_raw_parts(data, len)
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct WordObject {
    pub header: ObjectHeader,
    pub name: ObjectRef,
    pub body: ObjectRef, // quotation
    pub properties: ObjectRef,
    pub primitive: usize, // true => body rust function // TODO: use t & f here
    pub syntax: usize,
}

impl WordObject {
    pub unsafe fn name<'a>(&'a self) -> &'a str {
        &self.name.bytearray_as_str()
    }
    pub unsafe fn quotation(&self) -> *const QuotationObject {
        self.body.0 as *const QuotationObject
    }
}

pub const SLOT_CONSTANT: usize = 0;
pub const SLOT_PARENT: usize = 1;
pub const SLOT_DATA: usize = 2;
pub const SLOT_ASSIGNMENT: usize = 3;
pub const SLOT_METHOD: usize = 4;
pub const SLOT_VARIABLE_DATA: usize = 5;
// TODO: probably get rid of embedded data or handle fixnums&floats always diff?
pub const SLOT_EMBEDDED_DATA: usize = 6;

#[repr(C)]
#[derive(Debug)]
pub struct SlotObject {
    pub header: ObjectHeader,
    pub name: ObjectRef,       // String
    pub kind: usize, // 0: data, 1: variable data 2: constant, 3: parent, 4: assignent, 5: word
    pub value_type: ObjectRef, // null for untyped, parent => parent
    pub index: usize,
    pub read_only: usize, // 0/null/f => false
}

impl SlotObject {
    pub fn reference_objects(&self) -> [ObjectRef; 2] {
        [self.name, self.value_type]
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct Map {
    pub header: ObjectHeader, // points to root map
    pub name: ObjectRef,
    pub object_size: usize, // size of the object (indcluding header) in slot count
    pub slot_count: usize,  // slot count
    pub slots: ObjectRef,
    pub default_object: ObjectRef,
}

impl Map {
    pub unsafe fn name<'a>(&'a self) -> &'a str {
        self.name.bytearray_as_str()
    }

    pub unsafe fn slot_array(&self) -> *mut ArrayObject {
        self.slots.0 as *mut ArrayObject
    }

    pub unsafe fn slots(&self) -> &[SlotObject] {
        let data = self.slots.array_data() as *const SlotObject;
        let len = self.slots.array_data_len();
        let slice = slice::from_raw_parts(data, len);
        slice
    }

    pub unsafe fn slots_mut(&self) -> &mut [SlotObject] {
        let data = self.slots.array_data() as *mut SlotObject;
        let len = self.slots.array_data_len();
        let slice = slice::from_raw_parts_mut(data, len);
        slice
    }

    pub unsafe fn find_slot(&self, name: ObjectRef) -> Option<&SlotObject> {
        let array = self.slot_array();
        let slots = self.slots();
        slots.iter().find(|s| s.name.bytearray_is_eq(name))
    }

    pub unsafe fn find_slot_rust(&self, name: &str) -> Option<&SlotObject> {
        let array = self.slot_array();
        let slots = self.slots();
        slots.iter().find(|s| s.name.bytearray_is_eq_rust(name))
    }

    pub unsafe fn find_slot_mut(&mut self, name: ObjectRef) -> Option<&mut SlotObject> {
        let array = self.slot_array();
        let slots = self.slots_mut();
        slots.iter_mut().find(|s| s.name.bytearray_is_eq(name))
    }

    pub unsafe fn find_slot_rust_mut(&mut self, name: &str) -> Option<&mut SlotObject> {
        let array = self.slot_array();
        let slots = self.slots_mut();
        slots.iter_mut().find(|s| s.name.bytearray_is_eq_rust(name))
    }

    pub unsafe fn get_slot(&self, index: usize) -> &SlotObject {
        assert!(index < self.slot_count, "Index out of bounds");
        let obj = self.slots.get_array_at(index);
        mem::transmute(obj.0 as *const SlotObject)
    }

    pub unsafe fn get_slot_mut(&mut self, index: usize) -> &mut SlotObject {
        assert!(index < self.slot_count, "Index out of bounds");
        let obj = self.slots.get_array_at(index);
        mem::transmute(obj.0 as *mut SlotObject)
    }
}
