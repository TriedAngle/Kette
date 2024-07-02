use std::{mem, ptr, slice};

pub struct SpecialObjects {
    pub map_map: *mut Map,
    pub word_map: *mut Map,
    pub quotation_map: *mut Map,
    pub fixnum_map: *mut Map,
    pub fixfloat_map: *mut Map,
    pub box_map: *mut Map,
    pub array_map: *mut Map,
    pub bytearray_map: *mut Map,
    pub alien_map: *mut Map,
    pub context_map: *mut Map,
    pub context_object: ObjectRef,

    pub false_object: *mut Object,
    pub true_object: *mut Object,

    pub input: *mut ByteArrayObject,
    pub input_offset: *mut FixnumObject,
}

impl Default for SpecialObjects {
    fn default() -> Self {
        Self {
            map_map: ptr::null_mut(),
            word_map: ptr::null_mut(),
            quotation_map: ptr::null_mut(),
            fixnum_map: ptr::null_mut(),
            fixfloat_map: ptr::null_mut(),
            box_map: ptr::null_mut(),
            array_map: ptr::null_mut(),
            bytearray_map: ptr::null_mut(),
            alien_map: ptr::null_mut(),
            context_map: ptr::null_mut(),
            context_object: ObjectRef::null(),
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
        (*self.0).get_field(index)
    }

    pub unsafe fn set_field(&self, index: usize, value: ObjectRef) {
        (*self.0).set_field(index, value)
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
        self.0 as isize
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

impl ArrayObject {
    pub unsafe fn data_ptr(&self) -> *const u8 {
        (self as *const Self).add(1) as *const u8
    }

    pub unsafe fn data_ptr_mut(&mut self) -> *mut u8 {
        (self as *mut Self).add(1) as *mut u8
    }

    pub fn required_size(size: usize) -> usize {
        let object_size = mem::size_of::<Self>();
        let data_size = mem::size_of::<ObjectRef>() * size;
        object_size + data_size
    }

    pub unsafe fn data(&self) -> &[ObjectRef] {
        let p = self.data_ptr() as *const ObjectRef;
        slice::from_raw_parts(p, self.size)
    }

    pub unsafe fn data_mut(&mut self) -> &mut [ObjectRef] {
        let p = self.data_ptr_mut() as *mut ObjectRef;
        slice::from_raw_parts_mut(p, self.size)
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct ByteArrayObject {
    pub header: ObjectHeader,
    pub capacity: usize, // size of data
                         // data here
}

impl ByteArrayObject {
    pub unsafe fn data_ptr(&self) -> *const u8 {
        let self_ptr = self as *const Self as *const u8;
        let data_ptr = self_ptr.add(mem::size_of::<Self>());
        data_ptr
    }

    pub unsafe fn data_ptr_mut(&mut self) -> *mut u8 {
        let self_ptr = self as *mut Self;
        let data_ptr = self_ptr.add(1) as *mut u8;
        data_ptr
    }

    unsafe fn data(&self) -> &[u8] {
        let self_ptr = self as *const Self as *const u8;
        let data_ptr = self_ptr.add(mem::size_of::<Self>());
        slice::from_raw_parts(data_ptr, self.capacity)
    }

    pub unsafe fn is_eq(&self, other: &ByteArrayObject) -> bool {
        if self.capacity != other.capacity {
            return false;
        }
        self.data() == other.data()
    }

    pub unsafe fn is_eq_rust(&self, other: &str) -> bool {
        if self.capacity != other.len() {
            return false;
        }
        self.data() == other.as_bytes()
    }

    // pub unsafe fn copy_rust_string(&mut self, data: &str) {
    //     assert!(
    //         self.capacity >= data.len(),
    //         "Not enough capacity in ByteArrayObject"
    //     );
    //     let self_ptr = self as *mut Self as *mut u8;
    //     let data_ptr = self_ptr.add(mem::size_of::<ObjectHeader>() + mem::size_of::<usize>());

    // }

    pub unsafe fn as_str(&self) -> Result<&str, std::str::Utf8Error> {
        let data_ptr = (self as *const Self as *const u8)
            .add(std::mem::size_of::<ObjectHeader>() + std::mem::size_of::<usize>());
        let length = (0..self.capacity)
            .find(|&i| *data_ptr.add(i) == 0)
            .unwrap_or(self.capacity);
        let data_slice = slice::from_raw_parts(data_ptr, length);
        std::str::from_utf8(data_slice)
    }
}

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
        (*self.body.as_array()).data()
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct WordObject {
    pub header: ObjectHeader,
    pub name: ObjectRef,
    pub body: ObjectRef, // quotation
    pub properties: ObjectRef,
    pub primitive: usize, // true => body rust function
    pub syntax: usize,
}

impl WordObject {
    pub unsafe fn name<'a>(&'a self) -> &'a str {
        let arr = self.name.as_byte_array();
        (*arr).as_str().unwrap()
    }
    pub unsafe fn quotation(&self) -> *const QuotationObject {
        self.body.0 as *const QuotationObject
    }
}

pub const SLOT_CONSTANT: usize = 0;
pub const SLOT_PARENT: usize = 1;
pub const SLOT_DATA: usize = 2;
pub const SLOT_ASSIGNMENT: usize = 3;
pub const SLOT_WORD: usize = 4;
pub const SLOT_VARIABLE_DATA: usize = 5;
// TODO: probably get rid of embedded data or handle fixnums&floats always diff?
pub const SLOT_EMBEDDED_DATA: usize = 6;

#[repr(C)]
#[derive(Debug)]
pub struct Slot {
    pub name: ObjectRef,       // String
    pub kind: usize, // 0: data, 1: variable data 2: constant, 3: parent, 4: assignent, 5: word
    pub value_type: ObjectRef, // null for untyped, parent => parent
    pub index: usize,
    pub read_only: usize, // 0/null/f => false
}

impl Slot {
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
                            // slots here
}

impl Map {
    pub unsafe fn name<'a>(&'a self) -> &'a str {
        let arr = self.name.as_byte_array();
        (*arr).as_str().unwrap()
    }

    pub unsafe fn slots(&self) -> &[Slot] {
        let self_ptr = self as *const Map;
        let slots_ptr = self_ptr.add(1) as *const Slot;
        slice::from_raw_parts(slots_ptr, self.slot_count)
    }

    pub unsafe fn slots_mut(&mut self) -> &mut [Slot] {
        let self_ptr = self as *mut Map;
        let slots_ptr = self_ptr.add(1) as *mut Slot;
        slice::from_raw_parts_mut(slots_ptr, self.slot_count)
    }

    pub unsafe fn find_slot(&self, name: *const ByteArrayObject) -> Option<&Slot> {
        let slots = unsafe { self.slots() };
        slots
            .iter()
            .find(|s| (*s.name.as_byte_array()).is_eq(&*name))
    }

    pub unsafe fn find_slot_rust(&self, name: &str) -> Option<&Slot> {
        let slots = unsafe { self.slots() };
        slots
            .iter()
            .find(|s| (*s.name.as_byte_array()).is_eq_rust(name))
    }

    pub unsafe fn find_slot_mut(&mut self, name: *const ByteArrayObject) -> Option<&mut Slot> {
        let slots = unsafe { self.slots_mut() };
        slots
            .iter_mut()
            .find(|s| (*s.name.as_byte_array()).is_eq(&*name))
    }

    pub unsafe fn find_slot_rust_mut(&mut self, name: &str) -> Option<&mut Slot> {
        let slots = unsafe { self.slots_mut() };
        slots
            .iter_mut()
            .find(|s| (*s.name.as_byte_array()).is_eq_rust(name))
    }

    pub unsafe fn get_slot(&self, index: usize) -> &Slot {
        assert!(index < self.slot_count, "Index out of bounds");

        let self_ptr = self as *const Map;
        let slots_ptr = self_ptr.add(1) as *const Slot;
        &*slots_ptr.add(index)
    }

    pub unsafe fn get_slot_mut(&mut self, index: usize) -> &mut Slot {
        assert!(index < self.slot_count, "Index out of bounds");

        let self_ptr = self as *mut Map;
        let slots_ptr = self_ptr.add(1) as *mut Slot;
        &mut *slots_ptr.add(index)
    }

    pub fn required_size(slot_count: usize) -> usize {
        let header_size = mem::size_of::<Map>();
        let slots_size = slot_count * mem::size_of::<Slot>();
        header_size + slots_size
    }
}
