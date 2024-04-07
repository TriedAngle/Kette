use core::slice;
use std::ptr;
use std::mem;


#[repr(C)]
#[derive(Clone, Copy)]
pub struct Object {
    pointer: *mut (),
}

unsafe impl Send for Object {}
unsafe impl Sync for Object {}

impl Object {
    const fn from_i64(value: i64) -> Self {
        return Self { pointer: unsafe { mem::transmute::<_,_>(value) } }
    }

    const fn from_raw(pointer: *mut ()) -> Self {
        Self { pointer }
    }

    const fn null() -> Self {
        return Self{ pointer: ptr::null::<()>() as *mut _ }
    }


    fn is_integer(&self) -> bool {
        (self.pointer as usize & 1) == 1
    }
    fn is_float(&self) -> bool {
        (self.pointer as usize & 2) == 2
    }

    fn as_integer(&self) -> Option<i64> {
        if self.is_integer() {
            Some(unsafe { mem::transmute::<_, _>(self.pointer)})
        } else {
            None
        }
    }

    fn as_float(&self) -> Option<f64> {
        if self.is_float() {
            Some(unsafe { mem::transmute::<_, _>(self.pointer)})
        } else {
            None
        }
    }

    fn as_ptr<T>(&self) -> *const T {
        self.pointer as *const _
    }

    fn as_ptr_mut<T>(&self) -> *mut T {
        self.pointer as *mut T
    }

    fn deref<T>(&self) -> &T {
        unsafe { &*(self.pointer as *const T) }
    }

    fn deref_mut<T>(&mut self) -> &mut T {
        unsafe { &mut *(self.pointer as *mut T) }
    }
}

trait ToObject {
    fn to_object(&self) -> Object {
        unsafe { Object::from_raw(mem::transmute(self as *const Self as *const ()))}
    }

    fn to_object_mut(&mut self) -> Object {
        unsafe { Object::from_raw(mem::transmute(self as *mut Self as *mut ()))}
    }
}

impl ToObject for Integer {}
impl ToObject for Float {}
impl ToObject for Wrapper {}
impl ToObject for Array {}
impl ToObject for ByteArray {}
impl ToObject for Quotation {}
impl ToObject for Word {}

#[repr(C)]
struct ObjectHeader {
    meta: usize,
    parent: Object,
}

impl ObjectHeader {
    pub const fn empty() -> Self {
        return Self { meta: 0, parent: Object::null() }
    }

    pub const fn parent_int(self, parent: i64) -> Self {
        let mut s = self;
        s.parent = Object::from_i64(parent);
        return s;
    }
}

#[repr(C)]
pub struct Integer {
    header: ObjectHeader,
    value: i64,
}

impl Integer {
    pub fn new(value: i64) -> Self {
        return Self {
            header: ObjectHeader::empty().parent_int(1),
            value,
        }
    }

    pub fn set_from_ptr(ptr: *mut Integer, value: i64) {
        let pointer = ptr as *mut i64;
        let pointer = unsafe { pointer.add(2) };  
        unsafe { ptr::write(pointer, value); }
    }

    pub fn get_from_ptr(ptr: *const Integer) -> i64 {
        unsafe { (*ptr).value }
    }
}

#[repr(C)]
pub struct Float {
    header: ObjectHeader,
    value: f64,
}

impl Float {
    pub fn new(value: f64) -> Self {
        return Self {
            header: ObjectHeader::empty().parent_int(2),
            value,
        }
    }
}

#[repr(C)]
pub struct Alien {
    header: ObjectHeader,
    base: *mut (), // if LSB is tagged to 1, this is aboslute address 
    offset: usize,
}

// mainly used for words
#[repr(C)]
pub struct Wrapper {
    header: ObjectHeader,
    value: Object,
}

#[repr(C)]
pub struct Array {
    header: ObjectHeader,
    capacity: i64,
    length: i64,
}

impl Array {
    pub fn data(&self) -> *const Object {
        let ptr = self as *const Self as *const u8;
        let offest = mem::size_of::<Self>();
        unsafe { ptr.add(offest) as *const Object }
    }

    pub fn data_mut(&mut self) -> *mut Object {
        let ptr = self as *mut Self as *mut u8;
        let offest = mem::size_of::<Self>();
        unsafe { ptr.add(offest) as *mut Object }
    }
}


#[repr(C)]
pub struct ByteArray {
    header: ObjectHeader,
    length: i64,
    capacity: i64,
}

impl ByteArray {
    pub fn data(&self) -> *const u8 {
        let ptr = self as *const Self as *const u8;
        let offest = mem::size_of::<Self>();
        unsafe { ptr.add(offest) as *const u8 }
    }

    pub fn data_mut(&mut self) -> *mut Object {
        let ptr = self as *mut Self as *mut u8;
        let offest = mem::size_of::<Self>();
        unsafe { ptr.add(offest) as *mut Object }
    }
}

// utf8 strings
#[repr(C)]
pub struct VMString {
    header: ObjectHeader,
    length: i64,
    data: Object, // backing data count be a cptr too (would be tagged then (probably?))
}

impl VMString {
    pub fn from_bytearray(data: &ByteArray) -> Self {
        Self {
            header: ObjectHeader::empty(), // in the VM we can ignore it at least for now
            length: data.length,
            data: data.to_object(),
        }
    }

    pub fn data(&self) -> *const u8 {
        unimplemented!();
        // let ba = self.data.deref::<ByteArray>();
        // ba.data()
    }
}


#[repr(C)]
pub struct Quotation {
    header: ObjectHeader,
    definition: Object, // Array
    effect: Object, // inferred effect 
}


#[repr(C)]
pub struct Word {
    header: ObjectHeader,
    name: Object,
    body: Object, // quotation
    effect: Object, // declared effect
    properties: Object, // array
}



//-- HELPERS --//

pub struct ArrayIterator {
    current: *const Object,
    remaining: i64,
}

impl Iterator for ArrayIterator {
    type Item = Object;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining > 0 {
            unsafe {
                let obj = unsafe { ptr::read(self.current) };
                self.current.add(1);
                self.remaining -= 1;
                Some(obj)
            }
        } else {
            None
        }
    }
}

impl Array {
    pub fn iter(&self) -> ArrayIterator {
        ArrayIterator {
            current: self.data(),
            remaining: self.length,
        }
    }
}

impl VMString {
    pub fn to_string(&self) -> Result<String, std::str::Utf8Error> {
        let data = self.data();
        let len = self.length as usize;
        unsafe {
            let slice = slice::from_raw_parts(data, len);
            std::str::from_utf8(slice).map(|s| s.to_owned())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_size() {
        assert_eq!(mem::size_of::<ObjectHeader>(), 16);
    }

    #[test]
    fn object_creation() {
        let mut value = Integer::new(666);
        let mut obj = value.to_object_mut();
        let mut original = obj.deref_mut::<Integer>();
        original.value = 333;
        assert_eq!(333, value.value);
    }
}