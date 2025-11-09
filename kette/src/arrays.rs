use std::mem;

use crate::{
    Header, HeaderFlags, HeapObject, Map, MapType, Object, ObjectType, Tagged, Value, Visitable,
    Visitor,
};

// TODO: find a way to implement specific functions for arrays of some specific n
// we could introduce <size> as part of the the map.
// the question is, would that be good for the game? I am not sure yet
// keep it dynamically sized, and then figure out a nice way to have both dynamic and sized arrays.
#[repr(C)]
#[derive(Debug)]
pub struct ArrayMap {
    pub map: Map,
}

#[repr(C)]
#[derive(Debug)]
pub struct Array {
    pub header: Header,
    pub size: Tagged<usize>,
    pub fields: [Value; 0],
}

impl ArrayMap {
    #[inline]
    pub unsafe fn init(&mut self /* size: usize */) {
        // self.size = size.into();
        unsafe { self.map.init(MapType::Array) };
    }

    // #[inline]
    // pub fn size(&self) -> usize {
    //     usize::from(self.size)
    // }
}

impl Array {
    /// Initialize an Array with `map`. Caches size (u16) in header DATA[0..16].
    pub unsafe fn init(&mut self, size: usize) {
        // let cache16 = if size > u16::MAX as usize {
        //     0xFFFF
        // } else {
        //     size as u16
        // };

        self.header = Header::encode_object(ObjectType::Array, 0, HeaderFlags::empty(), 0);
        self.size = size.into();
        // self.header.set_data_lo16(cache16);
    }

    #[inline]
    fn fields_ptr(&self) -> *const Value {
        self.fields.as_ptr()
    }

    #[inline]
    fn fields_mut_ptr(&mut self) -> *mut Value {
        self.fields.as_mut_ptr()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.size.into()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn fields(&self) -> &[Value] {
        let len = self.len();
        unsafe { std::slice::from_raw_parts(self.fields_ptr(), len) }
    }

    #[inline]
    pub fn fields_mut(&mut self) -> &mut [Value] {
        let len = self.len();
        unsafe { std::slice::from_raw_parts_mut(self.fields_mut_ptr(), len) }
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<Value> {
        if index < self.len() {
            Some(unsafe { self.fields_ptr().add(index).read() })
        } else {
            None
        }
    }

    #[inline]
    pub fn set(&mut self, index: usize, value: Value) -> bool {
        if index < self.len() {
            unsafe { self.fields_mut_ptr().add(index).write(value) };
            true
        } else {
            false
        }
    }

    /// Caller must ensure `index < len()`.
    #[inline]
    pub unsafe fn get_unchecked(&self, index: usize) -> Value {
        unsafe { self.fields_ptr().add(index).read() }
    }

    /// Caller must ensure `index < len()`.
    #[inline]
    pub unsafe fn set_unchecked(&mut self, index: usize, value: Value) {
        unsafe { self.fields_mut_ptr().add(index).write(value) };
    }
}

impl Object for Array {}
impl HeapObject for Array {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>() + self.len() * mem::size_of::<Value>()
    }
}

impl Object for ArrayMap {}
impl HeapObject for ArrayMap {}

impl Visitable for ArrayMap {}
impl Visitable for Array {
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        self.fields().iter().for_each(|&obj| visitor.visit_mut(obj));
    }

    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        self.fields().iter().for_each(|&obj| visitor.visit(obj));
    }
}
