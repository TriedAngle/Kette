use std::mem;

use crate::{Header, HeapObject, Object, Tagged, Visitable, Visitor};

#[repr(C)]
#[derive(Debug)]
pub struct ByteArray {
    pub header: Header,
    pub size: Tagged<usize>,
    pub data: [u8; 0],
}

impl ByteArray {
    #[inline]
    pub fn len(&self) -> usize {
        self.size.into()
    }

    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        let len = self.len();
        unsafe { std::slice::from_raw_parts(self.data.as_ptr(), len) }
    }

    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        let len = self.len();
        unsafe { std::slice::from_raw_parts_mut(self.data.as_mut_ptr(), len) }
    }
}

impl Object for ByteArray {}
impl HeapObject for ByteArray {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>() + self.len()
    }
}

// nohting to visit in bytearray
impl Visitable for ByteArray {
    #[inline]
    fn visit_edges_mut(&mut self, _visitor: &mut impl Visitor) {}
    #[inline]
    fn visit_edges(&self, _visitor: &impl Visitor) {}
}
