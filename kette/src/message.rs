use std::mem;

use crate::{ByteArray, Handle, Header, HeapObject, Object, Tagged, Visitable};

#[repr(C)]
#[derive(Debug)]
pub struct Message {
    pub header: Header,
    pub value: Tagged<ByteArray>,
}

impl Message {
    pub fn bytearray_handle(&self) -> Handle<ByteArray> {
        // Safety: messages exist safely
        unsafe { self.value.promote_to_handle() }
    }
}

impl Visitable for Message {
    fn visit_edges_mut(&mut self, visitor: &mut impl crate::Visitor) {
        visitor.visit_mut(self.value.into());
    }
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        visitor.visit(self.value.into());
    }
}

impl Object for Message {}
impl HeapObject for Message {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}
