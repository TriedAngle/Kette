use std::mem;

use crate::{
    ByteArray, Handle, Header, HeapObject, Object, ObjectKind, ObjectType,
    Visitable,
};

#[repr(C)]
#[derive(Debug)]
pub struct Message {
    pub header: Header,
    pub value: Handle<ByteArray>,
}

impl Message {
    /// initialize message
    pub fn init(&mut self, value: Handle<ByteArray>) {
        self.header = Header::new_object(ObjectType::Message);
        self.value = value;
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
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Message as u8;

    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}
