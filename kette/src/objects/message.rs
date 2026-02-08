use std::mem;

use crate::{
    Handle, Header, HeapObject, LookupResult, Object, ObjectKind, ObjectType,
    Selector, StringObject, Visitable, VisitedLink,
};

#[repr(C)]
#[derive(Debug)]
pub struct Message {
    pub header: Header,
    pub value: Handle<StringObject>,
}

impl Message {
    /// initialize message
    pub fn init(&mut self, value: Handle<StringObject>) {
        self.header = Header::new_object(ObjectType::Message);
        self.value = value;
    }
}

impl Visitable for Message {
    fn visit_edges_mut(&mut self, visitor: &mut impl crate::Visitor) {
        visitor.visit_mut(self.value.as_value_mut());
    }
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        visitor.visit(self.value.as_value_ref());
    }
}

impl Object for Message {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.message_traits;
        traits.lookup(selector, link)
    }
}

impl HeapObject for Message {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Message as u8;

    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}
