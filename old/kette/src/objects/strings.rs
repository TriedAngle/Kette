use core::str;
use std::mem;

use crate::{
    ByteArray, Handle, Header, HeapObject, LookupResult, Object, ObjectKind,
    ObjectType, Selector, Visitable, VisitedLink,
};

#[repr(C)]
#[derive(Debug)]
pub struct StringObject {
    pub header: Header,
    pub value: Handle<ByteArray>,
}

impl StringObject {
    pub fn init(&mut self, value: Handle<ByteArray>) {
        self.header = Header::new_object(ObjectType::String);
        self.value = value;
    }

    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.value.as_bytes()
    }

    #[inline]
    pub fn as_utf8(&self) -> Result<&str, str::Utf8Error> {
        self.value.as_utf8()
    }
}

impl Visitable for StringObject {
    fn visit_edges_mut(&mut self, visitor: &mut impl crate::Visitor) {
        visitor.visit_mut(self.value.as_value_mut());
    }
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        visitor.visit(self.value.as_value_ref());
    }
}

impl Object for StringObject {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.string_traits;
        traits.lookup(selector, link)
    }
}

impl HeapObject for StringObject {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::String as u8;

    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}
