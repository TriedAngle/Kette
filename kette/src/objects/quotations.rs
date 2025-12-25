use std::mem;

use crate::{
    Array, Header, HeapObject, LookupResult, Object, ObjectKind, ObjectType,
    Selector, SlotMap, Tagged, Visitable, VisitedLink,
};

#[repr(C)]
#[derive(Debug)]
pub struct Quotation {
    pub header: Header,
    pub map: Tagged<SlotMap>,
    pub body: Tagged<Array>,
}

impl Quotation {
    /// # Safety
    /// must be allocated with corretc size
    pub fn init(&mut self, body: Tagged<Array>, map: Tagged<SlotMap>) {
        self.header = Header::new_object(ObjectType::Quotation);
        self.map = map;
        self.body = body;
    }
}

impl Object for Quotation {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.quotation_traits;
        traits.lookup(selector, link)
    }
}

impl HeapObject for Quotation {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Quotation as u8;
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl Visitable for Quotation {
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        visitor.visit(self.map.into());
        visitor.visit(self.body.into());
    }

    fn visit_edges_mut(&mut self, visitor: &mut impl crate::Visitor) {
        visitor.visit_mut(self.map.into());
        visitor.visit_mut(self.body.into());
    }
}
