use std::mem;

use crate::{
    Header, HeapObject, LookupResult, Object, ObjectKind, ObjectType, Selector,
    Value, Visitable, VisitedLink, Visitor,
};

#[repr(C)]
#[derive(Debug)]
pub struct Ratio {
    pub header: Header,
    pub numerator: Value,
    pub denominator: Value,
}

impl Ratio {
    pub fn init(&mut self, numerator: Value, denominator: Value) {
        self.header = Header::new_object(ObjectType::Ratio);
        self.numerator = numerator;
        self.denominator = denominator;
    }
}

impl Visitable for Ratio {
    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        visitor.visit(&self.numerator);
        visitor.visit(&self.denominator);
    }

    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        visitor.visit_mut(&mut self.numerator);
        visitor.visit_mut(&mut self.denominator);
    }
}

impl Object for Ratio {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.ratio_traits;
        traits.lookup(selector, link)
    }
}

impl HeapObject for Ratio {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Ratio as u8;

    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}
