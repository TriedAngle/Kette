use std::mem;

use crate::{
    Array, ExecutableMap, Header, HeapObject, Object, Tagged, Visitable,
};

#[repr(C)]
#[derive(Debug)]
pub struct QuotationMap {
    pub map: ExecutableMap,
    // this effect must be inferred at the creation of the map/quotation
    // 0..15 16 byte input count
    // 15..31 16 byte output count
    // 31..39 initialized
    pub effect: Tagged<u64>,
    pub body: Tagged<Array>,
}

impl QuotationMap {
    pub fn infer_effect(&self) -> u64 {
        // TODO: infer stack effect
        // this is a bit challenging as we do not know the calls inside
        // the idea I have is interpreting it the first time and compiling it after the call
        // for the next calls
        // a guard can be put in place for that, if the guard matches good
        // if the guard doesn't match, create a new guard.
        // quotations can also be called with explicit effect
        // effect information can also be gathered from outside e.g. explicit effect or calls on
        // quotations that require explicit effects.
        unimplemented!("TODO")
    }

    /// # Safety
    /// must be correctly allocated
    pub unsafe fn init(&mut self, body: Tagged<Array>) {
        self.body = body;
    }
}

impl Object for QuotationMap {}
impl HeapObject for QuotationMap {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl Visitable for QuotationMap {
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        // SAFETY: safe if correctly allocated
        let body = unsafe { self.body.as_ref() };
        body.visit_edges(visitor);
    }
    fn visit_edges_mut(&mut self, visitor: &mut impl crate::Visitor) {
        // SAFETY: safe if correctly allocated
        let body = unsafe { self.body.as_mut() };
        body.visit_edges_mut(visitor);
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct Quotation {
    pub header: Header,
    pub map: Tagged<QuotationMap>,
}

impl Object for Quotation {}

impl HeapObject for Quotation {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl Visitable for Quotation {
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        // SAFETY: safe if correctly allocated
        let map = unsafe { self.map.as_ref() };
        map.visit_edges(visitor);
    }
}
