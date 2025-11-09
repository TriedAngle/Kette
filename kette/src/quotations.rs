use std::mem;

use crate::{Array, ExecutableMap, Header, HeapObject, Object, StackEffect, Tagged, Visitable};

#[repr(C)]
#[derive(Debug)]
pub struct QuotationMap {
    pub map: ExecutableMap,
    // this effect must be inferred at the creation of the map/quotation
    pub effect: Tagged<StackEffect>,
}

impl Object for QuotationMap {}
impl HeapObject for QuotationMap {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}
impl Visitable for QuotationMap {
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {}
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {}
}

#[repr(C)]
#[derive(Debug)]
pub struct Quotation {
    pub header: Header,
    pub body: Tagged<Array>,
}
