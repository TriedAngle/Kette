use std::mem;

use crate::{ByteArray, Map, Object, StackEffect, TaggedPtr, TaggedValue, Visitable};

// TODO: these maps should probably become slot maps,
// this way we can make methods "real" objects
// code is vm ptr
#[repr(C)]
#[derive(Debug)]
pub struct ExecutableMap {
    pub map: Map,
    pub code: TaggedValue,
}

#[repr(C)]
#[derive(Debug)]
pub struct MethodMap {
    pub map: ExecutableMap,
    // this effefct must be declared
    pub effect: TaggedPtr<StackEffect>,
    pub name: TaggedPtr<ByteArray>,
}

impl Object for ExecutableMap {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl Object for MethodMap {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl Visitable for ExecutableMap {
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {}
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {}
}
impl Visitable for MethodMap {
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {}
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {}
}
