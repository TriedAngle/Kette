use std::mem;

use crate::{ByteArray, Header, HeapObject, Map, Object, StackEffect, Tagged, Visitable};

// TODO: these maps should probably become slot maps,
// this way we can make methods "real" objects
// code is vm ptr
#[repr(C)]
#[derive(Debug)]
pub struct ExecutableMap {
    pub map: Map,
    // TODO: we could directly use Tagged<*mut Code> here probably
    pub code: Tagged<usize>,
}

#[repr(C)]
#[derive(Debug)]
pub struct MethodMap {
    pub map: ExecutableMap,
    // this effefct must be declared
    pub effect: Tagged<StackEffect>,
    pub name: Tagged<ByteArray>,
}

#[repr(C)]
#[derive(Debug)]
pub struct ParserMap {
    pub map: ExecutableMap,
}

#[repr(C)]
pub struct ParserObject {
    pub header: Header,
    pub map: Tagged<ParserMap>,
}

impl Object for ExecutableMap {}
impl Object for MethodMap {}
impl Object for ParserMap {}

impl HeapObject for ExecutableMap {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl HeapObject for MethodMap {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl HeapObject for ParserMap {
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

impl Visitable for ParserMap {
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {}
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {}
}
