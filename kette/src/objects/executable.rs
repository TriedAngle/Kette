use std::mem;

use crate::{
    ByteArray, Header, HeapObject, Object, SlotMap, StackEffect, Tagged,
    Visitable,
};

// TODO: these maps should probably become slot maps,
// this way we can make methods "real" objects
// code is vm ptr
#[repr(C)]
#[derive(Debug)]
pub struct ExecutableMap {
    pub map: SlotMap,
    // secretely a *const Block
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
pub struct Method {
    pub header: Header,
    pub map: Tagged<MethodMap>,
}

impl Object for ExecutableMap {}
impl HeapObject for ExecutableMap {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}
impl Visitable for ExecutableMap {
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {}
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {}
}

impl Object for MethodMap {}
impl HeapObject for MethodMap {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}
impl Visitable for MethodMap {
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {}
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {}
}

impl Object for Method {}
impl HeapObject for Method {}
impl Visitable for Method {}
