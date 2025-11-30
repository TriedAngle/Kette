use std::mem;

use crate::{Array, Header, HeapObject, Object, SlotMap, Tagged, Visitable};

#[repr(C)]
#[derive(Debug)]
pub struct StackEffect {
    pub header: Header,
    pub map: Tagged<SlotMap>,
    pub input: Tagged<Array>,
    pub output: Tagged<Array>,
}

impl Object for StackEffect {}
impl HeapObject for StackEffect {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl Visitable for StackEffect {
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        visitor.visit(self.map.into());
        visitor.visit(self.input.into());
        visitor.visit(self.output.into());
        unimplemented!()
    }

    fn visit_edges_mut(&mut self, visitor: &mut impl crate::Visitor) {
        visitor.visit(self.map.into());
        visitor.visit(self.input.into());
        visitor.visit(self.output.into());
    }
}
