use crate::Value;

pub trait Visitable {
    fn visit_edges(&self, _visitor: &impl Visitor) {}
    fn visit_edges_mut(&mut self, _visitor: &mut impl Visitor) {}
}

pub trait Visitor: Sized {
    fn visit(&self, value: Value) {
        let _ = value;
    }
    fn visit_mut(&mut self, value: Value) {
        let _ = value;
    }
}
