use std::any::type_name_of_val;

use crate::Value;

pub trait Visitable {
    fn visit_edges(&self, visitor: &impl Visitor) {
        unimplemented!(
            "Calling visit_edges on {} that doesn't implement it with visitor: {:?}",
            type_name_of_val(self),
            type_name_of_val(visitor)
        );
    }

    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        unimplemented!(
            "Calling visit_edges_mut on {} that doesn't implement it with visitor: {:?}",
            type_name_of_val(self),
            type_name_of_val(visitor)
        );
    }
}

pub trait Visitor: Sized {
    fn visit(&self, value: Value) {
        let _ = value;
    }
    fn visit_mut(&mut self, value: Value) {
        let _ = value;
    }
}
