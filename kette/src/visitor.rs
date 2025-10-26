use crate::{Heap, Object, ObjectType, SlotObject, TaggedPtr, TaggedValue};

pub trait Visitor {
    fn visit(&mut self, value: TaggedValue);
    fn visit_object(&mut self, object: TaggedPtr<Object>);
}

pub struct MarkVisitor<'h> {
    heap: &'h mut Heap,
}

impl<'h> Visitor for MarkVisitor<'h> {
    #[inline]
    fn visit(&mut self, value: TaggedValue) {
        if value.is_small_int() {
            return;
        }

        let reference = TaggedPtr::<Object>::from(value);
        self.visit_object(reference);
    }

    #[inline]
    fn visit_object(&mut self, object: TaggedPtr<Object>) {
        let obj = unsafe { object.as_mut() };
        if obj.header.is_marked() {
            return;
        }

        obj.header.mark();
        match obj.header.object_type() {
            ObjectType::Slot => {
                let object = unsafe { object.qualify::<SlotObject>().as_mut() };
                object.visit(self);
            }
            ObjectType::Map => {}
            ObjectType::Array => {}
            ObjectType::ByteArray => (),
            _ => {}
        }
    }
}
