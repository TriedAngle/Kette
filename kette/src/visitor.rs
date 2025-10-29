use crate::{
    Array, ArrayMap, ByteArray, GenericObject, Map, MapType, ObjectKind, ObjectType, SlotMap,
    SlotObject, TaggedPtr, TaggedValue,
};

pub trait Visitable {
    fn visit_edges(&self, visitor: &impl Visitor);
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor);
}

pub trait Visitor: Sized {
    fn visit(&self, value: TaggedValue) {
        let _ = value;
    }
    fn visit_mut(&mut self, value: TaggedValue) {
        let _ = value;
    }
}

// Idea:
// visiting an object means we visit only its direct nodes.
// so when we call on a generic object, we dispatch here on the actual object types.
// the actual object types will then call visitor.visit() on its edges.
impl Visitable for GenericObject {
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        match self.header.kind() {
            ObjectKind::Map => {
                let map = unsafe { std::mem::transmute::<_, &mut Map>(self) };
                map.visit_edges_mut(visitor);
            }
            ObjectKind::Object => match self.header.object_type().unwrap() {
                ObjectType::Slot => {
                    let slot_object = unsafe { std::mem::transmute::<_, &mut SlotObject>(self) };
                    slot_object.visit_edges_mut(visitor);
                }
                ObjectType::Array => {
                    let array_object = unsafe { std::mem::transmute::<_, &mut Array>(self) };
                    array_object.visit_edges_mut(visitor);
                }
                ObjectType::ByteArray => (),
                _ => {
                    unimplemented!()
                }
            },
        }
    }
    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        match self.header.kind() {
            ObjectKind::Map => {
                let map = unsafe { std::mem::transmute::<_, &Map>(self) };
                map.visit_edges(visitor);
            }
            ObjectKind::Object => match self.header.object_type().unwrap() {
                ObjectType::Slot => {
                    let slot_object = unsafe { std::mem::transmute::<_, &SlotObject>(self) };
                    slot_object.visit_edges(visitor);
                }
                ObjectType::Array => {
                    let array_object = unsafe { std::mem::transmute::<_, &Array>(self) };
                    array_object.visit_edges(visitor);
                }
                ObjectType::ByteArray => (),
                _ => {
                    unimplemented!()
                }
            },
        }
    }
}

// just like object, we dispatch here.
impl Visitable for Map {
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        match self.header.map_type() {
            Some(MapType::Slot) => unsafe {
                let sm: &mut SlotMap = &mut *(self as *mut Map as *mut SlotMap);
                sm.visit_edges_mut(visitor);
            },
            Some(MapType::Array) => unsafe {
                let am: &mut ArrayMap = &mut *(self as *mut Map as *mut ArrayMap);
                am.visit_edges_mut(visitor);
            },
            None => {
                panic!("visiting map type that doesnt exist")
            }
        }
    }

    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        match self.header.map_type() {
            Some(MapType::Slot) => unsafe {
                let sm: &SlotMap = &*(self as *const Map as *const SlotMap);
                sm.visit_edges(visitor);
            },
            Some(MapType::Array) => unsafe {
                let am: &ArrayMap = &*(self as *const Map as *const ArrayMap);
                am.visit_edges(visitor);
            },
            None => {
                panic!("visiting map type that doesnt exist")
            }
        }
    }
}

impl Visitable for SlotMap {
    // TODO: update this once we actually use stuff here
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        let _ = visitor;
    }

    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        let _ = visitor;
    }
}

impl Visitable for ArrayMap {
    // TODO: update this once we actually use stuff here
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        let _ = visitor;
    }
    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        let _ = visitor;
    }
}

impl Visitable for SlotObject {
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        visitor.visit_mut(self.map.into());
        self.slots().iter().for_each(|&obj| visitor.visit_mut(obj));
    }
    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        visitor.visit(self.map.into());
        self.slots().iter().for_each(|&obj| visitor.visit(obj));
    }
}

impl Visitable for Array {
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        visitor.visit_mut(self.map.into());
        self.fields().iter().for_each(|&obj| visitor.visit_mut(obj));
    }

    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        visitor.visit(self.map.into());
        self.fields().iter().for_each(|&obj| visitor.visit(obj));
    }
}

// nohting to visit in bytearray
impl Visitable for ByteArray {
    #[inline]
    fn visit_edges_mut(&mut self, _visitor: &mut impl Visitor) {}
    #[inline]
    fn visit_edges(&self, _visitor: &impl Visitor) {}
}

impl Visitable for TaggedPtr<GenericObject> {
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        let obj = unsafe { self.as_mut() };
        obj.visit_edges_mut(visitor);
    }

    fn visit_edges(&self, visitor: &impl Visitor) {
        let obj = unsafe { self.as_mut() };
        obj.visit_edges(visitor);
    }
}
