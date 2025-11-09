use std::mem;

use crate::{
    ByteArray, Header, HeaderFlags, HeapObject, Map, MapType, Object, ObjectType, Tagged, Value,
    Visitable, Visitor,
};

#[repr(C)]
#[derive(Debug)]
pub struct SlotDescriptor {
    pub name: Tagged<ByteArray>,
    pub kind: Tagged<Value>,
    pub value: Value,
}

#[repr(C)]
#[derive(Debug)]
pub struct SlotMap {
    pub map: Map,
    pub assignable_slots: Tagged<usize>,
    pub total_slots: Tagged<usize>,
    pub slots: [SlotDescriptor; 0],
}

#[repr(C)]
#[derive(Debug)]
pub struct SlotObject {
    pub header: Header,
    pub map: Tagged<SlotMap>,
    pub slots: [Value; 0],
}

impl SlotMap {
    #[inline]
    pub unsafe fn init(&mut self, assignable_slots: usize, total_slots: usize) {
        self.assignable_slots = assignable_slots.into();
        self.total_slots = total_slots.into();
        unsafe { self.map.init(MapType::Slot) };
    }

    #[inline]
    pub fn assignable_slots_count(&self) -> usize {
        usize::from(self.assignable_slots) as usize
    }
}

impl SlotObject {
    pub unsafe fn init(&mut self, map: Tagged<SlotMap>) {
        self.map = map;
        self.header = Header::encode_object(ObjectType::Slot, 0, HeaderFlags::empty(), 0);
    }

    #[inline]
    fn slots_ptr(&self) -> *const Value {
        self.slots.as_ptr()
    }

    #[inline]
    fn slots_mut_ptr(&mut self) -> *mut Value {
        self.slots.as_mut_ptr()
    }

    #[inline]
    pub fn slots(&self) -> &[Value] {
        let len = self.assignable_slots();
        unsafe { std::slice::from_raw_parts(self.slots_ptr(), len) }
    }

    /// Borrow all slots as a mutable slice (checked).
    #[inline]
    pub fn slots_mut(&mut self) -> &mut [Value] {
        let len = self.assignable_slots();
        unsafe { std::slice::from_raw_parts_mut(self.slots_mut_ptr(), len) }
    }

    #[inline]
    pub fn assignable_slots(&self) -> usize {
        let cached16 = self.header.data_lo16();

        if cached16 != u16::MAX {
            cached16 as usize
        } else {
            let map = unsafe { self.map.as_ref() };
            map.assignable_slots_count()
        }
    }

    #[inline]
    pub fn get_slot(&self, index: usize) -> Option<Value> {
        if index < self.assignable_slots() {
            Some(unsafe { self.slots_ptr().add(index).read() })
        } else {
            None
        }
    }

    #[inline]
    pub fn set_slot(&mut self, index: usize, value: Value) -> bool {
        if index < self.assignable_slots() {
            unsafe { self.slots_mut_ptr().add(index).write(value) };
            true
        } else {
            false
        }
    }

    /// Caller must ensure `index < assignable_slots()`.
    #[inline]
    pub unsafe fn get_slot_unchecked(&self, index: usize) -> Value {
        unsafe { self.slots_ptr().add(index).read() }
    }

    /// Caller must ensure `index < assignable_slots()`.
    #[inline]
    pub unsafe fn set_slot_unchecked(&mut self, index: usize, value: Value) {
        unsafe { self.slots_mut_ptr().add(index).write(value) };
    }
}

impl Object for SlotObject {}
impl HeapObject for SlotObject {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>() + self.assignable_slots() * mem::size_of::<Value>()
    }
}

impl Object for SlotMap {}
impl HeapObject for SlotMap {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>() // TODO: add slots  
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

impl Visitable for SlotObject {
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        visitor.visit_mut(self.map.as_value());
        self.slots().iter().for_each(|&obj| visitor.visit_mut(obj));
    }
    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        visitor.visit(self.map.as_value());
        self.slots().iter().for_each(|&obj| visitor.visit(obj));
    }
}
