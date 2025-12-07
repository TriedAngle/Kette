use std::{mem, ptr};

use bitflags::{Flags, bitflags};
use rand::seq::IndexedRandom;

use crate::{
    ByteArray, Header, HeaderFlags, HeapObject, Map, MapType, Object,
    ObjectType, Tagged, Value, Visitable, Visitor,
};

bitflags! {
    /// constant 00
    /// parent 01
    /// assignable 10
    /// assignable parent 11
    pub struct SlotTags: u8 {
        const PARENT = 1 << 0;
        const ASSIGNABLE = 1 << 1;
    }
}

/// assignable slot: offset to value in object
/// Const slot: value
/// Parent slot: constant lookup (static?)
/// Assignable Parent slot: normal data slot that is also parent
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SlotInfo {
    /// guaranteed to be interned
    pub name: Tagged<ByteArray>,
    pub metadata: Tagged<usize>,
    pub value: Value,
}

/// slot ordering:
/// assignable parent > assignable > parent > constant
#[repr(C)]
#[derive(Debug)]
pub struct SlotMap {
    pub map: Map,
    pub assignable_slots: Tagged<usize>,
    pub total_slots: Tagged<usize>,
    pub slots: [SlotInfo; 0],
}

#[repr(C)]
#[derive(Debug)]
pub struct SlotObject {
    pub header: Header,
    pub map: Tagged<SlotMap>,
    pub slots: [Value; 0],
}

impl SlotInfo {
    pub fn new() -> Self {
        unimplemented!()
    }

    pub fn tags(&self) -> SlotTags {
        let value: u64 = self.metadata.into();
        let raw: u8 = (value & 0xFF) as u8; // cutting off
        SlotTags::from_bits(raw).expect("must have valid tags")
    }
}

impl SlotMap {
    // will go through the slots
    pub unsafe fn init_with_data(&mut self, slots: &[SlotInfo]) {
        let mut slots = slots.to_vec();
        // a > b => b, a
        slots.sort_by(|a, b| {
            let tags_a = a.tags();
            let tags_b = b.tags();
            let raw_a = tags_a.bits();
            let raw_b = tags_b.bits();

            let order_a = raw_a & 0b11;
            let order_b = raw_b & 0b11;

            order_a.cmp(&order_b)
        });

        let assignable_slots = slots
            .iter()
            .filter(|s| s.tags().contains(SlotTags::ASSIGNABLE))
            .count();

        let total_slots = slots.len();

        unsafe {
            ptr::copy_nonoverlapping(
                slots.as_ptr(),
                self.slots.as_mut_ptr(),
                total_slots,
            )
        };

        // SAFETY: we calculate correctly
        unsafe { self.init(assignable_slots, total_slots) };
    }

    /// Initialize a slot map
    /// this is unsafe as this is intended to be a mostly internal api
    /// # Safety
    /// the reference must be valid and assignable slots < total slots
    #[inline]
    pub unsafe fn init(&mut self, assignable_slots: usize, total_slots: usize) {
        self.assignable_slots = assignable_slots.into();
        self.total_slots = total_slots.into();
        unsafe { self.map.init(MapType::Slot) };
    }

    #[inline]
    pub fn assignable_slots_count(&self) -> usize {
        self.assignable_slots.into()
    }
}

impl SlotObject {
    /// Initialize a slot object
    /// # Safety
    /// the reference must be valid and assignable slots < total slots
    pub unsafe fn init(&mut self, map: Tagged<SlotMap>) {
        self.map = map;
        self.header =
            Header::encode_object(ObjectType::Slot, 0, HeaderFlags::empty(), 0);
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
        // SAFETY: pointer and length must be valid
        unsafe { std::slice::from_raw_parts(self.slots_ptr(), len) }
    }

    /// Borrow all slots as a mutable slice (checked).
    #[inline]
    pub fn slots_mut(&mut self) -> &mut [Value] {
        let len = self.assignable_slots();
        // SAFETY: pointer and length must be valid
        unsafe { std::slice::from_raw_parts_mut(self.slots_mut_ptr(), len) }
    }

    #[inline]
    pub fn assignable_slots(&self) -> usize {
        // SAFETY: every object MUST have a map object
        let map = unsafe { self.map.as_ref() };
        map.assignable_slots_count()
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

    /// get the slot at index
    /// # Safety
    /// Caller must ensure `index < assignable_slots()`.
    #[inline]
    pub unsafe fn get_slot_unchecked(&self, index: usize) -> Value {
        unsafe { self.slots_ptr().add(index).read() }
    }

    /// get the slot at index
    /// # Safety
    /// Caller must ensure `index < assignable_slots()`.
    #[inline]
    pub unsafe fn set_slot_unchecked(&mut self, index: usize, value: Value) {
        unsafe { self.slots_mut_ptr().add(index).write(value) };
    }
}

impl Object for SlotObject {}
impl HeapObject for SlotObject {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
            + self.assignable_slots() * mem::size_of::<Value>()
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
        visitor.visit_mut(self.map.into());
        self.slots().iter().for_each(|&obj| visitor.visit_mut(obj));
    }
    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        visitor.visit(self.map.into());
        self.slots().iter().for_each(|&obj| visitor.visit(obj));
    }
}
