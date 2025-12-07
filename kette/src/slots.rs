use std::{alloc::Layout, mem, ptr};

use bitflags::bitflags;

use crate::{
    ByteArray, Header, HeaderFlags, HeapObject, LookupResult, Map, MapType,
    Object, ObjectType, PrimitiveMessageIndex, Selector, Tagged, Value,
    Visitable, VisitedLink, Visitor, get_primitive, primitive_index,
};

bitflags! {
    /// constant 00
    /// parent 01
    /// assignable 10
    /// assignable parent 11
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub struct SlotTags: u8 {
        const PARENT = 1 << 0;
        const ASSIGNABLE = 1 << 1;
        const PRIMITIVE = 1 << 2;
        const EXECUTABLE = 1 << 3;
    }
}

/// assignable slot: offset to value in object
/// Const slot: value
/// Parent slot: constant lookup (static?)
/// Assignable Parent slot: normal data slot that is also parent
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SlotDescriptor {
    /// guaranteed to be interned
    pub name: Tagged<ByteArray>,
    pub metadata: Tagged<usize>,
    pub value: Value,
}

// Helper for Rust side slot creation
#[derive(Debug, Clone, Copy)]
pub struct SlotHelper<'a> {
    pub name: &'a str,
    pub tags: SlotTags,
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
    pub slots: [SlotDescriptor; 0],
}

#[repr(C)]
#[derive(Debug)]
pub struct SlotObject {
    pub header: Header,
    pub map: Tagged<SlotMap>,
    pub slots: [Value; 0],
}

impl SlotDescriptor {
    pub fn new(name: Tagged<ByteArray>, tags: SlotTags, value: Value) -> Self {
        let tags_raw = tags.bits();
        let metadata = Tagged::new_value(tags_raw as usize);
        Self {
            name,
            metadata,
            value,
        }
    }

    pub fn tags(&self) -> SlotTags {
        let value: u64 = self.metadata.into();
        let raw: u8 = (value & 0xFF) as u8; // cutting off
        SlotTags::from_bits(raw).expect("must have valid tags")
    }
}

impl SlotMap {
    // will go through the slots
    pub unsafe fn init_with_data(&mut self, slots: &[SlotDescriptor]) {
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

    #[inline]
    pub fn slot_count(&self) -> usize {
        self.total_slots.into()
    }

    /// calculate the layout of a map with n slots
    pub fn required_layout(slots: usize) -> Layout {
        let head = Layout::new::<Self>();
        let slots_layout = Layout::array::<SlotDescriptor>(slots)
            .expect("create valid layout");
        let (layout, _) =
            head.extend(slots_layout).expect("create valid layout");
        layout
    }

    /// Returns a slice containing all slot descriptors
    #[inline]
    pub fn slots(&self) -> &[SlotDescriptor] {
        let count = self.slot_count();
        // SAFETY: this is safe
        unsafe { std::slice::from_raw_parts(self.slots.as_ptr(), count) }
    }

    /// Returns a slice containing only the assignable slot descriptors
    /// Relies on the invariant that slots are sorted such that assignable
    /// slots always appear at the start of the array (indices `0..assignable_count`).
    #[inline]
    pub fn assignable_slots(&self) -> &[SlotDescriptor] {
        let count = self.assignable_slots_count();
        // SAFETY: this is safe
        // 2. The sorting invariant ensures the first `n` slots are the assignable ones.
        unsafe { std::slice::from_raw_parts(self.slots.as_ptr(), count) }
    }
}

impl SlotObject {
    pub unsafe fn init_with_data(
        &mut self,
        map: Tagged<SlotMap>,
        data: &[Value],
    ) {
        // SAFETY: map must be valid here
        let map_slot_count = unsafe { map.as_ref().assignable_slots_count() };
        assert_eq!(map_slot_count, data.len());
        // SAFETY: length checked and slot object correctly sized
        unsafe {
            ptr::copy_nonoverlapping(
                data.as_ptr(),
                self.slots_mut_ptr(),
                map_slot_count,
            )
        };
        // SAFETY: this is safe
        unsafe { self.init(map) };
    }
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

    /// calculate the layout of an object with n assignable slots
    pub fn required_layout(assignable_slots: usize) -> Layout {
        let head = Layout::new::<Self>();
        let slots_layout = Layout::array::<Value>(assignable_slots)
            .expect("create valid layout");
        let (layout, _) =
            head.extend(slots_layout).expect("create valid layout");
        layout
    }
}

impl Object for SlotObject {
    fn lookup(
        &self,
        selector: Selector,
        _link: Option<&VisitedLink>,
    ) -> LookupResult {
        let self_ptr = self as *const Self as *mut Self;
        // SAFETY: map must be valid
        let map = unsafe { self.map.as_ref() };
        let slots = map.slots();
        // interning guarantees same string == same pointer
        let res = slots
            .iter()
            .enumerate()
            .find(|(_idx, slot)| {
                slot.name.as_ptr()
                    == selector.name.as_tagged::<ByteArray>().as_ptr()
            })
            .map(|(idx, slot)| (idx, *slot));
        if let Some((idx, slot)) = res {
            return LookupResult::Found {
                object: Tagged::new_ptr(self_ptr).as_tagged_value(),
                slot,
                slot_index: idx,
            };
        }
        // TODO: implement parent lookup and cycle detection using Link
        LookupResult::None
    }
}
impl HeapObject for SlotObject {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
            + self.assignable_slots() * mem::size_of::<Value>()
    }
}

impl Object for SlotMap {}
impl HeapObject for SlotMap {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>() + self.slot_count()
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

impl<'a> SlotHelper<'a> {
    #[inline]
    pub fn new(name: &'a str, value: Value, tags: SlotTags) -> Self {
        Self { name, value, tags }
    }

    #[inline]
    pub fn primitive(name: &'a str, value: Value, tags: SlotTags) -> Self {
        let tags = tags | SlotTags::PRIMITIVE;
        Self::new(name, value, tags)
    }

    #[inline]
    pub fn primitive_message(name: &'a str, tags: SlotTags) -> Self {
        let tags = tags | SlotTags::PRIMITIVE | SlotTags::EXECUTABLE;
        let index = primitive_index(name);
        let value = index.as_raw();
        Self::new(name, value.into(), tags)
    }
}
