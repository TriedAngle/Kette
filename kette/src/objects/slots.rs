use std::{alloc::Layout, mem, ptr};

use bitflags::bitflags;

use crate::{
    ByteArray, Handle, Header, HeapObject, LookupResult, Map, MapType, Method,
    Object, ObjectKind, ObjectType, Selector, Tagged, Value, Visitable,
    VisitedLink, Visitor, primitive_index,
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
        const ASSIGNMENT = 1 << 4;
    }
}

// Helper for Rust side slot creation
#[derive(Debug, Clone, Copy)]
pub struct SlotHelper<'a> {
    pub name: &'a str,
    pub tags: SlotTags,
    pub value: Value,
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

/// slot ordering:
/// assignable parent > assignable > parent > constant
/// for objects, its in assiginable in order of definition
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
    /// initialize slot map with data
    pub fn init_with_data(&mut self, slots: &[SlotDescriptor]) {
        let mut slots = slots.to_vec();

        #[inline(always)]
        fn rank(tags: SlotTags) -> u8 {
            // lowest rank = earliest in array
            if tags.contains(SlotTags::ASSIGNABLE) {
                0
            } else if tags.contains(SlotTags::ASSIGNMENT) {
                1
            } else {
                2
            }
        }

        // stable: preserves definition order within equal ranks
        slots.sort_by(|a, b| {
            let ra = rank(a.tags());
            let rb = rank(b.tags());
            ra.cmp(&rb)
        });

        let assignable_slots = slots
            .iter()
            .filter(|s| s.tags().contains(SlotTags::ASSIGNABLE))
            .count();

        let total_slots = slots.len();

        // SAFETY: safe if allocation is correctly sized
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
        // SAFETY: safe if contract holds
        self.map.init(MapType::Slot);
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

    /// # Safety
    /// maps are expected to me immutable always, use this only if necessary!
    #[inline]
    pub unsafe fn slots_mut(&mut self) -> &mut [SlotDescriptor] {
        let count = self.slot_count();
        // SAFETY: this is safe
        unsafe {
            std::slice::from_raw_parts_mut(self.slots.as_mut_ptr(), count)
        }
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
    /// # Panics
    /// data length must match assignable slot count of map
    pub fn init_with_data(&mut self, map: Tagged<SlotMap>, data: &[Value]) {
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
    /// must set the data
    pub unsafe fn init(&mut self, map: Tagged<SlotMap>) {
        self.map = map;
        self.header = Header::new_object(ObjectType::Slot);
    }

    #[inline]
    pub fn slots_ptr(&self) -> *const Value {
        self.slots.as_ptr()
    }

    #[inline]
    pub fn slots_mut_ptr(&mut self) -> *mut Value {
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
            // SAFETY: checked
            Some(unsafe { self.slots_ptr().add(index).read() })
        } else {
            None
        }
    }

    #[inline]
    pub fn set_slot(&mut self, index: usize, value: Value) -> bool {
        if index < self.assignable_slots() {
            // SAFETY: checked
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
        // SAFETY: safe if contract holds
        unsafe { self.slots_ptr().add(index).read() }
    }

    /// get the slot at index
    /// # Safety
    /// Caller must ensure `index < assignable_slots()`.
    #[inline]
    pub unsafe fn set_slot_unchecked(&mut self, index: usize, value: Value) {
        // SAFETY: safe if contract holds
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
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let self_ptr = self as *const Self as *mut Self;
        let self_value = Tagged::new_ptr(self_ptr).as_tagged_value();

        // 1. Cycle Detection
        if let Some(history) = link
            && history.contains(self_value.into())
        {
            return LookupResult::None;
        }

        // SAFETY: map must be valid
        let map = unsafe { self.map.as_ref() };
        let slots = map.slots();

        // Local Lookup
        let local_match = slots
            .iter()
            .enumerate()
            .find(|(_idx, slot)| {
                slot.name.as_ptr()
                    == selector.name.as_tagged::<ByteArray>().as_ptr()
            })
            .map(|(idx, slot)| (idx, *slot));

        if let Some((idx, mut slot)) = local_match {
            // Normalize assignable: slot.value is offset -> return actual stored value
            if slot.tags().contains(SlotTags::ASSIGNABLE) {
                let offset = slot
                    .value
                    .as_tagged_fixnum::<usize>()
                    .expect("assignable slot must store offset");
                // SAFETY: offset must be valid by construction
                slot.value = unsafe { self.get_slot_unchecked(offset.into()) };
            }

            return LookupResult::Found {
                object: self_value,
                slot,
                slot_index: idx,
            };
        }

        // Parent Lookup
        let current_link = VisitedLink::new(self_value.into(), link);

        for slot in slots {
            let tags = slot.tags();

            if tags.contains(SlotTags::PARENT) {
                let parent = if tags.contains(SlotTags::ASSIGNABLE) {
                    // slot.value stores offset for assignable slots
                    let offset = slot
                        .value
                        .as_tagged_fixnum::<usize>()
                        .expect("assignable parent slot must store offset");
                    // SAFETY: offset must be valid by construction
                    unsafe { self.get_slot_unchecked(offset.into()) }
                } else {
                    slot.value
                };

                match parent.lookup(selector.clone(), Some(&current_link)) {
                    LookupResult::None => continue,
                    found => return found,
                }
            }
        }

        LookupResult::None
    }
}

impl HeapObject for SlotObject {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Slot as u8;
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
            + self.assignable_slots() * mem::size_of::<Value>()
    }
}

impl Object for SlotMap {}
impl HeapObject for SlotMap {
    const KIND: ObjectKind = ObjectKind::Map;
    const TYPE_BITS: u8 = MapType::Slot as u8;
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
            + self.slot_count() * mem::size_of::<SlotDescriptor>()
    }
}

impl Visitable for SlotMap {
    // TODO: update this once we actually use stuff here
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        self.slots().iter().for_each(|desc| {
            visitor.visit_mut(desc.name.into());
            visitor.visit_mut(desc.value);
        });
    }

    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        self.slots().iter().for_each(|desc| {
            visitor.visit(desc.name.into());
            visitor.visit(desc.value);
        });
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

    pub fn assignable(name: &'a str, value: Value, tags: SlotTags) -> Self {
        let tags = tags | SlotTags::ASSIGNABLE;
        Self { name, value, tags }
    }

    pub fn constant(name: &'a str, value: Value, tags: SlotTags) -> Self {
        Self { name, value, tags }
    }

    #[inline]
    pub fn primitive_message(name: &'a str, tags: SlotTags) -> Self {
        let tags = tags | SlotTags::PRIMITIVE | SlotTags::EXECUTABLE;
        let index = primitive_index(name);
        let value = index.as_raw();
        Self::new(name, value.into(), tags)
    }

    #[inline]
    pub fn primitive_message2(
        name: &'a str,
        primitive: &'a str,
        tags: SlotTags,
    ) -> Self {
        let tags = tags | SlotTags::PRIMITIVE | SlotTags::EXECUTABLE;
        let index = primitive_index(primitive);
        let value = index.as_raw();
        Self::new(name, value.into(), tags)
    }

    #[inline]
    pub fn message(
        name: &'a str,
        method: Handle<Method>,
        tags: SlotTags,
    ) -> Self {
        let tags = tags | SlotTags::EXECUTABLE;
        let value = method.as_value();
        Self::new(name, value, tags)
    }
}
