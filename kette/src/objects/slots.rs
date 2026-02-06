use std::{alloc::Layout, mem, ops::Deref, ptr};

use bitflags::bitflags;

use crate::{
    ByteArray, Code, Handle, Header, HeapObject, LookupResult, Object,
    ObjectKind, ObjectType, ParentLookup, Selector, Tagged, Value, Visitable,
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
    pub name: Handle<ByteArray>,
    pub metadata: Tagged<usize>,
    pub value: Value,
}

/// slot ordering:
/// assignable parent > assignable > parent > constant
/// for objects, its in assiginable in order of definition
#[repr(C)]
#[derive(Debug)]
pub struct Map {
    pub header: Header,
    pub code: Handle<Code>,
    pub effect: Tagged<u64>,
    pub assignable_slots: Tagged<usize>,
    pub data_slots: Tagged<usize>,
    pub total_slots: Tagged<usize>,
    pub hotness: Tagged<usize>,
    pub slots: [SlotDescriptor; 0],
}

#[repr(C)]
#[derive(Debug)]
pub struct SlotObject {
    pub header: Header,
    pub map: Handle<Map>,
    pub slots: [Value; 0],
}

impl SlotDescriptor {
    #[must_use]
    pub fn new(name: Handle<ByteArray>, tags: SlotTags, value: Value) -> Self {
        let tags_raw = tags.bits();
        let metadata = Tagged::new_value(tags_raw as usize);
        Self {
            name,
            metadata,
            value,
        }
    }

    #[must_use]
    pub fn tags(&self) -> SlotTags {
        let value: u64 = self.metadata.into();
        let raw: u8 = (value & 0xFF) as u8; // cutting off
        SlotTags::from_bits(raw).expect("must have valid tags")
    }

    #[inline]
    #[must_use]
    pub fn is_data_consumer(&self) -> bool {
        let tags = self.tags();
        !tags.contains(SlotTags::ASSIGNMENT)
            && !tags.contains(SlotTags::PRIMITIVE)
    }
}

impl Map {
    pub fn collect_values(&mut self, values: &[Value]) -> Vec<Value> {
        let assignable_count = self.assignable_slots_count();
        let mut object_storage = Vec::with_capacity(assignable_count);

        let mut val_iter = values.iter().cloned();

        // SAFETY: this must exist here
        for slot in unsafe { self.slots_mut() } {
            if slot.is_data_consumer() {
                let val = val_iter.next().expect("Stack values count mismatch");

                if slot.tags().contains(SlotTags::ASSIGNABLE) {
                    object_storage.push(val);
                } else {
                    slot.value = val;
                }
            }
        }

        object_storage
    }

    /// initialize slot map with data
    pub fn init_with_data(
        &mut self,
        slots: &[SlotDescriptor],
        code_ptr: Handle<Code>,
        effect: Tagged<u64>,
    ) {
        let data_slots = slots.iter().filter(|s| s.is_data_consumer()).count();

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
        unsafe {
            self.init(
                assignable_slots,
                data_slots,
                total_slots,
                code_ptr,
                effect,
            )
        };
    }

    /// Initialize a slot map
    /// this is unsafe as this is intended to be a mostly internal api
    /// # Safety
    /// the reference must be valid and assignable slots < total slots
    #[inline]
    pub unsafe fn init(
        &mut self,
        assignable_slots: usize,
        data_slots: usize,
        total_slots: usize,
        code_ptr: Handle<Code>,
        effect: Tagged<u64>,
    ) {
        self.assignable_slots = assignable_slots.into();
        self.data_slots = data_slots.into();
        self.total_slots = total_slots.into();
        self.hotness = 0usize.into();
        // SAFETY: safe if contract holds
        self.header = Header::new_map();
        self.code = code_ptr;
        self.effect = effect;
    }

    #[inline]
    pub fn increment_hotness(&mut self) {
        let current: usize = self.hotness.into();
        // Saturating add to avoid overflow panics, though strictly usize wrap might be intended behavior in some VMs.
        // Saturating is safer.
        self.hotness = current.saturating_add(1).into();
    }

    #[inline]
    pub fn hotness(&self) -> usize {
        self.hotness.into()
    }

    #[inline]
    pub fn assignable_slots_count(&self) -> usize {
        self.assignable_slots.into()
    }

    #[inline]
    pub fn slot_count(&self) -> usize {
        self.total_slots.into()
    }

    #[inline]
    pub fn data_slots(&self) -> usize {
        self.data_slots.into()
    }

    /// calculate the layout of a map with n slots
    #[must_use]
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

    #[inline]
    pub fn input_count(&self) -> usize {
        let encoded: u64 = self.effect.into();
        (encoded >> 32) as usize
    }

    /// Extracts the number of outputs from the effect field.
    /// The effect is encoded as: ((inputs << 32) | outputs) tagged (shifted left 1).
    /// `self.effect.into()` performs the untagging.
    #[inline]
    pub fn output_count(&self) -> usize {
        let encoded: u64 = self.effect.into();
        (encoded & 0xFFFF_FFFF) as usize
    }

    #[inline]
    pub fn has_code(&self) -> bool {
        // Assuming 0 or Nil indicates no code. Adjust if your type differs.
        !self.code.as_ptr().is_null()
    }

    /// Returns the raw pointer to the executable Block.
    #[inline]
    pub fn code(&self) -> Option<&Code> {
        if self.has_code() {
            return Some(self.code.deref());
        }
        None
    }
}

impl SlotObject {
    /// # Panics
    /// data length must match assignable slot count of map
    pub fn init_with_data(&mut self, map: Handle<Map>, data: &[Value]) {
        let map_slot_count = map.assignable_slots_count();
        assert_eq!(map_slot_count, data.len());
        // SAFETY: map_slot_count matches data.len() and object was allocated
        // with sufficient space via required_layout().
        unsafe {
            ptr::copy_nonoverlapping(
                data.as_ptr(),
                self.slots_mut_ptr(),
                map_slot_count,
            )
        };
        // SAFETY: Object is fully allocated and slots are copied; init completes initialization.
        unsafe { self.init(map) };
    }
    /// Initialize a slot object
    /// # Safety
    /// the reference must be valid and assignable slots < total slots
    /// must set the data
    pub unsafe fn init(&mut self, map: Handle<Map>) {
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
        self.map.assignable_slots_count()
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
        debug_assert!(
            index < self.assignable_slots(),
            "get_slot_unchecked out of bounds: {} >= {}",
            index,
            self.assignable_slots()
        );
        // SAFETY: safe if contract holds
        unsafe { self.slots_ptr().add(index).read() }
    }

    /// get the slot at index
    /// # Safety
    /// Caller must ensure `index < assignable_slots()`.
    #[inline]
    pub unsafe fn set_slot_unchecked(&mut self, index: usize, value: Value) {
        debug_assert!(
            index < self.assignable_slots(),
            "set_slot_unchecked out of bounds: {} >= {}",
            index,
            self.assignable_slots()
        );
        // SAFETY: safe if contract holds
        unsafe { self.slots_mut_ptr().add(index).write(value) };
    }

    /// calculate the layout of an object with n assignable slots
    #[must_use]
    pub fn required_layout(assignable_slots: usize) -> Layout {
        let head = Layout::new::<Self>();
        let slots_layout = Layout::array::<Value>(assignable_slots)
            .expect("create valid layout");
        let (layout, _) =
            head.extend(slots_layout).expect("create valid layout");
        layout
    }

    fn lookup_local_only(
        &self,
        selector: Selector,
        self_value: Tagged<Value>,
    ) -> LookupResult {
        let slots = self.map.slots();
        self.lookup_local(selector, self_value, &slots)
    }

    fn lookup_local(
        &self,
        selector: Selector,
        self_value: Tagged<Value>,
        slots: &[SlotDescriptor],
    ) -> LookupResult {
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
                traversed_assignable_parent: false,
            };
        }

        LookupResult::None
    }
}

impl Object for SlotObject {
    /// Looks up a slot by name, traversing parent chains.
    /// Uses cycle detection to avoid infinite loops in circular parent relationships.
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

        match selector.parent_lookup {
            ParentLookup::SelfOnly => {
                return self.lookup_local_only(selector, self_value);
            }
            ParentLookup::StartAtParent(parent) => {
                let current_link = VisitedLink::new(self_value.into(), link);
                let selector =
                    selector.with_parent_lookup(ParentLookup::SelfAndParents);
                return parent.lookup(selector, Some(&current_link));
            }
            ParentLookup::SelfAndParents => {}
        }

        let slots = self.map.slots();

        // Local Lookup
        let local_lookup =
            self.lookup_local(selector.clone(), self_value, &slots);
        if let LookupResult::Found { .. } = local_lookup {
            return local_lookup;
        }

        // Parent Lookup
        let current_link = VisitedLink::new(self_value.into(), link);

        for slot in slots {
            let tags = slot.tags();

            if tags.contains(SlotTags::PARENT) {
                let is_assignable_parent = tags.contains(SlotTags::ASSIGNABLE);
                let parent = if is_assignable_parent {
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
                    LookupResult::Found {
                        object,
                        slot,
                        slot_index,
                        traversed_assignable_parent,
                    } => {
                        // Propagate the flag: if we traversed an assignable
                        // parent, or if our child lookup did
                        return LookupResult::Found {
                            object,
                            slot,
                            slot_index,
                            traversed_assignable_parent:
                                traversed_assignable_parent
                                    || is_assignable_parent,
                        };
                    }
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

impl Object for Map {}
impl HeapObject for Map {
    const KIND: ObjectKind = ObjectKind::Map;
    const TYPE_BITS: u8 = 0;
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
            + self.slot_count() * mem::size_of::<SlotDescriptor>()
    }
}

impl Visitable for Map {
    // TODO: update this once we actually use stuff here
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        if self.has_code() {
            visitor.visit_mut(self.code.as_value_mut());
        }
        // SAFETY: maps are expected to be immutable, but GC needs to update edges.
        let slots = unsafe { self.slots_mut() };
        slots.iter_mut().for_each(|desc| {
            visitor.visit_mut(desc.name.as_value_mut());
            visitor.visit_mut(&mut desc.value);
        });
    }

    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        if self.has_code() {
            visitor.visit(self.code.as_value_ref());
        }
        self.slots().iter().for_each(|desc| {
            visitor.visit(desc.name.as_value_ref());
            visitor.visit(&desc.value);
        });
    }
}

impl Visitable for SlotObject {
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        visitor.visit_mut(self.map.as_value_mut());
        self.slots_mut()
            .iter_mut()
            .for_each(|obj| visitor.visit_mut(obj));
    }
    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        visitor.visit(self.map.as_value_ref());
        self.slots().iter().for_each(|obj| visitor.visit(obj));
    }
}

impl<'a> SlotHelper<'a> {
    #[inline]
    #[must_use]
    pub fn new(name: &'a str, value: Value, tags: SlotTags) -> Self {
        Self { name, tags, value }
    }

    #[must_use]
    pub fn assignable(name: &'a str, value: Value, tags: SlotTags) -> Self {
        let tags = tags | SlotTags::ASSIGNABLE;
        Self { name, tags, value }
    }

    #[must_use]
    pub fn constant(name: &'a str, value: Value, tags: SlotTags) -> Self {
        Self { name, tags, value }
    }

    #[inline]
    #[must_use]
    pub fn primitive_message(name: &'a str, tags: SlotTags) -> Self {
        let tags = tags | SlotTags::PRIMITIVE;
        let index = primitive_index(name);
        let value = index.as_raw();
        Self::new(name, value.into(), tags)
    }

    #[inline]
    #[must_use]
    pub fn primitive_message2(
        name: &'a str,
        primitive: &'a str,
        tags: SlotTags,
    ) -> Self {
        let tags = tags | SlotTags::PRIMITIVE;
        let index = primitive_index(primitive);
        let value = index.as_raw();
        Self::new(name, value.into(), tags)
    }

    #[inline]
    #[must_use]
    pub fn message(
        name: &'a str,
        method: Handle<SlotObject>,
        tags: SlotTags,
    ) -> Self {
        let value = method.as_value();
        Self::new(name, value, tags)
    }
}
