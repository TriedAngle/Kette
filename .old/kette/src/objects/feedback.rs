use std::mem;

use crate::{
    Handle, Header, HeapObject, HeapValue, Map, Object, ObjectKind, ObjectType,
    Tagged, Visitable, Visitor,
};

/// Cached lookup result for inline caching.
///
/// Stores the information needed to skip a full lookup when the receiver's
/// map matches a previously seen map.
#[repr(C)]
#[derive(Debug)]
pub struct FeedbackEntry {
    pub header: Header,
    /// Map of the receiver at cache time
    pub receiver_map: Handle<Map>,
    /// Map of the holder at cache time (for invalidation)
    pub holder_map: Handle<Map>,
    /// Object where slot was found (may be receiver or a parent)
    pub holder: Handle<HeapValue>,
    /// Index into holder.map.slots()
    pub slot_index: Tagged<usize>,
}

impl FeedbackEntry {
    /// Initialize a feedback entry with cached lookup data.
    pub fn init(
        &mut self,
        receiver_map: Handle<Map>,
        holder_map: Handle<Map>,
        holder: Handle<HeapValue>,
        slot_index: usize,
    ) {
        self.header = Header::new_object(ObjectType::FeedbackEntry);
        self.receiver_map = receiver_map;
        self.holder_map = holder_map;
        self.holder = holder;
        self.slot_index = slot_index.into();
    }

    /// Get the cached slot index.
    #[inline]
    pub fn slot_index(&self) -> usize {
        self.slot_index.into()
    }
}

impl Object for FeedbackEntry {}

impl HeapObject for FeedbackEntry {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::FeedbackEntry as u8;

    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl Visitable for FeedbackEntry {
    fn visit_edges(&self, visitor: &impl Visitor) {
        visitor.visit(self.receiver_map.as_value_ref());
        visitor.visit(self.holder_map.as_value_ref());
        visitor.visit(self.holder.as_value_ref());
    }

    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        visitor.visit_mut(self.receiver_map.as_value_mut());
        visitor.visit_mut(self.holder_map.as_value_mut());
        visitor.visit_mut(self.holder.as_value_mut());
    }
}
