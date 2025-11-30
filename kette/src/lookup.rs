use std::ptr::NonNull;

use crate::{ByteArray, Handle, Object, SlotInfo, Tagged, VMShared, Value};

#[derive(Debug, Copy, Clone)]
pub struct Selector<'vm> {
    pub name: Handle<ByteArray>,
    pub hash: u64,
    pub vm: &'vm VMShared,
}

/// used to find and break cycles
#[derive(Debug)]
pub struct VisitedLink {
    pub prev: Option<NonNull<Self>>,
    pub value: Value,
}

pub struct Lookup {
    pub object: Tagged<Value>,
    pub slot: SlotInfo,
    pub slot_index: usize,
}

pub enum LookupResult {
    None,
    Found(Lookup),
}

impl<'vm> Selector<'vm> {
    fn lookup_object(self, object: &impl Object) -> LookupResult {
        self.lookup_object_chained(object, None)
    }

    fn lookup_object_chained(
        self,
        object: &impl Object,
        chain: Option<&VisitedLink>,
    ) -> LookupResult {
        object.lookup(self, chain)
    }
}
