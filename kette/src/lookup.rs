use std::{ptr::NonNull, sync::Arc};

use crate::{
    ByteArray, Handle, Message, Object, SlotDescriptor, Tagged, VMShared, Value,
};

#[derive(Debug, Clone)]
pub struct Selector {
    pub name: Handle<ByteArray>,
    pub vm: Arc<VMShared>,
}

/// used to find and break cycles
#[derive(Debug)]
pub struct VisitedLink {
    pub prev: Option<NonNull<Self>>,
    pub value: Value,
}

#[derive(Debug)]
pub enum LookupResult {
    None,
    Found {
        object: Tagged<Value>,
        slot: SlotDescriptor,
        slot_index: usize,
    },
}

impl Selector {
    pub fn new(name: Handle<ByteArray>, vm: Arc<VMShared>) -> Self {
        Self { name, vm }
    }
    pub fn new_message(message: Handle<Message>, vm: Arc<VMShared>) -> Self {
        // SAFETY: must be safe here
        let name = unsafe { message.value.promote_to_handle() };
        Self { name, vm }
    }

    pub fn lookup_object(self, object: &impl Object) -> LookupResult {
        self.lookup_object_chained(object, None)
    }

    pub fn lookup_object_chained(
        self,
        object: &impl Object,
        chain: Option<&VisitedLink>,
    ) -> LookupResult {
        object.lookup(self, chain)
    }
}

impl VisitedLink {
    pub fn contains(&self, target: Value) -> bool {
        if self.value == target {
            return true;
        }

        let mut cursor = self.prev;
        while let Some(ptr) = cursor {
            // SAFETY: VisitedLinks are stack-allocated in the recursion chain
            // and remain valid for the duration of the lookup.
            let node = unsafe { ptr.as_ref() };
            if node.value == target {
                return true;
            }
            cursor = node.prev;
        }

        false
    }

    #[inline]
    pub fn new(value: Value, prev: Option<&Self>) -> Self {
        Self {
            prev: prev.map(NonNull::from),
            value,
        }
    }
}
