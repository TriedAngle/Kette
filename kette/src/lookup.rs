use std::{ptr::NonNull, sync::Arc};

use crate::{
    ByteArray, Handle, Message, Object, SlotDescriptor, Tagged, VMShared, Value,
};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ParentLookup {
    /// Lookup in the receiver, then traverse parents.
    SelfAndParents,
    /// Lookup only in the receiver; skip parents.
    SelfOnly,
    /// Start lookup at a specific parent, then traverse its parents.
    StartAtParent(Value),
}

#[derive(Debug, Clone)]
pub struct Selector {
    pub name: Handle<ByteArray>,
    pub vm: Arc<VMShared>,
    pub parent_lookup: ParentLookup,
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
        /// True if the lookup traversed through an assignable parent slot.
        /// Used by IC to decide whether to cache (assignable parents can change).
        traversed_assignable_parent: bool,
    },
}

impl Selector {
    #[must_use]
    pub fn new(name: Handle<ByteArray>, vm: Arc<VMShared>) -> Self {
        Self {
            name,
            vm,
            parent_lookup: ParentLookup::SelfAndParents,
        }
    }
    #[must_use]
    pub fn new_message(message: Handle<Message>, vm: Arc<VMShared>) -> Self {
        let name = message.value;
        Self {
            name,
            vm,
            parent_lookup: ParentLookup::SelfAndParents,
        }
    }

    #[must_use]
    pub fn with_no_parents(mut self) -> Self {
        self.parent_lookup = ParentLookup::SelfOnly;
        self
    }

    #[must_use]
    pub fn with_parent_start(mut self, parent: Value) -> Self {
        self.parent_lookup = ParentLookup::StartAtParent(parent);
        self
    }

    #[must_use]
    pub fn with_parent_lookup(mut self, parent_lookup: ParentLookup) -> Self {
        self.parent_lookup = parent_lookup;
        self
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
    #[must_use]
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
