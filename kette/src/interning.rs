use std::{collections::HashMap, sync::Arc};

use parking_lot::RwLock;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InternedId(u64);

pub struct InternedString {
    id: InternedId,
    value: Arc<str>,
}

// TODO: investigate if it is possible to remove the string allocation and use a 'static str or similar instead
pub struct InternedStringsImpl {
    table: HashMap<InternedId, Arc<str>>,
    mappings: HashMap<String, InternedId>,
}

pub struct InternedStrings(Arc<RwLock<InternedStringsImpl>>);

impl InternedStringsImpl {
    fn new() -> Self {
        Self {
            table: HashMap::new(),
            mappings: HashMap::new(),
        }
    }

    fn get_or_add(&mut self, value: &str) -> InternedId {
        if let Some(&id) = self.mappings.get(value) {
            return id;
        }
        use std::hash::Hasher;
        let mut hasher = ahash::AHasher::default();
        hasher.write(value.as_bytes());
        let hash = hasher.finish();
        let id = InternedId(hash);
        let owned = value.to_owned();
        let interned_allocation = owned.clone();
        let interned = Arc::<str>::from(interned_allocation);
        self.mappings.insert(owned, id);
        self.table.insert(id, interned);
        id
    }

    fn get(&self, id: &InternedId) -> Option<Arc<str>> {
        self.table.get(id).cloned()
    }

    fn get_string(&self, id: &InternedId) -> Option<InternedString> {
        Some(InternedString {
            id: *id,
            value: self.table.get(id).cloned()?,
        })
    }
}

impl InternedStrings {
    pub fn new() -> Self {
        Self(Arc::new(RwLock::new(InternedStringsImpl::new())))
    }
    pub fn add(&self, value: &str) -> InternedId {
        self.0.write().get_or_add(value)
    }
    pub fn get(&self, id: &InternedId) -> Option<Arc<str>> {
        self.0.read().get(id)
    }

    fn get_string(&self, id: &InternedId) -> Option<InternedString> {
        self.0.read().get_string(id)
    }
}
