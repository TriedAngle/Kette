use dashmap::DashMap;

use crate::{Allocator, ByteArray, Handle, HeapProxy, Message};

/// Concurrent string interning table.
///
/// ByteArrays in this struct are rooted and thus handles.
/// Note: this table must be updated in case the GC compacts.
#[derive(Debug)]
pub struct Strings {
    table: DashMap<String, Handle<ByteArray>, ahash::RandomState>,
}

impl Default for Strings {
    fn default() -> Self {
        Self::new()
    }
}

impl Strings {
    #[must_use]
    pub fn new() -> Self {
        Self {
            table: DashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    pub fn get(&self, s: &str, heap: &mut impl Allocator) -> Handle<ByteArray> {
        // Fast path: check if already exists
        if let Some(ba) = self.table.get(s).map(|r| *r.value()) {
            return ba;
        }

        // Slow path: allocate and insert
        let ba = heap.allocate_aligned_bytearray(s.as_bytes(), 8);
        // Safety: the table is part of the rootset
        self.table.insert(s.to_owned(), ba);
        ba
    }
}

/// Concurrent message interning table.
///
/// Messages in this struct are rooted and thus handles.
/// Note: this table must be updated in case the GC compacts.
#[derive(Debug)]
pub struct Messages {
    table: DashMap<Handle<ByteArray>, Handle<Message>, ahash::RandomState>,
}

impl Default for Messages {
    fn default() -> Self {
        Self::new()
    }
}

impl Messages {
    pub fn new() -> Self {
        Self {
            table: DashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    pub fn get(
        &self,
        ba: Handle<ByteArray>,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        // Fast path: check if already exists
        if let Some(msg) = self.table.get(&ba).map(|r| *r.value()) {
            return msg;
        }

        // Slow path: allocate and insert
        let message = heap.allocate_message(ba);
        self.table.insert(ba, message);
        message
    }
}
