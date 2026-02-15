use dashmap::DashMap;

use crate::{Allocator, Handle, HeapProxy, Message, StringObject};

/// Concurrent string interning table.
///
/// ByteArrays in this struct are rooted and thus handles.
/// Note: this table must be updated in case the GC compacts.
#[derive(Debug)]
pub struct Strings {
    table: DashMap<String, Handle<StringObject>, ahash::RandomState>,
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

    pub fn get(
        &self,
        s: &str,
        heap: &mut impl Allocator,
    ) -> Handle<StringObject> {
        // Fast path: check if already exists
        if let Some(string) = self.table.get(s).map(|r| *r.value()) {
            return string;
        }

        // Slow path: allocate and insert
        let ba = heap.allocate_aligned_bytearray(s.as_bytes(), 8);
        let string = heap.allocate_string(ba);
        // Safety: the table is part of the rootset
        self.table.insert(s.to_owned(), string);
        string
    }
}

/// Concurrent message interning table.
///
/// Messages in this struct are rooted and thus handles.
/// Note: this table must be updated in case the GC compacts.
#[derive(Debug)]
pub struct Messages {
    table: DashMap<Handle<StringObject>, Handle<Message>, ahash::RandomState>,
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
        string: Handle<StringObject>,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        // Fast path: check if already exists
        if let Some(msg) = self.table.get(&string).map(|r| *r.value()) {
            return msg;
        }

        // Slow path: allocate and insert
        let message = heap.allocate_message(string);
        self.table.insert(string, message);
        message
    }
}
