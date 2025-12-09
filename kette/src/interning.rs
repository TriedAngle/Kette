use std::collections::HashMap;

use parking_lot::RwLock;

use crate::{ByteArray, Handle, HeapProxy, Message};

/// TODO: single RW lock is bad in multithreading.
/// I think a better solution would be to have first thread local
/// with an afterwards one time merge (or none at all if the eval doesn't "dirty" anything)
/// sharding could also be a valid option
/// ByteArrays in this struct are rooted and thus handles.
/// But: this table must be updated in case the GC compacts
#[derive(Debug)]
pub struct Strings {
    table: RwLock<HashMap<String, Handle<ByteArray>, ahash::RandomState>>,
}

impl Default for Strings {
    fn default() -> Self {
        Self::new()
    }
}

impl Strings {
    pub fn new() -> Self {
        Self {
            table: RwLock::new(HashMap::default()),
        }
    }

    pub fn get(&self, s: &str, heap: &mut HeapProxy) -> Handle<ByteArray> {
        {
            let table = self.table.read();
            if let Some(ba) = table.get(s).copied() {
                return ba;
            }
        }
        let ba = heap.allocate_bytearray_data(s.as_bytes());
        let s = s.to_owned();
        // Safety: the table is part of the rootset;
        let ba = unsafe { ba.promote_to_handle() };
        {
            let mut table = self.table.write();
            table.insert(s, ba);
        }
        ba
    }
}

/// TODO: single RW lock is bad in multithreading.
/// I think a better solution would be to have first thread local
/// with an afterwards one time merge (or none at all if the eval doesn't "dirty" anything)
/// sharding could also be a valid option
/// ByteArrays in this struct are rooted and thus handles.
/// But: this table must be updated in case the GC compacts
#[derive(Debug)]
pub struct Messages {
    table:
        RwLock<HashMap<Handle<ByteArray>, Handle<Message>, ahash::RandomState>>,
}

impl Default for Messages {
    fn default() -> Self {
        Self::new()
    }
}

impl Messages {
    pub fn new() -> Self {
        Self {
            table: RwLock::new(HashMap::default()),
        }
    }

    pub fn get(
        &self,
        ba: Handle<ByteArray>,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        {
            let table = self.table.read();
            if let Some(ba) = table.get(&ba).copied() {
                return ba;
            }
        }

        let message = heap.allocate_message(ba.into());
        // SAFETY: this is safe
        let message = unsafe { message.promote_to_handle() };
        {
            let mut table = self.table.write();
            table.insert(ba, message);
        }
        message
    }
}
