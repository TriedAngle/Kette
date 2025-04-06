use std::{collections::linked_list, mem};

use crate::{
    Array, GarbageCollector, MemoryRegion, Object, ObjectHeader,
    SLOT_CONST_DATA, StackFn, Tagged, Word,
};

pub struct Context {
    pub header: ObjectHeader,
    pub datastack: Tagged,
    pub retainstack: Tagged,
    pub namestack: Tagged,
    pub callstack: Tagged,

    pub gc: GarbageCollector,

    pub data: MemoryRegion<Tagged>,
    pub retain: MemoryRegion<Tagged>,
    pub name: MemoryRegion<Tagged>,
}

pub struct ContextConfig {
    pub data_size: usize,
    pub retian_size: usize,
    pub name_size: usize,
}

impl Context {
    pub fn new(config: &ContextConfig) -> Self {
        let mut gc = GarbageCollector::new();
        let datastack = gc.allocate_array(config.data_size);
        let retainstack = gc.allocate_array(config.retian_size);
        let namestack = gc.allocate_array(config.name_size);
        let callstack = Tagged::ffalse();

        let data = (datastack.to_ptr() as *mut Array).into();
        let retain = (retainstack.to_ptr() as *mut Array).into();
        let name = (namestack.to_ptr() as *mut Array).into();

        gc.add_root(datastack);
        gc.add_root(retainstack);
        gc.add_root(namestack);

        let ctx_map = gc.create_map(
            "Context",
            &[
                ("datastack", SLOT_CONST_DATA, Tagged::from_int(0)),
                ("retainstack", SLOT_CONST_DATA, Tagged::from_int(1)),
                ("namestack", SLOT_CONST_DATA, Tagged::from_int(2)),
                ("callstack", SLOT_CONST_DATA, Tagged::from_int(3)),
            ],
        );

        Self {
            header: ObjectHeader::new(ctx_map.to_ptr() as *mut _),
            datastack,
            retainstack,
            namestack,
            callstack,
            data,
            retain,
            name,
            gc,
        }
    }

    pub fn push(&mut self, value: Tagged) {
        let _ = self.data.replace(value);
        self.data.increment(1);
    }

    pub fn pop(&mut self) -> Tagged {
        self.data.decrement(1);
        self.data.replace(Tagged::null())
    }

    pub fn retain_push(&mut self, value: Tagged) {
        let _ = self.retain.replace(value);
        self.retain.increment(1);
    }

    pub fn retain_pop(&mut self) -> Tagged {
        self.retain.decrement(1);
        self.retain.replace(Tagged::null())
    }

    pub fn data_retain(&mut self) {
        let value = self.pop();
        self.retain_push(value);
    }

    pub fn retain_data(&mut self) {
        let value = self.retain_pop();
        self.push(value);
    }

    pub fn is_quotation(&self, tagged: Tagged) -> bool {
        if tagged.is_int() || tagged == Tagged::null() {
            return false;
        }

        let obj_ptr = tagged.to_ptr();
        let map_ptr = unsafe { (*obj_ptr).header.get_map() };
        let map_tagged = Tagged::from_ptr(map_ptr as *mut Object);

        map_tagged == self.gc.specials.quotation_map
    }

    pub fn is_word(&self, tagged: Tagged) -> bool {
        if tagged.is_int() || tagged == Tagged::null() {
            return false;
        }

        let obj_ptr = tagged.to_ptr();
        let map_ptr = unsafe { (*obj_ptr).header.get_map() };
        let map_tagged = Tagged::from_ptr(map_ptr as *mut Object);

        map_tagged == self.gc.specials.word_map
    }

    pub fn word_primitive(&self, tagged: Tagged) -> Option<StackFn> {
        if !self.is_word(tagged) {
            return None;
        }

        let word = tagged.to_ptr() as *const Word;

        if unsafe { !(*word).has_tag(self.gc.specials.primitive_tag) } {
            return None;
        }

        let body = unsafe { (*word).body };
        let num = body.to_int();
        let ptr = unsafe { mem::transmute(num) };
        Some(ptr)
    }
}
