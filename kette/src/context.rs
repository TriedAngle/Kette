use crate::{
    Array, ByteArray, CodeHeap, GarbageCollector, Handler, Map, MemoryRegion,
    Mutex, Object, ObjectHeader, Parser, Quotation, SLOT_CONST_DATA, StackFn,
    Tagged, Word,
};
use std::{
    collections::{HashMap, HashSet},
    mem,
    sync::Arc,
};

pub struct Context {
    pub header: ObjectHeader,
    pub datastack: Tagged,
    pub retainstack: Tagged,
    pub namestack: Tagged,
    pub callstack: Tagged,
    pub handlerstack: Tagged,

    pub gc: GarbageCollector,
    pub codes: Arc<Mutex<CodeHeap>>,

    pub data: MemoryRegion<Tagged>,
    pub retain: MemoryRegion<Tagged>,
    pub call: MemoryRegion<Tagged>,
    pub name: MemoryRegion<(Tagged, Tagged)>,
    pub handlers: MemoryRegion<Tagged>,
    pub supertypes: HashMap<*mut Map, HashSet<*mut Map>>,
}

pub struct ContextConfig {
    pub data_size: usize,
    pub retian_size: usize,
    pub name_size: usize,
    pub call_size: usize,
    pub handler_size: usize,
}

impl Context {
    pub fn new(config: &ContextConfig, codes: Arc<Mutex<CodeHeap>>) -> Self {
        let mut gc = GarbageCollector::new();
        let datastack = gc.allocate_array(config.data_size);
        let retainstack = gc.allocate_array(config.retian_size);
        let namestack = gc.allocate_array(config.name_size);
        let callstack = gc.allocate_array(config.call_size);
        let handlerstack = gc.allocate_array(config.handler_size);

        let data = (datastack.to_ptr() as *mut Array).into();
        let retain = (retainstack.to_ptr() as *mut Array).into();
        let name = (namestack.to_ptr() as *mut Array).into();
        let call = (callstack.to_ptr() as *mut Array).into();
        let handlers = (handlerstack.to_ptr() as *mut Array).into();

        gc.add_root(datastack);
        gc.add_root(retainstack);
        gc.add_root(namestack);
        gc.add_root(callstack);

        let ctx_map = gc.create_map(
            "Context",
            &[
                (
                    "datastack",
                    SLOT_CONST_DATA,
                    Tagged::from_int(0),
                    Tagged::ffalse(),
                ),
                (
                    "retainstack",
                    SLOT_CONST_DATA,
                    Tagged::from_int(1),
                    Tagged::ffalse(),
                ),
                (
                    "namestack",
                    SLOT_CONST_DATA,
                    Tagged::from_int(2),
                    Tagged::ffalse(),
                ),
                (
                    "callstack",
                    SLOT_CONST_DATA,
                    Tagged::from_int(3),
                    Tagged::ffalse(),
                ),
                (
                    "handlerstack",
                    SLOT_CONST_DATA,
                    Tagged::from_int(4),
                    Tagged::ffalse(),
                ),
            ],
        );

        let header = ObjectHeader::new(ctx_map.to_ptr() as *mut _);
        gc.add_root(ctx_map);
        let supertypes = HashMap::new();

        let mut new = Self {
            header,
            datastack,
            retainstack,
            namestack,
            callstack,
            handlerstack,
            data,
            retain,
            name,
            call,
            handlers,
            codes,
            gc,
            supertypes,
        };

        new.register_map_inheritance(new.gc.specials.object_map.to_ptr() as _);
        new.register_map_inheritance(new.gc.specials.false_map.to_ptr() as _);
        new.register_map_inheritance(new.gc.specials.map_map.to_ptr() as _);
        new.register_map_inheritance(new.gc.specials.fixnum_map.to_ptr() as _);
        new.register_map_inheritance(new.gc.specials.array_map.to_ptr() as _);
        new.register_map_inheritance(
            new.gc.specials.bytearray_map.to_ptr() as _
        );
        new.register_map_inheritance(new.gc.specials.slot_map.to_ptr() as _);
        new.register_map_inheritance(
            new.gc.specials.quotation_map.to_ptr() as _
        );
        new.register_map_inheritance(new.gc.specials.word_map.to_ptr() as _);
        new.register_map_inheritance(new.gc.specials.handler_map.to_ptr() as _);

        new
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

    pub fn push_handler(&mut self, handler: Tagged) {
        self.handlers.replace(handler);
        self.handlers.increment(1);
    }

    pub fn pop_handler(&mut self) -> Tagged {
        if self.handlers.current <= self.handlers.start {
            return Tagged::ffalse();
        }

        self.handlers.decrement(1);
        self.handlers.replace(Tagged::null())
    }

    pub fn get_current_frame(&mut self) -> Tagged {
        if self.call.current <= self.call.start {
            return Tagged::ffalse();
        }

        let frame = unsafe { *self.call.current.sub(1) };
        return frame;
    }

    pub fn unwind_to_frame(&mut self, frame: Tagged) {
        let mut current_ptr = self.call.current;

        while current_ptr >= self.call.start {
            let frame_obj = unsafe { *current_ptr };
            if frame_obj == frame {
                self.call.current = unsafe { current_ptr.add(1) };
                return;
            }

            unsafe { current_ptr = current_ptr.sub(1) };
        }

        panic!("Fatal VM State: unwinding target not found")
    }

    pub fn throw(&mut self, exception: Tagged) {
        let handler_count = (self.handlers.current as usize
            - self.handlers.start as usize)
            / std::mem::size_of::<Tagged>();

        if handler_count == 0 {
            panic!("Fatal VM State: No handlers installed");
        }

        for i in (0..handler_count).rev() {
            let handler = unsafe { *(self.handlers.start.add(i)) };
            let handler_ptr = handler.to_ptr() as *mut Handler;

            let tty = unsafe { (*handler_ptr).tty };
            let handler_quot = unsafe { (*handler_ptr).handler };
            let handler_frame = unsafe { (*handler_ptr).frame };

            // TODO: support inheritance
            if self.is_instance_of(exception, tty) {
                self.push(handler_frame);
                self.execute(handler_quot.to_ptr() as *const Quotation);
                return;
            }
        }

        panic!("Fatal VM State: No matching handler found");
    }

    pub fn create_map(
        &mut self,
        name: &str,
        slots: &[(&str, i64, Tagged, Tagged)],
    ) -> Tagged {
        let map_tagged = self.gc.create_map(name, slots);

        self.register_map_inheritance(map_tagged.to_ptr() as *mut Map);

        map_tagged
    }

    fn register_map_inheritance(&mut self, map_ptr: *mut Map) {
        if self.supertypes.contains_key(&map_ptr) {
            return;
        }

        let mut parents = HashSet::new();
        parents.insert(map_ptr);

        let parent_slots = unsafe { (*map_ptr).get_parent_slots() };

        for parent_slot in parent_slots {
            let parent_tagged = unsafe { (*parent_slot).value };
            if !parent_tagged.is_false() {
                let parent_map_ptr = parent_tagged.to_ptr() as *mut Map;

                self.register_map_inheritance(parent_map_ptr);

                parents.insert(parent_map_ptr);

                if let Some(parent_set) = self.supertypes.get(&parent_map_ptr) {
                    for &ancestor in parent_set {
                        parents.insert(ancestor);
                    }
                }
            }
        }

        self.supertypes.insert(map_ptr, parents);
    }

    pub fn is_instance_of(&self, obj: Tagged, map: Tagged) -> bool {
        if obj.is_int() || obj.is_false() {
            if obj.is_false() && map == self.gc.specials.false_map {
                return true;
            }
            return false;
        }

        let obj_ptr = obj.to_ptr();
        let obj_map_ptr = unsafe { (*obj_ptr).header.get_map() };

        self.is_subtype_of(obj_map_ptr, map.to_ptr() as _)
    }

    pub fn is_subtype_of(&self, map: *mut Map, parent: *mut Map) -> bool {
        if let Some(parents) = self.supertypes.get(&map) {
            parents.contains(&parent)
        } else {
            panic!("Fatal VM State: Map '{:?}' not registered", map);
        }
    }

    pub fn lookup(&self, tagged: Tagged) -> (Tagged, Tagged) {
        let Some((search_name, _)) = self.get_name_bytearray(tagged) else {
            return (Tagged::ffalse(), Tagged::ffalse());
        };

        let mut current_ptr = self.name.current;

        while current_ptr >= self.name.start {
            let entry = unsafe { *(current_ptr as *const (Tagged, Tagged)) };
            let (key, value) = entry;

            if key == Tagged::ffalse() && value == Tagged::ffalse() {
                unsafe { current_ptr = current_ptr.sub(1) };
                continue;
            }

            let Some((key_name, _)) = self.get_name_bytearray(key) else {
                unsafe { current_ptr = current_ptr.sub(1) };
                continue;
            };

            let search_name_ptr = search_name.to_ptr() as *const ByteArray;
            let key_name_ptr = key_name.to_ptr() as *const ByteArray;

            let search_str = unsafe { (*search_name_ptr).as_str() };
            let key_str = unsafe { (*key_name_ptr).as_str() };

            if search_str == key_str {
                return (key, value);
            }

            unsafe { current_ptr = current_ptr.sub(1) };
        }

        (Tagged::ffalse(), Tagged::ffalse())
    }

    pub fn reset_parser_string(&mut self, input: &str) {
        let input = self.gc.allocate_string(input);
        self.reset_parser(input);
    }
    pub fn reset_parser(&mut self, input: Tagged) {
        let parser = self.gc.specials.parser.to_ptr() as *mut Parser;
        unsafe {
            (*parser).reset(input);
        };
    }

    pub fn read_next(&mut self) -> Tagged {
        let parser = self.gc.specials.parser.to_ptr() as *mut Parser;
        unsafe { (*parser).read_next(self) }
    }

    pub fn parse_until(&mut self, delimiter: Option<&str>) -> Tagged {
        let parser = self.gc.specials.parser.to_ptr() as *mut Parser;
        unsafe { (*parser).parse_until(self, delimiter) }
    }

    pub fn read_until(&mut self, end: &str) -> Tagged {
        let parser = self.gc.specials.parser.to_ptr() as *mut Parser;
        unsafe { (*parser).read_until(self, end) }
    }

    pub fn namestack_push(
        &mut self,
        key: Tagged,
        value: Tagged,
    ) -> (Tagged, Tagged) {
        let Some(_) = self.get_name_bytearray(key) else {
            return (Tagged::ffalse(), Tagged::ffalse());
        };

        let (existing_key, _existing_value) = self.lookup(key);
        if existing_key != Tagged::ffalse() {
            let mut current_ptr = self.name.current;

            while current_ptr >= self.name.start {
                let entry_ptr = current_ptr as *mut (Tagged, Tagged);
                let (entry_key, _) = unsafe { *entry_ptr };

                if entry_key == existing_key {
                    let old_value = unsafe { (*entry_ptr).1 };
                    unsafe { (*entry_ptr).1 = value };
                    return (existing_key, old_value);
                }

                unsafe { current_ptr = current_ptr.sub(1) };
            }
        }

        let mut current_ptr = self.name.start;

        while current_ptr <= self.name.current {
            let entry_ptr = current_ptr as *mut (Tagged, Tagged);
            let (entry_key, _) = unsafe { *entry_ptr };

            if entry_key == Tagged::ffalse() {
                unsafe {
                    *entry_ptr = (key, value);
                }
                return (key, value);
            }

            unsafe { current_ptr = current_ptr.add(1) };
        }

        if self.name.current == self.name.end {
            panic!("Namestack is full");
        }

        self.name.increment(1);

        let entry_ptr = self.name.current as *mut (Tagged, Tagged);
        unsafe {
            *entry_ptr = (key, value);
        }

        (key, value)
    }

    pub fn namestack_remove(&mut self, key: Tagged) -> (Tagged, Tagged) {
        let (existing_key, _existing_value) = self.lookup(key);
        if existing_key == Tagged::ffalse() {
            return (Tagged::ffalse(), Tagged::ffalse());
        }

        let mut current_ptr = self.name.current;

        while current_ptr >= self.name.start {
            let entry_ptr = current_ptr as *mut (Tagged, Tagged);
            let (entry_key, _) = unsafe { *entry_ptr };

            if entry_key == existing_key {
                let old_entry = unsafe { *entry_ptr };

                unsafe {
                    *entry_ptr = (Tagged::ffalse(), Tagged::ffalse());
                }

                return old_entry;
            }

            unsafe { current_ptr = current_ptr.sub(1) };
        }

        (Tagged::ffalse(), Tagged::ffalse())
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

    pub fn is_parsing_word(&self, word: Tagged) -> bool {
        if !self.is_word(word) {
            return false;
        }

        let word_ptr = word.to_ptr() as *const Word;
        unsafe { (*word_ptr).has_tag(self.gc.specials.parser_tag) }
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

    fn get_name_bytearray(&self, tagged: Tagged) -> Option<(Tagged, bool)> {
        if tagged.is_int() || tagged == Tagged::null() {
            return None;
        }

        let obj_ptr = tagged.to_ptr();
        let map_ptr = unsafe { (*obj_ptr).header.get_map() };
        let map_tagged = Tagged::from_ptr(map_ptr as *mut Object);

        if map_tagged == self.gc.specials.word_map {
            let word_ptr = obj_ptr as *const Word;
            let name = unsafe { (*word_ptr).name };
            Some((name, true))
        } else if map_tagged == self.gc.specials.bytearray_map {
            Some((tagged, false))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use parking_lot::Mutex;

    use crate::{CodeHeap, Context, ContextConfig, Map, SLOT_PARENT, Tagged};

    fn setup_context() -> Context {
        let code_heap = Arc::new(Mutex::new(CodeHeap::new()));
        let config = ContextConfig {
            data_size: 100,
            retian_size: 100,
            name_size: 100,
            call_size: 100,
            handler_size: 100,
        };
        Context::new(&config, code_heap)
    }

    #[test]
    fn test_namestack_basic_operations() {
        let mut ctx = setup_context();

        let key1 = ctx.gc.allocate_string("key1");
        let value1 = Tagged::from_int(42);

        let key2 = ctx.gc.allocate_string("key2");
        let value2 = Tagged::from_int(100);

        let result = ctx.lookup(key1);
        assert_eq!(result, (Tagged::ffalse(), Tagged::ffalse()));

        let push_result = ctx.namestack_push(key1, value1);
        assert_eq!(push_result, (key1, value1));

        let result = ctx.lookup(key1);
        assert_eq!(result, (key1, value1));

        let result = ctx.lookup(key2);
        assert_eq!(result, (Tagged::ffalse(), Tagged::ffalse()));

        let push_result = ctx.namestack_push(key2, value2);
        assert_eq!(push_result, (key2, value2));

        let result1 = ctx.lookup(key1);
        assert_eq!(result1, (key1, value1));

        let result2 = ctx.lookup(key2);
        assert_eq!(result2, (key2, value2));
    }

    #[test]
    fn test_namestack_update_value() {
        let mut ctx = setup_context();

        let key = ctx.gc.allocate_string("test_key");
        let value1 = Tagged::from_int(42);
        let value2 = Tagged::from_int(100);

        let push_result = ctx.namestack_push(key, value1);
        assert_eq!(push_result, (key, value1));

        let result = ctx.lookup(key);
        assert_eq!(result, (key, value1));

        let update_result = ctx.namestack_push(key, value2);
        assert_eq!(update_result, (key, value1));

        let result = ctx.lookup(key);
        assert_eq!(result, (key, value2));
    }

    #[test]
    fn test_namestack_remove() {
        let mut ctx = setup_context();

        let key1 = ctx.gc.allocate_string("key1");
        let value1 = Tagged::from_int(42);

        let key2 = ctx.gc.allocate_string("key2");
        let value2 = Tagged::from_int(100);

        ctx.namestack_push(key1, value1);
        ctx.namestack_push(key2, value2);

        assert_eq!(ctx.lookup(key1), (key1, value1));
        assert_eq!(ctx.lookup(key2), (key2, value2));

        let remove_result = ctx.namestack_remove(key1);
        assert_eq!(remove_result, (key1, value1));

        assert_eq!(ctx.lookup(key1), (Tagged::ffalse(), Tagged::ffalse()));
        assert_eq!(ctx.lookup(key2), (key2, value2));

        let remove_result = ctx.namestack_remove(key1);
        assert_eq!(remove_result, (Tagged::ffalse(), Tagged::ffalse()));

        let remove_result = ctx.namestack_remove(key2);
        assert_eq!(remove_result, (key2, value2));

        assert_eq!(ctx.lookup(key1), (Tagged::ffalse(), Tagged::ffalse()));
        assert_eq!(ctx.lookup(key2), (Tagged::ffalse(), Tagged::ffalse()));
    }

    #[test]
    fn test_namestack_reuse_slots() {
        let mut ctx = setup_context();

        let key1 = ctx.gc.allocate_string("key1");
        let value1 = Tagged::from_int(42);

        let key2 = ctx.gc.allocate_string("key2");
        let value2 = Tagged::from_int(100);

        let key3 = ctx.gc.allocate_string("key3");
        let value3 = Tagged::from_int(200);

        let push_result1 = ctx.namestack_push(key1, value1);
        assert_eq!(push_result1, (key1, value1));

        let push_result2 = ctx.namestack_push(key2, value2);
        assert_eq!(push_result2, (key2, value2));

        ctx.namestack_remove(key1);

        let push_result3 = ctx.namestack_push(key3, value3);
        assert_eq!(push_result3, (key3, value3));

        assert_eq!(ctx.lookup(key1), (Tagged::ffalse(), Tagged::ffalse()));
        assert_eq!(ctx.lookup(key2), (key2, value2));
        assert_eq!(ctx.lookup(key3), (key3, value3));

        let entry_ptr = ctx.name.start as *const (Tagged, Tagged);
        let (stored_key, stored_value) = unsafe { *entry_ptr };

        if stored_key != Tagged::ffalse() {
            let key3_name_ptr = unsafe {
                (stored_key.to_ptr() as *const crate::ByteArray)
                    .as_ref()
                    .unwrap()
            };
            let stored_name = unsafe { key3_name_ptr.as_str() };
            assert_eq!(stored_name, "key3");
            assert_eq!(stored_value, value3);
        }
    }

    #[test]
    fn test_namestack_with_words() {
        let mut ctx = setup_context();

        let name = ctx.gc.allocate_string("test_word");

        let word = ctx.gc.allocate_object(ctx.gc.specials.word_map);
        unsafe {
            let word_ptr = word.to_ptr();
            (*word_ptr).set_slot(0, name);
            (*word_ptr).set_slot(1, Tagged::null());
            (*word_ptr).set_slot(2, Tagged::null());
            (*word_ptr).set_slot(3, Tagged::null());
        }

        let value = Tagged::from_int(42);

        let push_result = ctx.namestack_push(word, value);
        assert_eq!(push_result, (word, value));

        let result = ctx.lookup(word);
        assert_eq!(result, (word, value));

        let result = ctx.lookup(name);
        assert_eq!(result.1, value);

        assert!(result.0 == word || result.0 == name);

        let remove_result = ctx.namestack_remove(word);
        assert_eq!(remove_result.1, value);

        assert_eq!(ctx.lookup(word), (Tagged::ffalse(), Tagged::ffalse()));
        assert_eq!(ctx.lookup(name), (Tagged::ffalse(), Tagged::ffalse()));
    }

    #[test]
    fn test_namestack_shadowing() {
        let mut ctx = setup_context();

        let key = ctx.gc.allocate_string("shadowed_key");
        let value1 = Tagged::from_int(42);
        let value2 = Tagged::from_int(100);

        let push_result1 = ctx.namestack_push(key, value1);
        assert_eq!(push_result1, (key, value1));

        let push_result2 = ctx.namestack_push(key, value2);
        assert_eq!(push_result2, (key, value1));

        let result = ctx.lookup(key);
        assert_eq!(result, (key, value2));

        ctx.namestack_remove(key);

        assert_eq!(ctx.lookup(key), (Tagged::ffalse(), Tagged::ffalse()));
    }

    #[test]
    #[should_panic(expected = "Namestack is full")]
    fn test_namestack_overflow() {
        let config = ContextConfig {
            data_size: 10,
            retian_size: 10,
            name_size: 2,
            call_size: 0,
            handler_size: 0,
        };
        let code_heap = Arc::new(Mutex::new(CodeHeap::new()));
        let mut ctx = Context::new(&config, code_heap);

        let key1 = ctx.gc.allocate_string("key1");
        let key2 = ctx.gc.allocate_string("key2");
        let key3 = ctx.gc.allocate_string("key3");
        let value = Tagged::from_int(42);

        ctx.namestack_push(key1, value);
        ctx.namestack_push(key2, value);

        ctx.namestack_push(key3, value);
    }

    #[test]
    fn test_invalid_keys() {
        let mut ctx = setup_context();

        let int_key = Tagged::from_int(42);
        let null_key = Tagged::null();
        let value = Tagged::from_int(100);

        assert_eq!(ctx.lookup(int_key), (Tagged::ffalse(), Tagged::ffalse()));
        assert_eq!(ctx.lookup(null_key), (Tagged::ffalse(), Tagged::ffalse()));

        assert_eq!(
            ctx.namestack_push(int_key, value),
            (Tagged::ffalse(), Tagged::ffalse())
        );
        assert_eq!(
            ctx.namestack_push(null_key, value),
            (Tagged::ffalse(), Tagged::ffalse())
        );

        assert_eq!(
            ctx.namestack_remove(int_key),
            (Tagged::ffalse(), Tagged::ffalse())
        );
        assert_eq!(
            ctx.namestack_remove(null_key),
            (Tagged::ffalse(), Tagged::ffalse())
        );
    }

    #[test]
    fn test_map_inheritance() {
        let mut ctx = setup_context();

        let parent_map = ctx.create_map("Parent", &[]);
        let child_map = ctx.create_map(
            "Child",
            &[("Parent", SLOT_PARENT, parent_map, Tagged::ffalse())],
        );
        let grandchild_map = ctx.create_map(
            "Grandchild",
            &[("Parent", SLOT_PARENT, child_map, Tagged::ffalse())],
        );

        let parent_obj = ctx.gc.allocate_object(parent_map);
        let child_obj = ctx.gc.allocate_object(child_map);
        let grandchild_obj = ctx.gc.allocate_object(grandchild_map);

        assert!(ctx.is_instance_of(parent_obj, parent_map));
        assert!(!ctx.is_instance_of(parent_obj, child_map));

        assert!(ctx.is_instance_of(child_obj, child_map));
        assert!(ctx.is_instance_of(child_obj, parent_map));
        assert!(!ctx.is_instance_of(child_obj, grandchild_map));

        assert!(ctx.is_instance_of(grandchild_obj, grandchild_map));
        assert!(ctx.is_instance_of(grandchild_obj, child_map));
        assert!(ctx.is_instance_of(grandchild_obj, parent_map));

        assert!(ctx.is_subtype_of(
            parent_map.to_ptr() as *mut Map,
            parent_map.to_ptr() as *mut Map
        ));
        assert!(!ctx.is_subtype_of(
            parent_map.to_ptr() as *mut Map,
            child_map.to_ptr() as *mut Map
        ));

        assert!(ctx.is_subtype_of(
            child_map.to_ptr() as *mut Map,
            child_map.to_ptr() as *mut Map
        ));
        assert!(ctx.is_subtype_of(
            child_map.to_ptr() as *mut Map,
            parent_map.to_ptr() as *mut Map
        ));
        assert!(!ctx.is_subtype_of(
            child_map.to_ptr() as *mut Map,
            grandchild_map.to_ptr() as *mut Map
        ));

        assert!(ctx.is_subtype_of(
            grandchild_map.to_ptr() as *mut Map,
            grandchild_map.to_ptr() as *mut Map
        ));
        assert!(ctx.is_subtype_of(
            grandchild_map.to_ptr() as *mut Map,
            child_map.to_ptr() as *mut Map
        ));
        assert!(ctx.is_subtype_of(
            grandchild_map.to_ptr() as *mut Map,
            parent_map.to_ptr() as *mut Map
        ));
    }

    #[test]
    #[should_panic]
    fn test_unregistered_map() {
        let mut ctx = setup_context();

        let unregistered_map = ctx.gc.create_map("Unregistered", &[]);
        let registered_map = ctx.create_map("Registered", &[]);

        assert!(
            !ctx.supertypes
                .contains_key(&(unregistered_map.to_ptr() as *mut Map))
        );
        assert!(
            ctx.supertypes
                .contains_key(&(registered_map.to_ptr() as *mut Map))
        );

        assert!(!ctx.is_subtype_of(
            unregistered_map.to_ptr() as *mut Map,
            registered_map.to_ptr() as *mut Map
        ));

        ctx.register_map_inheritance(unregistered_map.to_ptr() as *mut Map);

        assert!(
            ctx.supertypes
                .contains_key(&(unregistered_map.to_ptr() as *mut Map))
        );
        assert!(ctx.is_subtype_of(
            unregistered_map.to_ptr() as *mut Map,
            unregistered_map.to_ptr() as *mut Map
        ));
    }
}
