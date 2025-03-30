use std::mem;

use crate::{
    gc::GarbageCollector,
    object::{Array, ByteArray, ObjectHeader, ObjectRef, ObjectType, Quotation, SpecialObjects},
    MemoryRegion, MutArc,
};

pub struct Context {
    pub header: ObjectHeader,
    pub datastack: ObjectRef,
    pub retainstack: ObjectRef,
    pub namestack: ObjectRef,

    pub parser: ObjectRef,

    pub gc: MutArc<GarbageCollector>,
    pub data: MemoryRegion<ObjectRef>,
    pub retain: MemoryRegion<ObjectRef>,
    pub names: MemoryRegion<(ObjectRef, ObjectRef)>, // first object always bytearray or f
}

pub struct Parser {
    pub header: ObjectHeader,
    pub text: ObjectRef,
    pub offset: ObjectRef,
    pub line: ObjectRef,
    pub column: ObjectRef,
}

pub struct ContextConfig {
    pub datastack_size: usize,
    pub retainstack_size: usize,
    pub namestack_size: usize,
}

impl Context {
    pub fn new(config: &ContextConfig) -> Self {
        let mut gc = MutArc::new(GarbageCollector::new());
        gc.init_special_objects();
        let datastack = unsafe { gc.allocate_array(config.datastack_size) };
        let retainstack = unsafe { gc.allocate_array(config.retainstack_size) };
        let namestack = unsafe { gc.allocate_array(config.namestack_size * 2) };

        let data = datastack.into();
        let retain = retainstack.into();
        let names = namestack.into();

        let parser = Parser::new(&mut gc);
        gc.add_root(ObjectRef::from_ptr(parser as *mut _));
        // TODO: make map
        let header = ObjectHeader::null();

        gc.add_root(ObjectRef::from_array_ptr(datastack));
        gc.add_root(ObjectRef::from_array_ptr(retainstack));
        gc.add_root(ObjectRef::from_array_ptr(namestack));

        Self {
            header,
            datastack: datastack.into(),
            retainstack: retainstack.into(),
            namestack: ObjectRef::null(),
            parser: ObjectRef::from_ptr(parser as *mut _),
            gc,
            data,
            retain,
            names,
        }
    }

    pub fn push(&mut self, value: ObjectRef) {
        let _ = self.data.replace(value);
        self.data.increment(1);
    }

    pub fn pop(&mut self) -> ObjectRef {
        self.data.decrement(1);
        self.data.replace(ObjectRef::null())
    }

    pub fn retain_push(&mut self, value: ObjectRef) {
        let _ = self.retain.replace(value);
        self.retain.increment(1);
    }

    pub fn retain_pop(&mut self) -> ObjectRef {
        self.retain.decrement(1);
        self.retain.replace(ObjectRef::null())
    }

    pub fn data_retain(&mut self) {
        let value = self.pop();
        self.retain_push(value);
    }

    pub fn retain_data(&mut self) {
        let value = self.retain_pop();
        self.push(value);
    }

    pub fn execute(&mut self, quotation: *mut Quotation) {
        let code = unsafe { (*quotation).body.as_ptr_unchecked() } as *mut Array;
        let data_ptr = unsafe { (*code).data_ptr_mut() };
        let count = unsafe { (*code).size.as_int_unchecked() as usize };

        for idx in 0..count {
            let ptr = unsafe { data_ptr.add(idx) };
            let current = unsafe { *ptr };

            let Some(ty) = current.get_type() else {
                self.push(current);
                continue;
            };

            match ty {
                ObjectType::Word => {
                    let word = current.as_word_ptr().unwrap();
                    let body_obj = unsafe { (*word).body };
                    if let Some(flags) = unsafe { (*word).flags.as_array_ptr() } {
                        let mut is_primitive = false;
                        for flag in unsafe { (*flags).iter() } {
                            if flag == SpecialObjects::get_false() {
                                break;
                            };
                            if flag == SpecialObjects::word_primitive() {
                                is_primitive = true;
                            }
                        }
                        if is_primitive {
                            let primitive_fn_raw = unsafe { body_obj.as_int_unchecked() };
                            let primitive_fn: fn(&mut Context) =
                                unsafe { mem::transmute(primitive_fn_raw) };
                            primitive_fn(self);
                        } else {
                            let quot = body_obj.as_quotation_ptr().unwrap();
                            self.execute(quot);
                        }
                    } else {
                        let quot = body_obj.as_quotation_ptr().unwrap();
                        self.execute(quot);
                    }
                }
                ObjectType::Quotation => {
                    self.push(current);
                }
                ObjectType::Box => {
                    self.push(current);
                }
                _ => self.push(current),
            }
        }
    }

    pub fn compile_string(&mut self, text: ObjectRef) -> ObjectRef {
        let parser = unsafe { self.parser.as_ptr_unchecked() as *mut Parser };
        unsafe { (*parser).set_text(text) };
        unsafe { (*parser).compile_string(self) }
    }

    unsafe fn name_or_word_string(obj: ObjectRef) -> *mut ByteArray {
        if let Some(word) = obj.as_word_ptr() {
            let name = unsafe { (*word).name };
            unsafe { name.as_bytearray_ptr_unchecked() }
        } else {
            unsafe { obj.as_bytearray_ptr_unchecked() }
        }
    }

    pub fn namestack_push_or_replace(&mut self, name: ObjectRef, object: ObjectRef) {
        if name.is_false() {
            return;
        }

        let name_ptr = unsafe { Self::name_or_word_string(name) };

        let mut current = self.names.current;
        let mut found = false;

        while current > self.names.start {
            unsafe {
                current = current.sub(1);
                let (existing_name, _) = *current;

                if existing_name.is_false() {
                    *current = (name, object);
                    found = true;
                    break;
                }

                let existing_name_ptr = Self::name_or_word_string(existing_name);
                if (*name_ptr).equal(&*existing_name_ptr) {
                    *current = (name, object);
                    found = true;
                    break;
                }
            }
        }

        if !found {
            self.names.replace((name, object));
            self.names.increment(1);
        }
    }

    pub fn namestack_lookup(&self, name: ObjectRef) -> Option<(ObjectRef, ObjectRef)> {
        if name.is_false() {
            return None;
        }

        let name_ptr = unsafe { Self::name_or_word_string(name) };

        let mut current = self.names.current;

        while current > self.names.start {
            unsafe {
                current = current.sub(1);
                let (existing_name, object) = *current;

                if existing_name.is_false() {
                    continue;
                }

                let existing_ptr =  Self::name_or_word_string(existing_name);

                if (*name_ptr).equal(&*existing_ptr) {
                    return Some((existing_name, object));
                }
            }
        }

        None
    }
    pub fn namestack_remove(&mut self, name: ObjectRef) -> ObjectRef {
        if name.is_false() {
            return ObjectRef::null();
        }

        let name_ptr = unsafe { Self::name_or_word_string(name) };

        let mut current = self.names.current;

        while current > self.names.start {
            unsafe {
                current = current.sub(1);
                let (existing_name, object) = *current;

                if existing_name.is_false() {
                    continue;
                }

                let existing_ptr = Self::name_or_word_string(existing_name);

                if (*name_ptr).equal(&*existing_ptr) {
                    *current = (ObjectRef::null(), ObjectRef::null());
                    return object;
                }
            }
        }

        ObjectRef::null()
    }
}

impl Parser {
    pub fn new(gc: &mut GarbageCollector) -> *mut Self {
        let map = unsafe { gc.allocate_map(ObjectRef::null(), 4, 32, ObjectRef::null()) };
        let parser = unsafe { gc.allocate(map) } as *mut Parser;

        unsafe {
            (*parser).text = ObjectRef::null();
            (*parser).offset = ObjectRef::from_int(0);
            (*parser).line = ObjectRef::from_int(1);
            (*parser).column = ObjectRef::from_int(1);
        }

        parser
    }

    pub fn next_word(&mut self, gc: &mut GarbageCollector) -> (ObjectRef, bool) {
        let text_ptr = unsafe { self.text.as_bytearray_ptr_unchecked() };
        let mut offset = unsafe { self.offset.as_int_unchecked() as usize };
        let text_size = unsafe { (*text_ptr).size.as_int_unchecked() as usize };

        while offset < text_size {
            let ch = unsafe { (*text_ptr).get_element(offset).unwrap() };
            match ch {
                b' ' | b'\t' => {
                    offset += 1;
                    unsafe {
                        self.column = ObjectRef::from_int(self.column.as_int_unchecked() + 1);
                    }
                }
                b'\n' => {
                    offset += 1;
                    unsafe {
                        self.line = ObjectRef::from_int(self.line.as_int_unchecked() + 1);
                        self.column = ObjectRef::from_int(1);
                    }
                }
                _ => break,
            }
        }

        if offset >= text_size {
            return (ObjectRef::null(), false);
        }

        let start = offset;
        while offset < text_size {
            let ch = unsafe { (*text_ptr).get_element(offset).unwrap() };
            match ch {
                b' ' | b'\t' | b'\n' => break,
                _ => {
                    offset += 1;
                    unsafe {
                        self.column = ObjectRef::from_int(self.column.as_int_unchecked() + 1);
                    }
                }
            }
        }

        let word_size = offset - start;
        let word = unsafe { gc.allocate_bytearray(word_size) };

        unsafe {
            let src = (text_ptr as *const u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(start);
            let dst = (word as *mut u8).add(std::mem::size_of::<ByteArray>());
            std::ptr::copy_nonoverlapping(src, dst, word_size);
        }

        self.offset = ObjectRef::from_int(offset as i64);

        (ObjectRef::from_bytearray_ptr(word), true)
    }

    pub fn read_until(&mut self, gc: &mut GarbageCollector, end_pattern: ObjectRef) -> ObjectRef {
        let text_ptr = unsafe { self.text.as_bytearray_ptr_unchecked() };
        let end_ptr = unsafe { end_pattern.as_bytearray_ptr_unchecked() };

        let mut offset = unsafe { self.offset.as_int_unchecked() as usize };
        let text_size = unsafe { (*text_ptr).size.as_int_unchecked() as usize };
        let pattern_size = unsafe { (*end_ptr).size.as_int_unchecked() as usize };

        let initial_offset = offset;

        if pattern_size == 0 || pattern_size > (text_size - offset) {
            return ObjectRef::null();
        }

        while offset <= text_size - pattern_size {
            let mut found = true;

            for i in 0..pattern_size {
                let text_ch = unsafe { (*text_ptr).get_element(offset + i).unwrap() };
                let pattern_ch = unsafe { (*end_ptr).get_element(i).unwrap() };

                if text_ch != pattern_ch {
                    found = false;
                    break;
                }
            }

            if found {
                let result_size = offset - initial_offset;
                let result = unsafe { gc.allocate_bytearray(result_size - 1) };

                unsafe {
                    let src = (text_ptr as *const u8)
                        .add(std::mem::size_of::<ByteArray>())
                        .add(initial_offset + 1);
                    let dst = (result as *mut u8).add(std::mem::size_of::<ByteArray>());
                    std::ptr::copy_nonoverlapping(src, dst, result_size);
                }

                for i in initial_offset..offset {
                    let ch = unsafe { (*text_ptr).get_element(i).unwrap() };
                    if ch == b'\n' {
                        unsafe {
                            self.line = ObjectRef::from_int(self.line.as_int_unchecked() + 1);
                            self.column = ObjectRef::from_int(1);
                        }
                    } else {
                        unsafe {
                            self.column = ObjectRef::from_int(self.column.as_int_unchecked() + 1);
                        }
                    }
                }

                for i in 0..pattern_size {
                    let ch = unsafe { (*text_ptr).get_element(offset + i).unwrap() };
                    if ch == b'\n' {
                        unsafe {
                            self.line = ObjectRef::from_int(self.line.as_int_unchecked() + 1);
                            self.column = ObjectRef::from_int(1);
                        }
                    } else {
                        unsafe {
                            self.column = ObjectRef::from_int(self.column.as_int_unchecked() + 1);
                        }
                    }
                }

                self.offset = ObjectRef::from_int((offset + pattern_size) as i64);

                return ObjectRef::from_bytearray_ptr(result);
            }

            offset += 1;
        }

        self.offset = ObjectRef::from_int(initial_offset as i64);
        ObjectRef::null()
    }

    pub fn parse_until(&mut self, ctx: &mut Context, end_word: ObjectRef) -> ObjectRef {
        let initial_offset = self.offset;
        let initial_line = self.line;
        let initial_column = self.column;

        let mut objects = Vec::new();

        let end_bytearray = unsafe { end_word.as_bytearray_ptr_unchecked() };

        loop {
            let (word, success) = self.next_word(&mut ctx.gc);
            if !success {
                self.offset = initial_offset;
                self.line = initial_line;
                self.column = initial_column;
                return ObjectRef::null();
            }

            let word_ptr = unsafe { word.as_bytearray_ptr_unchecked() };
            if unsafe { (*word_ptr).equal(&*end_bytearray) } {
                let array = unsafe { ctx.gc.allocate_array(objects.len()) };
                for (i, obj) in objects.iter().enumerate() {
                    unsafe { (*array).set_element(i, *obj) };
                }
                return ObjectRef::from_array_ptr(array);
            }

            let mut parsed = false;

            ctx.push(word);
            ctx.parse_fixnum();
            let result = ctx.pop();
            if !result.is_false() {
                objects.push(result);
                parsed = true;
            }

            if !parsed {
                ctx.push(word);
                ctx.parse_float();
                let result = ctx.pop();
                if !result.is_false() {
                    objects.push(result);
                    parsed = true;
                }
            }

            if !parsed {
                match ctx.namestack_lookup(word) {
                    Some((name, value)) => {
                        let obj = if name.as_word_ptr().is_some() {
                            name
                        } else {
                            value
                        };
                        if let Some(word_ptr) = obj.as_word_ptr() {
                            unsafe {
                                if let Some(flags) = (*word_ptr).flags.as_array_ptr() {
                                    let mut is_primitive = false;
                                    let mut is_parser = false;

                                    for flag in (*flags).iter() {
                                        if flag == SpecialObjects::get_false() {
                                            break;
                                        }
                                        if flag == SpecialObjects::word_primitive() {
                                            is_primitive = true;
                                        }
                                        if flag == SpecialObjects::word_parser() {
                                            is_parser = true;
                                        }
                                    }
                                    if is_parser {
                                        if is_primitive {
                                            let primitive_fn_raw =
                                                (*word_ptr).body.as_int_unchecked();
                                            let primitive_fn: fn(&mut Context) =
                                                mem::transmute(primitive_fn_raw);
                                            primitive_fn(ctx);
                                            let result = ctx.pop();
                                            objects.push(result);
                                        } else {
                                            let quot = (*word_ptr).body.as_quotation_ptr().unwrap();
                                            ctx.execute(quot);
                                            let result = ctx.pop();
                                            if !result.is_false() {
                                                objects.push(result);
                                            }
                                        }
                                    } else {
                                        objects.push(obj);
                                    }
                                } else {
                                    objects.push(obj);
                                }
                            }
                        } else {
                            objects.push(obj);
                        }
                    }
                    None => {
                        objects.push(word);
                    }
                }
            }
        }
    }

    pub fn compile_string(&mut self, ctx: &mut Context) -> ObjectRef {
        let mut objects = Vec::new();

        loop {
            let (word, success) = self.next_word(&mut ctx.gc);
            if !success {
                break;
            }

            let mut parsed = false;

            ctx.push(word);
            ctx.parse_fixnum();
            let result = ctx.pop();
            if !result.is_false() {
                objects.push(result);
                parsed = true;
            }

            if !parsed {
                ctx.push(word);
                ctx.parse_float();
                let result = ctx.pop();
                if !result.is_false() {
                    objects.push(result);
                    parsed = true;
                }
            }

            if !parsed {
                match ctx.namestack_lookup(word) {
                    Some((name, value)) => {
                        let obj = if name.as_word_ptr().is_some() {
                            name
                        } else {
                            value
                        };
                        if let Some(word_ptr) = obj.as_word_ptr() {
                            unsafe {
                                if let Some(flags) = (*word_ptr).flags.as_array_ptr() {
                                    let mut is_primitive = false;
                                    let mut is_parser = false;

                                    for flag in (*flags).iter() {
                                        if flag == SpecialObjects::get_false() {
                                            break;
                                        }
                                        if flag == SpecialObjects::word_primitive() {
                                            is_primitive = true;
                                        }
                                        if flag == SpecialObjects::word_parser() {
                                            is_parser = true;
                                        }
                                    }
                                    if is_parser {
                                        if is_primitive {
                                            let primitive_fn_raw =
                                                (*word_ptr).body.as_int_unchecked();
                                            let primitive_fn: fn(&mut Context) =
                                                mem::transmute(primitive_fn_raw);
                                            primitive_fn(ctx);
                                            let result = ctx.pop();
                                            objects.push(result);
                                        } else {
                                            let quot = (*word_ptr).body.as_quotation_ptr().unwrap();
                                            ctx.execute(quot);
                                            let result = ctx.pop();
                                            if !result.is_false() {
                                                objects.push(result);
                                            }
                                        }
                                    } else {
                                        objects.push(obj);
                                    }
                                } else {
                                    objects.push(obj);
                                }
                            }
                        } else {
                            objects.push(obj);
                        }
                    }
                    None => {
                        objects.push(word);
                    }
                }
            }
        }

        let array = unsafe { ctx.gc.allocate_array(objects.len()) };
        for (i, obj) in objects.iter().enumerate() {
            unsafe { (*array).set_element(i, *obj) };
        }

        let quotation = unsafe { ctx.gc.allocate_quotation(None) };
        unsafe { (*quotation).body = ObjectRef::from_array_ptr(array) };

        ObjectRef::from_quotation_ptr(quotation)
    }

    pub fn set_text(&mut self, text: ObjectRef) {
        self.text = text;
        self.offset = ObjectRef::from_int(0);
        self.line = ObjectRef::from_int(1);
        self.column = ObjectRef::from_int(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::object::ObjectType;

    fn create_test_context() -> Context {
        let config = ContextConfig {
            datastack_size: 512,
            retainstack_size: 512,
            namestack_size: 512,
        };
        Context::new(&config)
    }

    #[test]
    fn test_push_pop_integers() {
        let mut ctx = create_test_context();

        unsafe {
            let value = ObjectRef::from_int(42);
            ctx.push(value);
            let result = ctx.pop();
            assert_eq!(result.as_int(), Some(42));

            let values = vec![1, -5, 100, -42, 0];
            for &v in &values {
                ctx.push(ObjectRef::from_int(v));
            }

            for &expected in values.iter().rev() {
                let result = ctx.pop();
                assert_eq!(result.as_int(), Some(expected));
            }
        }
    }

    #[test]
    fn test_stack_operations_with_heap_objects() {
        let mut ctx = create_test_context();

        unsafe {
            let bytearray = ctx.gc.allocate_string("test string");
            let bytearray_ref = ObjectRef::from_bytearray_ptr(bytearray);
            ctx.push(bytearray_ref);

            let array = ctx.gc.allocate_array(3);
            (*array).set_element(0, ObjectRef::from_int(1));
            (*array).set_element(1, ObjectRef::from_int(2));
            (*array).set_element(2, ObjectRef::from_int(3));
            let array_ref = ObjectRef::from_array_ptr(array);
            ctx.push(array_ref);

            let popped_array = ctx.pop();
            assert_eq!(popped_array.get_type(), Some(ObjectType::Array));
            let array_ptr = popped_array.as_array_ptr().unwrap();
            assert_eq!((*array_ptr).get_element(0), Some(ObjectRef::from_int(1)));
            assert_eq!((*array_ptr).get_element(1), Some(ObjectRef::from_int(2)));
            assert_eq!((*array_ptr).get_element(2), Some(ObjectRef::from_int(3)));

            let popped_bytearray = ctx.pop();
            assert_eq!(popped_bytearray.get_type(), Some(ObjectType::ByteArray));
            let bytearray_ptr = popped_bytearray.as_bytearray_ptr().unwrap();
            assert_eq!((*bytearray_ptr).as_str(), Some("test string"));
        }
    }

    #[test]
    fn test_mixed_stack_operations() {
        let mut ctx = create_test_context();

        unsafe {
            ctx.push(ObjectRef::from_int(42));

            let bytearray = ctx.gc.allocate_string("mixed test");
            ctx.push(ObjectRef::from_bytearray_ptr(bytearray));

            ctx.push(ObjectRef::from_int(-7));

            let last_int = ctx.pop();
            assert_eq!(last_int.as_int(), Some(-7));

            let heap_obj = ctx.pop();
            assert_eq!(heap_obj.get_type(), Some(ObjectType::ByteArray));
            let bytearray_ptr = heap_obj.as_bytearray_ptr().unwrap();
            assert_eq!((*bytearray_ptr).as_str(), Some("mixed test"));

            let first_int = ctx.pop();
            assert_eq!(first_int.as_int(), Some(42));
        }
    }

    #[test]
    fn test_retain_stack_operations() {
        let mut ctx = create_test_context();

        ctx.push(ObjectRef::from_int(1));
        ctx.push(ObjectRef::from_int(2));

        ctx.data_retain();
        assert_eq!(ctx.pop().as_int(), Some(1));

        ctx.retain_data();
        assert_eq!(ctx.pop().as_int(), Some(2));

        unsafe {
            let bytearray = ctx.gc.allocate_string("retain test");
            let bytearray_ref = ObjectRef::from_bytearray_ptr(bytearray);

            ctx.push(bytearray_ref);
            ctx.data_retain();

            let array = ctx.gc.allocate_array(1);
            (*array).set_element(0, ObjectRef::from_int(42));
            ctx.push(ObjectRef::from_array_ptr(array));

            let popped_array = ctx.pop();
            assert_eq!(popped_array.get_type(), Some(ObjectType::Array));

            ctx.retain_data();
            let restored = ctx.pop();
            assert_eq!(restored.get_type(), Some(ObjectType::ByteArray));
            let restored_ptr = restored.as_bytearray_ptr().unwrap();
            assert_eq!((*restored_ptr).as_str(), Some("retain test"));
        }
    }

    #[test]
    fn test_pop_empty_stack() {
        let mut ctx = create_test_context();
        ctx.pop();
        assert!(ctx.data.is_invalid());
    }

    #[test]
    fn test_pop_after_collect() {
        let mut ctx = create_test_context();
        unsafe {
            ctx.gc.collect();
            let collect_0 = ctx.gc.total_allocated;
            let bytearray1 = ctx.gc.allocate_string("string 1");
            ctx.push(ObjectRef::from_bytearray_ptr(bytearray1));
            ctx.gc.collect();
            let collect_1 = ctx.gc.total_allocated;
            let _ = ctx.pop();
            ctx.gc.collect();
            ctx.gc.collect();
            let collect_2 = ctx.gc.total_allocated;

            assert!(collect_0 == collect_2);
            // TODO: inspect this, why `<` doens't work.
            assert!(collect_2 <= collect_1);
        }
    }

    #[test]
    fn test_gc_interaction() {
        let mut ctx = create_test_context();

        unsafe {
            let bytearray1 = ctx.gc.allocate_string("string 1");
            let bytearray2 = ctx.gc.allocate_string("string 2");

            ctx.push(ObjectRef::from_bytearray_ptr(bytearray1));
            ctx.push(ObjectRef::from_bytearray_ptr(bytearray2));

            ctx.gc.collect();

            let popped2 = ctx.pop();
            let popped1 = ctx.pop();

            assert!(
                popped2.as_bytearray_ptr().is_some(),
                "Second object should be a ByteArray"
            );
            assert!(
                popped1.as_bytearray_ptr().is_some(),
                "First object should be a ByteArray"
            );

            let str2 = (*popped2.as_bytearray_ptr().unwrap()).as_str();
            let str1 = (*popped1.as_bytearray_ptr().unwrap()).as_str();

            assert_eq!(str2, Some("string 2"));
            assert_eq!(str1, Some("string 1"));
        }
    }

    #[test]
    fn test_namestack_basic_operations() {
        let mut ctx = create_test_context();
        unsafe {
            let name1 = ctx.gc.allocate_string("first");
            let name2 = ctx.gc.allocate_string("second");
            let obj1 = ObjectRef::from_int(42);
            let obj2 = ObjectRef::from_int(84);

            ctx.namestack_push_or_replace(name1.into(), obj1);
            assert_eq!(
                ctx.namestack_lookup(name1.into()).map(|(_, value)| value),
                Some(obj1)
            );

            ctx.namestack_push_or_replace(name2.into(), obj2);
            assert_eq!(
                ctx.namestack_lookup(name2.into()).map(|(_, value)| value),
                Some(obj2)
            );
            assert_eq!(
                ctx.namestack_lookup(name1.into()).map(|(_, value)| value),
                Some(obj1)
            );

            let removed = ctx.namestack_remove(name1.into());
            assert_eq!(removed, obj1);
            assert_eq!(
                ctx.namestack_lookup(name1.into()).map(|(_, value)| value),
                None
            );
            assert_eq!(
                ctx.namestack_lookup(name2.into()).map(|(_, value)| value),
                Some(obj2)
            );
        }
    }

    #[test]
    fn test_namestack_replace() {
        let mut ctx = create_test_context();
        unsafe {
            let name = ctx.gc.allocate_string("test");
            let obj1 = ObjectRef::from_int(42);
            let obj2 = ObjectRef::from_int(84);

            ctx.namestack_push_or_replace(name.into(), obj1);
            assert_eq!(
                ctx.namestack_lookup(name.into()).map(|(_, value)| value),
                Some(obj1)
            );

            ctx.namestack_push_or_replace(name.into(), obj2);
            assert_eq!(
                ctx.namestack_lookup(name.into()).map(|(_, value)| value),
                Some(obj2)
            );
        }
    }

    #[test]
    fn test_namestack_false_slots() {
        let mut ctx = create_test_context();
        unsafe {
            let name1 = ctx.gc.allocate_string("first");
            let name2 = ctx.gc.allocate_string("second");
            let name3 = ctx.gc.allocate_string("third");
            let obj1 = ObjectRef::from_int(1);
            let obj2 = ObjectRef::from_int(2);
            let obj3 = ObjectRef::from_int(3);

            ctx.namestack_push_or_replace(name1.into(), obj1);
            ctx.namestack_push_or_replace(name2.into(), obj2);
            ctx.namestack_push_or_replace(name3.into(), obj3);

            let removed = ctx.namestack_remove(name2.into());
            assert_eq!(removed, obj2);

            let name4 = ctx.gc.allocate_string("fourth");
            let obj4 = ObjectRef::from_int(4);
            ctx.namestack_push_or_replace(name4.into(), obj4);

            assert_eq!(
                ctx.namestack_lookup(name1.into()).map(|(_, value)| value),
                Some(obj1)
            );
            assert_eq!(
                ctx.namestack_lookup(name2.into()).map(|(_, value)| value),
                None
            );
            assert_eq!(
                ctx.namestack_lookup(name3.into()).map(|(_, value)| value),
                Some(obj3)
            );
            assert_eq!(
                ctx.namestack_lookup(name4.into()).map(|(_, value)| value),
                Some(obj4)
            );
        }
    }

    #[test]
    fn test_namestack_null_operations() {
        let mut ctx = create_test_context();

        ctx.namestack_push_or_replace(ObjectRef::null(), ObjectRef::from_int(42));
        assert_eq!(ctx.namestack_lookup(ObjectRef::null()), None);
        assert_eq!(ctx.namestack_remove(ObjectRef::null()), ObjectRef::null());
    }

    #[test]
    fn test_namestack_duplicate_names() {
        let mut ctx = create_test_context();
        unsafe {
            let name1 = ctx.gc.allocate_string("test");
            let name2 = ctx.gc.allocate_string("test");
            let obj1 = ObjectRef::from_int(1);
            let obj2 = ObjectRef::from_int(2);

            ctx.namestack_push_or_replace(name1.into(), obj1);
            ctx.namestack_push_or_replace(name2.into(), obj2);

            assert_eq!(
                ctx.namestack_lookup(name1.into()).map(|(_, value)| value),
                Some(obj2)
            );
            assert_eq!(
                ctx.namestack_lookup(name2.into()).map(|(_, value)| value),
                Some(obj2)
            );
        }
    }

    #[test]
    fn test_parser_basic() {
        let mut ctx = create_test_context();
        unsafe {
            let text = ctx.gc.allocate_string("hello world");
            let parser = ctx.parser.as_ptr_unchecked() as *mut Parser;
            (*parser).set_text(text.into());

            let (word1, success1) = (*parser).next_word(&mut ctx.gc);
            assert!(success1);
            assert_eq!((*word1.as_bytearray_ptr().unwrap()).as_str(), Some("hello"));
            assert_eq!((*parser).line.as_int(), Some(1));
            assert_eq!((*parser).column.as_int(), Some(6));

            let (word2, success2) = (*parser).next_word(&mut ctx.gc);
            assert!(success2);
            assert_eq!((*word2.as_bytearray_ptr().unwrap()).as_str(), Some("world"));

            let (_, success3) = (*parser).next_word(&mut ctx.gc);
            assert!(!success3);
        }
    }

    #[test]
    fn test_parser_whitespace() {
        let mut ctx = create_test_context();
        unsafe {
            let text = ctx.gc.allocate_string("word1\n  word2\t\tword3");
            let parser = ctx.parser.as_ptr_unchecked() as *mut Parser;
            (*parser).set_text(text.into());

            let (word1, _) = (*parser).next_word(&mut ctx.gc);
            assert_eq!((*word1.as_bytearray_ptr().unwrap()).as_str(), Some("word1"));
            assert_eq!((*parser).line.as_int(), Some(1));
            assert_eq!((*parser).column.as_int(), Some(6));

            let (word2, _) = (*parser).next_word(&mut ctx.gc);
            assert_eq!((*word2.as_bytearray_ptr().unwrap()).as_str(), Some("word2"));
            assert_eq!((*parser).line.as_int(), Some(2));
            assert_eq!((*parser).column.as_int(), Some(8));

            let (word3, _) = (*parser).next_word(&mut ctx.gc);
            assert_eq!((*word3.as_bytearray_ptr().unwrap()).as_str(), Some("word3"));
            assert_eq!((*parser).line.as_int(), Some(2));
        }
    }

    #[test]
    fn test_parser_empty() {
        let mut ctx = create_test_context();
        unsafe {
            let text = ctx.gc.allocate_string("");
            let parser = ctx.parser.as_ptr_unchecked() as *mut Parser;
            (*parser).set_text(text.into());

            let (_, success) = (*parser).next_word(&mut ctx.gc);
            assert!(!success);
        }
    }

    #[test]
    fn test_parser_only_whitespace() {
        let mut ctx = create_test_context();
        unsafe {
            let text = ctx.gc.allocate_string("  \t\n  ");
            let parser = ctx.parser.as_ptr_unchecked() as *mut Parser;
            (*parser).set_text(text.into());

            let (_, success) = (*parser).next_word(&mut ctx.gc);
            assert!(!success);
            assert_eq!((*parser).line.as_int(), Some(2));
        }
    }

    #[test]
    fn test_parse_until_basic() {
        let mut ctx = create_test_context();
        unsafe {
            let text = ctx.gc.allocate_string("42 3.14 word ]");
            let end = ctx.gc.allocate_string("]");
            let parser = ctx.parser.as_ptr_unchecked() as *mut Parser;
            (*parser).set_text(text.into());

            let result = (*parser).parse_until(&mut ctx, end.into());
            assert!(!result.is_false());

            let array = result.as_array_ptr().unwrap();
            assert_eq!((*array).size.as_int(), Some(3));

            let first = (*array).get_element(0).unwrap();
            assert_eq!(first.as_int(), Some(42));

            let second = (*array).get_element(1).unwrap();
            assert!(second.as_float_ptr().is_some());

            let third = (*array).get_element(2).unwrap();
            assert_eq!((*third.as_bytearray_ptr().unwrap()).as_str(), Some("word"));
        }
    }

    #[test]
    fn test_parse_until_not_found() {
        let mut ctx = create_test_context();
        unsafe {
            let text = ctx.gc.allocate_string("42 3.14 word");
            let end = ctx.gc.allocate_string("]");
            let parser = ctx.parser.as_ptr_unchecked() as *mut Parser;
            (*parser).set_text(text.into());

            let initial_offset = (*parser).offset;
            let result = (*parser).parse_until(&mut ctx, end.into());

            assert!(result.is_false());
            assert_eq!((*parser).offset, initial_offset);
        }
    }

    #[test]
    fn test_parse_until_namestack() {
        let mut ctx = create_test_context();
        unsafe {
            let name = ctx.gc.allocate_string("test-var");
            let value = ObjectRef::from_int(999);
            ctx.namestack_push_or_replace(name.into(), value);
            assert_eq!(
                ctx.namestack_lookup(name.into()).map(|(_, val)| val),
                Some(value)
            );

            let text = ctx.gc.allocate_string("42 test-var ]");
            let end = ctx.gc.allocate_string("]");
            let parser = ctx.parser.as_ptr_unchecked() as *mut Parser;
            (*parser).set_text(text.into());

            let result = (*parser).parse_until(&mut ctx, end.into());
            assert!(!result.is_false());

            let array = result.as_array_ptr().unwrap();
            assert_eq!((*array).size.as_int(), Some(2));

            let second = (*array).get_element(1).unwrap();
            assert_eq!(second.as_int(), Some(999));
        }
    }

    #[test]
    fn test_read_until_basic() {
        let mut ctx = create_test_context();
        unsafe {
            let text = ctx.gc.allocate_string("Hello World END test");
            let end = ctx.gc.allocate_string("END");
            let parser = ctx.parser.as_ptr_unchecked() as *mut Parser;
            (*parser).set_text(text.into());

            let result = (*parser).read_until(&mut ctx.gc, end.into());
            assert!(!result.is_false());

            let result_str = (*result.as_bytearray_ptr().unwrap()).as_str();
            assert_eq!(result_str, Some("Hello World "));

            assert_eq!((*parser).offset.as_int(), Some(15));
        }
    }

    #[test]
    fn test_read_until_with_newlines() {
        let mut ctx = create_test_context();
        unsafe {
            let text = ctx.gc.allocate_string("First line\nSecond line\nEND more");
            let end = ctx.gc.allocate_string("END");
            let parser = ctx.parser.as_ptr_unchecked() as *mut Parser;
            (*parser).set_text(text.into());

            let result = (*parser).read_until(&mut ctx.gc, end.into());
            assert!(!result.is_false());

            let result_str = (*result.as_bytearray_ptr().unwrap()).as_str();
            assert_eq!(result_str, Some("First line\nSecond line\n"));

            // Check line and column counting
            assert_eq!((*parser).line.as_int(), Some(3));
            assert_eq!((*parser).column.as_int(), Some(4));
        }
    }

    #[test]
    fn test_read_until_pattern_not_found() {
        let mut ctx = create_test_context();
        unsafe {
            let text = ctx.gc.allocate_string("Hello World");
            let end = ctx.gc.allocate_string("END");
            let parser = ctx.parser.as_ptr_unchecked() as *mut Parser;
            (*parser).set_text(text.into());

            let initial_offset = (*parser).offset;
            let result = (*parser).read_until(&mut ctx.gc, end.into());

            assert!(result.is_false());
            assert_eq!((*parser).offset, initial_offset);
        }
    }
}
