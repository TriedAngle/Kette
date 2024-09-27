#![allow(unused)]
use std::collections::HashMap;
use std::fs;
use std::mem;
use std::ptr;

use context::Context;
use context::Segment;
use object::ArrayObject;
use object::ByteArrayObject;
use object::Map;
use object::ObjectHeader;
use object::QuotationObject;
use object::WordObject;
use object::{Object, ObjectRef};

pub mod context;
pub mod gc;
pub mod object;
pub mod primitives;
pub mod system;

pub struct VM {
    pub gc: gc::MarkAndSweep,
    pub active_context: *mut Context,

    pub maps: HashMap<String, *mut Map>,
    pub words: HashMap<String, *mut WordObject>,
    pub special_objects: object::SpecialObjects,

    pub retainstack: Vec<ObjectRef>,
    pub callstack: Vec<ObjectRef>,
}

impl VM {
    pub fn new() -> Self {
        Self {
            gc: gc::MarkAndSweep::new(),
            active_context: ptr::null_mut(),
            retainstack: Vec::new(),
            callstack: Vec::new(),
            special_objects: Default::default(),
            maps: HashMap::new(),
            words: HashMap::new(),
        }
    }

    pub unsafe fn ctx(&mut self) -> &mut Context {
        &mut *self.active_context
    }

    pub fn push(&mut self, obj: ObjectRef) {
        // self.stack.push(obj);
        unsafe {
            self.ctx().push(obj);
        }
    }

    pub fn pop(&mut self) -> ObjectRef {
        unsafe {
            self.ctx().pop()
        }
        // self.stack.pop().unwrap()
    }

    pub fn peek(&mut self) -> ObjectRef {
        unsafe {
            self.ctx().peek()
        }
        // *self.stack.last().unwrap()
    }

    pub fn retain_push(&mut self, obj: ObjectRef) {
        self.retainstack.push(obj)
    }

    pub fn retain_pop(&mut self) -> ObjectRef {
        self.retainstack.pop().unwrap()
    }

    pub fn pop_retain_push(&mut self) {
        let x = self.pop();
        self.retain_push(x);
    }

    pub fn retain_pop_push(&mut self) {
        let x = self.retain_pop();
        self.push(x);
    }

    pub fn call_push(&mut self, obj: ObjectRef) {
        self.callstack.push(obj)
    }

    pub fn call_pop(&mut self) -> ObjectRef {
        self.callstack.pop().unwrap()
    }

    pub unsafe fn execute_primitive(&mut self, word: *const WordObject) {
        let fun: fn(vm: *mut VM) = unsafe {
            assert_eq!((*word).primitive, 1);
            mem::transmute((*word).body.0)
        };

        let vm = self as *mut VM;
        fun(vm);
    }

    pub unsafe fn execute_quotation(&mut self, quotation: *const QuotationObject) {
        for obj in (*quotation).body() {
            let map = obj.get_map();

            if map == self.special_objects.word_map {
                self.execute_word(obj.as_word());
                continue;
            }

            let copy = self.clone_object(*obj);

            self.push(copy)
        }
    }

    pub unsafe fn execute_word(&mut self, word: *const WordObject) {
        if (*word).primitive == 1 {
            self.execute_primitive(word);
            return;
        }
        let body = (*word).quotation();
        self.execute_quotation(body);
    }

    // ( end -- array )
    pub unsafe fn parse_until(&mut self) {
        let mut vec = Vec::<ObjectRef>::new();
        let end_obj = self.pop().as_box();
        let end_word = (*end_obj).boxed;
        loop {
            self.read_word();
            self.dup();
            if self.is_false() {
                self.drop();
                break; // TODO HANDLE ERROR
            }
            self.dup();
            self.try_parse_number();
            self.dup();
            if self.is_true() {
                let num = self.pop();
                self.drop();
                vec.push(num);
                continue;
            }
            self.drop();
            let word_name_before = self.peek();
            self.lookup_word();
            self.dup();
            if self.is_false() {
                println!(
                    "ERROR: word not found: {:?}",
                    word_name_before.bytearray_as_str()
                );
                self.drop();
                continue;
                // TODO handle error better
            }
            self.dup();
            if self.is_syntax_word() {
                let word = self.pop().as_word();
                self.execute_word(word);
                let accum = self.pop();
                if accum.object_mut() != self.special_objects.true_object {
                    vec.push(accum);
                }
                continue;
            }
            let word = self.pop();
            if word == end_word {
                break;
            }
            vec.push(word);
        }
        let arr = self.allocate_array_from_slice(&vec);
        self.push(arr);
    }

    pub unsafe fn compile_source_file(&mut self, p: &str) -> ObjectRef {
        let source = fs::read_to_string(p).unwrap();
        self.compile_string(&source)
    }

    // returns a quotation
    pub unsafe fn compile_string(&mut self, s: &str) -> ObjectRef {
        self.bind_input(s);
        let mut vec = Vec::<ObjectRef>::new();

        loop {
            self.read_word();
            self.dup();
            if self.is_false() {
                self.drop();
                break;
            }
            self.dup();
            self.try_parse_number();
            self.dup();
            if self.is_true() {
                let num = self.pop();
                self.drop();
                vec.push(num);
                continue;
            }
            self.drop();
            self.lookup_word();
            self.dup();
            if self.is_false() {
                // TODO HANDLE ERROR
            }
            self.dup();
            if self.is_syntax_word() {
                let word = self.pop().as_word();
                self.execute_word(word);
                let accum = self.pop();
                if accum.object_mut() != self.special_objects.true_object {
                    vec.push(accum);
                }
                continue;
            }
            let word = self.pop();

            vec.push(word);
        }

        let arr = self.allocate_array_from_slice(&vec);
        self.push(arr);
        primitives::primitive_array_to_quotation(self as *mut Self);
        self.pop()
    }

    // ( name -- word/f )
    pub unsafe fn lookup_word(&mut self) {
        let word_name = self.pop();
        let word = self.words.get(word_name.bytearray_as_str());
        if let Some(word) = word {
            self.push(ObjectRef::from_word(*word))
        } else {
            self.push_false();
        }
    }

    // ( word -- ? )
    pub unsafe fn is_primitive_word(&mut self) -> bool {
        let word = self.pop().as_word();
        (*word).primitive == 1
    }

    // ( word -- ? )
    pub unsafe fn is_syntax_word(&mut self) -> bool {
        let word = self.pop().as_word();
        (*word).syntax == 1
    }

    pub fn init(&mut self) {
        self.gc.link_vm(self as *const VM);
        self.init_primitive_maps();
        let context = self.allocate_context(3000, 3000, 3000);
        self.active_context = context.0 as *mut Context;
        self.add_primitives();
    }

    pub fn deinit(&mut self) {
        unsafe {
            self.gc.deallocate_all();
        }
    }

    pub fn bind_input(&mut self, input: &str) {
        self.gc
            .unset_object_root(ObjectRef(self.special_objects.input as *mut Object));
        self.gc
            .unset_object_root(ObjectRef(self.special_objects.input_offset as *mut Object));

        let input_object = self.allocate_string(input);
        self.gc.set_object_root(input_object);
        self.special_objects.input = input_object.as_byte_array_mut();

        let input_offset_object = self.allocate_fixnum(0);
        self.gc.set_object_root(input_offset_object);
        self.special_objects.input_offset = input_offset_object.as_fixnum_mut();
    }

    pub fn push_input_stream(&mut self) {
        self.push(ObjectRef(self.special_objects.input as *mut Object));
    }

    pub fn push_input_stream_offset(&mut self) {
        self.push(ObjectRef(self.special_objects.input_offset as *mut Object));
    }

    pub fn read_word(&mut self) {
        let ino = self.special_objects.input;
        let inoffseto = self.special_objects.input_offset;
        let inoobj = ObjectRef(ino as *mut Object);

        let input = unsafe { inoobj.bytearray_as_str() };
        let mut offset = unsafe { (*inoffseto).value } as usize;

        while offset < input.len() && input.as_bytes()[offset].is_ascii_whitespace() {
            offset += 1;
        }

        if offset >= input.len() {
            self.push_false();
            unsafe {
                (*inoffseto).value = offset as isize;
            }
            return;
        }

        let start = offset;

        while offset < input.len() && !input.as_bytes()[offset].is_ascii_whitespace() {
            offset += 1;
        }

        unsafe {
            (*inoffseto).value = offset as isize;
        }

        let word = &input[start..offset];
        let word_obj = self.allocate_string(word);
        self.push(word_obj);
    }

    pub fn dup(&mut self) {
        let obj = self.peek();
        self.push(obj);
    }

    pub fn try_parse_number(&mut self) {
        let obj = self.pop();
        let string = unsafe { obj.bytearray_as_str() };
        if let Ok(num) = str::parse::<usize>(string) {
            let num_obj = self.allocate_fixnum(num as isize);
            self.push(num_obj);
        } else {
            self.push_false();
        }
    }

    pub fn drop(&mut self) {
        let _ = self.pop();
    }

    pub fn dropd(&mut self) {
        let obj = self.pop();
        let _ = self.pop();
        self.push(obj);
    }

    pub fn is_true(&mut self) -> bool {
        let obj = self.pop();
        obj.0 != self.special_objects.false_object
    }

    pub fn is_false(&mut self) -> bool {
        let obj = self.pop();
        obj.0 == self.special_objects.false_object
    }

    pub fn push_true(&mut self) {
        self.push(ObjectRef(self.special_objects.true_object));
    }

    pub fn push_false(&mut self) {
        self.push(ObjectRef(self.special_objects.false_object));
    }

    pub fn push_fixnum(&mut self, fixnum: isize) {
        let obj = self.allocate_fixnum(fixnum);
        self.push(obj);
    }

    pub fn pause_gc(&mut self) {
        self.gc.pause()
    }
    pub fn unpause_gc(&mut self) {
        self.gc.unpause()
    }
    pub fn run_gc(&mut self) {
        self.gc.mark_sweep();
    }

    pub fn object_count(&self) -> usize {
        self.gc.allocation_count()
    }

    pub fn print_all_objects(&self) {
        self.gc.print_all_objects();
    }
}

pub struct SlotDescriptor<'a> {
    pub name: &'a str,
    pub kind: usize,
    pub value_type: ObjectRef, // null for untyped
    pub index: usize,
    pub read_only: usize, // 0/null/f => false
}

impl<'a> Default for SlotDescriptor<'a> {
    fn default() -> Self {
        Self {
            name: "",
            kind: object::SLOT_DATA,
            value_type: ObjectRef::null(),
            index: 0,
            read_only: 0,
        }
    }
}

impl VM {
    pub fn allocate_object(&mut self, map: ObjectRef) -> ObjectRef {
        let map = map.as_map_mut();
        let required_size = unsafe { Object::required_size(&*map) };
        let obj = self.gc.allocate(required_size, 8, false).unwrap();
        unsafe {
            let object = obj.object_mut();
            (*object).set_map(map);
        }
        obj
    }

    pub fn allocate_fixnum(&mut self, value: isize) -> ObjectRef {
        let map = self.special_objects.fixnum_map;
        let object = self.allocate_object(ObjectRef::from_map(map));
        let num = object.as_fixnum_mut();
        unsafe {
            (*num).value = value;
        }
        object
    }

    pub fn allocate_fixfloat(&mut self, value: f64) -> ObjectRef {
        let map = self.special_objects.fixfloat_map;
        let object = self.allocate_object(ObjectRef::from_map(map));
        let num = object.as_fixfloat_mut();
        unsafe {
            (*num).value = value;
        }
        object
    }

    pub fn allocate_string<'a>(&mut self, s: &'a str) -> ObjectRef {
        let obj = self.allocate_bytearray(s.len());
        unsafe {
            let ba = obj.as_byte_array_mut();
            ptr::copy(s.as_ptr(), obj.bytearray_data(), s.len());
        }
        obj
    }

    pub fn allocate_bytearray<'a>(&mut self, size: usize) -> ObjectRef {
        let ba_size = mem::size_of::<ByteArrayObject>();
        let obj = self.gc.allocate(ba_size + size, 8, false).unwrap();
        let ba = obj.as_byte_array_mut();
        unsafe {
            (*ba).header = ObjectHeader {
                meta: 0,
                map: ObjectRef::from_map(self.special_objects.bytearray_map),
            };
            (*ba).capacity = size;
            ptr::write_bytes(obj.bytearray_data(), 0, size);
        }

        obj
    }

    pub fn allocate_array_from_slice(&mut self, slice: &[ObjectRef]) -> ObjectRef {
        let obj = self.allocate_array(slice.len());
        unsafe {
            for idx in 0..obj.array_data_len() {
                *(obj.array_data().add(idx)) = slice[idx];
            }
        }
        obj
    }

    pub fn allocate_array(&mut self, size: usize) -> ObjectRef {
        let required_size = mem::size_of::<ArrayObject>() + size * mem::size_of::<ObjectRef>();
        let obj = self.gc.allocate(required_size, 8, false).unwrap();
        let arr = obj.as_array_mut();
        unsafe {
            (*arr).header = ObjectHeader {
                meta: 0,
                map: ObjectRef::from_map(self.special_objects.array_map),
            };
            (*arr).size = size;
            ptr::write_bytes(obj.array_data(), 0, size);
        }
        obj
    }

    pub fn allocate_context(&mut self, data_size: usize, retain_size: usize, call_size: usize) -> ObjectRef {
        let alloc_size = mem::size_of::<Context>();
        let alloc_align = mem::align_of::<Context>();
        unsafe {
            let obj = self.gc.allocate(alloc_size, alloc_align, true).unwrap();
            let ctx = obj.0 as *mut Context;
            
            let data_array = self.allocate_array(data_size);
            let retain_array = self.allocate_array(retain_size);
            let call_array = self.allocate_array(call_size);

            // TODO: don't do this
            self.gc.set_object_root(data_array);
            self.gc.set_object_root(retain_array);
            self.gc.set_object_root(call_array);

            (*ctx).vm = self as *mut _;
            (*ctx).gc = &mut self.gc as *mut _;
            (*ctx).so = &mut self.special_objects as *mut _;

            (*ctx).header.map = ObjectRef::from_map(self.special_objects.context_map);
            (*ctx).data = Segment::from_array(data_array);
            (*ctx).retain = Segment::from_array(retain_array);
            (*ctx).call = Segment::from_array(call_array);

            (*ctx).data_array = data_array;
            (*ctx).retain_array = retain_array;
            (*ctx).call_array = call_array;

            (*ctx).reset();
            // (*ctx_ptr).
            obj
        }
    }

    pub fn allocate_map<'a>(&mut self, name: &str, slots: &[SlotDescriptor<'a>]) -> ObjectRef {
        let array = self.allocate_array(slots.len());

        let map_name = self.allocate_string(name);

        let slot_name_objects = slots
            .into_iter()
            .map(|d: &SlotDescriptor<'a>| {
                let obj = self.allocate_string(&d.name);
                obj
            })
            .collect::<Vec<_>>();

        let mut object_size = 2;
        for slot in slots {
            if slot.kind == object::SLOT_DATA || slot.kind == object::SLOT_EMBEDDED_DATA {
                object_size += 1;
            }
        }

        let map_obj = self.gc.allocate(mem::size_of::<Map>(), 8, true).unwrap();

        unsafe {
            let map = map_obj.as_map_mut();

            (*map).header.map = if self.special_objects.map_map.is_null() {
                ObjectRef::null()
            } else {
                ObjectRef::from_map(self.special_objects.map_map)
            };
            (*map).name = map_name;
            (*map).object_size = object_size;
            (*map).slot_count = slots.len();
            (*map).slots = array;

            for (index, (desc, slot_name)) in slots.iter().zip(slot_name_objects).enumerate() {
                let slot_obj = self
                    .gc
                    .allocate(mem::size_of::<object::SlotObject>(), 8, false)
                    .unwrap();

                array.set_array_at(index, slot_obj);

                let slot = slot_obj.as_slot_mut();
                (*slot).name = slot_name;
                (*slot).kind = desc.kind;
                (*slot).read_only = desc.read_only;
                (*slot).value_type = desc.value_type;
                (*slot).index = desc.index;
            }
            self.maps.insert(name.to_string(), map);
        }

        map_obj
    }

    pub unsafe fn clone_object(&mut self, obj: ObjectRef) -> ObjectRef {
        let map = obj.get_map_mut();
        if map == self.special_objects.fixnum_map {
            let num = obj.as_fixnum();
            self.allocate_fixnum((*num).value)
        } else if map == self.special_objects.fixfloat_map {
            let num = obj.as_fixfloat();
            self.allocate_fixfloat((*num).value)
        } else if map == self.special_objects.array_map {
            let size = obj.array_data_len();
            let copy = self.allocate_array(size);

            for idx in 0..size {
                *(copy.array_data().add(idx)) = *(obj.array_data().add(idx));
            }

            copy
        } else if map == self.special_objects.bytearray_map {
            let orig = obj.as_byte_array();
            let new = self.allocate_bytearray((*orig).capacity);
            ptr::copy_nonoverlapping(
                obj.bytearray_data(),
                new.bytearray_data(),
                new.bytearray_data_len(),
            );
            new
        } else {
            // TODO check map for custom clone
            obj
        }
    }

    pub fn init_primitive_maps(&mut self) {
        let map_map = self.allocate_map(
            "map",
            &[
                SlotDescriptor {
                    name: "name",
                    kind: object::SLOT_DATA,
                    value_type: ObjectRef::null(),
                    index: 0,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "object-size",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: ObjectRef::null(),
                    index: 1,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "slot-count",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: ObjectRef::null(),
                    index: 2,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "slots",
                    kind: object::SLOT_DATA,
                    value_type: ObjectRef::null(),
                    index: 3,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "default-instance",
                    kind: object::SLOT_DATA,
                    value_type: ObjectRef::null(),
                    index: 4,
                    read_only: 0,
                },
            ],
        );

        unsafe {
            self.special_objects.map_map = map_map.as_map_mut();
            let map = map_map.as_map_mut();
            (*map).header.map = map_map;
        }

        self.special_objects.map_map = map_map.as_map_mut();

        let bytearray_map = self.allocate_map(
            "bytearray",
            &[
                SlotDescriptor {
                    name: "capacity",
                    kind: object::SLOT_DATA,
                    value_type: ObjectRef::null(),
                    ..Default::default()
                },
                SlotDescriptor {
                    name: "data",
                    kind: object::SLOT_VARIABLE_DATA,
                    value_type: ObjectRef::null(),
                    index: 1,
                    read_only: 0,
                },
            ],
        );

        unsafe {
            let map_map = map_map.as_map_mut();
            let name = (*map_map).name.as_byte_array_mut();
            (*name).header.map = bytearray_map;

            let map = bytearray_map.as_map_mut();
            let name = (*map).name.as_byte_array_mut();
            (*name).header.map = bytearray_map;

            self.special_objects.bytearray_map = map;

            for slot_idx in 0..(*map).slot_count {
                let slot = (*map).get_slot_mut(slot_idx);
                let name = slot.name.as_byte_array_mut();
                (*name).header.map = bytearray_map;
            }
        }

        let number_traits = self.allocate_map("number-traits", &[]);

        let fixnum_map = self.allocate_map(
            "fixnum",
            &[
                SlotDescriptor {
                    name: "parent",
                    kind: object::SLOT_PARENT,
                    value_type: number_traits,
                    ..Default::default()
                },
                SlotDescriptor {
                    name: "value",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: ObjectRef::null(),
                    ..Default::default()
                },
            ],
        );

        let fixfloat_map = self.allocate_map(
            "fixfloat",
            &[
                SlotDescriptor {
                    name: "parent",
                    kind: object::SLOT_PARENT,
                    value_type: number_traits,
                    ..Default::default()
                },
                SlotDescriptor {
                    name: "value",
                    kind: object::SLOT_DATA,
                    value_type: ObjectRef::null(),
                    ..Default::default()
                },
            ],
        );

        unsafe {
            self.special_objects.fixnum_map = fixnum_map.as_map_mut();
            self.special_objects.fixfloat_map = fixfloat_map.as_map_mut();

            let map = bytearray_map.as_map_mut();
            (*map).get_slot_mut(1).value_type = fixfloat_map;
        }

        let array_map = self.allocate_map(
            "array",
            &[
                SlotDescriptor {
                    name: "size",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 0,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "data",
                    kind: object::SLOT_VARIABLE_DATA,
                    value_type: ObjectRef::null(),
                    index: 1,
                    read_only: 0,
                },
            ],
        );

        self.special_objects.array_map = array_map.as_map_mut();

        unsafe {
            (*(*self.special_objects.map_map).slots.as_array_mut())
                .header
                .map = array_map;
            (*(*self.special_objects.bytearray_map).slots.as_array_mut())
                .header
                .map = array_map;
            (*(*self.special_objects.fixnum_map).slots.as_array_mut())
                .header
                .map = array_map;
            (*(*self.special_objects.fixfloat_map).slots.as_array_mut())
                .header
                .map = array_map;
            (*(*self.special_objects.array_map).slots.as_array_mut())
                .header
                .map = array_map;

            (*(*number_traits.as_map()).slots.as_array_mut()).header.map = array_map;
        }

        let quotation_map = self.allocate_map(
            "quotation",
            &[
                SlotDescriptor {
                    name: "body",
                    kind: object::SLOT_DATA,
                    value_type: array_map,
                    index: 0,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "effect",
                    kind: object::SLOT_DATA,
                    value_type: ObjectRef::null(),
                    index: 1,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "entry",
                    kind: object::SLOT_DATA,
                    value_type: ObjectRef::null(),
                    index: 2,
                    read_only: 0,
                },
            ],
        );
        self.special_objects.quotation_map = quotation_map.as_map_mut();

        let word_map = self.allocate_map(
            "word",
            &[
                SlotDescriptor {
                    name: "name",
                    kind: object::SLOT_DATA,
                    value_type: bytearray_map,
                    index: 0,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "body",
                    kind: object::SLOT_DATA,
                    value_type: quotation_map,
                    index: 1,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "properties",
                    kind: object::SLOT_DATA,
                    value_type: ObjectRef::null(),
                    index: 2,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "primitive?",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 3,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "syntax?",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 4,
                    read_only: 0,
                },
            ],
        );

        self.special_objects.word_map = word_map.as_map_mut();

        let bool_map = self.allocate_map("bool", &[]);

        let false_object = self.allocate_object(bool_map);
        let true_object = self.allocate_object(bool_map);
        self.gc.set_object_root(false_object);
        self.gc.set_object_root(true_object);
        self.special_objects.false_object = false_object.0;
        self.special_objects.true_object = true_object.0;

        let box_map = self.allocate_map(
            "box",
            &[SlotDescriptor {
                name: "boxed",
                kind: object::SLOT_DATA,
                value_type: ObjectRef::null(),
                index: 0,
                read_only: 1,
            }],
        );
        self.special_objects.box_map = box_map.as_map_mut();

        let slot_map = self.allocate_map(
            "map-slot",
            &[
                SlotDescriptor {
                    name: "name",
                    kind: object::SLOT_DATA,
                    value_type: bytearray_map,
                    index: 0,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "kind",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: quotation_map,
                    index: 1,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "type",
                    kind: object::SLOT_DATA,
                    value_type: ObjectRef::null(),
                    index: 2,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "index",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 3,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "read-only?",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 4,
                    read_only: 0,
                },
            ],
        );

        self.special_objects.slot_map = slot_map.as_map_mut();

        let context_map = self.allocate_map(
            "context",
            &[
                SlotDescriptor {
                    name: "virtual-machine",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 0,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "garbage-collector",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 1,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "special-objects",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 2,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "data-top",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 3,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "retain-top",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 4,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "call-top",
                    kind: object::SLOT_EMBEDDED_DATA,
                    value_type: fixnum_map,
                    index: 5,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "data-stack",
                    kind: object::SLOT_DATA,
                    value_type: array_map,
                    index: 6,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "retain-stack",
                    kind: object::SLOT_DATA,
                    value_type: array_map,
                    index: 7,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "call-stack",
                    kind: object::SLOT_DATA,
                    value_type: array_map,
                    index: 8,
                    read_only: 0,
                },
            ],
        );
        self.special_objects.context_map = context_map.as_map_mut();

        unsafe {
            for map in self.maps.values() {
                let map = map.as_mut().unwrap();
                for idx in 0..map.slot_count {
                    let slot = map.get_slot_mut(idx);
                    slot.header.map = slot_map;
                }
            }
        }
    }

    pub fn print_array(&self, obj: ObjectRef, size: usize) {
        unsafe {
            print!("{{ ");
            let arr = obj;
            self.print_array_inner(arr, size);
            print!("}}");
            println!();
        }
    }

    pub fn print_quotation(&self, obj: ObjectRef) {
        unsafe {
            print!("[ ");
            let arr = (*obj.as_quotation()).body;
            let len = obj.array_data_len();
            self.print_array_inner(arr, len);
            print!("]");
            println!();
        }
    }

    unsafe fn print_array_inner(&self, arr: ObjectRef, size: usize) {
        for idx in 0..size {
            let o = *(arr.array_data().add(idx));
            let map = o.get_map();
            if map == self.special_objects.fixnum_map {
                print!("{:?}", (*o.as_fixnum()).value);
            } else if map == self.special_objects.word_map {
                print!("{}", (*o.as_word()).name());
            } else if map == self.special_objects.quotation_map {
                print!("[ ");
                let qarr = (*o.as_quotation()).body;
                let size = qarr.array_data_len();
                self.print_array_inner(qarr, size);
                print!("]");
            } else if map == self.special_objects.box_map {
                let inner = (*o.as_box()).boxed;
                let inner_map = inner.get_map();
                print!("\\ ");
                if inner_map == self.special_objects.fixnum_map {
                    print!("{:?}", (*inner.as_fixnum()).value);
                } else if inner_map == self.special_objects.word_map {
                    print!("{}", (*inner.as_word()).name());
                }
            } else if o.0 == self.special_objects.false_object {
                print!("f");
            } else if o.0 == self.special_objects.true_object {
                print!("t");
            } else {
                let map_name = (*map).name();
                print!("T{{{}}}", map_name)
            }
            print!(" ");
        }
    }
}
