use std::collections::HashMap;
use std::mem;
// use std::ptr;

use object::Object;

pub mod gc;
pub mod object;
pub mod primitives;
pub mod system;

pub struct VM {
    pub gc: gc::MarkAndSweep,
    pub stack: Vec<object::ObjectRef>,
    pub retainstack: Vec<object::ObjectRef>,
    pub callstack: Vec<object::ObjectRef>,
    pub maps: HashMap<String, *mut object::Map>,
    pub words: HashMap<String, *mut object::WordObject>,
    pub special_objects: object::SpecialObjects,
}

impl VM {
    pub fn new() -> Self {
        Self {
            gc: gc::MarkAndSweep::new(),
            stack: Vec::new(),
            retainstack: Vec::new(),
            callstack: Vec::new(),
            maps: HashMap::new(),
            words: HashMap::new(),
            special_objects: Default::default(),
        }
    }

    pub fn push(&mut self, obj: object::ObjectRef) {
        self.stack.push(obj)
    }

    pub fn pop(&mut self) -> object::ObjectRef {
        self.stack.pop().unwrap()
    }

    pub fn peek(&mut self) -> object::ObjectRef {
        *self.stack.last().unwrap()
    }

    pub fn retain_push(&mut self, obj: object::ObjectRef) {
        self.retainstack.push(obj)
    }

    pub fn retain_pop(&mut self) -> object::ObjectRef {
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

    pub fn call_push(&mut self, obj: object::ObjectRef) {
        self.callstack.push(obj)
    }

    pub fn call_pop(&mut self) -> object::ObjectRef {
        self.callstack.pop().unwrap()
    }

    pub unsafe fn execute_primitive(&mut self, word: *const object::WordObject) {
        let fun: fn(vm: *mut VM) = unsafe {
            assert_eq!((*word).primitive, 1);
            mem::transmute((*word).body.0)
        };

        let vm = self as *mut VM;
        fun(vm);
    }

    pub unsafe fn execute_quotation(&mut self, quotation: *const object::QuotationObject) {
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

    pub unsafe fn execute_word(&mut self, word: *const object::WordObject) {
        if (*word).primitive == 1 {
            self.execute_primitive(word);
            return;
        }
        let body = (*word).quotation();
        self.execute_quotation(body);
    }

    // ( end -- array )
    pub unsafe fn parse_until(&mut self) {
        let mut vec = Vec::<object::ObjectRef>::new();
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
                vec.push(accum);
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

    // returns a quotation
    pub unsafe fn compile_string(&mut self, s: &str) -> object::ObjectRef {
        self.bind_input(s);
        let mut vec = Vec::<object::ObjectRef>::new();

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
        let word_name = self.pop().as_byte_array();
        let word = self.words.get((*word_name).as_str().unwrap());
        if let Some(word) = word {
            self.push(object::ObjectRef::from_word(*word))
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
        self.add_primitives();
    }

    pub fn bind_input(&mut self, input: &str) {
        self.gc.unset_object_root(object::ObjectRef(
            self.special_objects.input as *mut object::Object,
        ));
        self.gc.unset_object_root(object::ObjectRef(
            self.special_objects.input_offset as *mut object::Object,
        ));

        let input_object = self.allocate_string(input);
        self.gc.set_object_root(input_object);
        self.special_objects.input = input_object.as_byte_array_mut();

        let input_offset_object = self.allocate_fixnum(0);
        self.gc.set_object_root(input_offset_object);
        self.special_objects.input_offset = input_offset_object.as_fixnum_mut();
    }

    pub fn push_input_stream(&mut self) {
        self.push(object::ObjectRef(self.special_objects.input as *mut Object));
    }

    pub fn push_input_stream_offset(&mut self) {
        self.push(object::ObjectRef(
            self.special_objects.input_offset as *mut Object,
        ));
    }

    pub fn read_word(&mut self) {
        let ino = self.special_objects.input;
        let inoffseto = self.special_objects.input_offset;

        let input = unsafe { (*ino).as_str().unwrap() };
        let mut offset = unsafe { (*inoffseto).value };

        while offset < input.len() && input.as_bytes()[offset].is_ascii_whitespace() {
            offset += 1;
        }

        if offset >= input.len() {
            self.push_false();
            unsafe {
                (*inoffseto).value = offset;
            }
            return;
        }

        let start = offset;

        while offset < input.len() && !input.as_bytes()[offset].is_ascii_whitespace() {
            offset += 1;
        }

        unsafe {
            (*inoffseto).value = offset;
        }

        let word = &input[start..offset];
        let word_obj = self.allocate_string(word);
        self.push(word_obj);
    }

    pub fn dup(&mut self) {
        let obj = self.pop();
        self.push(obj);
        self.push(obj);
    }

    pub fn try_parse_number(&mut self) {
        let obj = self.pop();
        let ba = obj.as_byte_array();
        let string = unsafe { (*ba).as_str().unwrap() };
        if let Ok(num) = str::parse::<usize>(string) {
            let num_obj = self.allocate_fixnum(num);
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
        self.push(object::ObjectRef(self.special_objects.true_object));
    }

    pub fn push_false(&mut self) {
        self.push(object::ObjectRef(self.special_objects.false_object));
    }

    pub fn push_fixnum(&mut self, fixnum: usize) {
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
    pub value_type: object::ObjectRef, // null for untyped
    pub index: usize,
    pub read_only: usize, // 0/null/f => false
}

impl<'a> Default for SlotDescriptor<'a> {
    fn default() -> Self {
        Self {
            name: "",
            kind: object::SLOT_DATA,
            value_type: object::ObjectRef::null(),
            index: 0,
            read_only: 0,
        }
    }
}

impl VM {
    pub fn allocate_string<'a>(&mut self, s: &'a str) -> object::ObjectRef {
        let required_size = object::ByteArrayObject::required_string_size(s);
        let obj = self.gc.allocate(required_size, 8, false).unwrap();

        unsafe {
            let ba = obj.as_byte_array_mut();
            if !self.special_objects.bytearray_map.is_null() {
                (*ba).header.map = object::ObjectRef::from_map(self.special_objects.bytearray_map);
            }

            (*ba).set_size(s.len());
            (*ba).copy_rust_string(s);
        }

        obj
    }

    pub fn allocate_array_from_slice(&mut self, slice: &[object::ObjectRef]) -> object::ObjectRef {
        let array_obj = self.allocate_array(slice.len());
        let array = array_obj.as_array_mut();
        unsafe {
            for (i, field) in (*array).data_mut().iter_mut().enumerate() {
                *field = slice[i];
            }
        }

        array_obj
    }

    pub fn allocate_array(&mut self, capacity: usize) -> object::ObjectRef {
        let required_size = object::ArrayObject::required_size(capacity);
        let obj = self.gc.allocate(required_size, 8, false).unwrap();
        unsafe {
            let arr = obj.as_array_mut();
            (*arr).size = capacity;
        }

        obj
    }

    pub fn allocate_map<'a>(
        &mut self,
        name: &str,
        slots: &[SlotDescriptor<'a>],
    ) -> object::ObjectRef {
        let required_size = object::Map::required_size(slots.len());

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
            if slot.kind == object::SLOT_DATA {
                object_size += 1;
            }
        }

        let map_obj = self.gc.allocate(required_size, 8, true).unwrap();
        unsafe {
            let map = map_obj.as_map_mut();
            (*map).header.map = if self.special_objects.map_map.is_null() {
                object::ObjectRef::null()
            } else {
                object::ObjectRef::from_map(self.special_objects.map_map)
            };
            (*map).name = map_name;
            (*map).object_size = object_size;
            (*map).slot_count = slots.len();
            for (index, (desc, slot_name)) in slots.iter().zip(slot_name_objects).enumerate() {
                let slot = (*map).get_slot_mut(index);
                slot.name = slot_name;
                slot.kind = desc.kind;
                slot.read_only = slot.read_only;
                slot.value_type = desc.value_type;
                slot.index = desc.index;
            }

            self.maps.insert(name.to_string(), map);
        }

        map_obj
    }

    pub fn allocate_object(&mut self, map: object::ObjectRef) -> object::ObjectRef {
        let map = map.as_map_mut();
        let required_size = unsafe { object::Object::required_size(&*map) };
        let obj = self.gc.allocate(required_size, 8, false).unwrap();
        unsafe {
            let object = obj.object_mut();
            (*object).set_map(map);
        }
        obj
    }

    pub unsafe fn clone_object(&mut self, obj: object::ObjectRef) -> object::ObjectRef {
        let map = obj.get_map_mut();
        if map == self.special_objects.fixnum_map {
            let num = obj.as_fixnum();
            self.allocate_fixnum((*num).value)
        } else if map == self.special_objects.array_map {
            let orig = obj.as_array();
            let size = (*orig).size;
            let data = (*orig).data();
            let copy = self.allocate_array(size);
            let copy_data = (*copy.as_array_mut()).data_mut();
            for (od, cd) in data.iter().zip(copy_data) {
                *cd = self.clone_object(*od);
            }
            copy
        } else if map == self.special_objects.bytearray_map {
            // let orig = obj.as_byte_array();
            // let copy = self.gc.allocate((*orig).capacity, 8, false).unwrap();
            // let new = copy.as_byte_array_mut();
            // (*new).capacity = (*orig).capacity;
            // ptr::copy_nonoverlapping((*orig).data_ptr(), (*new).data_ptr_mut(), (*new).capacity);
            obj
        } else {
            // TODO check map for custom clone
            obj
        }
    }

    pub fn allocate_fixnum(&mut self, value: usize) -> object::ObjectRef {
        let map = *self.maps.get("fixnum").unwrap();
        let object = self.allocate_object(object::ObjectRef::from_map(map));
        let num = object.as_fixnum_mut();
        unsafe {
            (*num).value = value;
        }
        object
    }

    pub fn init_primitive_maps(&mut self) {
        let map_map = self.allocate_map("map", &[]);
        unsafe {
            self.special_objects.map_map = map_map.as_map_mut();
            let map = map_map.as_map_mut();
            (*map).header.map = map_map;
        }

        let bytearray_traits = self.allocate_map("bytearray-traits", &[]);

        let bytearray_map = self.allocate_map(
            "bytearray",
            &[
                SlotDescriptor {
                    name: "parent",
                    kind: object::SLOT_PARENT,
                    value_type: bytearray_traits,
                    ..Default::default()
                },
                SlotDescriptor {
                    name: "capacity",
                    kind: object::SLOT_DATA,
                    value_type: object::ObjectRef::null(),
                    ..Default::default()
                },
                SlotDescriptor {
                    name: "data",
                    kind: object::SLOT_VARIABLE_DATA,
                    value_type: object::ObjectRef::null(),
                    index: 1,
                    read_only: 0,
                },
            ],
        );

        unsafe {
            let map_map = map_map.as_map_mut();
            let name = (*map_map).name.as_byte_array_mut();
            (*name).header.map = bytearray_map;

            let map_traits = bytearray_traits.as_map_mut();
            let name = (*map_traits).name.as_byte_array_mut();
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

        let integer_traits = self.allocate_map("integer-traits", &[]);

        let float_traits = self.allocate_map("float-traits", &[]);

        let fixnum_map = self.allocate_map(
            "fixnum",
            &[
                SlotDescriptor {
                    name: "parent",
                    kind: object::SLOT_PARENT,
                    value_type: integer_traits,
                    ..Default::default()
                },
                SlotDescriptor {
                    name: "value",
                    kind: object::SLOT_DATA,
                    value_type: object::ObjectRef::null(),
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
                    value_type: float_traits,
                    ..Default::default()
                },
                SlotDescriptor {
                    name: "value",
                    kind: object::SLOT_DATA,
                    value_type: object::ObjectRef::null(),
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

        let array_traits = self.allocate_map("array-traits", &[]);

        let array_map = self.allocate_map(
            "array",
            &[
                SlotDescriptor {
                    name: "parent",
                    kind: object::SLOT_PARENT,
                    value_type: array_traits,
                    index: 0,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "capacity",
                    kind: object::SLOT_DATA,
                    value_type: fixnum_map,
                    index: 0,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "size",
                    kind: object::SLOT_DATA,
                    value_type: fixnum_map,
                    index: 1,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "data",
                    kind: object::SLOT_VARIABLE_DATA,
                    value_type: object::ObjectRef::null(),
                    index: 1,
                    read_only: 0,
                },
            ],
        );

        self.special_objects.array_map = array_map.as_map_mut();

        let quotation_traits = self.allocate_map("quotation-traits", &[]);

        let quotation_map = self.allocate_map(
            "quotation",
            &[
                SlotDescriptor {
                    name: "parent",
                    kind: object::SLOT_PARENT,
                    value_type: quotation_traits,
                    index: 0,
                    read_only: 0,
                },
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
                    value_type: object::ObjectRef::null(),
                    index: 1,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "entry",
                    kind: object::SLOT_DATA,
                    value_type: object::ObjectRef::null(),
                    index: 2,
                    read_only: 0,
                },
            ],
        );
        self.special_objects.quotation_map = quotation_map.as_map_mut();

        let word_traits = self.allocate_map("word-traits", &[]);

        let word_map = self.allocate_map(
            "word",
            &[
                SlotDescriptor {
                    name: "parent",
                    kind: object::SLOT_PARENT,
                    value_type: word_traits,
                    index: 0,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "name",
                    kind: object::SLOT_DATA,
                    value_type: bytearray_map,
                    index: 0,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "primitive?",
                    kind: object::SLOT_DATA,
                    value_type: fixnum_map,
                    index: 1,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "syntax?",
                    kind: object::SLOT_DATA,
                    value_type: fixnum_map,
                    index: 2,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "properties",
                    kind: object::SLOT_DATA,
                    value_type: object::ObjectRef::null(),
                    index: 3,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "body",
                    kind: object::SLOT_DATA,
                    value_type: quotation_map,
                    index: 4,
                    read_only: 0,
                },
            ],
        );

        self.special_objects.word_map = word_map.as_map_mut();

        let false_traits = self.allocate_map("false-traits", &[]);
        let true_traits = self.allocate_map("true-traits", &[]);

        let false_map = self.allocate_map(
            "f",
            &[SlotDescriptor {
                name: "parent",
                kind: object::SLOT_PARENT,
                value_type: false_traits,
                index: 0,
                read_only: 0,
            }],
        );

        let true_map = self.allocate_map(
            "t",
            &[SlotDescriptor {
                name: "parent",
                kind: object::SLOT_PARENT,
                value_type: true_traits,
                index: 0,
                read_only: 0,
            }],
        );

        let false_object = self.allocate_object(false_map);
        let true_object = self.allocate_object(true_map);
        self.gc.set_object_root(false_object);
        self.gc.set_object_root(true_object);
        self.special_objects.false_object = false_object.0;
        self.special_objects.true_object = true_object.0;

        let box_map = self.allocate_map(
            "box",
            &[SlotDescriptor {
                name: "boxed",
                kind: object::SLOT_DATA,
                value_type: object::ObjectRef::null(),
                index: 0,
                read_only: 1,
            }],
        );
        self.special_objects.box_map = box_map.as_map_mut();
    }

    pub fn print_quotation(&self, obj: object::ObjectRef) {
        unsafe {
            let quot = obj.as_quotation().as_ref().unwrap();
            quot.print(self);
            println!();
        }
    }
}
