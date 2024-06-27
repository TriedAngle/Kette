#![allow(unused)]

use std::collections::HashMap;
use std::{mem, ptr};

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

    pub fn retain_push(&mut self, obj: object::ObjectRef) {
        self.retainstack.push(obj)
    }

    pub fn retain_pop(&mut self) -> object::ObjectRef {
        self.retainstack.pop().unwrap()
    }

    pub fn call_push(&mut self, obj: object::ObjectRef) {
        self.callstack.push(obj)
    }

    pub fn call_pop(&mut self) -> object::ObjectRef {
        self.callstack.pop().unwrap()
    }

    pub fn execute_primitive(&mut self, word: *const object::WordObject) {
        let fun: fn(vm: *mut VM) = unsafe {
            assert_eq!((*word).primitive, 1);
            mem::transmute((*word).body.0)
        };

        let vm = self as *mut VM;
        fun(vm);
    }

    pub fn init(&mut self) {
        self.gc.link_vm(self as *const VM);
    }

    pub fn bind_input(&mut self, input: &str) {
        self.gc.unset_object_root(object::ObjectRef(self.special_objects.input as *mut object::Object));
        self.gc.unset_object_root(object::ObjectRef(self.special_objects.input_offset as *mut object::Object));

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
        self.push(object::ObjectRef(self.special_objects.input_offset as *mut Object));
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
            unsafe { (*inoffseto).value = offset; }
            return;
        }

        let start = offset;

        while offset < input.len() && !input.as_bytes()[offset].is_ascii_whitespace() {
            offset += 1;
        }

        unsafe { (*inoffseto).value = offset; }

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

impl<'a> SlotDescriptor<'a> {
    const fn word(name: &'a str) -> Self {
        Self {
            name,
            kind: object::SLOT_WORD,
            value_type: object::ObjectRef::null(),
            index: 0,
            read_only: 0,
        }
    } 
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

    pub fn allocate_array(&mut self, capacity: usize) -> object::ObjectRef {
        let required_size = object::ArrayObject::required_size(capacity);
        let obj = self.gc.allocate(required_size, 8, false).unwrap();
        unsafe {
            let arr = obj.as_array_mut();
            (*arr).capacity = capacity;
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



    pub fn allocate_fixnum(&mut self, value: usize) -> object::ObjectRef {
        let map = *self.maps.get("fixnum").unwrap();
        let object = self.allocate_object(object::ObjectRef::from_map(map));
        let num = object.as_fixnum_mut();
        unsafe {
            (*num).value = value;
        }
        object
    }

    pub fn initialize_primitive_maps(&mut self) {
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
                SlotDescriptor::word("utf8print"),
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
                SlotDescriptor::word("fixnum+"),
                SlotDescriptor::word("fixnum-"),
                SlotDescriptor::word("fixnum*"),
                SlotDescriptor::word("fixnum/"),
                SlotDescriptor::word("fixnum%"),
                SlotDescriptor::word("fixnum."),
                SlotDescriptor::word("fixnum<"),
                SlotDescriptor::word("fixnum>"),
                SlotDescriptor::word("fixnum<="),
                SlotDescriptor::word("fixnum>="),
                SlotDescriptor::word("fixnum-bitand"),
                SlotDescriptor::word("fixnum-bitor"),
                SlotDescriptor::word("fixnum-bitnot"),
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
                SlotDescriptor::word("fixfloat+"),
                SlotDescriptor::word("fixfloat-"),
                SlotDescriptor::word("fixfloat*"),
                SlotDescriptor::word("fixfloat/"),
                SlotDescriptor::word("fixfloat."),
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
                SlotDescriptor {
                    name: "call",
                    kind: object::SLOT_WORD,
                    value_type: object::ObjectRef::null(),
                    index: 0,
                    read_only: 0,
                },
            ],
        );

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
                    value_type: fixfloat_map,
                    index: 1,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "body",
                    kind: object::SLOT_DATA,
                    value_type: object::ObjectRef::null(),
                    index: 2,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "effect",
                    kind: object::SLOT_DATA,
                    value_type: object::ObjectRef::null(),
                    index: 3,
                    read_only: 0,
                },
                SlotDescriptor {
                    name: "flags",
                    kind: object::SLOT_DATA,
                    value_type: object::ObjectRef::null(),
                    index: 4,
                    read_only: 0,
                },
            ],
        );

        let false_traits = self.allocate_map("false-traits", &[]);
        let true_traits = self.allocate_map("true-traits", &[]);

        let false_map = self.allocate_map("f", &[
            SlotDescriptor {
                name: "parent",
                kind: object::SLOT_PARENT,
                value_type: false_traits,
                index: 0,
                read_only: 0,
            },
            SlotDescriptor::word("f"),
        ]);

        let true_map = self.allocate_map("t", &[
            SlotDescriptor {
                name: "parent",
                kind: object::SLOT_PARENT,
                value_type: true_traits,
                index: 0,
                read_only: 0,
            },
            SlotDescriptor::word("t"),
        ]);

        let false_object = self.allocate_object(false_map);
        let true_object = self.allocate_object(true_map);
        self.gc.set_object_root(false_object);
        self.gc.set_object_root(true_object);


    }
}