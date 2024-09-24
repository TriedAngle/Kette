use std::mem;

use crate::object;
use crate::object::Object;
use crate::system;
use crate::VM;

impl VM {
    // requires slot to already exist
    pub unsafe fn add_primitive(&mut self, name: &str, fun: unsafe fn(vm: *mut VM), syntax: bool) {
        let word_map = *self.maps.get("word").unwrap();
        let word_object = self.allocate_object(object::ObjectRef::from_map(word_map));

        let word_name = self.allocate_string(name);
        let word = word_object.as_word_mut();
        (*word).name = word_name;
        (*word).primitive = 1;
        (*word).syntax = if syntax { 1 } else { 0 };
        (*word).properties = object::ObjectRef::null();
        (*word).body = object::ObjectRef::from_fn(fun);

        self.words.insert(name.to_string(), word);
    }

    pub fn add_primitives(&mut self) {
        unsafe {
            self.add_globals_primitives();
            self.add_fixnum_primitives();
        }
    }
}

unsafe fn primitive_open_library(vm: *mut VM) {
    let ba = (*vm).pop();
    let str = ba.bytearray_as_str();
    let library = system::open_library(str);
    (*vm).push_fixnum(mem::transmute(library));
}

unsafe fn primitive_close_library(vm: *mut VM) {
    let lib = (*vm).pop().as_fixnum();
    let library = mem::transmute((*lib).value);
    let value = system::close_library(library);
    (*vm).push_fixnum(value as isize);
}

unsafe fn primitive_library_symbol(vm: *mut VM) {
    let lib = (*vm).pop().as_fixnum();
    let symbol = (*vm).pop();
    let library = mem::transmute((*lib).value);
    let sym = system::library_symbol(library, symbol.bytearray_as_str());
    (*vm).push_fixnum(mem::transmute(sym));
}


unsafe fn primitive_box(vm: *mut VM) {
    let obj = (*vm).pop();
    let box_map = (*vm).special_objects.box_map;
    let box_obj = (*vm).allocate_object(object::ObjectRef::from_map(box_map));
    let boxx = box_obj.as_box_mut();
    (*boxx).boxed = obj;
    (*vm).push(box_obj);
}

unsafe fn primitive_unbox(vm: *mut VM) {
    let box_obj = (*vm).pop().as_box();
    let boxed = (*box_obj).boxed;
    (*vm).push(boxed);
}

unsafe fn primitive_peek_next_token(vm: *mut VM) {
    let position = (*(*vm).special_objects.input_offset).value;
    (*vm).read_word();
    (*(*vm).special_objects.input_offset).value = position;
}

unsafe fn primitive_next_token(vm: *mut VM) {
    (*vm).read_word();
}

unsafe fn primitive_parse_until(vm: *mut VM) {
    (*vm).parse_until();
}

unsafe fn primitive_skip_until(vm: *mut VM) {
    let mut vec = Vec::<object::ObjectRef>::new();
    let end_obj = (*vm).pop().as_box();
    let end_word = (*end_obj).boxed;
    loop {
        (*vm).read_word();
        (*vm).dup();
        if (*vm).is_false() {
            (*vm).drop();
            break; // TODO HANDLE ERROR
        }
        (*vm).dup();
        (*vm).try_parse_number();
        (*vm).dup();
        if (*vm).is_true() {
            (*vm).drop();
            (*vm).drop();
            continue;
        }
        (*vm).drop();
        let name = (*vm).peek();
        (*vm).lookup_word();
        (*vm).dup();
        if (*vm).is_false() {
            vec.push(name);
            (*vm).drop();
            continue;
        }
        let word = (*vm).pop();
        if word == end_word {
            break;
        }
        vec.push(name);
    }
    let arr = (*vm).allocate_array_from_slice(&vec);
    (*vm).push(arr);
}

unsafe fn primitive_link_token(vm: *mut VM) {
    (*vm).lookup_word();
}

unsafe fn primitive_link_map(vm: *mut VM) {
    let ba = (*vm).pop();
    let name = ba.bytearray_as_str();
    let map = (*vm).maps.get(name);
    if let Some(map) = map {
        (*vm).push(object::ObjectRef::from_map(*map))
    } else {
        (*vm).push_false();
    }
}

unsafe fn primitive_try_parse_num(vm: *mut VM) {
    (*vm).try_parse_number();
}

unsafe fn create_empty_global_word(vm: *mut VM, name: object::ObjectRef) -> object::ObjectRef {
    let word_map = (*vm).special_objects.word_map;
    let word_object = (*vm).allocate_object(object::ObjectRef::from_map(word_map));

    let word = word_object.as_word_mut();
    (*word).name = name;
    (*word).primitive = 0;
    (*word).syntax = 0;
    (*word).properties = object::ObjectRef::null();
    (*word).body = object::ObjectRef::null();

    // TODO: implement global vocabulary
    let word_name = name.bytearray_as_str();
    (*vm).words.insert(word_name.to_owned(), word);

    word_object
}

unsafe fn create_empty_word(vm: *mut VM, name: object::ObjectRef) -> object::ObjectRef {
    let word_map = (*vm).special_objects.word_map;
    let word_object = (*vm).allocate_object(object::ObjectRef::from_map(word_map));

    let word = word_object.as_word_mut();
    (*word).name = name;
    (*word).primitive = 0;
    (*word).syntax = 0;
    (*word).properties = object::ObjectRef::null();
    (*word).body = object::ObjectRef::null();

    word_object
}

unsafe fn primitive_create_empty_global_word(vm: *mut VM) {
    let name = (*vm).pop();
    let word = create_empty_global_word(vm, name);

    (*vm).push(word);
}

unsafe fn primitive_define_empty_word(vm: *mut VM) {
    let name = (*vm).pop();
    let word = create_empty_word(vm, name);
    (*vm).push(word)
}

unsafe fn primitive_quotation_start(vm: *mut VM) {
    let word = (*vm).words.get("]").unwrap();
    (*vm).push(object::ObjectRef::from_word(*word));
    primitive_box(vm);
    (*vm).parse_until();
    primitive_array_to_quotation(vm);
}

unsafe fn primitive_quotation_end(vm: *mut VM) {
    (*vm).push_false();
}

unsafe fn primitive_string(vm: *mut VM) {
    let v = vm.as_mut().unwrap();
    let ino = v.special_objects.input;
    let inoffsetto = v.special_objects.input_offset;
    let inoobj = object::ObjectRef(ino as *mut object::Object);

    let input = inoobj.bytearray_as_str();
    let mut offset = (*inoffsetto).value as usize;
    let start = offset;

    while offset < input.len() {
        if input.as_bytes()[offset] == 34 {
            break;
        }
        offset += 1;
    }

    // TODO: handle error
    (*inoffsetto).value = (offset + 1) as isize;
    let string = &input[start + 1..offset];
    let string_obj = v.allocate_string(string);
    v.push(string_obj);
}

unsafe fn primitive_print_string(vm: *mut VM) {
    let obj = (*vm).pop();
    let s = obj.bytearray_as_str();
    println!("{:?}", s);
}

unsafe fn parse_stack_effect(vm: *mut VM) {
    (*vm).read_word();
    _ = (*vm).pop();
    loop {
        (*vm).read_word();
        let word = (*vm).pop();
        if word.bytearray_is_eq_rust("(") {
            parse_stack_effect(vm);
            continue;
        }
        if word.bytearray_is_eq_rust(")") {
            break;
        }
    }
}

unsafe fn primitive_define_word(vm: *mut VM) {
    (*vm).read_word();
    let name = (*vm).pop();
    let word_obj = create_empty_global_word(vm, name);
    let word = word_obj.as_word_mut();
    parse_stack_effect(vm); // ignore for now lol
    let word_end = (*vm).words.get(";").unwrap();
    (*vm).push(object::ObjectRef::from_word(*word_end));
    primitive_box(vm);
    (*vm).parse_until();
    primitive_array_to_quotation(vm);
    let quotation = (*vm).pop();
    (*word).body = quotation;
    (*vm).push_true();
}

unsafe fn primitive_define_syntax(vm: *mut VM) {
    (*vm).read_word();
    let name = (*vm).pop();
    let word_obj = create_empty_global_word(vm, name);
    let word = word_obj.as_word_mut();
    let word_end = (*vm).words.get(";").unwrap();
    (*vm).push(object::ObjectRef::from_word(*word_end));
    primitive_box(vm);
    (*vm).parse_until();
    primitive_array_to_quotation(vm);
    let quotation = (*vm).pop();
    (*word).body = quotation;
    (*word).syntax = 1;
    (*vm).push_true();
}

unsafe fn primitive_define_map(vm: *mut VM) {
    let name = (*vm).pop();
    let map_obj = (*vm)
        .gc
        .allocate(mem::size_of::<object::Map>(), 8, true)
        .unwrap();
    let map = map_obj.as_map_mut();
    let slots = (*vm).allocate_array(0);
    (*map).header.map = object::ObjectRef::from_map((*vm).special_objects.map_map);
    (*map).name = name;
    (*map).object_size = 2;
    (*map).slot_count = 0;
    (*map).slots = slots;

    let map_name = name.bytearray_as_str();
    (*vm).maps.insert(map_name.to_owned(), map);

    (*vm).push(map_obj);
}

unsafe fn primitive_clone(vm: *mut VM) {}

unsafe fn primitive_object_new_from_map(vm: *mut VM) {
    let map = (*vm).pop();
    let obj = (*vm).allocate_object(map);
    let slot_count = (*map.as_map()).object_size - 2;
    for i in (0..slot_count).rev() {
        let map_slot = (*map.as_map()).get_slot(i);
        if map_slot.kind == object::SLOT_EMBEDDED_DATA {
            let val = (*(*vm).pop().as_fixnum()).value;
            obj.set_field(i, object::ObjectRef::from_usize(mem::transmute(val)));
        } else {
            obj.set_field(i, (*vm).pop());
        }
    }
    (*vm).push(obj);
}

unsafe fn primitive_retain_push(vm: *mut VM) {
    (*vm).pop_retain_push();
}

unsafe fn primitive_retian_pop(vm: *mut VM) {
    (*vm).retain_pop_push();
}

unsafe fn primitive_vm_stack(vm: *mut VM) {
    let stack = (*vm).allocate_array_from_slice(&(*vm).stack);
    (*vm).push(stack);
}

unsafe fn primitive_define_end(vm: *mut VM) {
    (*vm).push_false();
}

// ( a -- a a )
unsafe fn primitive_dup(vm: *mut VM) {
    (*vm).dup();
}

// ( a b -- a a b )
unsafe fn primitive_dupd(vm: *mut VM) {
    let b = (*vm).pop();
    (*vm).dup();
    (*vm).push(b);
}

// ( a -- )
unsafe fn primitive_drop(vm: *mut VM) {
    (*vm).drop();
}

// ( a b -- b )
unsafe fn primitive_dropd(vm: *mut VM) {
    (*vm).dropd();
}

// ( a b -- b a )
unsafe fn primitive_swap(vm: *mut VM) {
    let b = (*vm).pop();
    let a = (*vm).pop();
    (*vm).push(b);
    (*vm).push(a);
}

// ( a b c -- b a c )
unsafe fn primitive_swapd(vm: *mut VM) {
    let c = (*vm).pop();
    let b = (*vm).pop();
    let a = (*vm).pop();
    (*vm).push(b);
    (*vm).push(a);
    (*vm).push(c);
}

// ( a b c -- b c a )
unsafe fn primitive_rot(vm: *mut VM) {
    let c = (*vm).pop();
    let b = (*vm).pop();
    let a = (*vm).pop();
    (*vm).push(b);
    (*vm).push(c);
    (*vm).push(a);
}

// ( a b c -- c a b )
unsafe fn primitive_neg_rot(vm: *mut VM) {
    let c = (*vm).pop();
    let b = (*vm).pop();
    let a = (*vm).pop();
    (*vm).push(c);
    (*vm).push(a);
    (*vm).push(b);
}

unsafe fn primitive_push_true(vm: *mut VM) {
    (*vm).push_true();
}

unsafe fn primitive_push_false(vm: *mut VM) {
    (*vm).push_false();
}

unsafe fn primitive_if(vm: *mut VM) {
    let false_branch = (*vm).pop();
    let true_branch = (*vm).pop();
    let truth = (*vm).pop();
    if truth.0 == (*vm).special_objects.false_object {
        (*vm).execute_quotation(false_branch.as_quotation());
    } else {
        (*vm).execute_quotation(true_branch.as_quotation());
    }
}

unsafe fn primitive_not(vm: *mut VM) {
    let a = (*vm).pop();
    if a.0 == (*vm).special_objects.false_object {
        (*vm).push_true();
    } else {
        (*vm).push_false();
    };
}

unsafe fn primitive_and(vm: *mut VM) {
    let b = (*vm).pop();
    let a = (*vm).pop();
    let is_a = a.0 != (*vm).special_objects.false_object;
    let is_b = b.0 != (*vm).special_objects.false_object;
    if is_a && is_b {
        (*vm).push_true();
    } else {
        (*vm).push_false();
    };
}

unsafe fn primitive_or(vm: *mut VM) {
    let b = (*vm).pop();
    let a = (*vm).pop();
    let is_a = a.0 != (*vm).special_objects.false_object;
    let is_b = b.0 != (*vm).special_objects.false_object;
    if is_a || is_b {
        (*vm).push_true();
    } else {
        (*vm).push_false();
    };
}

pub unsafe fn primitive_array_to_quotation(vm: *mut VM) {
    let array = (*vm).pop();
    let quot_map = (*vm).special_objects.quotation_map;
    let quot_obj = (*vm).allocate_object(object::ObjectRef::from_map(quot_map));
    let quot = quot_obj.as_quotation_mut();
    (*quot).body = array;
    (*vm).push(quot_obj);
}

unsafe fn primitive_call_quotation(vm: *mut VM) {
    let quot = (*vm).pop().as_quotation();
    (*vm).execute_quotation(quot);
}

unsafe fn primitive_call_primitive(vm: *mut VM) {
    let word = (*vm).pop().as_word();
    (*vm).execute_primitive(word)
}

unsafe fn primitive_word_to_quotation(vm: *mut VM) {
    let word = (*vm).pop().as_quotation();
    let body = (*word).body;
    (*vm).push(body);
}

unsafe fn primitive_print_quotation(vm: *mut VM) {
    let quot = (*vm).pop();
    (*vm).print_quotation(quot);
}

unsafe fn primitive_print_array(vm: *mut VM) {
    let arr = (*vm).pop();
    (*vm).print_array(arr);
}

unsafe fn primitive_context(vm: *mut VM) {
    (*vm).push((*vm).special_objects.context_object);
}

unsafe fn primitive_get_map(vm: *mut VM) {
    let obj = (*vm).pop();
    let map = obj.get_map_mut();
    (*vm).push(object::ObjectRef::from_map(map));
}

// ( object index -- value )
unsafe fn primitive_slot(vm: *mut VM) {
    let index = (*vm).pop().as_fixnum();
    let obj = (*vm).pop();
    let value = obj.get_field((*index).value as usize);

    if obj.get_map().as_ref().is_some() {
        let map = obj.get_map();
        let slots = (*map).slots;
        let slot_count = slots.array_data_len();

        for idx in 0..slot_count {
            let slot = slots.get_array_at(idx);
            let slot = slot.as_slot();
            if (*slot).index == (*index).value as usize
                && (*slot).kind == object::SLOT_EMBEDDED_DATA
            {
                (*vm).push_fixnum(value.as_isize());
                return;
            }
        }
    }

    (*vm).push(value);
}

// ( value object index -- )
unsafe fn primitive_set_slot(vm: *mut VM) {
    let index = (*vm).pop().as_fixnum();
    let obj = (*vm).pop();
    let value = (*vm).pop();

    if obj.get_map().as_ref().is_some() {
        let map = obj.get_map();
        let slots = (*map).slots;
        let slot_count = slots.array_data_len();

        for idx in 0..slot_count {
            let slot = slots.get_array_at(idx);
            let slot = slot.as_slot();
            if (*slot).index == (*index).value as usize
                && (*slot).kind == object::SLOT_EMBEDDED_DATA
            {
                let num = (*value.as_fixnum()).value;
                obj.set_field(
                    (*index).value as usize,
                    object::ObjectRef(mem::transmute(num)),
                );
                return;
            }
        }
    }

    obj.set_field((*index).value as usize, value);
}

unsafe fn primitive_ptr_get(vm: *mut VM) {
    let address = (*(*vm).pop().as_fixnum()).value as usize;
    let ptr = address as *mut isize;
    (*vm).push_fixnum(*ptr);
}

unsafe fn primitive_object_ptr_get(vm: *mut VM) {
    let object = (*vm).pop();
    let ptr: isize = mem::transmute(object.0);
    (*vm).push_fixnum(ptr);
}

unsafe fn primitive_ptr_deref(vm: *mut VM) {
    let ptr = (*vm).pop().as_fixnum();
    let obj = (*ptr).value;
    (*vm).push(object::ObjectRef(obj as *mut Object));
}

unsafe fn primitive_ptr_set(vm: *mut VM) {
    let address = (*(*vm).pop().as_fixnum()).value;
    let value = (*(*vm).pop().as_fixnum()).value;
    let ptr: *mut isize = mem::transmute(address);
    *ptr = value;
}

// ( size default-value -- array )
unsafe fn primitive_create_array(vm: *mut VM) {
    let initial = (*vm).pop();
    let size = (*vm).pop().as_fixnum();
    let obj = (*vm).allocate_array((*size).value as usize);

    for index in 0..obj.array_data_len() {
        *(obj.array_data().add(index)) = initial;
    }
    (*vm).push(obj);
}

unsafe fn primitive_create_bytearray(vm: *mut VM) {
    let size = (*vm).pop().as_fixnum();
    let ba = (*vm).allocate_bytearray((*size).value as usize);
    (*vm).push(ba);
}

unsafe fn primitive_bytearray_eq(vm: *mut VM) {
    let b = (*vm).pop();
    let a = (*vm).pop();

    if a.bytearray_is_eq(b) {
        (*vm).push_true();
    } else {
        (*vm).push_false();
    }
}

unsafe fn primitive_bytearray_concat(vm: *mut VM) {
    let b = (*vm).pop();
    let a = (*vm).pop();
    let new_size = a.bytearray_data_len() + b.bytearray_data_len();
    let new = (*vm).allocate_bytearray(new_size);
    std::ptr::copy_nonoverlapping(
        a.bytearray_data(),
        new.bytearray_data(),
        a.bytearray_data_len(),
    );
    std::ptr::copy_nonoverlapping(
        b.bytearray_data(),
        new.bytearray_data().add(a.bytearray_data_len()),
        b.bytearray_data_len(),
    );
    (*vm).push(new);
}

impl VM {
    unsafe fn add_globals_primitives(&mut self) {
        self.add_primitive("@vm-peek-next-token", primitive_peek_next_token, false);
        self.add_primitive("@vm-next-token", primitive_next_token, false);
        self.add_primitive("@vm-parse-until", primitive_parse_until, false);
        self.add_primitive("@vm-skip-until", primitive_skip_until, false);
        self.add_primitive("@vm-link-word", primitive_link_token, false);
        self.add_primitive("@vm-link-map", primitive_link_map, false);
        self.add_primitive("@vm-?number", primitive_try_parse_num, false);
        self.add_primitive(
            "@vm-define-empty-global-word",
            primitive_create_empty_global_word,
            false,
        );
        self.add_primitive("@vm-define-empty-word", primitive_define_empty_word, false);

        self.add_primitive("@vm-stack", primitive_vm_stack, false);
        self.add_primitive("@vm-define-map", primitive_define_map, false);
        self.add_primitive("@vm-clone", primitive_clone, false);
        self.add_primitive("@vm-new-object", primitive_object_new_from_map, false);
        self.add_primitive("@>r", primitive_retain_push, false);
        self.add_primitive("@r>", primitive_retian_pop, false);
        self.add_primitive("(open-library)", primitive_open_library, false);
        self.add_primitive("(close-library)", primitive_close_library, false);
        self.add_primitive("(library-symbol)", primitive_library_symbol, false);
        self.add_primitive(">box", primitive_box, false);
        self.add_primitive("unbox", primitive_unbox, false);
        self.add_primitive("[", primitive_quotation_start, true);
        self.add_primitive("]", primitive_quotation_end, false);
        self.add_primitive(":", primitive_define_word, true);
        self.add_primitive("@:", primitive_define_syntax, true);
        self.add_primitive(";", primitive_define_end, false);

        self.add_primitive("s\"", primitive_string, true);

        self.add_primitive("dup", primitive_dup, false);
        self.add_primitive("dupd", primitive_dupd, false);
        self.add_primitive("drop", primitive_drop, false);
        self.add_primitive("dropd", primitive_dropd, false);
        self.add_primitive("swap", primitive_swap, false);
        self.add_primitive("swapd", primitive_swapd, false);
        self.add_primitive("rot", primitive_rot, false);
        self.add_primitive("-rot", primitive_neg_rot, false);

        self.add_primitive("t", primitive_push_true, false);
        self.add_primitive("f", primitive_push_false, false);

        self.add_primitive("let-me-cook", primitive_context, false);
        self.add_primitive("slot", primitive_slot, false);
        self.add_primitive("set-slot", primitive_set_slot, false);

        self.add_primitive("get^", primitive_ptr_get, false);
        self.add_primitive("object^", primitive_object_ptr_get, false);
        self.add_primitive("^object", primitive_ptr_deref, false);
        self.add_primitive("set^", primitive_ptr_set, false);

        self.add_primitive("if", primitive_if, false);
        self.add_primitive("and", primitive_and, false);
        self.add_primitive("or", primitive_or, false);
        self.add_primitive("not", primitive_not, false);

        self.add_primitive("array>quotation", primitive_array_to_quotation, false);
        self.add_primitive("(call)", primitive_call_quotation, false);
        self.add_primitive("(call-primitive)", primitive_call_primitive, false);
        self.add_primitive("<array>", primitive_create_array, false);
        self.add_primitive("<bytearray>", primitive_create_bytearray, false);
        self.add_primitive("bytearray=", primitive_bytearray_eq, false);
        self.add_primitive("bytearray-concat", primitive_bytearray_concat, false);

        self.add_primitive("utf8.", primitive_print_string, false);
        self.add_primitive("quotation.", primitive_print_quotation, false);
        self.add_primitive("array.", primitive_print_array, false);
    }
}

unsafe fn primitive_fixnum_neg(vm: *mut VM) {
    let a = (*vm).pop().as_fixnum();
    (*vm).push_fixnum(-(*a).value);
}

unsafe fn primitive_fixnum_add(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    let value = (*a).value + (*b).value;
    (*vm).push_fixnum(value);
}

unsafe fn primitive_fixnum_sub(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    let value = (*a).value - (*b).value;
    (*vm).push_fixnum(value);
}

unsafe fn primitive_fixnum_mul(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    let value = (*a).value * (*b).value;
    (*vm).push_fixnum(value);
}

unsafe fn primitive_fixnum_div(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    let value = (*a).value / (*b).value;
    (*vm).push_fixnum(value);
}

unsafe fn primitive_fixnum_mod(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    let value = (*a).value % (*b).value;
    (*vm).push_fixnum(value);
}

unsafe fn primitive_fixnum_dot(vm: *mut VM) {
    let obj = (*vm).pop().as_fixnum();
    let val = (*obj).value;
    println!("{}", val);
}

unsafe fn primitive_fixnum_eq(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    if (*a).value == (*b).value {
        (*vm).push_true();
    } else {
        (*vm).push_false();
    };
}

unsafe fn primitive_fixnum_lt(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    if (*a).value < (*b).value {
        (*vm).push_true();
    } else {
        (*vm).push_false();
    };
}

unsafe fn primitive_fixnum_gt(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    if (*a).value > (*b).value {
        (*vm).push_true();
    } else {
        (*vm).push_false();
    };
}

unsafe fn primitive_fixnum_lte(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    if (*a).value <= (*b).value {
        (*vm).push_true();
    } else {
        (*vm).push_false();
    };
}

unsafe fn primitive_fixnum_gte(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    if (*a).value >= (*b).value {
        (*vm).push_true();
    } else {
        (*vm).push_false();
    };
}

unsafe fn primitive_fixnum_bitand(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    let res = (*vm).allocate_fixnum((*a).value & (*b).value);
    (*vm).push(res);
}

unsafe fn primitive_fixnum_bitor(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    let res = (*vm).allocate_fixnum((*a).value | (*b).value);
    (*vm).push(res);
}

unsafe fn primitive_fixnum_bitxor(vm: *mut VM) {
    let b = (*vm).pop().as_fixnum();
    let a = (*vm).pop().as_fixnum();
    let res = (*vm).allocate_fixnum((*a).value ^ (*b).value);
    (*vm).push(res);
}

unsafe fn primitive_fixnum_bitnot(vm: *mut VM) {
    let a = (*vm).pop().as_fixnum();
    let res = (*vm).allocate_fixnum(!(*a).value);
    (*vm).push(res);
}

unsafe fn primitive_fixnum_shift_left(vm: *mut VM) {
    let n = (*vm).pop().as_fixnum();
    let x = (*vm).pop().as_fixnum();
    let res = (*vm).allocate_fixnum((*x).value << (*n).value);
    (*vm).push(res);
}

unsafe fn primitive_fixnum_shift_right(vm: *mut VM) {
    let n = (*vm).pop().as_fixnum();
    let x = (*vm).pop().as_fixnum();
    let res = (*vm).allocate_fixnum((*x).value >> (*n).value);
    (*vm).push(res);
}

impl VM {
    unsafe fn add_fixnum_primitives(&mut self) {
        self.add_primitive("fixnum-neg", primitive_fixnum_neg, false);
        self.add_primitive("fixnum+", primitive_fixnum_add, false);
        self.add_primitive("fixnum-", primitive_fixnum_sub, false);
        self.add_primitive("fixnum*", primitive_fixnum_mul, false);
        self.add_primitive("fixnum/", primitive_fixnum_div, false);
        self.add_primitive("fixnum%", primitive_fixnum_mod, false);
        self.add_primitive("fixnum.", primitive_fixnum_dot, false);
        self.add_primitive("fixnum=", primitive_fixnum_eq, false);
        self.add_primitive("fixnum<", primitive_fixnum_lt, false);
        self.add_primitive("fixnum>", primitive_fixnum_gt, false);
        self.add_primitive("fixnum<=", primitive_fixnum_lte, false);
        self.add_primitive("fixnum>=", primitive_fixnum_gte, false);
        self.add_primitive("fixnum-bitand", primitive_fixnum_bitand, false);
        self.add_primitive("fixnum-bitor", primitive_fixnum_bitor, false);
        self.add_primitive("fixnum-bitxor", primitive_fixnum_bitxor, false);
        self.add_primitive("fixnum-bitnot", primitive_fixnum_bitnot, false);
        self.add_primitive("fixnum-bitshift-left", primitive_fixnum_shift_left, false);
        self.add_primitive("fixnum-bitshift-right", primitive_fixnum_shift_right, false);
    }
}
