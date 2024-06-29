use crate::object;
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

unsafe fn primitive_place_word(vm: *mut VM) {
    let v = vm.as_mut().unwrap();
    v.read_word();
    v.lookup_word();
    primitive_box(vm);
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

    let input = (*ino).as_str().unwrap();
    let mut offset = (*inoffsetto).value;
    let start = offset;

    while offset < input.len() {
        if input.as_bytes()[offset] == 34 {
            break;
        }
        offset += 1;
    }

    // TODO: handle error
    (*inoffsetto).value = offset + 1;
    let string = &input[start + 1..offset];
    let string_obj = v.allocate_string(string);
    v.push(string_obj);
}

unsafe fn primitive_print_string(vm: *mut VM) {
    let obj = (*vm).pop();
    let ba = obj.as_byte_array();
    let s = (*ba).as_str().unwrap();
    println!("{}", s);
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
    let word_name = (*name.as_byte_array()).as_str().unwrap().to_string();
    (*vm).words.insert(word_name, word);

    word_object
}

unsafe fn parse_stack_effect(vm: *mut VM) {
    loop {
        (*vm).read_word();
        let word = (*vm).pop().as_byte_array();
        if (*word).is_eq_rust(")") {
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

unsafe fn primitive_define_word_end(vm: *mut VM) {
    (*vm).push_false();
}

// unsafe fn get_map(vm: *mut VM) {
//     let
// }

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
    (*vm).push(b);
    (*vm).push(c);
    (*vm).push(a);
}

// ( x q -- x )
unsafe fn primitive_dip(vm: *mut VM) {
    let q = (*vm).pop().as_quotation();
    (*vm).pop_retain_push();
    (*vm).execute_quotation(q);
    (*vm).retain_pop_push();
}

// ( x q: ( ... x -- ... ) -- x )
unsafe fn primitive_keep(vm: *mut VM) {
    let q = (*vm).pop().as_quotation();
    let x = (*vm).peek();
    (*vm).pop_retain_push();
    (*vm).push(x);
    (*vm).execute_quotation(q);
    (*vm).retain_pop_push();
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

unsafe fn primitive_word_to_quotation(vm: *mut VM) {
    let word = (*vm).pop().as_word();
    let body = (*word).body;
    (*vm).push(body);
}

unsafe fn primitive_print_quotation(vm: *mut VM) {
    let quot = (*vm).pop();
    (*vm).print_quotation(quot);
}

impl VM {
    unsafe fn add_globals_primitives(&mut self) {
        self.add_primitive(">box", primitive_box, false);
        self.add_primitive("unbox", primitive_unbox, false);
        self.add_primitive("\\", primitive_place_word, true);

        self.add_primitive("[", primitive_quotation_start, true);
        self.add_primitive("]", primitive_quotation_end, false);
        self.add_primitive(":", primitive_define_word, true);
        self.add_primitive(";", primitive_define_word_end, false);

        self.add_primitive("s\"", primitive_string, true);
        self.add_primitive("utf8.", primitive_print_string, false);

        self.add_primitive("dup", primitive_dup, false);
        self.add_primitive("dupd", primitive_dupd, false);
        self.add_primitive("drop", primitive_drop, false);
        self.add_primitive("dropd", primitive_dropd, false);
        self.add_primitive("swap", primitive_swap, false);
        self.add_primitive("swapd", primitive_swapd, false);
        self.add_primitive("rot", primitive_rot, false);
        self.add_primitive("-rot", primitive_neg_rot, false);
        self.add_primitive("dip", primitive_dip, false);
        self.add_primitive("keep", primitive_keep, false);

        self.add_primitive("t", primitive_push_true, false);
        self.add_primitive("f", primitive_push_false, false);

        self.add_primitive("if", primitive_if, false);
        self.add_primitive("and", primitive_and, false);
        self.add_primitive("or", primitive_or, false);
        self.add_primitive("not", primitive_not, false);

        self.add_primitive("array>quotation", primitive_array_to_quotation, false);
        self.add_primitive("call", primitive_call_quotation, false);
        self.add_primitive("word>quotation", primitive_word_to_quotation, false);
        self.add_primitive("quotation.", primitive_print_quotation, false);
    }
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
        self.add_primitive("fixnum-bitshiftleft", primitive_fixnum_shift_left, false);
        self.add_primitive("fixnum-bitshiftright", primitive_fixnum_shift_right, false);
    }
}
