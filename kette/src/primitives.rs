use crate::object;
use crate::VM;

impl VM {
    // requires slot to already exist
    pub unsafe fn add_primitive(
        &mut self,
        name: &str,
        fun: unsafe fn(vm: *mut VM),
        syntax: bool,
        map_name: &str,
    ) {
        let word_map = *self.maps.get("word").unwrap();
        let word_object = self.allocate_object(object::ObjectRef::from_map(word_map));

        let word_name = self.allocate_string(name);
        let word = word_object.as_word_mut();
        (*word).name = word_name;
        (*word).primitive = 1;
        (*word).syntax = if syntax { 1 } else { 0 };
        (*word).body = object::ObjectRef::from_fn(fun);

        let map = *self.maps.get(map_name).unwrap();
        let slot = (*map).find_slot_rust_mut(name).unwrap();

        slot.value_type = word_object;
        self.words.insert(name.to_string(), word);
    }

    pub fn add_primitives(&mut self) {
        unsafe {
            self.add_globals_primitives();
            self.add_quotation_primitives();
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

impl VM {
    unsafe fn add_globals_primitives(&mut self) {
        let map = "globals";
        self.add_primitive(">box", primitive_box, false, map);
        self.add_primitive("\\", primitive_place_word, true, map);
        self.add_primitive("[", primitive_quotation_start, true, map);
        self.add_primitive("]", primitive_quotation_end, false, map);
    }
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

impl VM {
    unsafe fn add_quotation_primitives(&mut self) {
        let map = "quotation";
        self.add_primitive("array>quotation", primitive_array_to_quotation, false, map);
        self.add_primitive("call", primitive_call_quotation, false, map);
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

unsafe fn primitive_not(vm: *mut VM) {
    let a = (*vm).pop();
    if a.0 == (*vm).special_objects.false_object {
        (*vm).push_true();
    } else {
        (*vm).push_false();
    };
}

impl VM {
    unsafe fn add_fixnum_primitives(&mut self) {
        let map = "fixnum";
        self.add_primitive("fixnum+", primitive_fixnum_add, false, map);
        self.add_primitive("fixnum-", primitive_fixnum_sub, false, map);
        self.add_primitive("fixnum*", primitive_fixnum_mul, false, map);
        self.add_primitive("fixnum/", primitive_fixnum_div, false, map);
        self.add_primitive("fixnum%", primitive_fixnum_mod, false, map);
        self.add_primitive("fixnum.", primitive_fixnum_dot, false, map);
    }
}
