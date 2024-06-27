use crate::object;
use crate::VM;

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
    // requires slot to already exist
    pub unsafe fn add_primitive(&mut self, name: &str, fun: unsafe fn(vm: *mut VM), map_name: &str) {
        let word_map = *self.maps.get("word").unwrap();
        let word_object = self.allocate_object(object::ObjectRef::from_map(word_map));

        let word_name = self.allocate_string(name);
        let word = word_object.as_word_mut();
        (*word).name = word_name;
        (*word).primitive = 1;
        (*word).body = object::ObjectRef::from_fn(fun);
        (*word).effect = object::ObjectRef::null();

        let map = *self.maps.get(map_name).unwrap();
        let slot = (*map).find_slot_rust_mut(name).unwrap();
        
        slot.value_type = word_object;
        self.words.insert(name.to_string(), word);
    }

    pub fn add_fixnum_primitives(&mut self) {
        let map = "fixnum";
        unsafe {
            self.add_primitive("fixnum+", primitive_fixnum_add, map);
            self.add_primitive("fixnum-", primitive_fixnum_sub, map);
            self.add_primitive("fixnum*", primitive_fixnum_mul, map);
            self.add_primitive("fixnum/", primitive_fixnum_div, map);
            self.add_primitive("fixnum%", primitive_fixnum_mod, map);
            self.add_primitive("fixnum.", primitive_fixnum_dot, map);
        }
    }
}
