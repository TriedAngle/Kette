use crate::{
    context::Context,
    object::{Array, ByteArray, Object, ObjectRef, ObjectType, SpecialObjects},
};

fn add_primities(ctx: &mut Context) {
    #[rustfmt::skip]
    let words: &[(&str, &[&str], fn(&mut Context))] = &[
        ("drop", &["x","--"], Context::stack_drop),
        ("over", &["x", "y", "--", "x", "y", "x"], Context::stack_over),
        ("swap", &["x", "y", "--", "y", "x"], Context::stack_swap),
        ("dup", &["x", "--", "x", "x"], Context::stack_dup),
        ("pick", &["n", "--", "x"], Context::stack_pick),
        ("npick", &["x y z", "--", "x y z x"], Context::stack_n_pick),
        ("2dup", &["x", "y", "--", "x", "y", "x", "y"], Context::stack_2dup),
        ("2drop", &["x", "y", "--"], Context::stack_2drop),
        ("clear", &["x_n", "...", "x_0", "--"], Context::stack_clear),
        ("2over", &["a", "b", "c", "d", "--", "a", "b", "c", "d", "a", "b"], Context::stack_2over),
        ("2swap", &["a", "b", "c", "d", "--", "c", "d", "a", "b"], Context::stack_2swap),
        ("rot", &["x", "y", "z", "--", "y", "z", "x"], Context::stack_rot),
        ("-rot", &["x", "y", "z", "--", "y", "z", "x"], Context::stack_neg_rot),
        ("dropd", &["x", "y", "--", "y"], Context::stack_dropd),
        ("swapd", &["x", "y", "--", "y", "x"], Context::stack_swapd),
        ("tuck", &["x", "y", "--", "y", "x", "y"], Context::stack_tuck),
        
        ("@parse-fixnum", &["str", "--", "n/?"], Context::parse_fixnum),
        ("@parse-float", &["str", "--", "n/?"], Context::parse_float),
        
        ("@r>", &["x", "--"], Context::data_retain),
        ("<r@", &["--", "x"], Context::retain_data),

        ("array-nth", &["n", "array", "--", "x"], Context::array_nth),
        ("array-set-nth", &["x", "n", "array", "--"], Context::array_set_nth),
        ("get-slot", &["n", "object", "--", "x"], Context::object_nth),
        ("set-slot", &["x", "n", "object", "--"], Context::object_set_nth),
        ("object>ptr", &["obj", "--", "ptr"], Context::object_to_pointer),
        ("ptr>object", &["ptr", "--", "obj"], Context::pointer_to_object),
        ("ptr@>object", &["ptr", "T", "--", "obj"], Context::pointer_to_object_special),
        ("(call)", &["..a", "q", "--", "..b"], Context::quotation_call),
        ("if", &["..a", "[..a ..b]", "[..a ..b]", "?", "--", "..b"], Context::stack_tuck),


        ("fixnum+", &["x", "y", "--", "z"], Context::fixnum_add),
        ("fixnum-", &["x", "y", "--", "z"], Context::fixnum_sub),
        ("fixnum*", &["x", "y", "--", "z"], Context::fixnum_mul),
        ("fixnum/", &["x", "y", "--", "z"], Context::fixnum_div),
        ("fixnum%", &["x", "y", "--", "z"], Context::fixnum_mod),
        ("-fixnum", &["n", "--", "-n"], Context::fixnum_neg),
        ("fixnum&", &["x", "y", "--", "z"], Context::fixnum_and),
        ("fixnum|", &["x", "y", "--", "z"], Context::fixnum_or), 
        ("fixnum^", &["x", "y", "--", "z"], Context::fixnum_xor),
        ("fixnum!", &["x", "--", "y"], Context::fixnum_not),
        ("fixnum<<", &["x", "n", "--", "y"], Context::fixnum_shift_left),
        ("fixnum>>", &["x", "n", "--", "y"], Context::fixnum_shift_right),
        ("fixnum<~", &["x", "n", "--", "y"], Context::fixnum_rotate_left),
        ("fixnum~>", &["x", "n", "--", "y"], Context::fixnum_rotate_right),
        ("fixnum=", &["x", "y", "--", "?"], Context::fixnum_eq),
        ("fixnum<>", &["x", "y", "--", "?"], Context::fixnum_neq),
        ("fixnum<", &["x", "y", "--", "?"], Context::fixnum_lt),
        ("fixnum>", &["x", "y", "--", "?"], Context::fixnum_gt),
        ("fixnum<=", &["x", "y", "--", "?"], Context::fixnum_lte),
        ("fixnum>=", &["x", "y", "--", "?"], Context::fixnum_gte),

        ("float+", &["x", "y", "--", "z"], Context::float_add),
        ("float-", &["x", "y", "--", "z"], Context::float_sub),
        ("float*", &["x", "y", "--", "z"], Context::float_mul),
        ("float/", &["x", "y", "--", "z"], Context::float_div),
        ("-float", &["x", "--", "-x"], Context::float_neg),
        ("float=", &["x", "y", "--", "?"], Context::float_eq),
        ("float<>", &["x", "y", "--", "?"], Context::float_neq),
        ("float<", &["x", "y", "--", "?"], Context::float_lt),
        ("float>", &["x", "y", "--", "?"], Context::float_gt),
        ("float<=", &["x", "y", "--", "?"], Context::float_lte),
        ("float>=", &["x", "y", "--", "?"], Context::float_gte),
        ("float=~", &["x", "y", "e", "--", "?"], Context::float_eq_epsilon),
        ("float<>~", &["x", "y", "e", "--", "?"], Context::float_neq_epsilon),
        ("float=~0", &["x", "e", "--", "?"], Context::float_near_zero),

        ("fixnum>bytes-utf8", &["n", "", "utf8"], Context::fixnum_to_string),
        ("print-bytes-utf8", &["utf8", "--"], Context::bytearray_print_utf8),
        ("println-bytes-utf8", &["utf8", "--"], Context::bytearray_println_utf8),
        ("<array>", &["n", "obj", "--", "array"], Context::create_array),
        ("<bytearray>", &["n", "--", "bytearray"], Context::create_bytearray),
        ("resize-array", &["n", "array", "--", "new"], Context::resize_array),
        ("resize-bytearray", &["n", "bytearray", "--", "new"], Context::resize_bytearray),
        ("array-copy", &["src", "dst", "src-offset", "dst-offset", "n", "--"], Context::array_copy),
        ("bytearray-copy", &["src", "dst", "src-offset", "dst-offset", "n", "--"], Context::bytearray_copy),
        ("set-alien-u8", &["value", "offset", "dest", "--"], Context::set_alien_u8),
        ("set-alien-u16", &["value", "offset", "dest", "--"], Context::set_alien_u16),
        ("set-alien-u32", &["value", "offset", "dest", "--"], Context::set_alien_u32),
        ("set-alien-u64", &["value", "offset", "dest", "--"], Context::set_alien_u64),
        ("alien-u8", &["offset", "src", "--", "value"], Context::alien_u8),
        ("alien-u16", &["offset", "src", "--", "value"], Context::alien_u16),
        ("alien-u32", &["offset", "src", "--", "value"], Context::alien_u32),
        ("alien-u64", &["offset", "src", "--", "value"], Context::alien_u64),
        ("fixnum>alien-u8", &["n", "--", "bytes"], Context::fixnum_to_alien_u8),
        ("fixnum>alien-u16", &["n", "--", "bytes"], Context::fixnum_to_alien_u16),
        ("fixnum>alien-u32", &["n", "--", "bytes"], Context::fixnum_to_alien_u32),
        ("fixnum>alien-u64", &["n", "--", "bytes"], Context::fixnum_to_alien_u64),
        ("alien-u8>fixnum", &["bytes", "--", "n"], Context::alien_u8_to_fixnum),
        ("alien-u16>fixnum", &["bytes", "--", "n"], Context::alien_u16_to_fixnum),
        ("alien-u32>fixnum", &["bytes", "--", "n"], Context::alien_u32_to_fixnum),
        ("alien-u64>fixnum", &["bytes", "--", "n"], Context::alien_u64_to_fixnum),
    ];

    for (name, stack_effect, fp) in words {
        let word = primitive_word(ctx, name, stack_effect, *fp);
    }
}

impl Context {
    // -- HELPERS
    fn push_fixnum(&mut self, num: i64) {
        let obj = ObjectRef::from_int(num);
        self.push(obj);
    }

    fn pop_fixnum(&mut self) -> i64 {
        let obj = self.pop();
        let num = unsafe { obj.as_int_unchecked() };
        num
    }

    fn pop_2fixnum(&mut self) -> (i64, i64) {
        let obj_y = self.pop();
        let obj_x = self.pop();
        let x = unsafe { obj_x.as_int_unchecked() };
        let y = unsafe { obj_y.as_int_unchecked() };
        (x, y)
    }

    fn push_float(&mut self, num: f64) {
        let float_ptr = unsafe { self.gc.allocate_float(num) };
        let obj = ObjectRef::from_float_ptr(float_ptr);
        self.push(obj);
    }

    fn pop_float(&mut self) -> f64 {
        let obj = self.pop();
        unsafe { (*obj.as_float_ptr().unwrap()).float }
    }

    fn pop_2float(&mut self) -> (f64, f64) {
        let y = self.pop_float();
        let x = self.pop_float();
        (x, y)
    }

    fn push_bool(&mut self, cond: bool) {
        if cond {
            self.push(self.gc.specials.true_object);
        } else {
            self.push(SpecialObjects::get_false());
        }
    }

    fn pop_bool(&mut self) -> bool {
        let obj = self.pop();
        obj != SpecialObjects::get_false()
    }

    // -- STACK
    fn stack_drop(&mut self) {
        let _ = self.pop();
    }

    fn stack_dup(&mut self) {
        let x = self.data.nth(0);
        self.push(x);
    }

    fn stack_over(&mut self) {
        let x = self.data.nth(1);
        self.push(x);
    }

    fn stack_swap(&mut self) {
        let y = self.data.nth(0);
        let x = self.data.nth(1);
        self.data.set_nth(1, y);
        self.data.set_nth(0, x);
    }

    fn stack_pick(&mut self) {
        let value = self.data.nth(2);
        self.push(value);
    }

    fn stack_n_pick(&mut self) {
        let idx = self.pop_fixnum() as usize;
        let value = self.data.nth(idx);
        self.push(value);
    }

    fn stack_2dup(&mut self) {
        let y = self.data.nth(0);
        let x = self.data.nth(1);
        self.push(x);
        self.push(y);
    }

    fn stack_2drop(&mut self) {
        self.stack_drop();
        self.stack_drop();
    }

    fn stack_rot(&mut self) {
        let z = self.data.nth(0);
        let y = self.data.nth(1);
        let x = self.data.nth(2);
        self.data.set_nth(2, y);
        self.data.set_nth(1, z);
        self.data.set_nth(0, x);
    }

    fn stack_neg_rot(&mut self) {
        let z = self.data.nth(0);
        let y = self.data.nth(1);
        let x = self.data.nth(2);
        self.data.set_nth(0, z);
        self.data.set_nth(1, x);
        self.data.set_nth(2, y);
    }

    fn stack_swapd(&mut self) {
        let y = self.data.nth(1);
        let x = self.data.nth(2);
        self.data.set_nth(2, y);
        self.data.set_nth(1, x);
    }

    fn stack_dropd(&mut self) {
        let y = self.pop();
        self.stack_drop();
        self.stack_drop();
        self.push(y);
    }

    fn stack_tuck(&mut self) {
        let y = self.data.nth(0);
        let x = self.data.nth(1);
        self.data.set_nth(1, y);
        self.data.set_nth(0, x);
        self.push(y);
    }

    fn stack_clear(&mut self) {
        let current = self.data.current;
        let start = self.data.start;

        let count = unsafe { current.offset_from(start) } as usize;

        unsafe {
            std::ptr::write_bytes(start, 0, count);
        }

        self.data.current = self.data.start;
    }

    fn stack_2over(&mut self) {
        let b = self.data.nth(2);
        let a = self.data.nth(3);
        self.push(a);
        self.push(b);
    }

    fn stack_2swap(&mut self) {
        let d = self.data.nth(0);
        let c = self.data.nth(1);
        let b = self.data.nth(2);
        let a = self.data.nth(3);

        self.data.set_nth(3, c);
        self.data.set_nth(2, d);
        self.data.set_nth(1, a);
        self.data.set_nth(0, b);
    }

    // -- PARSING
    fn parse_fixnum(&mut self) {
        let obj = self.pop();
        let bytearray = unsafe { obj.as_bytearray_ptr_unchecked() };
        let bytes = unsafe { (*bytearray).as_bytes() };

        if let Ok(s) = std::str::from_utf8(bytes) {
            if s.is_empty() {
                self.push(SpecialObjects::get_false());
                return;
            }

            if !s.chars().next().unwrap().is_ascii_digit() {
                self.push(SpecialObjects::get_false());
                return;
            }

            match s.parse::<i64>() {
                Ok(num) => {
                    self.push_fixnum(num);
                }
                Err(_) => {
                    self.push(SpecialObjects::get_false());
                }
            }
        } else {
            self.push(SpecialObjects::get_false());
        }
    }

    fn parse_float(&mut self) {
        let obj = self.pop();
        let bytearray = unsafe { obj.as_bytearray_ptr_unchecked() };
        let bytes = unsafe { (*bytearray).as_bytes() };

        if let Ok(s) = std::str::from_utf8(bytes) {
            let s = s.trim();

            if s.is_empty() {
                self.push(SpecialObjects::get_false());
                return;
            }

            if !s.chars().next().unwrap().is_ascii_digit() {
                self.push(SpecialObjects::get_false());
                return;
            }

            match s.parse::<f64>() {
                Ok(num) => {
                    self.push_float(num);
                }
                Err(_) => {
                    self.push(SpecialObjects::get_false());
                }
            }
        } else {
            self.push(SpecialObjects::get_false());
        }
    }

    // -- GENERAL
    fn array_nth(&mut self) {
        let array_obj = self.pop();
        let idx = self.pop_fixnum() as usize;

        if let Some(array_ptr) = array_obj.as_array_ptr() {
            unsafe {
                let array = &*array_ptr;
                if let Some(value) = array.get_element(idx) {
                    self.push(value);
                    return;
                }
            }
        }

        self.push(SpecialObjects::get_false());
    }

    fn array_set_nth(&mut self) {
        let array_obj = self.pop();
        let idx = self.pop_fixnum() as usize;
        let value = self.pop();

        if let Some(array_ptr) = array_obj.as_array_ptr() {
            unsafe {
                let array = &*array_ptr;
                if array.set_element(idx, value) {
                    return;
                }
            }
        }

        self.push(SpecialObjects::get_false());
    }

    fn object_nth(&mut self) {
        let obj = self.pop();
        let idx = self.pop_fixnum() as usize;

        if let Some(ptr) = obj.as_ptr() {
            unsafe {
                let object = &*ptr;
                if let Some(value) = object.get_slot_value(idx) {
                    self.push(value);
                    return;
                }
            }
        }

        self.push(SpecialObjects::get_false());
    }

    fn object_set_nth(&mut self) {
        let obj = self.pop();
        let idx = self.pop_fixnum() as usize;
        let value = self.pop();

        if let Some(ptr) = obj.as_ptr() {
            unsafe {
                let object = &mut *ptr;
                object.set_slot_value(idx, value);
                return;
            }
        }

        self.push(SpecialObjects::get_false());
    }
    fn object_to_pointer(&mut self) {
        let obj = self.pop();
        let ptr = unsafe { obj.as_ptr_unchecked() };
        let ptr_num = ptr as i64;
        self.push_fixnum(ptr_num);
    }

    fn pointer_to_object(&mut self) {
        let ptr_num = self.pop_fixnum();
        let ptr = ptr_num as *mut Object;
        let obj = ObjectRef::from_ptr(ptr);
        self.push(obj);
    }

    fn pointer_to_object_special(&mut self) {
        let ty_num = self.pop_fixnum();
        let ptr_num = self.pop_fixnum();
        let ty = ObjectType::from(ty_num as u64);
        let ptr = ptr_num as *mut Object;
        let obj = ObjectRef::from_typed_ptr(ptr, ty);
        self.push(obj);
    }

    fn quotation_call(&mut self) {
        let quotation_obj = self.pop();
        let quotation = quotation_obj.as_quotation_ptr().unwrap();
        let body = unsafe { (*quotation).body.as_array_ptr().unwrap() };
    }

    fn call_if(&mut self) {
        let cond = self.pop_bool();
        let false_branch = self.pop();
        let true_branch = self.pop();
        if cond {
            let quot = true_branch.as_quotation_ptr().unwrap();
            self.execute(quot);
        } else {
            let quot = false_branch.as_quotation_ptr().unwrap();
            self.execute(quot);
        }
    }

    // -- FIXNUM
    fn fixnum_add(&mut self) {
        let (x, y) = self.pop_2fixnum();
        let z = x + y;
        self.push_fixnum(z);
    }

    fn fixnum_sub(&mut self) {
        let (x, y) = self.pop_2fixnum();
        let z = x - y;
        self.push_fixnum(z);
    }

    fn fixnum_mul(&mut self) {
        let (x, y) = self.pop_2fixnum();
        let z = x * y;
        self.push_fixnum(z);
    }

    fn fixnum_div(&mut self) {
        let (x, y) = self.pop_2fixnum();
        if y == 0 {
            self.push(ObjectRef::null());
        } else {
            let z = x / y;
            self.push_fixnum(z);
        }
    }

    fn fixnum_mod(&mut self) {
        let (x, y) = self.pop_2fixnum();
        if y == 0 {
            self.push(ObjectRef::null());
        } else {
            let z = x % y;
            self.push_fixnum(z);
        }
    }

    fn fixnum_neg(&mut self) {
        let obj = self.pop();
        let x = unsafe { obj.as_int_unchecked() };
        self.push(ObjectRef::from_int(-x));
    }

    fn fixnum_and(&mut self) {
        let (x, y) = self.pop_2fixnum();
        self.push_fixnum(x & y);
    }

    fn fixnum_or(&mut self) {
        let (x, y) = self.pop_2fixnum();
        self.push_fixnum(x | y);
    }

    fn fixnum_xor(&mut self) {
        let (x, y) = self.pop_2fixnum();
        self.push_fixnum(x ^ y);
    }

    fn fixnum_not(&mut self) {
        let x = self.pop_fixnum();
        self.push_fixnum(!x);
    }

    fn fixnum_shift_left(&mut self) {
        let (x, shift) = self.pop_2fixnum();
        self.push_fixnum(x << shift);
    }

    fn fixnum_shift_right(&mut self) {
        let (x, shift) = self.pop_2fixnum();
        self.push_fixnum(x >> shift);
    }

    fn fixnum_rotate_left(&mut self) {
        let (x, shift) = self.pop_2fixnum();
        self.push_fixnum(x.rotate_left(shift as u32));
    }

    fn fixnum_rotate_right(&mut self) {
        let (x, shift) = self.pop_2fixnum();
        self.push_fixnum(x.rotate_right(shift as u32));
    }

    fn fixnum_eq(&mut self) {
        let (x, y) = self.pop_2fixnum();
        let res = x == y;
        self.push_bool(res);
    }

    fn fixnum_neq(&mut self) {
        let (x, y) = self.pop_2fixnum();
        let res = x != y;
        self.push_bool(res);
    }

    fn fixnum_lt(&mut self) {
        let (x, y) = self.pop_2fixnum();
        let res = x < y;
        self.push_bool(res);
    }

    fn fixnum_gt(&mut self) {
        let (x, y) = self.pop_2fixnum();
        let res = x > y;
        self.push_bool(res);
    }

    fn fixnum_lte(&mut self) {
        let (x, y) = self.pop_2fixnum();
        let res = x <= y;
        self.push_bool(res);
    }

    fn fixnum_gte(&mut self) {
        let (x, y) = self.pop_2fixnum();
        let res = x >= y;
        self.push_bool(res);
    }

    // -- FLOAT
    fn float_add(&mut self) {
        let (x, y) = self.pop_2float();
        let z = x + y;
        self.push_float(z);
    }

    fn float_sub(&mut self) {
        let (x, y) = self.pop_2float();
        let z = x - y;
        self.push_float(z);
    }

    fn float_mul(&mut self) {
        let (x, y) = self.pop_2float();
        let z = x * y;
        self.push_float(z);
    }

    fn float_div(&mut self) {
        let (x, y) = self.pop_2float();
        if y == 0.0 {
            self.push(ObjectRef::null());
        } else {
            let z = x / y;
            self.push_float(z);
        }
    }

    fn float_neg(&mut self) {
        let x = self.pop_float();
        self.push_float(-x);
    }

    fn float_eq(&mut self) {
        let (x, y) = self.pop_2float();
        let res = x == y;
        self.push_bool(res);
    }

    fn float_neq(&mut self) {
        let (x, y) = self.pop_2float();
        let res = x != y;
        self.push_bool(res);
    }

    fn float_lt(&mut self) {
        let (x, y) = self.pop_2float();
        let res = x < y;
        self.push_bool(res);
    }

    fn float_gt(&mut self) {
        let (x, y) = self.pop_2float();
        let res = x > y;
        self.push_bool(res);
    }

    fn float_lte(&mut self) {
        let (x, y) = self.pop_2float();
        let res = x <= y;
        self.push_bool(res);
    }

    fn float_gte(&mut self) {
        let (x, y) = self.pop_2float();
        let res = x >= y;
        self.push_bool(res);
    }

    fn float_eq_epsilon(&mut self) {
        let epsilon = self.pop_float();
        let (x, y) = self.pop_2float();
        let res = (x - y).abs() <= epsilon;
        self.push_bool(res);
    }

    fn float_neq_epsilon(&mut self) {
        let epsilon = self.pop_float();
        let (x, y) = self.pop_2float();
        let res = (x - y).abs() > epsilon;
        self.push_bool(res);
    }

    fn float_near_zero(&mut self) {
        let epsilon = self.pop_float();
        let x = self.pop_float();
        self.push_bool(x.abs() <= epsilon);
    }

    // -- ARRAYS
    fn fixnum_to_string(&mut self) {
        let num = self.pop_fixnum();
        let bytearray = unsafe { self.gc.allocate_string(&format!("{}", num)) };
        self.push(bytearray.into());
    }

    fn bytearray_print_utf8(&mut self) {
        let obj = self.pop();
        let bytearray = unsafe { obj.as_bytearray_ptr_unchecked() };
        let s = unsafe { (*bytearray).as_str().unwrap() };
        print!("{}", s);
    }

    fn bytearray_println_utf8(&mut self) {
        let obj = self.pop();
        let bytearray = unsafe { obj.as_bytearray_ptr_unchecked() };
        let s = unsafe { (*bytearray).as_str().unwrap() };
        println!("{}", s);
    }

    fn create_bytearray(&mut self) {
        let size = self.pop_fixnum();
        let bytearray = unsafe { self.gc.allocate_bytearray(size as usize) };
        self.push(bytearray.into());
    }

    fn create_array(&mut self) {
        let size = self.pop_fixnum();
        let array = unsafe { self.gc.allocate_array(size as usize) };
        self.push(array.into());
    }

    fn resize_bytearray(&mut self) {
        let obj = self.pop();
        let new_size = self.pop_fixnum() as usize;

        let old_bytearray = unsafe { obj.as_bytearray_ptr_unchecked() };
        let old_size = unsafe { (*old_bytearray).size };

        let new_bytearray = unsafe { self.gc.allocate_bytearray(new_size) };

        let copy_size = std::cmp::min(old_size, new_size);
        unsafe {
            let src = (old_bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            let dst = (new_bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            std::ptr::copy_nonoverlapping(src, dst, copy_size);
        }

        self.push(ObjectRef::from_bytearray_ptr(new_bytearray));
    }

    fn resize_array(&mut self) {
        let obj = self.pop();
        let new_size = self.pop_fixnum() as usize;

        let old_array = unsafe { obj.as_array_ptr_unchecked() };
        let old_size = unsafe { (*old_array).size.as_int_unchecked() as usize };

        let new_array = unsafe { self.gc.allocate_array(new_size) };

        let copy_size = std::cmp::min(old_size, new_size);
        unsafe {
            let src = (old_array as *mut u8).add(std::mem::size_of::<Array>());
            let dst = (new_array as *mut u8).add(std::mem::size_of::<Array>());
            std::ptr::copy_nonoverlapping(src, dst, copy_size * std::mem::size_of::<ObjectRef>());
        }

        self.push(ObjectRef::from_array_ptr(new_array));
    }

    fn array_copy(&mut self) {
        let size = self.pop_fixnum() as usize;
        let dst_offset = self.pop_fixnum() as usize;
        let src_offset = self.pop_fixnum() as usize;
        let dst_obj = self.pop();
        let src_obj = self.pop();

        unsafe {
            let src_array = src_obj.as_array_ptr_unchecked();
            let dst_array = dst_obj.as_array_ptr_unchecked();

            let src_ptr = (src_array as *mut u8)
                .add(std::mem::size_of::<Array>())
                .add(src_offset * std::mem::size_of::<ObjectRef>());
            let dst_ptr = (dst_array as *mut u8)
                .add(std::mem::size_of::<Array>())
                .add(dst_offset * std::mem::size_of::<ObjectRef>());

            std::ptr::copy(src_ptr, dst_ptr, size * std::mem::size_of::<ObjectRef>());
        }
    }

    fn bytearray_copy(&mut self) {
        let size = self.pop_fixnum() as usize;
        let dst_offset = self.pop_fixnum() as usize;
        let src_offset = self.pop_fixnum() as usize;
        let dst_obj = self.pop();
        let src_obj = self.pop();

        unsafe {
            let src_array = src_obj.as_bytearray_ptr_unchecked();
            let dst_array = dst_obj.as_bytearray_ptr_unchecked();

            let src_ptr = (src_array as *mut u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(src_offset);
            let dst_ptr = (dst_array as *mut u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(dst_offset);

            std::ptr::copy(src_ptr, dst_ptr, size);
        }
    }

    fn set_alien_u8(&mut self) {
        let dest_obj = self.pop();
        let offset = self.pop_fixnum() as usize;
        let value_obj = self.pop();

        unsafe {
            let dest = dest_obj.as_bytearray_ptr_unchecked();
            let value = value_obj.as_bytearray_ptr_unchecked();

            // Verify value size is 1 byte
            if (*value).size != 1 {
                self.push(ObjectRef::null());
                return;
            }

            let value_ptr = (value as *mut u8).add(std::mem::size_of::<ByteArray>());
            let dest_ptr = (dest as *mut u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(offset);

            std::ptr::copy_nonoverlapping(value_ptr, dest_ptr, 1);
        }
    }

    fn set_alien_u16(&mut self) {
        let dest_obj = self.pop();
        let offset = self.pop_fixnum() as usize;
        let value_obj = self.pop();

        unsafe {
            let dest = dest_obj.as_bytearray_ptr_unchecked();
            let value = value_obj.as_bytearray_ptr_unchecked();

            if (*value).size != 2 {
                self.push(ObjectRef::null());
                return;
            }

            let value_ptr = (value as *mut u8).add(std::mem::size_of::<ByteArray>());
            let dest_ptr = (dest as *mut u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(offset);

            std::ptr::copy_nonoverlapping(value_ptr, dest_ptr, 2);
        }
    }

    fn set_alien_u32(&mut self) {
        let dest_obj = self.pop();
        let offset = self.pop_fixnum() as usize;
        let value_obj = self.pop();

        unsafe {
            let dest = dest_obj.as_bytearray_ptr_unchecked();
            let value = value_obj.as_bytearray_ptr_unchecked();

            // Verify value size is 4 bytes
            if (*value).size != 4 {
                self.push(ObjectRef::null());
                return;
            }

            let value_ptr = (value as *mut u8).add(std::mem::size_of::<ByteArray>());
            let dest_ptr = (dest as *mut u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(offset);

            std::ptr::copy_nonoverlapping(value_ptr, dest_ptr, 4);
        }
    }

    fn set_alien_u64(&mut self) {
        let dest_obj = self.pop();
        let offset = self.pop_fixnum() as usize;
        let value_obj = self.pop();

        unsafe {
            let dest = dest_obj.as_bytearray_ptr_unchecked();
            let value = value_obj.as_bytearray_ptr_unchecked();

            // Verify value size is 8 bytes
            if (*value).size != 8 {
                self.push(ObjectRef::null());
                return;
            }

            let value_ptr = (value as *mut u8).add(std::mem::size_of::<ByteArray>());
            let dest_ptr = (dest as *mut u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(offset);

            std::ptr::copy_nonoverlapping(value_ptr, dest_ptr, 8);
        }
    }

    fn alien_u8(&mut self) {
        let src_obj = self.pop();
        let offset = self.pop_fixnum() as usize;

        unsafe {
            let src = src_obj.as_bytearray_ptr_unchecked();
            let new_array = self.gc.allocate_bytearray(1);

            let src_ptr = (src as *mut u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(offset);
            let dst_ptr = (new_array as *mut u8).add(std::mem::size_of::<ByteArray>());

            std::ptr::copy_nonoverlapping(src_ptr, dst_ptr, 1);

            self.push(ObjectRef::from_bytearray_ptr(new_array));
        }
    }

    fn alien_u16(&mut self) {
        let src_obj = self.pop();
        let offset = self.pop_fixnum() as usize;

        unsafe {
            let src = src_obj.as_bytearray_ptr_unchecked();
            let new_array = self.gc.allocate_bytearray(2);

            let src_ptr = (src as *mut u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(offset);
            let dst_ptr = (new_array as *mut u8).add(std::mem::size_of::<ByteArray>());

            std::ptr::copy_nonoverlapping(src_ptr, dst_ptr, 2);

            self.push(ObjectRef::from_bytearray_ptr(new_array));
        }
    }

    fn alien_u32(&mut self) {
        let src_obj = self.pop();
        let offset = self.pop_fixnum() as usize;

        unsafe {
            let src = src_obj.as_bytearray_ptr_unchecked();
            let new_array = self.gc.allocate_bytearray(4);

            let src_ptr = (src as *mut u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(offset);
            let dst_ptr = (new_array as *mut u8).add(std::mem::size_of::<ByteArray>());

            std::ptr::copy_nonoverlapping(src_ptr, dst_ptr, 4);

            self.push(ObjectRef::from_bytearray_ptr(new_array));
        }
    }

    fn alien_u64(&mut self) {
        let src_obj = self.pop();
        let offset = self.pop_fixnum() as usize;

        unsafe {
            let src = src_obj.as_bytearray_ptr_unchecked();
            let new_array = self.gc.allocate_bytearray(8);

            let src_ptr = (src as *mut u8)
                .add(std::mem::size_of::<ByteArray>())
                .add(offset);
            let dst_ptr = (new_array as *mut u8).add(std::mem::size_of::<ByteArray>());

            std::ptr::copy_nonoverlapping(src_ptr, dst_ptr, 8);

            self.push(ObjectRef::from_bytearray_ptr(new_array));
        }
    }

    fn fixnum_to_alien_u8(&mut self) {
        let num = self.pop_fixnum() as u8;
        let bytearray = unsafe { self.gc.allocate_bytearray(1) };
        unsafe {
            let ptr = (bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            *ptr = num;
        }
        self.push(ObjectRef::from_bytearray_ptr(bytearray));
    }

    fn alien_u8_to_fixnum(&mut self) {
        let obj = self.pop();
        let value = unsafe {
            let bytearray = obj.as_bytearray_ptr_unchecked();
            let ptr = (bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            *ptr as i64
        };
        self.push_fixnum(value);
    }

    fn fixnum_to_alien_u16(&mut self) {
        let num = self.pop_fixnum() as u16;
        let bytearray = unsafe { self.gc.allocate_bytearray(2) };
        unsafe {
            let ptr = (bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            *(ptr as *mut u16) = num;
        }
        self.push(ObjectRef::from_bytearray_ptr(bytearray));
    }

    fn alien_u16_to_fixnum(&mut self) {
        let obj = self.pop();
        let value = unsafe {
            let bytearray = obj.as_bytearray_ptr_unchecked();
            let ptr = (bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            *(ptr as *const u16) as i64
        };
        self.push_fixnum(value);
    }

    fn fixnum_to_alien_u32(&mut self) {
        let num = self.pop_fixnum() as u32;
        let bytearray = unsafe { self.gc.allocate_bytearray(4) };
        unsafe {
            let ptr = (bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            *(ptr as *mut u32) = num;
        }
        self.push(ObjectRef::from_bytearray_ptr(bytearray));
    }

    fn alien_u32_to_fixnum(&mut self) {
        let obj = self.pop();
        let value = unsafe {
            let bytearray = obj.as_bytearray_ptr_unchecked();
            let ptr = (bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            *(ptr as *const u32) as i64
        };
        self.push_fixnum(value);
    }

    fn fixnum_to_alien_u64(&mut self) {
        let num = self.pop_fixnum() as u64;
        let bytearray = unsafe { self.gc.allocate_bytearray(8) };
        unsafe {
            let ptr = (bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            *(ptr as *mut u64) = num;
        }
        self.push(ObjectRef::from_bytearray_ptr(bytearray));
    }

    fn alien_u64_to_fixnum(&mut self) {
        let obj = self.pop();
        let value = unsafe {
            let bytearray = obj.as_bytearray_ptr_unchecked();
            let ptr = (bytearray as *mut u8).add(std::mem::size_of::<ByteArray>());
            *(ptr as *const u64) as i64
        };
        self.push_fixnum(value);
    }
}

fn primitive_word(
    ctx: &mut Context,
    name: &str,
    _stack_effect: &[&str],
    fp: fn(&mut Context),
) -> ObjectRef {
    let body = ObjectRef::from_int(fp as i64);

    let name = unsafe { ctx.gc.allocate_string(name) };
    let word = unsafe { ctx.gc.allocate_word(None, true) };
    unsafe { (*word).name = name.into() };
    unsafe { (*word).body = body }
    let flags = unsafe { (*word).flags.as_array_ptr().unwrap() };
    unsafe { (*flags).set_element(0, SpecialObjects::word_primitive()) };

    ObjectRef::from_word_ptr(word)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::ContextConfig;

    fn create_test_context() -> Context {
        let config = ContextConfig {
            datastack_size: 512,
            retainstack_size: 512,
        };
        Context::new(&config)
    }

    #[test]
    fn test_resize_bytearray() {
        let mut ctx = create_test_context();
        unsafe {
            let initial = ctx.gc.allocate_bytearray(5);
            (*initial).set_element(0, b'h');
            (*initial).set_element(1, b'e');
            (*initial).set_element(2, b'l');
            (*initial).set_element(3, b'l');
            (*initial).set_element(4, b'o');

            ctx.push_fixnum(3);
            ctx.push(ObjectRef::from_bytearray_ptr(initial));

            ctx.resize_bytearray();

            let result = ctx.pop();
            let new_array = result.as_bytearray_ptr().unwrap();
            assert_eq!((*new_array).size, 3);
            assert_eq!((*new_array).get_element(0), Some(b'h'));
            assert_eq!((*new_array).get_element(1), Some(b'e'));
            assert_eq!((*new_array).get_element(2), Some(b'l'));

            ctx.push_fixnum(7);
            ctx.push(result);
            ctx.resize_bytearray();

            let expanded = ctx.pop().as_bytearray_ptr().unwrap();
            assert_eq!((*expanded).size, 7);
            assert_eq!((*expanded).get_element(0), Some(b'h'));
            assert_eq!((*expanded).get_element(1), Some(b'e'));
            assert_eq!((*expanded).get_element(2), Some(b'l'));
        }
    }

    #[test]
    fn test_resize_array() {
        let mut ctx = create_test_context();
        unsafe {
            let initial = ctx.gc.allocate_array(4);
            (*initial).set_element(0, ObjectRef::from_int(1));
            (*initial).set_element(1, ObjectRef::from_int(2));
            (*initial).set_element(2, ObjectRef::from_int(3));
            (*initial).set_element(3, ObjectRef::from_int(4));

            ctx.push_fixnum(2);
            ctx.push(ObjectRef::from_array_ptr(initial));

            ctx.resize_array();

            let result = ctx.pop();
            let new_array = result.as_array_ptr().unwrap();
            assert_eq!((*new_array).size.as_int_unchecked(), 2);
            assert_eq!((*new_array).get_element(0), Some(ObjectRef::from_int(1)));
            assert_eq!((*new_array).get_element(1), Some(ObjectRef::from_int(2)));

            ctx.push_fixnum(6);
            ctx.push(result);
            ctx.resize_array();

            let expanded = ctx.pop().as_array_ptr().unwrap();
            assert_eq!((*expanded).size.as_int_unchecked(), 6);
            assert_eq!((*expanded).get_element(0), Some(ObjectRef::from_int(1)));
            assert_eq!((*expanded).get_element(1), Some(ObjectRef::from_int(2)));
        }
    }

    #[test]
    fn test_array_copy() {
        let mut ctx = create_test_context();
        unsafe {
            let src = ctx.gc.allocate_array(5);
            for i in 0..5 {
                (*src).set_element(i, ObjectRef::from_int(i as i64));
            }

            let dst = ctx.gc.allocate_array(5);

            ctx.push(ObjectRef::from_array_ptr(src));
            ctx.push(ObjectRef::from_array_ptr(dst));
            ctx.push_fixnum(1); // src offset
            ctx.push_fixnum(2); // dst offset
            ctx.push_fixnum(2); // size

            ctx.array_copy();

            assert_eq!((*dst).get_element(2), Some(ObjectRef::from_int(1)));
            assert_eq!((*dst).get_element(3), Some(ObjectRef::from_int(2)));
        }
    }

    #[test]
    fn test_bytearray_copy() {
        let mut ctx = create_test_context();
        unsafe {
            let src = ctx.gc.allocate_string("hello world");

            let dst = ctx.gc.allocate_bytearray(11);

            ctx.push(ObjectRef::from_bytearray_ptr(src));
            ctx.push(ObjectRef::from_bytearray_ptr(dst));
            ctx.push_fixnum(6); // src offset
            ctx.push_fixnum(0); // dst offset
            ctx.push_fixnum(5); // size

            ctx.bytearray_copy();

            assert_eq!((*dst).get_element(0), Some(b'w'));
            assert_eq!((*dst).get_element(1), Some(b'o'));
            assert_eq!((*dst).get_element(2), Some(b'r'));
            assert_eq!((*dst).get_element(3), Some(b'l'));
            assert_eq!((*dst).get_element(4), Some(b'd'));
        }
    }

    #[test]
    fn test_fixnum_operations() {
        let mut ctx = create_test_context();

        ctx.push_fixnum(6);
        ctx.push_fixnum(7);
        ctx.fixnum_mul();
        assert_eq!(ctx.pop_fixnum(), 42);

        ctx.push_fixnum(42);
        ctx.push_fixnum(7);
        ctx.fixnum_div();
        assert_eq!(ctx.pop_fixnum(), 6);

        ctx.push_fixnum(42);
        ctx.push_fixnum(0);
        ctx.fixnum_div();
        assert!(ctx.pop().is_false());

        ctx.push_fixnum(42);
        ctx.push_fixnum(5);
        ctx.fixnum_mod();
        assert_eq!(ctx.pop_fixnum(), 2);

        ctx.push_fixnum(42);
        ctx.fixnum_neg();
        assert_eq!(ctx.pop_fixnum(), -42);

        ctx.push_fixnum(-42);
        ctx.fixnum_neg();
        assert_eq!(ctx.pop_fixnum(), 42);
    }

    #[test]
    fn test_pointer_conversions() {
        let mut ctx = create_test_context();

        unsafe {
            let array = ctx.gc.allocate_array(5);
            let array_ref = ObjectRef::from_array_ptr(array);

            ctx.push(array_ref);
            ctx.object_to_pointer();
            let ptr_num = ctx.pop_fixnum();
            assert_eq!(ptr_num as *mut Object, array as *mut Object);

            ctx.push_fixnum(ptr_num);
            ctx.pointer_to_object();
            let restored = ctx.pop();
            assert_eq!(restored.as_ptr(), Some(array as *mut Object));

            ctx.push_fixnum(ptr_num);
            ctx.push_fixnum(ObjectType::Array as i64);
            ctx.pointer_to_object_special();
            let special = ctx.pop();
            assert_eq!(special.get_type(), Some(ObjectType::Array));
            assert_eq!(special.as_ptr(), Some(array as *mut Object));
        }
    }

    #[test]
    fn test_stack_2over() {
        let mut ctx = create_test_context();

        ctx.push(ObjectRef::from_int(1)); // a
        ctx.push(ObjectRef::from_int(2)); // b
        ctx.push(ObjectRef::from_int(3)); // c
        ctx.push(ObjectRef::from_int(4)); // d

        ctx.stack_2over(); // Should add copy of a,b on top

        // Check result ( 1 2 3 4 1 2 )
        assert_eq!(ctx.data.nth(5).as_int(), Some(1)); // Bottom
        assert_eq!(ctx.data.nth(4).as_int(), Some(2));
        assert_eq!(ctx.data.nth(3).as_int(), Some(3));
        assert_eq!(ctx.data.nth(2).as_int(), Some(4));
        assert_eq!(ctx.data.nth(1).as_int(), Some(1));
        assert_eq!(ctx.data.nth(0).as_int(), Some(2)); // Top
    }

    #[test]
    fn test_stack_2swap() {
        let mut ctx = create_test_context();

        ctx.push(ObjectRef::from_int(1)); // a
        ctx.push(ObjectRef::from_int(2)); // b
        ctx.push(ObjectRef::from_int(3)); // c
        ctx.push(ObjectRef::from_int(4)); // d

        ctx.stack_2swap(); // Should swap pairs

        // Check result ( 3 4 1 2 )
        assert_eq!(ctx.data.nth(3).as_int(), Some(3)); // Bottom
        assert_eq!(ctx.data.nth(2).as_int(), Some(4));
        assert_eq!(ctx.data.nth(1).as_int(), Some(1));
        assert_eq!(ctx.data.nth(0).as_int(), Some(2)); // Top
    }

    #[test]
    fn test_stack_clear() {
        let mut ctx = create_test_context();

        unsafe {
            let bytearray = ctx.gc.allocate_string("test");
            ctx.push(ObjectRef::from_bytearray_ptr(bytearray));
            ctx.push(ObjectRef::from_int(42));
            ctx.push(ObjectRef::from_int(123));
        }

        ctx.stack_clear();

        assert!(ctx.data.current == ctx.data.start);

        unsafe {
            for i in 0..3 {
                assert_eq!(*ctx.data.start.add(i), ObjectRef::null());
            }
        }

        ctx.push(ObjectRef::from_int(999));
        assert_eq!(ctx.data.nth(0).as_int(), Some(999));
    }

    #[test]
    fn test_stack_2swap_with_heap_objects() {
        let mut ctx = create_test_context();

        unsafe {
            let str1 = ctx.gc.allocate_string("first");
            let str2 = ctx.gc.allocate_string("second");
            let str3 = ctx.gc.allocate_string("third");
            let str4 = ctx.gc.allocate_string("fourth");

            ctx.push(ObjectRef::from_bytearray_ptr(str1));
            ctx.push(ObjectRef::from_bytearray_ptr(str2));
            ctx.push(ObjectRef::from_bytearray_ptr(str3));
            ctx.push(ObjectRef::from_bytearray_ptr(str4));

            ctx.stack_2swap();

            let top = ctx.pop().as_bytearray_ptr().unwrap();
            let second = ctx.pop().as_bytearray_ptr().unwrap();
            let third = ctx.pop().as_bytearray_ptr().unwrap();
            let fourth = ctx.pop().as_bytearray_ptr().unwrap();

            assert_eq!((*top).as_str(), Some("second"));
            assert_eq!((*second).as_str(), Some("first"));
            assert_eq!((*third).as_str(), Some("fourth"));
            assert_eq!((*fourth).as_str(), Some("third"));
        }
    }

    #[test]
    fn test_stack_pick() {
        let mut ctx = create_test_context();

        ctx.push(ObjectRef::from_int(1));
        ctx.push(ObjectRef::from_int(2));
        ctx.push(ObjectRef::from_int(3));

        ctx.stack_pick();

        assert_eq!(ctx.data.nth(3).as_int(), Some(1));
        assert_eq!(ctx.data.nth(2).as_int(), Some(2));
        assert_eq!(ctx.data.nth(1).as_int(), Some(3));
        assert_eq!(ctx.data.nth(0).as_int(), Some(1));
    }

    #[test]
    fn test_stack_n_pick() {
        let mut ctx = create_test_context();

        ctx.push(ObjectRef::from_int(10));
        ctx.push(ObjectRef::from_int(20));
        ctx.push(ObjectRef::from_int(30));
        ctx.push(ObjectRef::from_int(40));
        ctx.push(ObjectRef::from_int(50));
        ctx.push_fixnum(4);

        ctx.stack_n_pick();

        assert_eq!(ctx.data.nth(5).as_int(), Some(10));
        assert_eq!(ctx.data.nth(4).as_int(), Some(20));
        assert_eq!(ctx.data.nth(3).as_int(), Some(30));
        assert_eq!(ctx.data.nth(2).as_int(), Some(40));
        assert_eq!(ctx.data.nth(1).as_int(), Some(50));
        assert_eq!(ctx.data.nth(0).as_int(), Some(10));
    }

    #[test]
    fn test_stack_tuck() {
        let mut ctx = create_test_context();

        ctx.push(ObjectRef::from_int(1));
        ctx.push(ObjectRef::from_int(2));

        ctx.stack_tuck();

        assert_eq!(ctx.data.nth(2).as_int(), Some(2));
        assert_eq!(ctx.data.nth(1).as_int(), Some(1));
        assert_eq!(ctx.data.nth(0).as_int(), Some(2));
    }

    #[test]
    fn test_float_operations() {
        let mut ctx = create_test_context();

        ctx.push_float(3.14);
        ctx.push_float(2.0);
        ctx.float_mul();

        let result = ctx.pop_float();
        assert!((result - 6.28).abs() < f64::EPSILON);

        ctx.push_float(1.0);
        ctx.push_float(0.0);
        ctx.float_div();
        assert!(ctx.pop().is_false());

        ctx.push_float(1.0);
        ctx.push_float(2.0);
        ctx.float_lt();
        assert!(ctx.pop_bool());
    }

    // #[test]
    // fn test_stack_dip() {
    //     let mut ctx = create_test_context();
    //
    //     unsafe {
    //         let quotation = ctx.gc.allocate_quotation(None);
    //         let body = ctx.gc.allocate_array(1);
    //         (*body).set_element(0, ObjectRef::from_int(1));
    //         (*quotation).body = ObjectRef::from_array_ptr(body);
    //
    //         ctx.push(ObjectRef::from_int(5));
    //         ctx.push(ObjectRef::from_int(10));
    //         ctx.push(ObjectRef::from_quotation_ptr(quotation));
    //
    //         ctx.stack_dip();
    //
    //         assert_eq!(ctx.data.nth(1).as_int(), Some(6));
    //         assert_eq!(ctx.data.nth(0).as_int(), Some(10));
    //     }
    // }

    #[test]
    fn test_byte_array_operations() {
        let mut ctx = create_test_context();

        unsafe {
            ctx.push_fixnum(5);
            ctx.create_bytearray();
            let array = ctx.pop();
            let bytearray = array.as_bytearray_ptr().unwrap();
            assert_eq!((*bytearray).size, 5);

            ctx.push_fixnum(10);
            ctx.push(array);
            ctx.resize_bytearray();
            let resized = ctx.pop().as_bytearray_ptr().unwrap();
            assert_eq!((*resized).size, 10);
        }
    }

    #[test]
    fn test_fixnum_bitwise_ops() {
        let mut ctx = create_test_context();

        ctx.push_fixnum(0b1100);
        ctx.push_fixnum(0b1010);
        ctx.fixnum_and();
        assert_eq!(ctx.pop_fixnum(), 0b1000);

        ctx.push_fixnum(0b1100);
        ctx.push_fixnum(0b1010);
        ctx.fixnum_or();
        assert_eq!(ctx.pop_fixnum(), 0b1110);

        ctx.push_fixnum(0b1100);
        ctx.push_fixnum(0b1010);
        ctx.fixnum_xor();
        assert_eq!(ctx.pop_fixnum(), 0b0110);

        ctx.push_fixnum(0b1100);
        ctx.fixnum_not();
        assert_eq!(ctx.pop_fixnum() & 0b1111, 0b0011);

        ctx.push_fixnum(0b1100);
        ctx.push_fixnum(2);
        ctx.fixnum_shift_left();
        assert_eq!(ctx.pop_fixnum(), 0b110000);

        ctx.push_fixnum(0b1100);
        ctx.push_fixnum(2);
        ctx.fixnum_shift_right();
        assert_eq!(ctx.pop_fixnum(), 0b0011);
    }

    #[test]
    fn test_parse_fixnum() {
        let mut ctx = create_test_context();

        unsafe {
            let valid = ctx.gc.allocate_string("123");
            ctx.push(ObjectRef::from_bytearray_ptr(valid));
            ctx.parse_fixnum();
            assert_eq!(ctx.pop_fixnum(), 123);

            let invalid = ctx.gc.allocate_string("abc");
            ctx.push(ObjectRef::from_bytearray_ptr(invalid));
            ctx.parse_fixnum();
            assert!(ctx.pop().is_false());

            let empty = ctx.gc.allocate_string("");
            ctx.push(ObjectRef::from_bytearray_ptr(empty));
            ctx.parse_fixnum();
            assert!(ctx.pop().is_false());

            let non_numeric = ctx.gc.allocate_string("-123");
            ctx.push(ObjectRef::from_bytearray_ptr(non_numeric));
            ctx.parse_fixnum();
            assert!(ctx.pop().is_false());
        }
    }

    #[test]
    fn test_parse_float() {
        let mut ctx = create_test_context();

        unsafe {
            let valid = ctx.gc.allocate_string("123.456");
            ctx.push(ObjectRef::from_bytearray_ptr(valid));
            ctx.parse_float();
            assert!((ctx.pop_float() - 123.456).abs() < f64::EPSILON);

            let invalid = ctx.gc.allocate_string("abc");
            ctx.push(ObjectRef::from_bytearray_ptr(invalid));
            ctx.parse_float();
            assert!(ctx.pop().is_false());

            let empty = ctx.gc.allocate_string("");
            ctx.push(ObjectRef::from_bytearray_ptr(empty));
            ctx.parse_float();
            assert!(ctx.pop().is_false());

            let non_numeric = ctx.gc.allocate_string("-123.456");
            ctx.push(ObjectRef::from_bytearray_ptr(non_numeric));
            ctx.parse_float();
            assert!(ctx.pop().is_false());
        }
    }
    #[test]
    fn test_array_nth_primitives() {
        let mut ctx = create_test_context();

        unsafe {
            let array = ctx.gc.allocate_array(3);
            (*array).set_element(0, ObjectRef::from_int(10));
            (*array).set_element(1, ObjectRef::from_int(20));
            (*array).set_element(2, ObjectRef::from_int(30));

            ctx.push_fixnum(1);
            ctx.push(ObjectRef::from_array_ptr(array));
            ctx.array_nth();
            assert_eq!(ctx.pop_fixnum(), 20);

            ctx.push(ObjectRef::from_int(25));
            ctx.push_fixnum(1);
            ctx.push(ObjectRef::from_array_ptr(array));
            ctx.array_set_nth();

            ctx.push_fixnum(1);
            ctx.push(ObjectRef::from_array_ptr(array));
            ctx.array_nth();
            assert_eq!(ctx.pop_fixnum(), 25);

            ctx.push_fixnum(5);
            ctx.push(ObjectRef::from_array_ptr(array));
            ctx.array_nth();
            assert!(ctx.pop().is_false());
        }
    }

    #[test]
    fn test_object_nth_primitives() {
        let mut ctx = create_test_context();

        unsafe {
            let map = ctx.gc.allocate_map(
                SpecialObjects::get_false(),
                2,
                32,
                SpecialObjects::get_false(),
            );
            let obj = ctx.gc.allocate(map);

            (*obj).set_slot_value(0, ObjectRef::from_int(100));
            (*obj).set_slot_value(1, ObjectRef::from_int(200));

            ctx.push_fixnum(1);
            ctx.push(ObjectRef::from_ptr(obj as *mut _));
            ctx.object_nth();
            assert_eq!(ctx.pop_fixnum(), 200);

            ctx.push(ObjectRef::from_int(250));
            ctx.push_fixnum(1);
            ctx.push(ObjectRef::from_ptr(obj as *mut _));
            ctx.object_set_nth();

            ctx.push_fixnum(1);
            ctx.push(ObjectRef::from_ptr(obj as *mut _));
            ctx.object_nth();
            assert_eq!(ctx.pop_fixnum(), 250);

            ctx.push_fixnum(5);
            ctx.push(ObjectRef::from_ptr(obj as *mut _));
            ctx.object_nth();
            assert!(ctx.pop().is_false());
        }
    }
}
