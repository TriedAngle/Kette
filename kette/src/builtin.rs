use crate::{
    context::Context,
    object::{Array, ByteArray, Object, ObjectRef, ObjectType},
};

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

    // -- GENERAL
    fn drop(&mut self) {
        let _ = self.pop();
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

    // -- ARRAYS
    fn fixnum_to_string(&mut self) {
        let num = self.pop_fixnum();
        let bytearray = unsafe { self.gc.allocate_string(&format!("{}", num)) };
        self.push(bytearray.into());
    }

    fn byterray_print_utf8(&mut self) {
        let obj = self.pop();
        let bytearray = unsafe { obj.as_bytearray_ptr_unchecked() };
        let s = unsafe { (*bytearray).as_str().unwrap() };
        print!("{}", s);
    }

    fn byterray_println_utf8(&mut self) {
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
        let new_size = self.pop_fixnum() as usize;
        let obj = self.pop();

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
        let new_size = self.pop_fixnum() as usize;
        let obj = self.pop();

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

            ctx.push(ObjectRef::from_bytearray_ptr(initial));
            ctx.push_fixnum(3); // Shrink to 3

            ctx.resize_bytearray();

            let result = ctx.pop();
            let new_array = result.as_bytearray_ptr().unwrap();
            assert_eq!((*new_array).size, 3);
            assert_eq!((*new_array).get_element(0), Some(b'h'));
            assert_eq!((*new_array).get_element(1), Some(b'e'));
            assert_eq!((*new_array).get_element(2), Some(b'l'));

            ctx.push(result);
            ctx.push_fixnum(7);
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

            ctx.push(ObjectRef::from_array_ptr(initial));
            ctx.push_fixnum(2); // Shrink to 2

            ctx.resize_array();

            let result = ctx.pop();
            let new_array = result.as_array_ptr().unwrap();
            assert_eq!((*new_array).size.as_int_unchecked(), 2);
            assert_eq!((*new_array).get_element(0), Some(ObjectRef::from_int(1)));
            assert_eq!((*new_array).get_element(1), Some(ObjectRef::from_int(2)));

            ctx.push(result);
            ctx.push_fixnum(6);
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
}
