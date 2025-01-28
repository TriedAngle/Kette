use std::mem;

use crate::{
    gc::GarbageCollector,
    object::{Array, ObjectHeader, ObjectRef, ObjectType, Quotation, SpecialObjects},
    MemoryRegion, MutArc,
};

pub struct Context {
    pub header: ObjectHeader,
    pub datastack: ObjectRef,
    pub retainstack: ObjectRef,
    pub namestack: ObjectRef,

    pub gc: MutArc<GarbageCollector>,
    pub data: MemoryRegion<ObjectRef>,
    pub retain: MemoryRegion<ObjectRef>,
}

pub struct ContextConfig {
    pub datastack_size: usize,
    pub retainstack_size: usize,
}

impl Context {
    pub fn new(config: &ContextConfig) -> Self {
        let mut gc = MutArc::new(GarbageCollector::new());
        gc.init_special_objects();
        let datastack = unsafe { gc.allocate_array(config.datastack_size) };
        let retainstack = unsafe { gc.allocate_array(config.retainstack_size) };

        let data = datastack.into();
        let retain = retainstack.into();
        let header = ObjectHeader::null();

        gc.add_root(ObjectRef::from_array_ptr(datastack));
        gc.add_root(ObjectRef::from_array_ptr(retainstack));

        Self {
            header,
            datastack: datastack.into(),
            retainstack: retainstack.into(),
            namestack: ObjectRef::null(),
            gc,
            data,
            retain,
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

    fn execute(&mut self, quotation: *mut Quotation) {
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
                    let flags = unsafe { (*word).flags.as_array_ptr().unwrap_unchecked() };
                    let body_obj = unsafe { (*word).body };

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
                        let quotation_clone = unsafe { self.gc.deep_clone(body_obj, 1) };
                        self.gc.add_root(quotation_clone);

                        let body_quotation = quotation_clone.as_quotation_ptr().unwrap();
                        self.execute(body_quotation);

                        self.gc.remove_root(quotation_clone);
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::object::ObjectType;

    fn create_test_context() -> Context {
        let config = ContextConfig {
            datastack_size: 512,
            retainstack_size: 512,
        };
        Context::new(&config)
    }

    #[test]
    fn test_push_pop_integers() {
        let mut ctx = create_test_context();

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
}
