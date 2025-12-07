use std::{marker::PhantomData, sync::Arc};

use crate::{
    ByteArray, Handle, Heap, HeapCreateInfo, HeapProxy, HeapValue, Message,
    SlotHelper, SlotTags, Strings, Value,
};

#[derive(Debug)]
pub struct SpecialObjects {
    pub bytearray_traits: Handle<HeapValue>,
    pub array_traits: Handle<HeapValue>,
    pub fixnum_traits: Handle<HeapValue>,
    pub float_traits: Handle<HeapValue>,
    pub true_object: Handle<HeapValue>,
    pub false_object: Handle<HeapValue>,
    pub stack_object: Handle<HeapValue>,

    pub message_self: Handle<ByteArray>,
}

#[derive(Debug)]
pub struct VMShared {
    pub specials: SpecialObjects,
    pub heap: Heap,
    pub strings: Strings,
}

// Safety: VMProxy is never mutably shared / has internal locking
unsafe impl Send for VMShared {}
// Safety: VMProxy is never mutably shared / has internal locking
unsafe impl Sync for VMShared {}

#[allow(unused)]
pub struct VM {
    inner: Arc<VMShared>,
    _marker: PhantomData<*const ()>,
}

#[derive(Debug)]
pub struct VMProxy {
    pub shared: Arc<VMShared>,
}

// Safety: VMProxy is never mutably shared / has internal locking
unsafe impl Send for VMProxy {}
// Safety: VMProxy is never mutably shared / has internal locking
unsafe impl Sync for VMProxy {}

#[derive(Debug)]
pub struct VMCreateInfo {
    pub heap: HeapCreateInfo,
    pub image: Option<String>,
}

impl VM {
    pub fn new(info: VMCreateInfo) -> Self {
        let heap = Heap::new(info.heap);

        // Safety: we initialize these right after
        let inner = VMShared {
            // SAFETY: we initialize later, this is for simplicity
            specials: unsafe { SpecialObjects::null() },
            heap,
            strings: Strings::new(),
        };

        let mut new = Self {
            inner: Arc::new(inner),
            _marker: PhantomData,
        };

        match info.image {
            Some(image) => new.init_from_image(&image),
            None => new.init_new(),
        }

        new
    }

    pub fn new_proxy(&self) -> VMProxy {
        VMProxy {
            shared: self.inner.clone(),
        }
    }

    fn init_from_image(&self, _image_path: &str) {
        unimplemented!("TODO: images are not implemented yet")
    }

    // TODO: special objects should be allocated on the startup heap
    fn init_new(&mut self) {
        let mut heap = self.inner.heap.create_proxy();
        let strings = &self.inner.strings;

        let empty_map = heap.allocate_empty_map();

        #[rustfmt::skip]
        let stack_map = heap.allocate_slot_map_helper(
            strings,
            &[
                SlotHelper::primitive_message("dup", SlotTags::empty()),
                SlotHelper::primitive_message("drop", SlotTags::empty()),
                SlotHelper::primitive_message("2drop", SlotTags::empty()),
                SlotHelper::primitive_message("3drop", SlotTags::empty()),
                SlotHelper::primitive_message("swap", SlotTags::empty()),
                SlotHelper::primitive_message("over", SlotTags::empty()),
                SlotHelper::primitive_message("rot", SlotTags::empty()),
                SlotHelper::primitive_message("-rot", SlotTags::empty()),
                SlotHelper::primitive_message("spin", SlotTags::empty()),
                SlotHelper::primitive_message("dupd", SlotTags::empty()),
                SlotHelper::primitive_message("dropd", SlotTags::empty()),
                SlotHelper::primitive_message("2dropd", SlotTags::empty()),
                SlotHelper::primitive_message("swapd", SlotTags::empty()),
                SlotHelper::primitive_message("dip", SlotTags::empty()),
            ],
        );

        #[rustfmt::skip]
        let fixnum_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("fixnum?", SlotTags::empty()),
            SlotHelper::primitive_message("2fixnum?", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum+", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum*", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum/", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum%", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-bitneg", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-bitand", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-bitor", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-eq", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-neq", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-lt", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-gt", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-leq", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-geq", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum>utf8-bytes", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let bytearray_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("bytearray-print", SlotTags::empty()),
            SlotHelper::primitive_message("bytearray-println", SlotTags::empty()),
        ]);

        // SAFETY: this is safe, no gc can happen here and afterwards these are initialized
        unsafe {
            let stack_object = heap
                .allocate_slot_object(stack_map, &[])
                .promote_to_handle()
                .cast();

            let bytearray_traits = heap
                .allocate_slot_object(bytearray_map, &[])
                .promote_to_handle()
                .cast();

            let array_traits = heap
                .allocate_slot_object(empty_map, &[])
                .promote_to_handle()
                .cast();

            let fixnum_traits = heap
                .allocate_slot_object(fixnum_map, &[])
                .promote_to_handle()
                .cast();

            let float_traits = heap
                .allocate_slot_object(empty_map, &[])
                .promote_to_handle()
                .cast();

            let true_object = heap
                .allocate_slot_object(empty_map, &[])
                .promote_to_handle()
                .cast();

            let false_object = heap
                .allocate_slot_object(empty_map, &[])
                .promote_to_handle()
                .cast();

            let specials = SpecialObjects {
                bytearray_traits,
                array_traits,
                fixnum_traits,
                float_traits,
                true_object,
                false_object,
                stack_object,
                // TODO: this MUST be implemented
                message_self: Value::zero().as_heap_handle_unchecked().cast(),
            };

            let inner = Arc::get_mut(&mut self.inner).expect("get inner");
            inner.specials = specials;
        }
    }
}

impl VMProxy {
    pub fn create_proxy(&self) -> Self {
        Self {
            shared: self.shared.clone(),
        }
    }

    pub fn intern_string(
        &self,
        s: &str,
        heap: &mut HeapProxy,
    ) -> Handle<ByteArray> {
        self.shared.strings.get(s, heap)
    }

    pub fn specials<'a>(&'a self) -> &'a SpecialObjects {
        &self.shared.specials
    }
}

impl SpecialObjects {
    /// create an unitialized SpecialObjects holder
    /// # Safety:
    /// must be initialized before usage
    pub unsafe fn null() -> Self {
        Self {
            // SAFETY: we initialize later, this is for simplicity
            bytearray_traits: unsafe {
                Value::zero().as_heap_handle_unchecked()
            },
            // SAFETY: we initialize later, this is for simplicity
            array_traits: unsafe { Value::zero().as_heap_handle_unchecked() },
            // SAFETY: we initialize later, this is for simplicity
            fixnum_traits: unsafe { Value::zero().as_heap_handle_unchecked() },
            // SAFETY: we initialize later, this is for simplicity
            float_traits: unsafe { Value::zero().as_heap_handle_unchecked() },
            // SAFETY: we initialize later, this is for simplicity
            true_object: unsafe { Value::zero().as_heap_handle_unchecked() },
            // SAFETY: we initialize later, this is for simplicity
            false_object: unsafe { Value::zero().as_heap_handle_unchecked() },
            // SAFETY: we initialize later, this is for simplicity
            stack_object: unsafe { Value::zero().as_heap_handle_unchecked() },
            // SAFETY: we initialize later, this is for simplicity
            message_self: unsafe {
                Value::zero().as_heap_handle_unchecked().cast()
            },
        }
    }
}
