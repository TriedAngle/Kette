use std::{marker::PhantomData, sync::Arc};

use crate::{
    interning::Messages, primitive_index, primitives::Vector, Allocator,
    ByteArray, BytecodeWriter, Handle, Heap, HeapProxy, HeapSettings,
    HeapValue, Message, SlotHelper, SlotMap, SlotTags, Strings, Value,
};

/// Core VM objects required for bootstrap and runtime operation.
#[derive(Debug)]
pub struct SpecialObjects {
    pub universe: Handle<HeapValue>,
    pub parsers: Handle<HeapValue>,

    pub bytearray_traits: Handle<HeapValue>,
    pub array_traits: Handle<HeapValue>,
    pub fixnum_traits: Handle<HeapValue>,
    pub float_traits: Handle<HeapValue>,
    pub bignum_traits: Handle<HeapValue>,
    pub quotation_traits: Handle<HeapValue>,
    pub message_traits: Handle<HeapValue>,

    pub true_object: Handle<HeapValue>,
    pub false_object: Handle<HeapValue>,

    pub stack_object: Handle<HeapValue>,

    pub primitive_vector_map: Handle<SlotMap>,

    pub dip_map: Handle<SlotMap>,

    pub message_self: Handle<Message>,
    pub message_create_object: Handle<Message>,
    pub message_create_quotation: Handle<Message>,
}

/// Shared VM state accessible across threads.
// TODO: the code heap should be removed.
// why am I not using my normal heap for this? lol ?
#[derive(Debug)]
pub struct VMShared {
    pub specials: SpecialObjects,
    pub heap: Heap,
    pub strings: Strings,
    pub messages: Messages,
}

// Safety: VMProxy is never mutably shared / has internal locking
unsafe impl Send for VMShared {}
// Safety: VMProxy is never mutably shared / has internal locking
unsafe impl Sync for VMShared {}

/// Main VM instance managing the heap and special objects.
#[allow(unused)]
pub struct VM {
    inner: Arc<VMShared>,
    _marker: PhantomData<*const ()>,
}

/// Thread-safe proxy for accessing shared VM state.
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
    pub heap: HeapSettings,
    pub image: Option<String>,
}

impl VM {
    /// Creates a new VM instance, optionally loading from an image.
    pub fn new(info: VMCreateInfo) -> Self {
        let heap = Heap::new(info.heap);

        // Safety: we initialize these right after
        let inner = VMShared {
            // SAFETY: we initialize later, this is for simplicity
            specials: unsafe { SpecialObjects::null() },
            heap,
            strings: Strings::new(),
            messages: Messages::new(),
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

    pub fn proxy(&self) -> VMProxy {
        VMProxy {
            shared: self.inner.clone(),
        }
    }

    fn init_from_image(&self, _image_path: &str) {
        unimplemented!("TODO: images are not implemented yet")
    }

    fn init_new(&mut self) {
        let mut heap = self.inner.heap.proxy();
        let strings = &self.inner.strings;

        let empty_map = heap.allocate_empty_map();

        #[rustfmt::skip]
        let stack_map = heap.allocate_slot_map_helper(
            strings,
            &[
                SlotHelper::primitive_message("dup", SlotTags::empty()),
                SlotHelper::primitive_message("2dup", SlotTags::empty()),
                SlotHelper::primitive_message("drop", SlotTags::empty()),
                SlotHelper::primitive_message("2drop", SlotTags::empty()),
                SlotHelper::primitive_message("3drop", SlotTags::empty()),
                SlotHelper::primitive_message("swap", SlotTags::empty()),
                SlotHelper::primitive_message("over", SlotTags::empty()),
                SlotHelper::primitive_message("pick", SlotTags::empty()),
                SlotHelper::primitive_message("rot", SlotTags::empty()),
                SlotHelper::primitive_message("-rot", SlotTags::empty()),
                SlotHelper::primitive_message("spin", SlotTags::empty()),
                SlotHelper::primitive_message("dupd", SlotTags::empty()),
                SlotHelper::primitive_message("dropd", SlotTags::empty()),
                SlotHelper::primitive_message("2dropd", SlotTags::empty()),
                SlotHelper::primitive_message("swapd", SlotTags::empty()),
                SlotHelper::primitive_message("@vm-depth", SlotTags::empty()),
            ],
        );

        let stack_object = heap.allocate_slots(stack_map, &[]);

        #[rustfmt::skip]
        let fixnum_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("fixnum?", SlotTags::empty()),
            SlotHelper::primitive_message("2fixnum?", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum+", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum*", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum/", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum%", SlotTags::empty()),
            SlotHelper::primitive_message("fixnumNeg", SlotTags::empty()),
            SlotHelper::primitive_message("fixnumBitAnd", SlotTags::empty()),
            SlotHelper::primitive_message("fixnumBitOr", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum=", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum!=", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum<", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum>", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum<=", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum>=", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum>string", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "fixnumParent", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let float_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("float?", SlotTags::empty()),
            SlotHelper::primitive_message("2float?", SlotTags::empty()),
            SlotHelper::primitive_message("float+", SlotTags::empty()),
            SlotHelper::primitive_message("float-", SlotTags::empty()),
            SlotHelper::primitive_message("float*", SlotTags::empty()),
            SlotHelper::primitive_message("float/", SlotTags::empty()),
            SlotHelper::primitive_message("float%", SlotTags::empty()),
            SlotHelper::primitive_message("floatNeg", SlotTags::empty()),
            SlotHelper::primitive_message("float^", SlotTags::empty()),
            SlotHelper::primitive_message("floatSqrt", SlotTags::empty()),
            SlotHelper::primitive_message("floate^", SlotTags::empty()),
            SlotHelper::primitive_message("float2^", SlotTags::empty()),
            SlotHelper::primitive_message("floatSin", SlotTags::empty()),
            SlotHelper::primitive_message("floatCos", SlotTags::empty()),
            SlotHelper::primitive_message("floatTan", SlotTags::empty()),
            SlotHelper::primitive_message("floatAsin", SlotTags::empty()),
            SlotHelper::primitive_message("floatAcos", SlotTags::empty()),
            SlotHelper::primitive_message("floatAtan", SlotTags::empty()),
            SlotHelper::primitive_message("float=", SlotTags::empty()),
            SlotHelper::primitive_message("float!=", SlotTags::empty()),
            SlotHelper::primitive_message("float<", SlotTags::empty()),
            SlotHelper::primitive_message("float>", SlotTags::empty()),
            SlotHelper::primitive_message("float<=", SlotTags::empty()),
            SlotHelper::primitive_message("float>=", SlotTags::empty()),
            SlotHelper::primitive_message("float>string", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "floatParent", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let bytearray_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("(print)", SlotTags::empty()),
            SlotHelper::primitive_message("(println)", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "bytearrayParent", SlotTags::empty()),
            SlotHelper::primitive_message("(bytearraySize)", SlotTags::empty()),
            SlotHelper::primitive_message("(bytearrayNew)", SlotTags::empty()),
            SlotHelper::primitive_message("(bytearrayAt)", SlotTags::empty()),
            SlotHelper::primitive_message("(bytearrayAtPut)", SlotTags::empty()),
            SlotHelper::primitive_message("(bytearrayMemset)", SlotTags::empty()),
            SlotHelper::primitive_message("(bytearrayMemcpy)", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let array_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("(>quotation)", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "arrayParent", SlotTags::empty()),
            SlotHelper::primitive_message("(arraySize)", SlotTags::empty()),
            SlotHelper::primitive_message("(arrayNew)", SlotTags::empty()),
            SlotHelper::primitive_message("(arrayAt)", SlotTags::empty()),
            SlotHelper::primitive_message("(arrayAtPut)", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let quotation_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("(call)", SlotTags::empty()),
            SlotHelper::primitive_message("dip", SlotTags::empty()),
            SlotHelper::primitive_message("if", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "quotationParent", SlotTags::empty()),
            SlotHelper::primitive_message("(withHandler)", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let message_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message2("parent*", "messageParent", SlotTags::empty()),
            SlotHelper::primitive_message2("name", "messageName", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let parsers_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("[", SlotTags::empty()),
            SlotHelper::primitive_message("(|", SlotTags::empty()),
            SlotHelper::primitive_message("//", SlotTags::empty()),
            SlotHelper::primitive_message("/*", SlotTags::empty()),
            SlotHelper::primitive_message("$[", SlotTags::empty()),
        ]);

        let parsers = heap.allocate_slots(parsers_map, &[]);

        #[rustfmt::skip]
        let universe_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::constant("stack*", stack_object.as_value(), SlotTags::PARENT),
            SlotHelper::constant("parsers", parsers.as_value(), SlotTags::empty()),
            SlotHelper::primitive_message2("universe", "(identity)", SlotTags::empty()),
            SlotHelper::primitive_message("addTraitSlots", SlotTags::empty()),
            SlotHelper::primitive_message("removeTraitSlots", SlotTags::empty()),

            SlotHelper::primitive_message("(clone)", SlotTags::empty()),
            SlotHelper::primitive_message("(cloneBoa)", SlotTags::empty()),
            SlotHelper::primitive_message("(signal)", SlotTags::empty()),
            SlotHelper::primitive_message("(unwind)", SlotTags::empty()),
        ]);

        // SAFETY: No GC can occur during initialization; all special objects are fully initialized before use.
        unsafe {
            let primitive_vector_map = Vector::new_map(&mut heap, strings);

            let bytearray_traits =
                heap.allocate_slots(bytearray_map, &[]).cast();

            let array_traits = heap.allocate_slots(array_map, &[]).cast();

            let fixnum_traits = heap.allocate_slots(fixnum_map, &[]).cast();

            let float_traits = heap.allocate_slots(float_map, &[]).cast();

            let bignum_traits = heap.allocate_slots(empty_map, &[]).cast();

            let quotation_traits =
                heap.allocate_slots(quotation_map, &[]).cast();

            let true_object = heap.allocate_slots(empty_map, &[]).cast();

            let message_traits = heap.allocate_slots(message_map, &[]).cast();

            let false_object =
                heap.allocate_slots(empty_map, &[]).cast::<HeapValue>();

            let universe =
                heap.allocate_slots(universe_map, &[]).cast::<HeapValue>();

            // SAFETY: just allocated
            let dip_body = heap.allocate_array(&[]);

            let mut writer = BytecodeWriter::new();
            writer.emit_push_return();
            writer
                .emit_send_primitive(primitive_index("(call)").as_raw() as u16);
            writer.emit_pop_return();
            writer.emit_return();

            let dip_code = heap.allocate_code(
                &[],
                &writer.into_inner(),
                dip_body,
                Handle::null(),
            );

            let dip_map = heap.allocate_executable_map(dip_code, 0, 0);

            let message_self = self.intern_string_message("self", &mut heap);
            let message_create_object =
                self.intern_string_message("(CreateObjectFromMap)", &mut heap);
            let message_create_quotation = self
                .intern_string_message("(CreateQuotationFromMap)", &mut heap);

            let specials = SpecialObjects {
                universe,
                parsers: parsers.cast(),
                stack_object: stack_object.cast(),
                bytearray_traits,
                array_traits,
                fixnum_traits,
                float_traits,
                bignum_traits,
                quotation_traits,
                message_traits,
                primitive_vector_map,
                true_object,
                false_object,
                dip_map,
                message_self,
                message_create_object,
                message_create_quotation,
            };

            let inner = Arc::get_mut(&mut self.inner).expect("get inner");
            inner.specials = specials;
        }
    }

    pub fn intern_string(
        &self,
        s: &str,
        heap: &mut HeapProxy,
    ) -> Handle<ByteArray> {
        self.inner.strings.get(s, heap)
    }

    pub fn intern_message(
        &self,
        interned_bytearray: Handle<ByteArray>,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        self.inner.messages.get(interned_bytearray, heap)
    }

    pub fn intern_string_message(
        &self,
        s: &str,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        let bytearray = self.intern_string(s, heap);
        self.intern_message(bytearray, heap)
    }
}

impl VMProxy {
    pub fn create_proxy(&self) -> Self {
        Self {
            shared: self.shared.clone(),
        }
    }

    // TODO: the intern function should immix allocate and pin
    pub fn intern_string(
        &self,
        s: &str,
        heap: &mut HeapProxy,
    ) -> Handle<ByteArray> {
        self.shared.strings.get(s, heap)
    }

    pub fn intern_message(
        &self,
        interned_bytearray: Handle<ByteArray>,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        self.shared.messages.get(interned_bytearray, heap)
    }

    pub fn intern_string_message(
        &self,
        s: &str,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        let bytearray = self.intern_string(s, heap);
        self.intern_message(bytearray, heap)
    }

    pub fn specials(&self) -> &SpecialObjects {
        &self.shared.specials
    }
}

impl SpecialObjects {
    /// Creates an uninitialized SpecialObjects holder.
    /// # Safety
    /// Must be fully initialized before use.
    pub unsafe fn null() -> Self {
        // SAFETY: we initialize later, this is for simplicity
        unsafe {
            Self {
                universe: Value::zero().as_heap_handle_unchecked(),
                parsers: Value::zero().as_heap_handle_unchecked(),
                bytearray_traits: Value::zero().as_heap_handle_unchecked(),
                array_traits: Value::zero().as_heap_handle_unchecked(),
                fixnum_traits: Value::zero().as_heap_handle_unchecked(),
                float_traits: Value::zero().as_heap_handle_unchecked(),
                bignum_traits: Value::zero().as_heap_handle_unchecked(),
                quotation_traits: Value::zero().as_heap_handle_unchecked(),
                message_traits: Value::zero().as_heap_handle_unchecked(),
                primitive_vector_map: Value::zero()
                    .as_heap_handle_unchecked()
                    .cast(),
                true_object: Value::zero().as_heap_handle_unchecked(),
                false_object: Value::zero().as_heap_handle_unchecked(),
                stack_object: Value::zero().as_heap_handle_unchecked(),
                dip_map: Value::zero().as_heap_handle_unchecked().cast(),
                message_self: Value::zero().as_heap_handle_unchecked().cast(),
                message_create_object: Value::zero()
                    .as_heap_handle_unchecked()
                    .cast(),
                message_create_quotation: Value::zero()
                    .as_heap_handle_unchecked()
                    .cast(),
            }
        }
    }
}
