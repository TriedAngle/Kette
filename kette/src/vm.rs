use std::{marker::PhantomData, sync::Arc};

use crate::{
    Block, ByteArray, Handle, Heap, HeapCreateInfo, HeapProxy, HeapValue,
    Instruction, Message, Quotation, SlotHelper, SlotTags, Strings, Value,
    bytecode::CodeHeap, interning::Messages, primitive_index,
    primitives::Vector,
};

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
    pub effect_traits: Handle<HeapValue>,
    pub method_traits: Handle<HeapValue>,

    pub true_object: Handle<HeapValue>,
    pub false_object: Handle<HeapValue>,

    pub stack_object: Handle<HeapValue>,

    pub primitive_vector_map: Handle<HeapValue>,

    pub dip_quotation: Handle<Quotation>,

    pub message_self: Handle<Message>,
}

// TODO: the code heap should be removed.
// why am I not using my normal heap for this? lol ?
#[derive(Debug)]
pub struct VMShared {
    pub specials: SpecialObjects,
    pub heap: Heap,
    pub strings: Strings,
    pub messages: Messages,
    pub code_heap: CodeHeap,
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
            messages: Messages::new(),
            code_heap: CodeHeap::new(),
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
                SlotHelper::primitive_message("2dup", SlotTags::empty()),
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
                SlotHelper::primitive_message("@vm-depth", SlotTags::empty()),
            ],
        );

        let stack_object = heap.allocate_slot_object(stack_map, &[]);

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
            SlotHelper::primitive_message("(newArray)", SlotTags::empty()),
            SlotHelper::primitive_message("(arrayAt)", SlotTags::empty()),
            SlotHelper::primitive_message("(arrayAtPut)", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let quotation_map = heap.allocate_slot_map_helper(strings, &[
            // SlotHelper::constant("", value, tags)
            SlotHelper::primitive_message("(call)", SlotTags::empty()),
            SlotHelper::primitive_message("dip", SlotTags::empty()),
            SlotHelper::primitive_message("if", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "quotationParent", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let method_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("(call-method)", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let effect_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::assignable("inputs", Value::from_u64(0), SlotTags::empty()),
            SlotHelper::assignable("outputs", Value::from_u64(1), SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let parsers_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("[", SlotTags::empty()),
            SlotHelper::primitive_message(":", SlotTags::empty()),
            SlotHelper::primitive_message("(|", SlotTags::empty()),
            SlotHelper::primitive_message("//", SlotTags::empty()),
            SlotHelper::primitive_message("/*", SlotTags::empty()),
        ]);

        let parsers = heap.allocate_slot_object(parsers_map, &[]);

        #[rustfmt::skip]
        let universe_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::constant("stack*", stack_object.into(), SlotTags::PARENT),
            SlotHelper::constant("parsers", parsers.into(), SlotTags::PARENT),
            SlotHelper::primitive_message2("universe", "(identity)", SlotTags::empty()),
            SlotHelper::primitive_message("addTraitSlots", SlotTags::empty()),
            SlotHelper::primitive_message("removeTraitSlots", SlotTags::empty()),
            SlotHelper::primitive_message("(clone)", SlotTags::empty()),
            SlotHelper::primitive_message("(cloneBoa)", SlotTags::empty()),
        ]);

        // SAFETY: this is safe, no gc can happen here and afterwards these are initialized
        unsafe {
            let primitive_vector_map = Vector::new_map(&mut heap, strings)
                .promote_to_handle()
                .cast();

            let bytearray_traits = heap
                .allocate_slot_object(bytearray_map, &[])
                .promote_to_handle()
                .cast();

            let array_traits = heap
                .allocate_slot_object(array_map, &[])
                .promote_to_handle()
                .cast();

            let fixnum_traits = heap
                .allocate_slot_object(fixnum_map, &[])
                .promote_to_handle()
                .cast();

            let float_traits = heap
                .allocate_slot_object(float_map, &[])
                .promote_to_handle()
                .cast();

            let bignum_traits = heap
                .allocate_slot_object(empty_map, &[])
                .promote_to_handle()
                .cast();

            let quotation_traits = heap
                .allocate_slot_object(quotation_map, &[])
                .promote_to_handle()
                .cast();

            let method_traits = heap
                .allocate_slot_object(method_map, &[])
                .promote_to_handle()
                .cast();

            let true_object = heap
                .allocate_slot_object(empty_map, &[])
                .promote_to_handle()
                .cast();

            let false_object = heap
                .allocate_slot_object(empty_map, &[])
                .promote_to_handle()
                .cast::<HeapValue>();

            let effect_traits = heap
                .allocate_slot_object(
                    effect_map,
                    &[false_object.as_value(), false_object.as_value()],
                )
                .promote_to_handle()
                .cast();

            let universe = heap
                .allocate_slot_object(universe_map, &[])
                .promote_to_handle()
                .cast::<HeapValue>();

            let dip_code = self.inner.code_heap.push(Block {
                instructions: [
                    Instruction::StackToReturn,
                    Instruction::SendPrimitive {
                        id: primitive_index("(call)"),
                    },
                    Instruction::ReturnToStack,
                    Instruction::Return,
                ]
                .into(),
            });

            // SAFETY: just allocated
            let dip_body = heap.allocate_array(&[]).promote_to_handle();

            let dip_quotation = heap
                .allocate_quotation(dip_body, dip_code, 2, 1)
                .promote_to_handle();

            let message_self = self.intern_string_message("self", &mut heap);

            let specials = SpecialObjects {
                universe,
                parsers: parsers.promote_to_handle().cast(),
                stack_object: stack_object.promote_to_handle().cast(),
                bytearray_traits,
                array_traits,
                fixnum_traits,
                float_traits,
                bignum_traits,
                quotation_traits,
                effect_traits,
                method_traits,
                primitive_vector_map,
                true_object,
                false_object,
                dip_quotation,
                message_self,
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
    /// create an unitialized SpecialObjects holder
    /// # Safety:
    /// must be initialized before usage
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
                primitive_vector_map: Value::zero().as_heap_handle_unchecked(),
                effect_traits: Value::zero().as_heap_handle_unchecked(),
                method_traits: Value::zero().as_heap_handle_unchecked(),
                true_object: Value::zero().as_heap_handle_unchecked(),
                false_object: Value::zero().as_heap_handle_unchecked(),
                stack_object: Value::zero().as_heap_handle_unchecked(),
                dip_quotation: Value::zero().as_heap_handle_unchecked().cast(),
                message_self: Value::zero().as_heap_handle_unchecked().cast(),
            }
        }
    }
}
