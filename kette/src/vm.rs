use std::{marker::PhantomData, sync::Arc};

use crate::{
    Allocator, BytecodeWriter, Handle, Heap, HeapProxy, HeapSettings,
    HeapValue, Map, Message, SlotHelper, SlotTags, StringObject, Strings,
    interning::Messages, primitive_index, primitives::Vector,
};

/// Core VM objects required for bootstrap and runtime operation.
#[derive(Debug)]
pub struct SpecialObjects {
    pub universe: Handle<HeapValue>,
    pub reflect: Handle<HeapValue>,
    pub parsers: Handle<HeapValue>,
    pub stack_object: Handle<HeapValue>,

    pub bytearray_traits: Handle<HeapValue>,
    pub string_traits: Handle<HeapValue>,
    pub array_traits: Handle<HeapValue>,
    pub fixnum_traits: Handle<HeapValue>,
    pub float_traits: Handle<HeapValue>,
    pub bignum_traits: Handle<HeapValue>,
    pub ratio_traits: Handle<HeapValue>,
    pub quotation_traits: Handle<HeapValue>,
    pub message_traits: Handle<HeapValue>,
    pub alien_traits: Handle<HeapValue>,

    pub true_object: Handle<HeapValue>,
    pub false_object: Handle<HeapValue>,

    pub primitive_vector_map: Handle<Map>,

    pub dip_map: Handle<Map>,

    pub message_self: Handle<Message>,
    pub message_create_object: Handle<Message>,
    pub message_create_quotation: Handle<Message>,

    #[cfg(feature = "inline-cache")]
    pub uninitialized_ic_sentinel: Handle<HeapValue>,
    #[cfg(feature = "inline-cache")]
    pub megamorphic_sentinel: Handle<HeapValue>,
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
    #[must_use]
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

    #[must_use]
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

        #[rustfmt::skip]
        let fixnum_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("fixnum?", SlotTags::empty()),
            SlotHelper::primitive_message("2fixnum?", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum>bignum", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum+", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum*", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum/", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum%", SlotTags::empty()),
            SlotHelper::primitive_message("fixnumNeg", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum+Unchecked", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum-Unchecked", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum*Unchecked", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum/Unchecked", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum%Unchecked", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum^Unchecked", SlotTags::empty()),
            SlotHelper::primitive_message("fixnumNegUnchecked", SlotTags::empty()),
            SlotHelper::primitive_message("fixnumBitAnd", SlotTags::empty()),
            SlotHelper::primitive_message("fixnumBitOr", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum=", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum!=", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum<", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum>", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum<=", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum>=", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum>string", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum>float", SlotTags::empty()),
            SlotHelper::primitive_message("fixnum>ratio", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "fixnumParent", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let float_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("float?", SlotTags::empty()),
            SlotHelper::primitive_message("2float?", SlotTags::empty()),
            SlotHelper::primitive_message("float>bignum", SlotTags::empty()),
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
            SlotHelper::primitive_message("bytearray>string", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayU16At", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayI16At", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayU32At", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayI32At", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayU64At", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayI64At", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayU16AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayI16AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayU32AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayI32AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayU64AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("bytearrayI64AtPut", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let string_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("(print)", SlotTags::empty()),
            SlotHelper::primitive_message("(println)", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "stringParent", SlotTags::empty()),
            SlotHelper::primitive_message("stringSize", SlotTags::empty()),
            SlotHelper::primitive_message("string>bytearray", SlotTags::empty()),
            SlotHelper::primitive_message("string>message", SlotTags::empty()),
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
            // SlotHelper::primitive_message("if", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "quotationParent", SlotTags::empty()),
            SlotHelper::primitive_message("(withHandler)", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let message_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message2("parent*", "messageParent", SlotTags::empty()),
            SlotHelper::primitive_message2("name", "messageName", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let alien_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("alienU8At", SlotTags::empty()),
            SlotHelper::primitive_message("alienI8At", SlotTags::empty()),
            SlotHelper::primitive_message("alienU16At", SlotTags::empty()),
            SlotHelper::primitive_message("alienI16At", SlotTags::empty()),
            SlotHelper::primitive_message("alienU32At", SlotTags::empty()),
            SlotHelper::primitive_message("alienI32At", SlotTags::empty()),
            SlotHelper::primitive_message("alienU64At", SlotTags::empty()),
            SlotHelper::primitive_message("alienI64At", SlotTags::empty()),
            SlotHelper::primitive_message("alienU8AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("alienI8AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("alienU16AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("alienI16AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("alienU32AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("alienI32AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("alienU64AtPut", SlotTags::empty()),
            SlotHelper::primitive_message("alienI64AtPut", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let parsers_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("[", SlotTags::empty()),
            SlotHelper::primitive_message("[|", SlotTags::empty()),
            SlotHelper::primitive_message("(|", SlotTags::empty()),
            SlotHelper::primitive_message("//", SlotTags::empty()),
            SlotHelper::primitive_message("/*", SlotTags::empty()),
            SlotHelper::primitive_message("{", SlotTags::empty()),
            SlotHelper::primitive_message("$[", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let reflect_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("addTraitSlots", SlotTags::empty()),
            SlotHelper::primitive_message("removeTraitSlots", SlotTags::empty()),
        ]);

        let parsers = heap.allocate_slots(parsers_map, &[]);

        let stack_object = heap.allocate_slots(stack_map, &[]);

        let reflect = heap.allocate_slots(reflect_map, &[]);

        #[rustfmt::skip]
        let universe_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::constant("stack*", stack_object.as_value(), SlotTags::PARENT),
            SlotHelper::constant("parsers", parsers.as_value(), SlotTags::empty()),
            SlotHelper::constant("reflect", reflect.as_value(), SlotTags::empty()),
            SlotHelper::primitive_message2("universe", "(identity)", SlotTags::empty()),

            SlotHelper::primitive_message("(clone)", SlotTags::empty()),
            SlotHelper::primitive_message("(cloneBoa)", SlotTags::empty()),
            SlotHelper::primitive_message("(signal)", SlotTags::empty()),
            SlotHelper::primitive_message("(unwind)", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let bignum_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("bignumToFixnumChecked", SlotTags::empty()),
            SlotHelper::primitive_message("bignum+", SlotTags::empty()),
            SlotHelper::primitive_message("bignum-", SlotTags::empty()),
            SlotHelper::primitive_message("bignum*", SlotTags::empty()),
            SlotHelper::primitive_message("bignum/", SlotTags::empty()),
            SlotHelper::primitive_message("bignum%", SlotTags::empty()),
            SlotHelper::primitive_message("bignumNeg", SlotTags::empty()),
            SlotHelper::primitive_message("bignum=", SlotTags::empty()),
            SlotHelper::primitive_message("bignum!=", SlotTags::empty()),
            SlotHelper::primitive_message("bignum<", SlotTags::empty()),
            SlotHelper::primitive_message("bignum>", SlotTags::empty()),
            SlotHelper::primitive_message("bignum<=", SlotTags::empty()),
            SlotHelper::primitive_message("bignum>=", SlotTags::empty()),
            SlotHelper::primitive_message("bignum>float", SlotTags::empty()),
            SlotHelper::primitive_message("bignum>ratio", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "bignumParent", SlotTags::empty()),
        ]);

        #[rustfmt::skip]
        let ratio_map = heap.allocate_slot_map_helper(strings, &[
            SlotHelper::primitive_message("ratio?", SlotTags::empty()),
            SlotHelper::primitive_message("2ratio?", SlotTags::empty()),
            SlotHelper::primitive_message("ratioNew", SlotTags::empty()),
            SlotHelper::primitive_message("ratioNumerator", SlotTags::empty()),
            SlotHelper::primitive_message("ratioDenominator", SlotTags::empty()),
            SlotHelper::primitive_message("ratio>fixnum", SlotTags::empty()),
            SlotHelper::primitive_message("ratio+", SlotTags::empty()),
            SlotHelper::primitive_message("ratio-", SlotTags::empty()),
            SlotHelper::primitive_message("ratio*", SlotTags::empty()),
            SlotHelper::primitive_message("ratio/", SlotTags::empty()),
            SlotHelper::primitive_message("ratioNeg", SlotTags::empty()),
            SlotHelper::primitive_message("ratio=", SlotTags::empty()),
            SlotHelper::primitive_message("ratio!=", SlotTags::empty()),
            SlotHelper::primitive_message("ratio<", SlotTags::empty()),
            SlotHelper::primitive_message("ratio>", SlotTags::empty()),
            SlotHelper::primitive_message("ratio<=", SlotTags::empty()),
            SlotHelper::primitive_message("ratio>=", SlotTags::empty()),
            SlotHelper::primitive_message("ratio>float", SlotTags::empty()),
            SlotHelper::primitive_message("ratio>string", SlotTags::empty()),
            SlotHelper::primitive_message2("parent*", "ratioParent", SlotTags::empty()),
        ]);

        // SAFETY: No GC can occur during initialization; all special objects are fully initialized before use.
        unsafe {
            let universe =
                heap.allocate_slots(universe_map, &[]).cast::<HeapValue>();

            let primitive_vector_map =
                Vector::new_map(&mut heap, strings, universe);

            let bytearray_traits =
                heap.allocate_slots(bytearray_map, &[]).cast();

            let string_traits = heap.allocate_slots(string_map, &[]).cast();

            let array_traits = heap.allocate_slots(array_map, &[]).cast();

            let fixnum_traits = heap.allocate_slots(fixnum_map, &[]).cast();

            let float_traits = heap.allocate_slots(float_map, &[]).cast();

            let bignum_traits = heap.allocate_slots(bignum_map, &[]).cast();

            let ratio_traits = heap.allocate_slots(ratio_map, &[]).cast();

            let quotation_traits =
                heap.allocate_slots(quotation_map, &[]).cast();

            let true_object = heap.allocate_slots(empty_map, &[]).cast();

            let message_traits = heap.allocate_slots(message_map, &[]).cast();

            let alien_traits = heap.allocate_slots(alien_map, &[]).cast();

            let false_object =
                heap.allocate_slots(empty_map, &[]).cast::<HeapValue>();

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
                0, // no Send sites in dip
                dip_body,
                Handle::null(),
            );

            let dip_map = heap.allocate_executable_map(dip_code, 0, 0);

            let message_self = self.intern_string_message("self", &mut heap);
            let message_create_object =
                self.intern_string_message("(CreateObjectFromMap)", &mut heap);
            let message_create_quotation = self
                .intern_string_message("(CreateQuotationFromMap)", &mut heap);

            // IC sentinels - unique empty objects used to mark IC states
            #[cfg(feature = "inline-cache")]
            let uninitialized_ic_sentinel =
                heap.allocate_slots(empty_map, &[]).cast();
            #[cfg(feature = "inline-cache")]
            let megamorphic_sentinel =
                heap.allocate_slots(empty_map, &[]).cast();

            let specials = SpecialObjects {
                universe,
                reflect: reflect.cast(),
                parsers: parsers.cast(),
                stack_object: stack_object.cast(),
                bytearray_traits,
                string_traits,
                array_traits,
                fixnum_traits,
                float_traits,
                bignum_traits,
                ratio_traits,
                quotation_traits,
                message_traits,
                alien_traits,
                primitive_vector_map,
                true_object,
                false_object,
                dip_map,
                message_self,
                message_create_object,
                message_create_quotation,
                #[cfg(feature = "inline-cache")]
                uninitialized_ic_sentinel,
                #[cfg(feature = "inline-cache")]
                megamorphic_sentinel,
            };

            let inner = Arc::get_mut(&mut self.inner).expect("get inner");
            inner.specials = specials;
        }
    }

    pub fn intern_string(
        &self,
        s: &str,
        heap: &mut HeapProxy,
    ) -> Handle<StringObject> {
        self.inner.strings.get(s, heap)
    }

    pub fn intern_message(
        &self,
        interned_string: Handle<StringObject>,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        self.inner.messages.get(interned_string, heap)
    }

    pub fn intern_string_message(
        &self,
        s: &str,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        let string = self.intern_string(s, heap);
        self.intern_message(string, heap)
    }
}

impl VMProxy {
    #[must_use]
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
    ) -> Handle<StringObject> {
        self.shared.strings.get(s, heap)
    }

    pub fn intern_message(
        &self,
        interned_string: Handle<StringObject>,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        self.shared.messages.get(interned_string, heap)
    }

    pub fn intern_string_message(
        &self,
        s: &str,
        heap: &mut HeapProxy,
    ) -> Handle<Message> {
        let string = self.intern_string(s, heap);
        self.intern_message(string, heap)
    }

    #[must_use]
    pub fn specials(&self) -> &SpecialObjects {
        &self.shared.specials
    }
}

impl SpecialObjects {
    /// Returns all handles in SpecialObjects as a Vec for GC rooting.
    #[must_use]
    pub fn as_roots(&self) -> Vec<Handle<HeapValue>> {
        // SAFETY: cast() is safe for GC rooting - we just need the pointer
        let mut roots = unsafe {
            vec![
                self.universe,
                self.reflect,
                self.parsers,
                self.stack_object,
                self.bytearray_traits,
                self.string_traits,
                self.array_traits,
                self.fixnum_traits,
                self.float_traits,
                self.bignum_traits,
                self.ratio_traits,
                self.quotation_traits,
                self.message_traits,
                self.alien_traits,
                self.primitive_vector_map.cast(),
                self.true_object,
                self.false_object,
                self.dip_map.cast(),
                self.message_self.cast(),
                self.message_create_object.cast(),
                self.message_create_quotation.cast(),
            ]
        };
        #[cfg(feature = "inline-cache")]
        {
            roots.push(self.uninitialized_ic_sentinel);
            roots.push(self.megamorphic_sentinel);
        }
        roots
    }

    /// Creates an uninitialized SpecialObjects holder.
    /// # Safety
    /// Must be fully initialized before use.
    pub unsafe fn null() -> Self {
        // SAFETY: we initialize later, this is for simplicity
        unsafe {
            Self {
                universe: Handle::null(),
                reflect: Handle::null(),
                parsers: Handle::null(),
                stack_object: Handle::null(),
                bytearray_traits: Handle::null(),
                string_traits: Handle::null(),
                array_traits: Handle::null(),
                fixnum_traits: Handle::null(),
                float_traits: Handle::null(),
                bignum_traits: Handle::null(),
                ratio_traits: Handle::null(),
                quotation_traits: Handle::null(),
                message_traits: Handle::null(),
                alien_traits: Handle::null(),
                primitive_vector_map: Handle::null(),
                true_object: Handle::null(),
                false_object: Handle::null(),
                dip_map: Handle::null(),
                message_self: Handle::null(),
                message_create_object: Handle::null(),
                message_create_quotation: Handle::null(),
                #[cfg(feature = "inline-cache")]
                uninitialized_ic_sentinel: Handle::null(),
                #[cfg(feature = "inline-cache")]
                megamorphic_sentinel: Handle::null(),
            }
        }
    }
}
