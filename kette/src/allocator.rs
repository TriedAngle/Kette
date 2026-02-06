use std::{alloc::Layout, ptr::NonNull};

use crate::{
    ActivationObject, Array, BigNum, ByteArray, Code, FeedbackEntry, Float,
    Handle, HeapObject, HeapValue, Map, Message, Parser, Quotation,
    SlotDescriptor, SlotHelper, SlotObject, SlotTags, Strings, Tagged, Value,
};

/// Heap allocation interface for creating VM objects.
pub trait Allocator: Sized {
    /// Allocates raw memory with the given layout.
    fn allocate(&mut self, layout: Layout) -> NonNull<u8>;

    /// Allocates and returns a typed handle to a heap object.
    /// # Safety
    /// No GC may occur while the returned handle is live.
    unsafe fn allocate_handle<T: HeapObject>(
        &mut self,
        layout: Layout,
    ) -> Handle<T> {
        let raw = self.allocate(layout);
        // SAFETY: by contract will be initialized after
        unsafe { Handle::new_ptr(raw.cast().as_ptr()) }
    }

    fn allocate_float(&mut self, value: f64) -> Handle<Float> {
        let layout = Layout::new::<Float>();

        // SAFETY: allocate_handle returns valid memory, init called immediately after.
        let mut obj = unsafe { self.allocate_handle::<Float>(layout) };
        obj.init(value);
        obj
    }

    fn allocate_aligned_bytearray_zeroed(
        &mut self,
        size: usize,
        align: usize,
    ) -> Handle<ByteArray> {
        let layout = ByteArray::required_layout_size_align(size, align);
        // SAFETY: allocate_handle returns valid memory, init_zeroed called immediately after.
        let mut ba = unsafe { self.allocate_handle::<ByteArray>(layout) };
        ba.init_zeroed(size);
        ba
    }

    fn allocate_aligned_bytearray(
        &mut self,
        data: &[u8],
        align: usize,
    ) -> Handle<ByteArray> {
        let layout = ByteArray::required_layout_size_align(data.len(), align);
        // SAFETY: allocate_handle returns valid memory, init_data called immediately after.
        let mut ba = unsafe { self.allocate_handle::<ByteArray>(layout) };
        ba.init_data(data);
        ba
    }

    fn allocate_message(
        &mut self,
        interned: Handle<ByteArray>,
    ) -> Handle<Message> {
        let layout = Layout::new::<Message>();
        // SAFETY: allocate_handle returns valid memory, init called immediately after.
        let mut obj = unsafe { self.allocate_handle::<Message>(layout) };
        obj.init(interned);
        obj
    }

    fn allocate_bignum_from_u64(&mut self, value: u64) -> Handle<BigNum> {
        if value == 0 {
            let layout = BigNum::required_layout(0);
            let mut obj = unsafe { self.allocate_handle::<BigNum>(layout) };
            obj.init(0, &[]);
            return obj;
        }

        let layout = BigNum::required_layout(1);
        let mut obj = unsafe { self.allocate_handle::<BigNum>(layout) };
        obj.init(1, &[value]);
        obj
    }

    fn allocate_bignum_from_i64(&mut self, value: i64) -> Handle<BigNum> {
        if value == 0 {
            let layout = BigNum::required_layout(0);
            let mut obj = unsafe { self.allocate_handle::<BigNum>(layout) };
            obj.init(0, &[]);
            return obj;
        }

        let sign = if value < 0 { -1 } else { 1 };
        let magnitude = value.unsigned_abs();
        let layout = BigNum::required_layout(1);
        let mut obj = unsafe { self.allocate_handle::<BigNum>(layout) };
        obj.init(sign, &[magnitude]);
        obj
    }

    fn allocate_bignum_from_u128(&mut self, value: u128) -> Handle<BigNum> {
        if value == 0 {
            let layout = BigNum::required_layout(0);
            let mut obj = unsafe { self.allocate_handle::<BigNum>(layout) };
            obj.init(0, &[]);
            return obj;
        }

        if value <= u64::MAX as u128 {
            return self.allocate_bignum_from_u64(value as u64);
        }

        let low = value as u64;
        let high = (value >> 64) as u64;
        let limbs = [low, high];
        let layout = BigNum::required_layout(2);
        let mut obj = unsafe { self.allocate_handle::<BigNum>(layout) };
        obj.init(1, &limbs);
        obj
    }

    fn allocate_bignum_from_i128(&mut self, value: i128) -> Handle<BigNum> {
        if value == 0 {
            let layout = BigNum::required_layout(0);
            let mut obj = unsafe { self.allocate_handle::<BigNum>(layout) };
            obj.init(0, &[]);
            return obj;
        }

        let sign = if value < 0 { -1 } else { 1 };
        let magnitude = value.unsigned_abs();
        let mut obj = self.allocate_bignum_from_u128(magnitude);
        obj.sign = sign;
        obj
    }

    /// # Safety
    /// user code must initialize this
    unsafe fn allocate_raw_array(&mut self, size: usize) -> Handle<Array> {
        let layout = Array::required_layout(size);
        // SAFETY: allocate_handle returns valid memory, init called immediately after.
        let mut array = unsafe { self.allocate_handle::<Array>(layout) };
        array.init(size);
        array
    }

    fn allocate_array(&mut self, data: &[Value]) -> Handle<Array> {
        let layout = Array::required_layout(data.len());
        // SAFETY: allocate_handle returns valid memory, init_with_data called immediately after.
        let mut array = unsafe { self.allocate_handle::<Array>(layout) };
        array.init_with_data(data);
        array
    }

    /// Allocate an array with all slots initialized to the same value.
    fn allocate_array_fill(
        &mut self,
        size: usize,
        fill: Value,
    ) -> Handle<Array> {
        let layout = Array::required_layout(size);
        // SAFETY: allocate_handle returns valid memory, init_fill called immediately after.
        let mut array = unsafe { self.allocate_handle::<Array>(layout) };
        array.init_fill(size, fill);
        array
    }

    fn allocate_code(
        &mut self,
        constants: &[Value],
        instructions: &[u8],
        feedback_slot_count: u32,
        body: Handle<Array>,
        feedback_vector: Handle<Array>,
    ) -> Handle<Code> {
        let layout = Code::required_layout(constants.len(), instructions.len());
        // SAFETY: init is called immediately
        let mut code = unsafe { self.allocate_handle::<Code>(layout) };
        code.init_with_data(
            constants,
            instructions,
            feedback_slot_count,
            body,
            feedback_vector,
        );
        code
    }

    fn allocate_feedback_entry(
        &mut self,
        receiver_map: Handle<Map>,
        holder_map: Handle<Map>,
        holder: Handle<HeapValue>,
        slot_index: usize,
    ) -> Handle<FeedbackEntry> {
        let layout = Layout::new::<FeedbackEntry>();
        // SAFETY: allocate_handle returns valid memory, init called immediately after.
        let mut entry =
            unsafe { self.allocate_handle::<FeedbackEntry>(layout) };
        entry.init(receiver_map, holder_map, holder, slot_index);
        entry
    }

    fn allocate_slot_map_helper(
        &mut self,
        strings: &Strings,
        slots: &[SlotHelper],
    ) -> Handle<Map> {
        let slots = slots
            .iter()
            .map(|slot| {
                let interned = strings.get(slot.name, self);
                SlotDescriptor::new(interned, slot.tags, slot.value)
            })
            .collect::<Vec<_>>();

        // SAFETY: Null code handle is valid for non-executable slot maps.
        let code = unsafe { Handle::null() };
        self.allocate_slots_map(&slots, code, 0u64.into())
    }

    fn allocate_slot_map_helper2(
        &mut self,
        strings: &Strings,
        slots: &[SlotHelper],
        code: Handle<Code>,
        effect: Tagged<u64>,
    ) -> Handle<Map> {
        let slots = slots
            .iter()
            .map(|slot| {
                let interned = strings.get(slot.name, self);
                SlotDescriptor::new(interned, slot.tags, slot.value)
            })
            .collect::<Vec<_>>();

        self.allocate_slots_map(&slots, code, effect)
    }

    fn allocate_slots_map(
        &mut self,
        slots: &[SlotDescriptor],
        code: Handle<Code>,
        effect: Tagged<u64>,
    ) -> Handle<Map> {
        let layout = Map::required_layout(slots.len());
        // SAFETY: allocate_handle returns valid memory, init_with_data called immediately after.
        let mut map = unsafe { self.allocate_handle::<Map>(layout) };
        map.init_with_data(slots, code, effect);
        map
    }

    fn allocate_executable_map(
        &mut self,
        code: Handle<Code>,
        input: u64,
        output: u64,
    ) -> Handle<Map> {
        let effect = (input << 32) | output;
        self.allocate_slots_map(&[], code, effect.into())
    }

    fn allocate_empty_map(&mut self) -> Handle<Map> {
        // SAFETY: Null code handle is valid for non-executable slot maps.
        let code = unsafe { Handle::null() };
        self.allocate_slots_map(&[], code, 0u64.into())
    }

    fn allocate_slots(
        &mut self,
        map: Handle<Map>,
        slots: &[Value],
    ) -> Handle<SlotObject> {
        let assignable_slots = map.assignable_slots_count();
        let layout = SlotObject::required_layout(assignable_slots);
        // SAFETY: allocate_handle returns valid memory, init_with_data called immediately after.
        let mut obj = unsafe { self.allocate_handle::<SlotObject>(layout) };
        obj.init_with_data(map, slots);
        obj
    }

    fn allocate_quotation(
        &mut self,
        map: Handle<Map>,
        parent: Handle<ActivationObject>,
    ) -> Handle<Quotation> {
        let layout = Layout::new::<Quotation>();
        // SAFETY: allocate_handle returns valid memory, init called immediately after.
        let mut obj = unsafe { self.allocate_handle::<Quotation>(layout) };
        obj.init(map, parent);
        obj
    }

    /// # Safety
    /// must be initialed with data afterwards
    unsafe fn allocate_activation_raw(
        &mut self,
        receiver: Handle<Value>,
        map: Handle<Map>,
        slots: &[Handle<Value>],
    ) -> Handle<ActivationObject> {
        let layout = ActivationObject::required_layout(slots.len());
        // SAFETY: allocate_handle returns valid memory, init called immediately after.
        let mut obj =
            unsafe { self.allocate_handle::<ActivationObject>(layout) };
        obj.init(receiver, map, slots);
        obj
    }

    fn allocate_method_activation(
        &mut self,
        receiver: Handle<Value>,
        method: Handle<SlotObject>,
        slots: &[Handle<Value>],
    ) -> Handle<ActivationObject> {
        // SAFETY: All handles are valid, slots.len() matches map's requirements.
        unsafe { self.allocate_activation_raw(receiver, method.map, slots) }
    }

    fn allocate_quotation_activation(
        &mut self,
        quotation: Handle<Quotation>,
        slots: &[Handle<Value>],
    ) -> Handle<ActivationObject> {
        // SAFETY: Quotation maps are always executable maps (Map type).
        let map = unsafe { quotation.map.cast::<Map>() };
        let receiver = if quotation.parent.as_ptr().is_null() {
            Handle::<Value>::zero()
        } else {
            quotation.parent.receiver
        };
        // SAFETY: All handles are valid, slots.len() matches map's requirements.
        unsafe { self.allocate_activation_raw(receiver, map, slots) }
    }

    /// Allocate a Parser on the GC heap with the given source code.
    fn allocate_parser(
        &mut self,
        strings: &Strings,
        code: &[u8],
    ) -> Handle<Parser> {
        // Create the parser's map with its primitive slots
        let map = self.allocate_slot_map_helper(
            strings,
            &[
                SlotHelper::primitive_message("parseNext", SlotTags::empty()),
                SlotHelper::primitive_message("parseUntil", SlotTags::empty()),
                SlotHelper::primitive_message("parse", SlotTags::empty()),
            ],
        );

        let layout = Layout::new::<Parser>();
        // SAFETY: allocate_handle returns valid memory, init called immediately after.
        let mut parser = unsafe { self.allocate_handle::<Parser>(layout) };
        parser.init(map, code);
        parser
    }
}
