use std::{alloc::Layout, ptr::NonNull};

use crate::{
    ActivationObject, Array, ByteArray, Code, Float, Handle, HeapObject,
    Instruction, Message, Quotation, SlotDescriptor, SlotHelper, SlotMap,
    SlotObject, Strings, Tagged, Value,
};

pub trait Allocator: Sized {
    fn allocate(&mut self, layout: Layout) -> NonNull<u8>;

    /// Allocate a new Object and return it as a typed Handle
    /// # Safety
    /// the caller must guarantee to not experience any GC throughout the result's whole lifetime.
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

        // SAFETY: this is safe
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
        // SAFETY: this is safe
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
        // SAFETY: this is safe
        let mut ba = unsafe { self.allocate_handle::<ByteArray>(layout) };
        ba.init_data(data);
        ba
    }

    fn allocate_message(
        &mut self,
        interned: Handle<ByteArray>,
    ) -> Handle<Message> {
        let layout = Layout::new::<Message>();
        // SAFETY: this is safe
        let mut obj = unsafe { self.allocate_handle::<Message>(layout) };
        obj.init(interned);
        obj
    }

    /// # Safety
    /// user code must initialize this
    unsafe fn allocate_raw_array(&mut self, size: usize) -> Handle<Array> {
        let layout = Array::required_layout(size);
        // SAFETY: this is safe
        let mut array = unsafe { self.allocate_handle::<Array>(layout) };
        array.init(size);
        array
    }

    fn allocate_array(&mut self, data: &[Value]) -> Handle<Array> {
        let layout = Array::required_layout(data.len());
        // SAFETY: this is safe
        let mut array = unsafe { self.allocate_handle::<Array>(layout) };
        array.init_with_data(data);
        array
    }

    fn allocate_code(
        &mut self,
        constants: &[Value],
        instructions: &[Instruction],
        body: Handle<Array>,
    ) -> Handle<Code> {
        let layout = Code::required_layout(constants.len(), instructions.len());
        // SAFETY: init is called immediately
        let mut code = unsafe { self.allocate_handle::<Code>(layout) };
        code.init_with_data(constants, instructions, body);
        code
    }

    fn allocate_slot_map_helper(
        &mut self,
        strings: &Strings,
        slots: &[SlotHelper],
    ) -> Handle<SlotMap> {
        let slots = slots
            .iter()
            .map(|slot| {
                let interned = strings.get(slot.name, self);
                SlotDescriptor::new(interned, slot.tags, slot.value)
            })
            .collect::<Vec<_>>();

        // SAFETY: safe because this means no code exist
        let code = unsafe { Handle::null() };
        self.allocate_slots_map(&slots, code, 0u64.into())
    }

    fn allocate_slot_map_helper2(
        &mut self,
        strings: &Strings,
        slots: &[SlotHelper],
        code: Handle<Code>,
        effect: Tagged<u64>,
    ) -> Handle<SlotMap> {
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
    ) -> Handle<SlotMap> {
        let layout = SlotMap::required_layout(slots.len());
        // SAFETY: initialize after
        let mut map = unsafe { self.allocate_handle::<SlotMap>(layout) };
        map.init_with_data(slots, code, effect);
        map
    }

    fn allocate_executable_map(
        &mut self,
        code: Handle<Code>,
        input: u64,
        output: u64,
    ) -> Handle<SlotMap> {
        let effect = (input << 32) | output;
        self.allocate_slots_map(&[], code, effect.into())
    }

    fn allocate_empty_map(&mut self) -> Handle<SlotMap> {
        // SAFETY: safe because this means no code exist
        let code = unsafe { Handle::null() };
        self.allocate_slots_map(&[], code, 0u64.into())
    }

    fn allocate_slots(
        &mut self,
        map: Handle<SlotMap>,
        slots: &[Value],
    ) -> Handle<SlotObject> {
        let assignable_slots = map.assignable_slots_count();
        let layout = SlotObject::required_layout(assignable_slots);
        // SAFETY: this is safe
        let mut obj = unsafe { self.allocate_handle::<SlotObject>(layout) };
        obj.init_with_data(map, slots);
        obj
    }

    fn allocate_quotation(
        &mut self,
        map: Handle<SlotMap>,
        parent: Handle<ActivationObject>,
    ) -> Handle<Quotation> {
        let layout = Layout::new::<Quotation>();
        // SAFETY: this is safe
        let mut obj = unsafe { self.allocate_handle::<Quotation>(layout) };
        obj.init(map, parent);
        obj
    }

    /// # Safety
    /// must be initialed with data afterwards
    unsafe fn allocate_activation_raw(
        &mut self,
        receiver: Handle<Value>,
        map: Handle<SlotMap>,
        slots: &[Handle<Value>],
    ) -> Handle<ActivationObject> {
        let layout = ActivationObject::required_layout(slots.len());
        // SAFETY: initialize after
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
        // SAFETY: handles safe, slots must be same size as map wants
        unsafe { self.allocate_activation_raw(receiver, method.map, slots) }
    }

    fn allocate_quotation_activation(
        &mut self,
        quotation: Handle<Quotation>,
        slots: &[Handle<Value>],
    ) -> Handle<ActivationObject> {
        // SAFETY: every method map is an executable map
        let map = unsafe { quotation.map.cast::<SlotMap>() };
        let receiver = if quotation.parent.as_ptr().is_null() {
            Handle::<Value>::zero()
        } else {
            quotation.parent.receiver
        };
        // SAFETY: this is safe
        unsafe { self.allocate_activation_raw(receiver, map, slots) }
    }
}
