// this is a very simple vector implementation,
// intended to be only used for parsing bootstrapping
// later in runtime we define an actual vector

use crate::{
    Allocator, Array, ExecutionResult, Handle, Header, HeapObject, HeapProxy,
    Object, PrimitiveContext, SlotHelper, SlotMap, SlotTags, Strings, Tagged,
    VMShared, Value, Visitable,
};

#[repr(C)]
#[derive(Debug)]
pub struct Vector {
    pub header: Header,
    pub map: Tagged<SlotMap>,
    pub data: Tagged<Array>,
    pub length: Tagged<usize>,
}

impl Vector {
    pub fn new(
        heap: &mut HeapProxy,
        vm: &VMShared,
        size: usize,
    ) -> Handle<Vector> {
        let false_obj = vm.specials.false_object.as_value();
        // SAFETY: initialize directly after
        let mut array = unsafe { heap.allocate_raw_array(size) };
        array.fields_mut().fill(false_obj);
        let data = &[array.as_value(), 0usize.into()];
        let map = vm.specials.primitive_vector_map;
        let vector = heap.allocate_slots(map, data);
        // SAFETY: this is safe
        unsafe { vector.cast() }
    }

    #[rustfmt::skip]
    pub fn new_map(heap: &mut HeapProxy, strings: &Strings) -> Handle<SlotMap> {
        heap.allocate_slot_map_helper(strings, &[
            SlotHelper::assignable("data", Value::from_usize(0), SlotTags::empty()),
            SlotHelper::assignable("length", Value::from_usize(1), SlotTags::empty()),
            SlotHelper::primitive_message2("push", "vectorPush", SlotTags::empty()),
        ])
    }

    pub fn capacity(&self) -> usize {
        // SAFETY: this is safe by convention
        unsafe { self.data.as_ref() }.size()
    }

    pub fn len(&self) -> usize {
        self.length.into()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn push(&mut self, value: Value, heap: &mut HeapProxy, vm: &VMShared) {
        let current_len = self.len();
        let current_cap = self.capacity();

        if current_len == current_cap {
            let new_cap = if current_cap == 0 { 4 } else { current_cap * 2 };

            let false_obj = vm.specials.false_object.as_value();
            // SAFETY: initialize directly after
            let mut array = unsafe { heap.allocate_raw_array(new_cap) };

            array.fields_mut().fill(false_obj);

            // SAFETY: this must exist
            let old_array = unsafe { self.data.as_ref() };

            array.fields_mut()[..current_len]
                .copy_from_slice(old_array.fields());

            self.data = array.as_tagged();
        }
        // SAFETY: size checked
        unsafe {
            self.data.as_mut().set_unchecked(current_len, value);
        }
        self.length = (current_len + 1).into();
    }

    /// Returns a slice of the valid elements in the vector.
    pub fn as_slice(&self) -> &[Value] {
        let len = self.len();
        // SAFETY: The backing array is guaranteed to be at least `len` size.
        unsafe { &self.data.as_ref().fields()[..len] }
    }

    /// Returns a mutable slice of the valid elements in the vector.
    pub fn as_mut_slice(&mut self) -> &mut [Value] {
        let len = self.len();
        // SAFETY: The backing array is guaranteed to be at least `len` size.
        unsafe { &mut self.data.as_mut().fields_mut()[..len] }
    }
}

impl Visitable for Vector {}
impl Object for Vector {}
impl HeapObject for Vector {
    fn heap_size(&self) -> usize {
        std::mem::size_of::<Self>()
    }
}

pub fn push(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let value = ctx.inputs[0];
    // SAFETY: this is safe
    let mut vector = unsafe { ctx.receiver.cast::<Vector>() };
    vector.push(value.into(), ctx.heap, &ctx.vm.shared);

    ExecutionResult::Normal
}
