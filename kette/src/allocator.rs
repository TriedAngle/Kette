use std::{alloc::Layout, ptr::NonNull};

use crate::{
    ActivationObject, Array, Block, ByteArray, ExecutableMap, Float, Handle,
    HeapObject, Message, Method, MethodMap, Quotation, QuotationMap,
    SlotDescriptor, SlotHelper, SlotMap, SlotObject, StackEffect, Strings,
    Tagged, Value,
};

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocationType {
    Free = 0b00,
    Boxed = 0b01,
    Unboxed = 0b10,
    Code = 0b11,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapSpace {
    Nursery,
    Immix,
}

impl HeapSpace {
    pub const COUNT: usize = 2;
}

#[derive(Debug, Clone, Copy)]
pub struct Search {
    pub layout: Layout, 
    pub kind: AllocationType,
    pub space: HeapSpace,
}

#[derive(Debug, Clone, Copy)]
pub struct AllocationResult {
    pub page_index: usize,
    pub ptr: NonNull<u8>,
}

pub trait Allocator: Sized {
    fn allocate(&mut self, search: Search) -> AllocationResult;

    /// Allocate a new Object and return it as a typed Handle
    /// # Safety
    /// the caller must guarantee to not experience any GC throughout the result's whole lifetime.
    unsafe fn allocate_handle<T: HeapObject>(
        &mut self,
        search: Search,
    ) -> Handle<T> {
        let raw = self.allocate(search).ptr.cast::<T>();
        // SAFETY: by contract will be initialized after
        unsafe { Handle::new_ptr(raw.as_ptr()) }
    }

    fn allocate_float(&mut self, value: f64) -> Handle<Float> {
        let layout = Layout::new::<Float>();

        let search = Search::unboxed(layout);
        // SAFETY: initialize after
        let mut obj = unsafe { self.allocate_handle::<Float>(search) };

        obj.init(value);
        obj
    }

    fn allocate_aligned_bytearray_zeroed(
        &mut self,
        size: usize,
        align: usize,
    ) -> Handle<ByteArray> {
        let layout = ByteArray::required_layout_size_align(size, align);
        let search = Search::unboxed(layout);
        // SAFETY: this is safe
        let mut ba = unsafe { self.allocate_handle::<ByteArray>(search) };
        ba.init_zeroed(size);

        ba
    }

    fn allocate_aligned_bytearray(
        &mut self,
        data: &[u8],
        align: usize,
    ) -> Handle<ByteArray> {
        let layout = ByteArray::required_layout_size_align(data.len(), align);
        let search = Search::unboxed(layout);
        // SAFETY: this is safe
        let mut ba = unsafe { self.allocate_handle::<ByteArray>(search) };
        ba.init_data(data);

        ba
    }

    fn allocate_message(
        &mut self,
        interned: Handle<ByteArray>,
    ) -> Handle<Message> {
        let layout = Layout::new::<StackEffect>();
        let search = Search::boxed(layout.size());

        // SAFETY: this is safe
        let mut obj = unsafe { self.allocate_handle::<Message>(search) };

        obj.init(interned.as_tagged());
        obj
    }

    /// # Safety
    /// user code must initialize this
    unsafe fn allocate_raw_array(&mut self, size: usize) -> Handle<Array> {
        let layout = Array::required_layout(size);
        let search = Search::boxed(layout.size());

        // SAFETY: initialize after
        let mut array = unsafe { self.allocate_handle::<Array>(search) };

        // SAFETY: must be initialized before usage
        unsafe { array.init(size) };

        array
    }

    fn allocate_array(&mut self, data: &[Value]) -> Handle<Array> {
        let layout = Array::required_layout(data.len());
        let search = Search::boxed(layout.size());

        // SAFETY:
        let mut array = unsafe { self.allocate_handle::<Array>(search) };

        array.init_with_data(data);

        array
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
                SlotDescriptor::new(interned.into(), slot.tags, slot.value)
            })
            .collect::<Vec<_>>();

        self.allocate_slots_map(&slots)
    }

    fn allocate_slots_map(
        &mut self,
        slots: &[SlotDescriptor],
    ) -> Handle<SlotMap> {
        let layout = SlotMap::required_layout(slots.len());
        let search = Search::boxed(layout.size());

        // SAFETY: initialize after
        let mut map = unsafe { self.allocate_handle::<SlotMap>(search) };
        map.init_with_data(slots);

        map
    }

    fn allocate_empty_map(&mut self) -> Handle<SlotMap> {
        self.allocate_slots_map(&[])
    }

    fn allocate_slots(
        &mut self,
        map: Handle<SlotMap>,
        slots: &[Value],
    ) -> Handle<SlotObject> {
        let assignable_slots = map.assignable_slots_count();
        let layout = SlotObject::required_layout(assignable_slots);
        let search = Search::boxed(layout.size());
        // SAFETY: this is safe
        let mut obj = unsafe { self.allocate_handle::<SlotObject>(search) };
        obj.init_with_data(map.as_tagged(), slots);

        obj
    }

    fn allocate_effect(
        &mut self,
        inputs: Tagged<Array>,
        outputs: Tagged<Array>,
    ) -> Handle<StackEffect> {
        let layout = Layout::new::<StackEffect>();
        let search = Search::boxed(layout.size());

        // SAFETY: initialize after
        let mut obj = unsafe { self.allocate_handle::<StackEffect>(search) };

        obj.init(inputs, outputs);
        obj
    }

    /// name must be interned !
    fn allocate_method_map(
        &mut self,
        name: Handle<ByteArray>,
        code: &Block,
        slots: &[SlotDescriptor],
        effect: Tagged<StackEffect>,
    ) -> Handle<MethodMap> {
        let layout = MethodMap::required_layout(slots.len());
        let search = Search::boxed(layout.size());

        // SAFETY: this is safe
        let mut obj = unsafe { self.allocate_handle::<MethodMap>(search) };

        // SAFETY: this is safe
        obj.init_with_data(name, effect, code as *const _ as _, slots);
        obj
    }

    fn allocate_method_object(
        &mut self,
        map: Handle<MethodMap>,
    ) -> Handle<Method> {
        let layout = Layout::new::<Method>();
        let search = Search::boxed(layout.size());

        // SAFETY: initialize after
        let mut obj = unsafe { self.allocate_handle::<Method>(search) };

        obj.init(map.as_tagged());
        obj
    }

    fn allocate_quotation_map(
        &mut self,
        code: &Block,
        input: usize,
        output: usize,
    ) -> Handle<QuotationMap> {
        let layout = QuotationMap::required_layout();
        let search = Search::boxed(layout.size());

        // SAFETY: this is safe
        let mut obj = unsafe { self.allocate_handle::<QuotationMap>(search) };

        // SAFETY: initialize after
        obj.init(code, input, output);

        obj
    }

    fn allocate_quotation(
        &mut self,
        body: Handle<Array>,
        bytecode: &Block,
        input: usize,
        output: usize,
    ) -> Handle<Quotation> {
        let map = self.allocate_quotation_map(bytecode, input, output);
        let layout = Layout::new::<Quotation>();
        let search = Search::boxed(layout.size());

        // SAFETY: this is safe
        let mut obj = unsafe { self.allocate_handle::<Quotation>(search) };

        // SAFETY: we just create this here
        obj.init(body.as_tagged(), map.as_tagged());
        obj
    }

    /// # Safety
    /// must be initialed with data afterwards
    unsafe fn allocate_activation_raw(
        &mut self,
        receiver: Handle<Value>,
        map: Handle<ExecutableMap>,
        slots: &[Handle<Value>],
    ) -> Handle<ActivationObject> {
        let layout = ActivationObject::required_layout(slots.len());
        let search = Search::boxed(layout.size());

        // SAFETY: initialize after
        let mut obj =
            unsafe { self.allocate_handle::<ActivationObject>(search) };

        obj.init(receiver, map, slots);
        obj
    }

    fn allocate_method_activation(
        &mut self,
        receiver: Handle<Value>,
        method: Handle<Method>,
        slots: &[Handle<Value>],
    ) -> Handle<ActivationObject> {
        // SAFETY: safe by contract
        let map = unsafe { method.map.promote_to_handle() };
        // SAFETY: every method map is an executable map
        let map = unsafe { map.cast::<ExecutableMap>() };
        // SAFETY: handles safe, slots must be same size as map wants
        unsafe { self.allocate_activation_raw(receiver, map, slots) }
    }

    fn allocate_quotation_activation(
        &mut self,
        receiver: Handle<Value>,
        quotation: Handle<Quotation>,
        slots: &[Handle<Value>],
    ) -> Handle<ActivationObject> {
        // SAFETY: every method map is an executable map
        let map = unsafe {
            quotation.map.cast::<ExecutableMap>().promote_to_handle()
        };
        // SAFETY: handles safe, slots must be same size as map wants
        unsafe { self.allocate_activation_raw(receiver, map, slots) }
    }
}

impl Search {
    #[inline]
    pub fn new(
        layout: Layout,
        kind: AllocationType,
        space: HeapSpace,
    ) -> Self {
        Self {
            layout, 
            kind,
            space,
        }
    }

    #[inline]
    pub fn new_size_align(
        size: usize,
        align: usize,
        kind: AllocationType,
        space: HeapSpace,
    ) -> Self {
        let layout = Layout::from_size_align(size, align).expect("valid layout");
        Self {
            layout, 
            kind,
            space,
        }
    }

    #[inline]
    pub fn boxed(size: usize) -> Self {
        let layout = Layout::from_size_align(size, 16).expect("valid layout");
        Self::new(layout, AllocationType::Boxed, HeapSpace::Nursery)
    }

    #[inline]
    pub fn unboxed(layout: Layout) -> Self {
        Self::new(
           layout, 
            AllocationType::Unboxed,
            HeapSpace::Nursery,
        )
    }
}
