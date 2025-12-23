use std::{alloc::Layout, mem, ptr};

use crate::{
    Array, ByteArray, Handle, Header, HeapObject, LookupResult, Map, MapType,
    Object, ObjectKind, ObjectType, QuotationMap, Selector, SlotDescriptor,
    SlotMap, Tagged, Visitable, VisitedLink,
};

// TODO: I wish there was an easy way to share SlotMap here
#[repr(C)]
#[derive(Debug)]
pub struct ExecutableMap {
    pub map: Map,
    // secretely a *const Block
    pub code: Tagged<usize>,
    // this is like effect in method map, but just as number
    pub input_effect: Tagged<usize>,
    pub output_effect: Tagged<usize>,
    // here further implementation is expected
}

#[repr(C)]
#[derive(Debug)]
pub struct MethodMap {
    pub map: ExecutableMap,
    // this effefct must be declared
    pub effect: Tagged<StackEffect>,
    pub name: Tagged<ByteArray>,
    pub slott_count: Tagged<usize>,
    pub slots: [SlotDescriptor; 0],
}

#[repr(C)]
#[derive(Debug)]
pub struct Method {
    pub header: Header,
    pub map: Tagged<MethodMap>,
}

#[repr(C)]
#[derive(Debug)]
pub struct StackEffect {
    pub header: Header,
    pub map: Tagged<SlotMap>,
    pub inputs: Tagged<Array>,
    pub outputs: Tagged<Array>,
}

impl ExecutableMap {
    /// Initialize the ExecutableMap for a MethodMap
    /// # Safety
    /// Pointers must be valid
    /// usage must be valid
    pub unsafe fn init_method(
        &mut self,
        code: usize,
        input: usize,
        output: usize,
    ) {
        self.map.init(MapType::Method);
        self.code = Tagged::new_value(code);
        self.input_effect = input.into();
        self.output_effect = output.into();
    }

    /// Initialize the ExecutableMap for a MethodMap
    /// # Safety
    /// Pointers must be valid
    /// usage must be valid
    pub unsafe fn init_quotation(
        &mut self,
        code: usize,
        input: usize,
        output: usize,
    ) {
        self.map.init(MapType::Quotation);
        self.code = Tagged::new_value(code);
        self.input_effect = input.into();
        self.output_effect = output.into();
    }

    /// Cast an ExecutableMap to a MethodMap
    pub fn as_method_map(&self) -> Option<&MethodMap> {
        // SAFETY: must be safe by contract
        if unsafe { self.map.map_type().unwrap_unchecked() } == MapType::Method
        {
            // SAFETY: checked
            let map = unsafe { mem::transmute::<&Self, &MethodMap>(self) };
            return Some(map);
        }
        None
    }

    /// Cast an ExecutableMap to a QuotationMap
    pub fn as_quotation_map(&self) -> Option<&QuotationMap> {
        // SAFETY: must be safe by contract
        if unsafe { self.map.map_type().unwrap_unchecked() }
            == MapType::Quotation
        {
            // SAFETY: checked
            let map = unsafe { mem::transmute::<&Self, &QuotationMap>(self) };
            return Some(map);
        }
        None
    }

    pub fn slot_count(&self) -> usize {
        if let Some(method) = self.as_method_map() {
            return method.slot_count();
        }

        if let Some(_quotation) = self.as_quotation_map() {
            return 0;
        }

        unreachable!("all map types should be covered")
    }
}

impl MethodMap {
    pub fn required_layout(slots: usize) -> Layout {
        let head = Layout::new::<Self>();
        let slots_layout = Layout::array::<SlotDescriptor>(slots)
            .expect("create valid layout");
        let (layout, _) =
            head.extend(slots_layout).expect("create valid layout");
        layout
    }

    /// # Safety
    /// internal function, dicouraged to be used.
    /// must have valid allocation size
    /// inputs must not be null/false
    pub fn init_with_data(
        &mut self,
        name: Handle<ByteArray>,
        effect: Tagged<StackEffect>,
        code_ptr: usize,
        slots: &[SlotDescriptor],
    ) {
        // 1. Sort slots (Consistency with SlotMap: Assignable > Parent > Constant)
        let mut slots = slots.to_vec();
        slots.sort_by(|a, b| {
            let tags_a = a.tags();
            let tags_b = b.tags();
            // We only care about the ordering bits (0b11)
            (tags_a.bits() & 0b11).cmp(&(tags_b.bits() & 0b11))
        });

        // SAFETY: safe by contract
        let effect_ref = unsafe { effect.as_ref() };
        // SAFETY: safe by contract
        let input = unsafe { effect_ref.inputs.as_ref().size() };
        // SAFETY: safe by contract
        let output = unsafe { effect_ref.outputs.as_ref().size() };

        // SAFETY: safe by contract
        unsafe { self.map.init_method(code_ptr, input, output) };
        self.name = name.as_tagged();
        self.effect = effect;
        self.slott_count = Tagged::new_value(slots.len());

        // SAFETY: safe if allocation is correctly sized
        unsafe {
            ptr::copy_nonoverlapping(
                slots.as_ptr(),
                self.slots.as_mut_ptr(),
                slots.len(),
            )
        };
    }

    #[inline]
    pub fn slot_count(&self) -> usize {
        self.slott_count.into()
    }

    #[inline]
    pub fn slots(&self) -> &[SlotDescriptor] {
        let count = self.slot_count();
        // SAFETY: Safe if object initialized correctly via init_with_data
        unsafe { std::slice::from_raw_parts(self.slots.as_ptr(), count) }
    }

    #[inline]
    pub fn code_ptr(&self) -> usize {
        self.map.code.into()
    }
}

impl Method {
    pub fn init(&mut self, map: Tagged<MethodMap>) {
        self.header = Header::new_object(ObjectType::Method);
        self.map = map;
    }
}

impl StackEffect {
    /// # Safety
    /// internal function do not use pls
    pub fn init(&mut self, inputs: Tagged<Array>, outputs: Tagged<Array>) {
        self.header = Header::new_object(ObjectType::Effect);
        self.inputs = inputs;
        self.outputs = outputs;
    }
}

impl Object for StackEffect {
    fn lookup(
        &self,
        selector: crate::Selector,
        link: Option<&crate::VisitedLink>,
    ) -> crate::LookupResult {
        let traits = selector.vm.specials.effect_traits;
        traits.lookup(selector, link)
        // TODO: maybe add map lookup
    }
}
impl HeapObject for StackEffect {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Effect as u8;
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl Visitable for StackEffect {
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        // visitor.visit(self.map.into());
        visitor.visit(self.inputs.into());
        visitor.visit(self.outputs.into());
    }

    fn visit_edges_mut(&mut self, visitor: &mut impl crate::Visitor) {
        // visitor.visit(self.map.into());
        visitor.visit(self.inputs.into());
        visitor.visit(self.outputs.into());
    }
}

impl Object for ExecutableMap {}
impl HeapObject for ExecutableMap {
    const KIND: ObjectKind = ObjectKind::Map;
    const TYPE_BITS: u8 = MapType::Quotation as u8;

    fn heap_size(&self) -> usize {
        if let Some(method) = self.as_method_map() {
            return method.heap_size();
        }

        if let Some(quotation) = self.as_quotation_map() {
            return quotation.heap_size();
        }

        unreachable!()
    }
}
impl Visitable for ExecutableMap {}

// TODO: implment this
impl Object for MethodMap {}
impl HeapObject for MethodMap {
    const KIND: ObjectKind = ObjectKind::Map;
    const TYPE_BITS: u8 = MapType::Method as u8;
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}
impl Visitable for MethodMap {
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {}
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {}
}

// TODO: implment this
impl Object for Method {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.method_traits;
        traits.lookup(selector, link)
    }
}

impl HeapObject for Method {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Method as u8;
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl Visitable for Method {
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {}
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {}
}
