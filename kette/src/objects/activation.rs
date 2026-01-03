use std::{alloc::Layout, mem};

use crate::{
    Code, Handle, Header, HeapObject, LookupResult, Object, ObjectKind,
    ObjectType, Selector, SlotMap, Value, Visitable, VisitedLink, Visitor,
};

#[repr(C)]
#[derive(Debug)]
pub enum ActivationType {
    Method,
    Quotation,
}

#[repr(C)]
#[derive(Debug)]
pub struct Activation {
    pub object: Handle<ActivationObject>,
    pub ty: ActivationType,
    /// instruction index, combined with the code in ExecutableMap
    pub index: usize,
}

// TODO: add scope
#[repr(C)]
#[derive(Debug)]
pub struct ActivationObject {
    pub header: Header,
    pub map: Handle<SlotMap>,
    pub receiver: Handle<Value>,
    // either the parent or false. implement this with scope
    // lambdas must probably be handled special, because they can escape their creation scope
    // pub parent: Tagged<ActivationObject>,
    // currently: inputs, later locals too
    pub slots: [Handle<Value>; 0],
}

pub struct ActivationStack(Vec<Activation>);

impl Activation {
    #[inline]
    pub fn code(&self) -> &Code {
        self.object.code()
    }
}

impl ActivationObject {
    /// # Panics
    /// arguments must have same length as map requires
    pub fn init(
        &mut self,
        receiver: Handle<Value>,
        map: Handle<SlotMap>,
        arguments: &[Handle<Value>],
    ) {
        self.header = Header::new_object(ObjectType::Activation);
        self.map = map;
        self.receiver = receiver;

        // TODO: must be fixed for quotations
        // Safety: map is valid here
        assert_eq!(
            map.input_count(),
            arguments.len(),
            "map and arguments must be same length"
        );

        let ptr = self.slots.as_mut_ptr();
        // Safety: assumption activation object is allocated with correct size
        unsafe {
            std::ptr::copy_nonoverlapping(
                arguments.as_ptr(),
                ptr,
                arguments.len(),
            );
        };
    }

    #[inline]
    pub fn slots_ptr(&self) -> *const Handle<Value> {
        self.slots.as_ptr()
    }

    #[inline]
    pub fn slots_mut_ptr(&mut self) -> *mut Handle<Value> {
        self.slots.as_mut_ptr()
    }

    #[inline]
    pub fn assignable_slots(&self) -> usize {
        // SAFETY: every object MUST have a map object
        self.map.slot_count()
    }

    #[inline]
    pub fn slots(&self) -> &[Handle<Value>] {
        let len = self.assignable_slots();
        // SAFETY: pointer and length must be valid
        unsafe { std::slice::from_raw_parts(self.slots_ptr(), len) }
    }

    #[inline]
    pub fn code(&self) -> &Code {
        // SAFETY: safe by contract
        debug_assert!(self.map.has_code());

        let Some(code) = self.map.code() else {
            unreachable!("map must have code at this point")
        };
        code
    }

    /// calculate the layout of an Activation with inputs amount slots
    pub fn required_layout(inputs: usize) -> Layout {
        let head = Layout::new::<Self>();
        let slots_layout =
            Layout::array::<Value>(inputs).expect("create valid layout");
        let (layout, _) =
            head.extend(slots_layout).expect("create valid layout");
        layout
    }
}

impl ActivationStack {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn push(&mut self, activation: Activation) {
        self.0.push(activation);
    }

    pub fn pop(&mut self) -> Activation {
        self.0.pop().expect("popping activation")
    }

    pub fn current(&self) -> Option<&Activation> {
        self.0.last()
    }

    pub fn current_mut(&mut self) -> Option<&mut Activation> {
        self.0.last_mut()
    }

    pub fn depth(&self) -> usize {
        self.0.len()
    }

    pub fn new_activation(
        &mut self,
        object: Handle<ActivationObject>,
        ty: ActivationType,
    ) {
        // SAFETY: part of gc scan
        let activation = Activation {
            object,
            ty,
            index: 0,
        };

        self.0.push(activation);
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns an iterator over the activations (stack frames).
    pub fn iter(&self) -> std::slice::Iter<'_, Activation> {
        self.0.iter()
    }

    /// Returns a mutable iterator over the activations.
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, Activation> {
        self.0.iter_mut()
    }
}

impl Default for ActivationStack {
    fn default() -> Self {
        Self::new()
    }
}

impl Visitable for ActivationObject {
    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        visitor.visit(self.map.as_value());
        visitor.visit(self.receiver.as_value());
        self.slots()
            .iter()
            .for_each(|slot| visitor.visit(slot.as_value()))
    }

    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        visitor.visit_mut(self.map.as_value());
        visitor.visit_mut(self.receiver.as_value());
        self.slots()
            .iter()
            .for_each(|slot| visitor.visit_mut(slot.as_value()))
    }
}

impl Object for ActivationObject {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        self.receiver.as_value().lookup(selector, link)
    }
}

impl HeapObject for ActivationObject {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Activation as u8;

    fn heap_size(&self) -> usize {
        let count = self.map.assignable_slots_count();
        mem::size_of::<Self>() + count * mem::size_of::<Value>()
    }
}
