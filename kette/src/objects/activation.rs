use std::{alloc::Layout, mem};

use crate::{
    Block, ExecutableMap, Handle, Header, HeaderFlags, HeapObject,
    LookupResult, MethodMap, Object, Selector, Tagged, Value, Visitable,
    VisitedLink,
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
    pub map: Handle<ExecutableMap>,
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
    pub fn code(&self) -> *const Block {
        let object = self.object;
        object.code()
    }
}

impl ActivationObject {
    /// # Safety
    /// must all be valid ojects and correctly sized allocated
    /// # Panics
    /// arguments must have same length as map requires
    pub unsafe fn init(
        &mut self,
        receiver: Handle<Value>,
        map: Handle<ExecutableMap>,
        arguments: &[Handle<Value>],
    ) {
        self.header = Header::encode_object(
            crate::ObjectType::Activation,
            0,
            HeaderFlags::empty(),
            0,
        );
        self.map = map;
        self.receiver = receiver;

        // Safety: map is valid here
        assert_eq!(
            map.slot_count(),
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
    pub fn code(&self) -> *const Block {
        // SAFETY: safe by contract
        let code_value: usize = self.map.code.into();
        code_value as *const Block
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
        object: Tagged<ActivationObject>,
        ty: ActivationType,
    ) {
        // SAFETY: part of gc scan
        let object = unsafe { object.promote_to_handle() };
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
}

impl Default for ActivationStack {
    fn default() -> Self {
        Self::new()
    }
}

impl Visitable for ActivationObject {}

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
    fn heap_size(&self) -> usize {
        if let Some(method) = self.map.as_method_map() {
            let slot_count = method.slot_count();
            return mem::size_of::<MethodMap>()
                + slot_count * mem::size_of::<Value>();
        }

        if let Some(_quotation) = self.map.as_quotation_map() {
            unimplemented!("TODO: implement quotation fully")
            // let slot_count = method.slot_count();
            // return mem::size_of::<Self>() + slot_count * mem::size_of::<Value>()
        }

        unreachable!("all map types should be covered")
    }
}
