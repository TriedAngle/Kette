use std::mem;

use crate::{
    ExecutableMap, Header, HeaderFlags, HeapObject, Object, Selector, Tagged,
    Value, Visitable, VisitedLink,
};

pub enum ActivationType {
    Method,
    Quotation,
}

pub struct Activation {
    pub object: ActivationObject,
    pub ty: ActivationType,
    pub stack_ptr: usize,
}

pub struct ActivationObject {
    pub header: Header,
    pub map: Tagged<ExecutableMap>,
    pub receiver: Value,
    pub slots: [Value; 0],
}

pub struct ActivationStack(Vec<Activation>);

impl ActivationObject {
    pub unsafe fn init(
        &mut self,
        receiver: Value,
        map: Tagged<ExecutableMap>,
        arguments: &[Value],
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
        let map = unsafe { map.as_ref() };
        assert_eq!(
            map.map.assignable_slots_count(),
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
    fn slots_ptr(&self) -> *const Value {
        self.slots.as_ptr()
    }

    #[inline]
    fn slots_mut_ptr(&mut self) -> *mut Value {
        self.slots.as_mut_ptr()
    }

    #[inline]
    pub fn assignable_slots(&self) -> usize {
        // SAFETY: every object MUST have a map object
        let map = unsafe { self.map.as_ref() };
        map.map.assignable_slots_count()
    }

    #[inline]
    pub fn slots(&self) -> &[Value] {
        let len = self.assignable_slots();
        // SAFETY: pointer and length must be valid
        unsafe { std::slice::from_raw_parts(self.slots_ptr(), len) }
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

    pub fn current<'a>(&'a self) -> &'a Activation {
        self.0.last().expect("top most exists")
    }

    pub fn current_mut<'a>(&'a mut self) -> &'a mut Activation {
        self.0.last_mut().expect("top most exists")
    }

    pub fn new_activation(
        &mut self,
        ty: ActivationType,
        object: ActivationObject,
        stack_ptr: usize,
    ) {
        let activation = Activation {
            object,
            ty,
            stack_ptr,
        };

        self.0.push(activation);
    }
}

impl Visitable for ActivationObject {}

impl Object for ActivationObject {
    fn lookup(
        &self,
        selector: Selector<'_>,
        link: Option<&VisitedLink>,
    ) -> crate::LookupResult {
        // let slots = self.
        unimplemented!()
    }
}

impl HeapObject for ActivationObject {
    fn heap_size(&self) -> usize {
        let map = unsafe { self.map.as_ref() };
        let slot_count = map.map.assignable_slots_count();
        mem::size_of::<Self>() + slot_count * mem::size_of::<Value>()
    }
}
