use std::{alloc::Layout, mem};

use crate::{
    Code, Handle, Header, HeapObject, LookupResult, Map, Object, ObjectKind,
    ObjectType, Selector, SlotObject, SlotTags, Tagged, Value, Visitable,
    VisitedLink, Visitor,
};

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActivationType {
    Method,
    Quotation,
}

#[repr(C)]
#[derive(Debug, Clone)]
pub struct Activation {
    pub object: Handle<ActivationObject>,
    pub ty: ActivationType,
    /// instruction index, combined with the code in ExecutableMap
    pub index: usize,
    /// (any value, any callable)
    pub handlers: Vec<(Handle<Value>, Handle<Value>)>,
}

// TODO: add scope
#[repr(C)]
#[derive(Debug)]
pub struct ActivationObject {
    pub header: Header,
    pub map: Handle<Map>,
    pub receiver: Handle<Value>,
    pub parent: Handle<ActivationObject>,
    pub activation_type: ActivationType,
    /// The absolute index of this activation in the ActivationStack.
    /// Used for O(1) unwinding
    pub stack_index: Tagged<usize>,
    // either the parent or false. implement this with scope
    // lambdas must probably be handled special, because they can escape their creation scope
    // pub parent: Tagged<ActivationObject>,
    // currently: inputs, later locals too
    pub slots: [Handle<Value>; 0],
}

#[derive(Debug, Clone)]
pub struct ActivationStack(Vec<Activation>);

impl Activation {
    #[inline]
    #[must_use]
    pub fn code(&self) -> &Code {
        self.object.code()
    }

    /// Getter for the registered handlers in this activation.
    /// Returns: Vec<(Type/Map, Handler)>
    #[inline]
    #[must_use]
    pub fn handlers(&self) -> &[(Handle<Value>, Handle<Value>)] {
        &self.handlers
    }
}

impl ActivationObject {
    /// Initialize an activation object.
    ///
    /// `total_slots` is the number of slots allocated (must match the layout).
    /// `arguments` are the initial values for the first N slots (inputs).
    /// Remaining slots (outputs/locals) are zeroed.
    ///
    /// # Panics
    /// Panics if `arguments.len() > total_slots`.
    pub fn init(
        &mut self,
        receiver: Handle<Value>,
        parent: Handle<ActivationObject>,
        activation_type: ActivationType,
        map: Handle<Map>,
        arguments: &[Handle<Value>],
        total_slots: usize,
    ) {
        self.header = Header::new_object(ObjectType::Activation);
        self.map = map;
        self.receiver = receiver;
        self.parent = parent;
        self.activation_type = activation_type;

        assert!(
            arguments.len() <= total_slots,
            "arguments ({}) must not exceed total_slots ({})",
            arguments.len(),
            total_slots,
        );

        let ptr = self.slots.as_mut_ptr();
        // Safety: assumption activation object is allocated with correct size
        unsafe {
            // Copy the provided arguments (inputs)
            std::ptr::copy_nonoverlapping(
                arguments.as_ptr(),
                ptr,
                arguments.len(),
            );
            // Zero-fill remaining slots (outputs/locals for named-param maps)
            let remaining = total_slots - arguments.len();
            if remaining > 0 {
                std::ptr::write_bytes(ptr.add(arguments.len()), 0, remaining);
            }
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
        // For named-param maps, activations store all named slots (inputs + outputs).
        // For regular maps, only input values.
        self.map.total_named_slots()
    }

    #[inline]
    pub fn slots(&self) -> &[Handle<Value>] {
        let len = self.assignable_slots();
        // SAFETY: pointer and length must be valid
        unsafe { std::slice::from_raw_parts(self.slots_ptr(), len) }
    }

    #[inline]
    pub fn slots_mut(&mut self) -> &mut [Handle<Value>] {
        let len = self.assignable_slots();
        // SAFETY: pointer and length must be valid
        unsafe { std::slice::from_raw_parts_mut(self.slots_mut_ptr(), len) }
    }

    /// Set a slot at the given offset.
    /// # Safety
    /// Caller must ensure `index < assignable_slots()`.
    #[inline]
    pub unsafe fn set_slot_unchecked(&mut self, index: usize, value: Value) {
        debug_assert!(
            index < self.assignable_slots(),
            "set_slot_unchecked out of bounds: {} >= {}",
            index,
            self.assignable_slots()
        );
        // SAFETY: Handle<Value> and Value have the same repr (u64)
        unsafe { (self.slots_mut_ptr() as *mut Value).add(index).write(value) };
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
    #[must_use]
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
    #[must_use]
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn push(&mut self, activation: Activation) {
        self.0.push(activation);
    }

    pub fn pop(&mut self) -> Activation {
        self.0.pop().expect("popping activation")
    }

    #[must_use]
    pub fn current(&self) -> Option<&Activation> {
        self.0.last()
    }

    pub fn current_mut(&mut self) -> Option<&mut Activation> {
        self.0.last_mut()
    }

    #[must_use]
    pub fn depth(&self) -> usize {
        self.0.len()
    }

    pub fn new_activation(
        &mut self,
        mut object: Handle<ActivationObject>,
        ty: ActivationType,
    ) {
        object.stack_index = self.depth().into();

        // SAFETY: part of gc scan
        let activation = Activation {
            object,
            ty,
            index: 0,
            handlers: Vec::new(),
        };

        self.0.push(activation);
    }

    #[must_use]
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

    /// Pushes a new exception handler onto the *current* (top-most) activation.
    ///
    /// # Arguments
    /// * `ty` - The object type (Map/Class) that this handler catches.
    /// * `handler` - The callable (Block/Method) to execute.
    ///
    /// # Panics
    /// Panics if the stack is empty.
    pub fn push_handler(&mut self, ty: Handle<Value>, handler: Handle<Value>) {
        self.current_mut()
            .expect("cannot push handler to empty stack")
            .handlers
            .push((ty, handler));
    }

    /// Search for a handler that matches the provided exception object.
    ///
    /// Matching Logic:
    /// 1. **Fixnum**: Matches by strict equality (value match).
    /// 2. **SlotObject**: Matches if the object's `map` equals the `handler_tag`.
    /// 3. **Other Objects**: Matches if the `ObjectType` (header tag) is identical.
    #[must_use]
    pub fn find_handler(
        &self,
        exception_val: Handle<Value>,
    ) -> Option<(Handle<ActivationObject>, Handle<Value>)> {
        for activation in self.0.iter().rev() {
            for &(guard, handler) in activation.handlers.iter().rev() {
                if Self::matches_exception(exception_val, guard) {
                    return Some((activation.object, handler));
                }
            }
        }
        None
    }

    /// Helper to check if an exception value matches a handler tag/type.
    fn matches_exception(
        exception: Handle<Value>,
        guard: Handle<Value>,
    ) -> bool {
        if exception == guard {
            return true;
        }

        if exception.is_fixnum() || guard.is_fixnum() {
            return false;
        }

        // SAFETY: checked above that neither is a fixnum
        let ex_obj = unsafe { exception.as_heap_value_handle() };
        // SAFETY: checked above that neither is a fixnum
        let handler_obj = unsafe { guard.as_heap_value_handle() };

        if let Some(ex_slot) = ex_obj.downcast_ref::<SlotObject>() {
            // TODO: parenting
            if let Some(handler_slot) = handler_obj.downcast_ref::<SlotObject>()
            {
                return ex_slot.map == handler_slot.map;
            } else {
                return false;
            }
        }

        ex_obj.header.kind() == handler_obj.header.kind()
            && ex_obj.header.type_bits() == handler_obj.header.type_bits()
    }

    /// Unwinds the stack so that `index` becomes the new top of the stack.
    ///
    /// This drops all activations *above* `index`. The activation at `index`
    /// remains alive (it contains the handler code we are about to run).
    pub fn unwind_to(&mut self, index: usize) {
        if index >= self.0.len() {
            return;
        }
        self.0.truncate(index);
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
        visitor.visit(self.map.as_value_ref());
        visitor.visit(self.receiver.as_value_ref());
        if !self.parent.as_ptr().is_null() {
            visitor.visit(self.parent.as_value_ref());
        }
        self.slots()
            .iter()
            .for_each(|slot| visitor.visit(slot.as_value_ref()))
    }

    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        visitor.visit_mut(self.map.as_value_mut());
        visitor.visit_mut(self.receiver.as_value_mut());
        if !self.parent.as_ptr().is_null() {
            visitor.visit_mut(self.parent.as_value_mut());
        }
        self.slots_mut()
            .iter_mut()
            .for_each(|slot| visitor.visit_mut(slot.as_value_mut()))
    }
}

impl Object for ActivationObject {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        // Check own named parameters first (only if the map opts in)
        if self.map.has_named_params() {
            let self_ptr = self as *const Self as *mut Self;
            let self_value = Tagged::new_ptr(self_ptr).as_tagged_value();

            for (idx, slot_desc) in self.map.slots().iter().enumerate() {
                if slot_desc.name.as_ptr() == selector.name.as_ptr() {
                    let mut slot = *slot_desc;
                    // For ASSIGNABLE (getter) slots, resolve the offset to the actual value
                    if slot.tags().contains(SlotTags::ASSIGNABLE) {
                        let offset: usize = slot
                            .value
                            .as_tagged_fixnum::<usize>()
                            .expect("assignable slot must store offset")
                            .into();
                        // SAFETY: offset is valid by construction from the parser
                        slot.value = unsafe {
                            std::ptr::read(self.slots_ptr().add(offset))
                                .as_value()
                        };
                    }
                    return LookupResult::Found {
                        object: self_value,
                        slot,
                        slot_index: idx,
                        traversed_assignable_parent: false,
                    };
                }
            }
        }
        // Walk lexical parent chain (quotations only)
        let mut parent = self.parent;
        while !parent.as_ptr().is_null() {
            // SAFETY: parent handle is valid by construction
            let parent_obj = unsafe { &*parent.as_ptr() };
            if parent_obj.map.has_named_params() {
                let parent_ptr = parent_obj as *const Self as *mut Self;
                let parent_value =
                    Tagged::new_ptr(parent_ptr).as_tagged_value();

                for (idx, slot_desc) in
                    parent_obj.map.slots().iter().enumerate()
                {
                    if slot_desc.name.as_ptr() == selector.name.as_ptr() {
                        let mut slot = *slot_desc;
                        if slot.tags().contains(SlotTags::ASSIGNABLE) {
                            let offset: usize = slot
                                .value
                                .as_tagged_fixnum::<usize>()
                                .expect("assignable slot must store offset")
                                .into();
                            // SAFETY: offset is valid by construction
                            slot.value = unsafe {
                                std::ptr::read::<Handle<Value>>(
                                    parent_obj.slots_ptr().add(offset),
                                )
                                .as_value()
                            };
                        }
                        return LookupResult::Found {
                            object: parent_value,
                            slot,
                            slot_index: idx,
                            traversed_assignable_parent: false,
                        };
                    }
                }
            }
            if parent_obj.activation_type == ActivationType::Method {
                break;
            }
            parent = parent_obj.parent;
        }
        // Fall back to receiver lookup
        self.receiver.as_value().lookup(selector, link)
    }
}

impl HeapObject for ActivationObject {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Activation as u8;

    fn heap_size(&self) -> usize {
        let count = self.map.total_named_slots();
        mem::size_of::<Self>() + count * mem::size_of::<Value>()
    }
}
