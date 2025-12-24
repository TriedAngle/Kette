use crate::{
    Activation, ActivationStack, ActivationType, Allocator, ExecutionState,
    Handle, HeapProxy, Instruction, LookupResult, Method,
    PrimitiveMessageIndex, Quotation, Selector, SlotObject, SlotTags,
    ThreadProxy, VMProxy, Value, get_primitive, transmute,
};

pub struct Interpreter {
    pub vm: VMProxy,
    pub thread: ThreadProxy,
    pub heap: HeapProxy,
    pub state: ExecutionState,
    pub activations: ActivationStack,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NumberError {
    Overflow,
    DivisionByZero,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ExecutionResult {
    Normal,
    ActivationChanged,
    NumberError(NumberError),
    Yield,
    Panic(&'static str),
}

impl Interpreter {
    pub fn new(
        vm: VMProxy,
        thread: ThreadProxy,
        heap: HeapProxy,
        state: ExecutionState,
    ) -> Self {
        Self {
            vm,
            thread,
            heap,
            state,
            activations: ActivationStack::new(),
        }
    }

    #[inline(always)]
    pub fn current_activation(&self) -> Option<&Activation> {
        self.activations.current()
    }

    #[inline(always)]
    pub fn current_activation_mut(&mut self) -> Option<&mut Activation> {
        self.activations.current_mut()
    }

    #[inline(always)]
    pub fn increment_instruction(&mut self) {
        if let Some(activation) = self.current_activation_mut() {
            activation.index += 1
        };
    }

    #[inline(always)]
    pub fn current_instruction(&mut self) -> Option<Instruction> {
        if let Some(activation) = self.current_activation() {
            let index = activation.index;
            let code = activation.code();
            // SAFETY: this is safe
            let instructions = unsafe { &(*code).instructions };
            return Some(instructions[index]);
        }
        None
    }

    pub fn add_quotation(&mut self, quotation: Handle<Quotation>) {
        let receiver = self
            .current_activation()
            .map(|a| a.object.receiver)
            .unwrap_or(self.vm.specials().false_object.as_value_handle());

        let new =
            self.heap
                .allocate_quotation_activation(receiver, quotation, &[]);
        self.activations
            .new_activation(new, ActivationType::Quotation);
    }

    pub fn add_method(
        &mut self,
        receiver: Handle<Value>,
        method: Handle<Method>,
    ) {
        // SAFETY: this is safe, method must exist
        let map = unsafe { method.map.promote_to_handle() };

        let slot_count = map.slot_count();

        // idea: peek here, this saves the inputs,
        // now just continue with normal stack
        // SAFETY: TODO: stack depth check
        let slots =
            unsafe { self.state.stack_peek_slice_unchecked(slot_count) };
        // SAFETY: TODO: actually put them into handle set
        let slots = unsafe { crate::transmute::values_as_handles(slots) };

        let new = self
            .heap
            .allocate_method_activation(receiver, method, slots);
        self.activations.new_activation(new, ActivationType::Method);
    }

    pub fn execute(&mut self) -> ExecutionResult {
        while let Some(instruction) = self.current_instruction() {
            let res = self.execute_single_bytecode(instruction);
            match res {
                ExecutionResult::Normal => self.increment_instruction(),
                ExecutionResult::ActivationChanged => (),
                _ => unimplemented!("TODO"),
            }
        }

        ExecutionResult::Normal
    }

    pub fn execute_with_depth(&mut self) -> ExecutionResult {
        let depth = self.activations.depth();
        while let Some(instruction) = self.current_instruction() {
            let res = self.execute_single_bytecode(instruction);
            match res {
                ExecutionResult::Normal => self.increment_instruction(),
                ExecutionResult::ActivationChanged => {
                    if self.activations.depth() == depth {
                        break;
                    }
                }
                _ => unimplemented!("TODO"),
            }
        }

        ExecutionResult::Normal
    }

    pub fn execute_single_bytecode(
        &mut self,
        instruction: Instruction,
    ) -> ExecutionResult {
        match instruction {
            Instruction::PushSelf => {
                tracing::trace!("push_self");
                let value = self
                    .activations
                    .current()
                    .expect("must exist")
                    .object
                    .receiver;
                self.state.push(value.into());
                self.record_depth();
                ExecutionResult::Normal
            }
            Instruction::PushFixnum { value } => {
                tracing::trace!("push_fixnum: {:?}", value);
                self.state.push(value.into());
                self.record_depth();
                ExecutionResult::Normal
            }
            Instruction::PushValue { value } => {
                tracing::trace!("push_value: {:?}", value);
                self.state.push(value);
                self.record_depth();
                ExecutionResult::Normal
            }
            Instruction::PushQuotaton { value } => {
                tracing::trace!("push_quot: {:?}", value);
                self.state.push(value.as_value());
                self.record_depth();
                ExecutionResult::Normal
            }
            Instruction::StackToReturn => {
                tracing::trace!("stack>return");
                // SAFETY: compiler ensures safety
                let value = unsafe { self.state.pop_unchecked() };
                self.state.push_return(value);
                ExecutionResult::Normal
            }
            Instruction::ReturnToStack => {
                tracing::trace!("return>stack");
                // SAFETY: compiler ensures safety
                let value = unsafe { self.state.pop_return_unchecked() };
                self.state.push(value);
                ExecutionResult::Normal
            }
            Instruction::AllocateSlotObject { map } => {
                tracing::trace!("allocate_slot_object: {:?}", map);
                self.heap.safepoint_poll();
                let slot_count = map.assignable_slots_count();

                // SAFETY: not safe yet, TODO: depth check
                let slots =
                    unsafe { self.state.stack_pop_slice_unchecked(slot_count) };

                let obj = self.heap.allocate_slots(map, slots);
                self.state.push(obj.into());
                self.record_depth();
                ExecutionResult::Normal
            }
            Instruction::SendPrimitive { id } => {
                self.heap.safepoint_poll();
                // SAFETY: after depth check, this is safe
                let receiver =
                    unsafe { self.state.pop_unchecked().as_handle_unchecked() };
                let res = self.primitive_send(receiver, id);
                self.record_depth();
                res
            }
            Instruction::Send { message } => {
                let selector =
                    Selector::new_message(message, self.vm.shared.clone());

                self.heap.safepoint_poll();

                let universe = self.vm.specials().universe;

                let receiver = match selector
                    .clone()
                    .lookup_object(&universe.as_value())
                {
                    LookupResult::Found { object, .. } => {
                        // SAFETY: this is safe
                        unsafe { object.as_value().as_handle_unchecked() }
                    }
                    LookupResult::None => {
                        // SAFETY: this is safe
                        unsafe {
                            self.state.pop_unchecked().as_handle_unchecked()
                        }
                    }
                };

                let res = self.send(receiver, selector);
                self.record_depth();
                res
            }
            Instruction::SendNamed { message } => {
                let message = self.vm.intern_string(message, &mut self.heap);
                let selector = Selector::new(message, self.vm.shared.clone());

                self.heap.safepoint_poll();
                // SAFETY: after depth check, this is safe
                let receiver =
                    unsafe { self.state.pop_unchecked().as_handle_unchecked() };
                let res = self.send(receiver, selector);
                self.record_depth();
                res
            }
            Instruction::Return => {
                let _last = self.activations.pop();
                tracing::trace!(target: "interpreter", "callstack depth {}", self.activations.depth());
                ExecutionResult::Normal
            }
            _ => unimplemented!("TODO: implement"),
        }
    }

    fn record_depth(&self) {
        tracing::info!(target: "interpreter", "stack {}", self.state.depth);
    }

    pub fn primitive_send(
        &mut self,
        receiver: Handle<Value>,
        id: PrimitiveMessageIndex,
    ) -> ExecutionResult {
        let message = get_primitive(id);
        let _span = tracing::span!(tracing::Level::TRACE, "primitive send", receiver = ?receiver, message = ?message.name).entered();
        // SAFETY: not safe yet, TOOD: depth check
        let inputs = unsafe { self.state.stack_pop_unchecked(message.inputs) };
        // the initialization is guaranted after the call
        let mut outputs = Vec::with_capacity(message.outputs);

        // SAFETY: gc not running
        let inputs = unsafe { transmute::values_as_handles(inputs.as_slice()) };
        // SAFETY: allocated with this size
        #[allow(clippy::uninit_vec)]
        unsafe {
            outputs.set_len(message.outputs)
        };

        let res = message.call(self, receiver, inputs, &mut outputs);

        match res {
            ExecutionResult::Normal => {
                let outputs = transmute::handles_as_values(outputs.as_slice());

                // SAFETY: not safe in general yet, TODO: size check
                unsafe { self.state.stack_push_slice_unchecked(outputs) };
            }
            ExecutionResult::ActivationChanged => {}
            _ => unimplemented!(
                "TODO: implement the different ExecutionResult handling"
            ),
        }
        if res != ExecutionResult::Normal {
            outputs
                .into_iter()
                .for_each(|out| self.state.push(out.into()));
        }

        res
    }

    pub fn send(
        &mut self,
        receiver: Handle<Value>,
        selector: Selector,
    ) -> ExecutionResult {
        let selector_name = selector.name.as_utf8();
        let _span = tracing::span!(tracing::Level::TRACE, "send message", receiver = ?receiver, selector = ?selector_name).entered();

        let res = selector.clone().lookup_object(&receiver.inner());

        let slot = match res {
            LookupResult::Found { slot, .. } => slot,
            LookupResult::None => {
                panic!("Panic: {:?} not found", selector_name)
            }
        };

        if slot.tags().contains(SlotTags::ASSIGNMENT) {
            let offset = slot
                .value
                .as_tagged_fixnum::<usize>()
                .expect("assignment slot must store offset");

            // SAFETY: must be valid by protocol
            // TODO: depth check maybe
            let new_value = unsafe { self.state.pop_unchecked() };

            let recv_val = receiver.inner();
            // SAFETY: must be valid by protocol
            let recv_obj = unsafe {
                recv_val.as_heap_handle_unchecked().cast::<SlotObject>()
            };
            let recv_ptr = recv_obj.as_ptr();
            // SAFETY: must be valid by protocol
            let dst_ptr = unsafe { (*recv_ptr).slots_mut_ptr().add(offset.into()) }; 
            self.heap.heap.write_barrier(dst_ptr as _);
            unsafe { (*recv_ptr).set_slot_unchecked(offset.into(), new_value) };
            return ExecutionResult::Normal;
        }

        if slot
            .tags()
            .contains(SlotTags::EXECUTABLE | SlotTags::PRIMITIVE)
        {
            let id = slot
                .value
                .as_tagged_fixnum::<usize>()
                .expect("primitive must have fixnum");
            // Safety: must store valid primitive idx if primitive executable
            let message_idx =
                unsafe { PrimitiveMessageIndex::from_usize(id.into()) };
            // directly execute primitive
            return self.primitive_send(receiver, message_idx);
        }

        if !slot.tags().contains(SlotTags::EXECUTABLE) {
            self.state.push(slot.value);
            return ExecutionResult::Normal;
        }

        // SAFETY: must by protocol
        let method =
            unsafe { slot.value.as_handle_unchecked().cast::<Method>() };

        self.add_method(receiver, method);

        ExecutionResult::ActivationChanged
    }
}
