use crate::{
    ActivationStack, ExecutionState, Handle, HeapProxy, Instruction,
    LookupResult, PrimitiveMessageIndex, Selector, ThreadProxy, VMProxy, Value,
    get_primitive, slots::SlotTags,
};

pub struct Interpreter {
    pub vm: VMProxy,
    pub thread: ThreadProxy,
    pub heap: HeapProxy,
    pub state: ExecutionState,
    pub activations: ActivationStack,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum IntegerError {
    Overflow,
    DivisionByZero,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ExecutionResult {
    Normal,
    IntegerError(IntegerError),
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

    pub fn execute_bytecode(&mut self, instruction: Instruction) {
        match instruction {
            Instruction::PushFixnum { value } => self.state.push(value.into()),
            Instruction::PushValue { value } => self.state.push(value),
            Instruction::SendPrimitive { id } => {
                // SAFETY: after depth check, this is safe
                let receiver =
                    unsafe { self.state.pop_unchecked().as_handle_unchecked() };
                match self.primitive_send(receiver, id) {
                    ExecutionResult::Normal => (),
                    _ => unimplemented!("TODO: implementend"),
                }
            }
            Instruction::AllocateSlotObject { map } => {
                // SAFETY: map must be valid here
                let map_ref = unsafe { map.as_ref() };
                let slot_count = map_ref.assignable_slots_count();
                // SAFETY: not safe yet, TODO: depth check
                let slots =
                    unsafe { self.state.stack_pop_slice_unchecked(slot_count) };
                let obj = self.heap.allocate_slot_object(map, slots);
                self.state.push(obj.into());
            }
            Instruction::Send { message } => {
                let selector =
                    Selector::new_message(message, self.vm.shared.clone());

                // SAFETY: after depth check, this is safe
                let receiver =
                    unsafe { self.state.pop_unchecked().as_handle_unchecked() };
                match self.send(receiver, selector) {
                    ExecutionResult::Normal => (),
                    _ => unimplemented!("TODO: implementend"),
                }
            }
            Instruction::SendNamed { message } => {
                let message = self.vm.intern_string(message, &mut self.heap);
                let selector = Selector::new(message, self.vm.shared.clone());
                // SAFETY: after depth check, this is safe
                let receiver =
                    unsafe { self.state.pop_unchecked().as_handle_unchecked() };
                match self.send(receiver, selector) {
                    ExecutionResult::Normal => (),
                    _ => unimplemented!("TODO: implemented"),
                }
            }
            // Instruction::Send { message } => self.state.push(value.into()),
            _ => unimplemented!(),
        }

        println!("stack: {:?}", self.state.depth);
    }

    pub fn primitive_send(
        &mut self,
        receiver: Handle<Value>,
        id: PrimitiveMessageIndex,
    ) -> ExecutionResult {
        let message = get_primitive(id);
        println!("primitive call: {:?}", message.name);
        // SAFETY: not safe yet, TOOD: depth check
        let inputs = unsafe { self.state.stack_pop_unchecked(message.inputs) };
        // the initialization is guaranted after the call
        let mut outputs = Vec::with_capacity(message.outputs);
        // SAFETY: allocated with this size
        #[allow(clippy::uninit_vec)]
        unsafe {
            outputs.set_len(message.outputs)
        };
        let res = message.call(
            self,
            receiver,
            // SAFETY: same memory layout, same type, no gc here
            unsafe {
                std::mem::transmute::<&[Value], &[Handle<Value>]>(
                    inputs.as_slice(),
                )
            },
            &mut outputs,
        );

        if res == ExecutionResult::Normal {
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
        println!(
            "call: {:?}",
            str::from_utf8(selector.name.as_bytes())
                .expect("valid utf8 message")
        );

        let res = selector.lookup_object(&receiver.inner());

        let slot = match res {
            LookupResult::Found { slot, .. } => slot,
            LookupResult::None => {
                panic!("TODO: implement error handling")
            }
        };

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
            self.primitive_send(receiver, message_idx)
        } else if slot.tags().contains(SlotTags::EXECUTABLE) {
            unimplemented!("TODO: append to execution stack");
        } else {
            // Value constant, push it
            self.state.push(slot.value);
            ExecutionResult::Normal
        }
    }
}
