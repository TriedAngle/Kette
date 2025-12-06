use crate::{
    ActivationStack, ExecutionState, HeapProxy, Instruction, PrimitiveContext, ThreadProxy,
    VMProxy, get_primitive, object,
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
    pub fn new(vm: VMProxy, thread: ThreadProxy, heap: HeapProxy, state: ExecutionState) -> Self {
        Self {
            vm,
            thread,
            heap,
            state,
            activations: ActivationStack::new(),
        }
    }

    // pub fn run(code)
    //

    pub fn execute_bytecode(&mut self, instruction: Instruction) {
        match instruction {
            Instruction::PushFixnum { value } => self.state.push(value.into()),
            Instruction::SendPrimitive { id } => {
                let message = get_primitive(id);
                println!("call: {:?}", message.name);
                let receiver = self.state.pop().expect("must have item");
                let receiver = unsafe { receiver.as_handle_unchecked() };
                let inputs = unsafe { self.state.stack_pop_slice_unchecked(message.inputs) };
                let mut outputs = Vec::with_capacity(message.outputs);
                unsafe { outputs.set_len(message.outputs) };
                let res = message.call(
                    self,
                    receiver,
                    unsafe { std::mem::transmute(inputs.as_slice()) },
                    &mut outputs,
                );
                match res {
                    ExecutionResult::Normal => {
                        for output in outputs {
                            self.state.push(output.into());
                        }
                    }
                    _ => panic!("not happy"),
                }
            }
            // Instruction::Send { message } => self.state.push(value.into()),
            _ => unimplemented!(),
        }

        println!("stack: {:?}", self.state.depth);
    }
}
