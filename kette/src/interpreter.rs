use crate::{ActivationStack, ExecutionState, HeapProxy, ThreadProxy, VMProxy};

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
}
