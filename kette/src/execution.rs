use crate::{VMThreadProxy, Value};

// TODO: automate their construction and give them mostly fixed sizes
// we don't need a full Vector in most cases, we often don't want bounds check in fast path
#[derive(Debug)]
pub struct ExecutionState {
    pub stack: Vec<Value>,
    pub return_stack: Vec<Value>,
    // pub handlers:
}

#[derive(Debug)]
pub struct Executor {
    pub thread: VMThreadProxy,
    pub state: ExecutionState,
}

pub enum IntegerError {
    Overflow,
    DivisionByZero,
}

pub enum ExecutionResult {
    Normal,
    IntegerError(IntegerError),
    Yield,
    Panic,
}

#[derive(Debug, Clone, Default)]
pub struct ExecutionStateCreateInfo {
    pub stack_size: usize,
    pub return_stack_size: usize,
}

impl ExecutionState {
    pub fn new(info: &ExecutionStateCreateInfo) -> Self {
        let stack = Vec::with_capacity(info.stack_size);
        let return_stack = Vec::with_capacity(info.return_stack_size);
        Self {
            stack,
            return_stack,
        }
    }
    pub fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    pub fn pop(&mut self) -> Value {
        self.stack.pop().expect("stack should not underflow")
    }

    pub fn push_return(&mut self, value: Value) {
        self.return_stack.push(value);
    }

    pub fn pop_return(&mut self) -> Value {
        self.return_stack
            .pop()
            .expect("return stack should not underflow")
    }
}

impl Executor {
    pub fn new(thread: VMThreadProxy, state: ExecutionState) -> Self {
        Self { thread, state }
    }

    pub fn run(self) {}
}
