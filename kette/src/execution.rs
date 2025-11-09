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

impl ExecutionState {
    pub fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    pub fn pop(&mut self) -> Value {
        self.stack.pop().expect("stack should not underflow")
    }
}

impl Executor {
    pub fn new(thread: VMThreadProxy, state: ExecutionState) -> Self {
        Self { thread, state }
    }

    pub fn run(self) {}
}
