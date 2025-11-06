use crate::{TaggedValue, VMThreadProxy};

// TODO: automate their construction and give them mostly fixed sizes
// we don't need a full Vector in most cases, we often don't want bounds check in fast path
#[derive(Debug)]
pub struct ExecutionState {
    pub stack: Vec<TaggedValue>,
    pub return_stack: Vec<TaggedValue>,
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
    pub fn push(&mut self, value: TaggedValue) {
        self.stack.push(value);
    }

    pub fn pop(&mut self) -> TaggedValue {
        self.stack.pop().expect("stack should not underflow")
    }
}

impl Executor {
    pub fn new(thread: VMThreadProxy, state: ExecutionState) -> Self {
        Self { thread, state }
    }

    pub fn run(self) {}
}
