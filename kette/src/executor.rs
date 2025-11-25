use crate::{HeapProxy, VMThreadProxy, Value};

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
    pub heap: HeapProxy,
    pub state: ExecutionState,
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

    pub fn pop(&mut self) -> Option<Value> {
        self.stack.pop()
    }

    pub fn push_return(&mut self, value: Value) {
        self.return_stack.push(value);
    }

    pub fn pop_return(&mut self) -> Option<Value> {
        self.return_stack.pop()
    }

    // stack pop -> return push
    pub fn stack_to_return(&mut self) -> Option<()> {
        let value = self.pop()?;
        self.push_return(value);
        Some(())
    }

    /// return pop -> stack push
    pub fn return_to_stack(&mut self) -> Option<()> {
        let value = self.pop_return()?;
        self.push(value);
        Some(())
    }

    /// the the n from the top of the stack
    pub fn stack_get_nth(&self, n: usize) -> Option<Value> {
        let top_idx = self.stack.len() - 1;
        let idx = top_idx - n;
        self.stack.get(idx).copied()
    }

    /// set the value at n from the top of the stack
    pub fn stack_set_nth(&mut self, n: usize, value: Value) {
        let top_idx = self.stack.len() - 1;
        let idx = top_idx - n;
        self.stack[idx] = value;
    }

    pub fn depth(&self) -> usize {
        self.stack.len()
    }

    /// # Safety
    /// caller must make sure that at least one element is in the stack
    pub unsafe fn pop_unchecked(&mut self) -> Value {
        let new_len = self.stack.len() - 1;
        // Safety: depth check
        unsafe { self.stack.set_len(new_len) };
        unsafe { self.stack.as_ptr().add(new_len).read() }
    }

    /// the the n from the top of the stack
    /// # Safety
    /// caller must make sure that at least n elements are in the stack
    pub unsafe fn stack_get_nth_unchecked(&self, n: usize) -> Value {
        let top_idx = self.stack.len() - 1;
        let idx = top_idx - n;
        // Safety: depth check
        unsafe { self.stack.as_ptr().add(idx).read() }
    }

    /// set the value at n from the top of the stack
    /// # Safety
    /// caller must make sure that at least n elements are in the stack
    pub unsafe fn stack_set_nth_unchecked(&mut self, n: usize, value: Value) {
        let top_idx = self.stack.len() - 1;
        let idx = top_idx - n;
        unsafe { self.stack.as_mut_ptr().add(idx).write(value) }
    }

    /// # Safety
    /// caller must make sure that at least one element is in the return stack
    pub unsafe fn pop_return_unchecked(&mut self) -> Value {
        let new_len = self.return_stack.len() - 1;
        unsafe { self.return_stack.set_len(new_len) };
        unsafe { self.return_stack.as_ptr().add(new_len).read() }
    }

    /// stack pop -> return push
    /// # Safety
    /// caller must make sure that at least 1 element is in the stack
    pub unsafe fn stack_to_return_unchecked(&mut self) {
        // Safety: depth check
        let value = unsafe { self.pop_unchecked() };
        self.push_return(value);
    }

    /// return pop -> stack push
    /// # Safety
    /// caller must make sure that at least 1 element is in the return stack
    pub unsafe fn return_to_stack_unchecked(&mut self) {
        // Safety: depth check
        let value = unsafe { self.pop_return_unchecked() };
        self.push(value);
    }
}

impl Executor {
    pub fn new(thread: VMThreadProxy, heap: HeapProxy, state: ExecutionState) -> Self {
        Self {
            thread,
            heap,
            state,
        }
    }

    pub fn run(self) {}
}
