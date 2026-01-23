use crate::Value;

// TODO: automate their construction and give them mostly fixed sizes
// we don't need a full Vector in most cases, we often don't want bounds check in fast path
#[derive(Debug, Clone)]
pub struct ExecutionState {
    pub stack: Vec<Value>,
    pub depth: usize,

    pub return_stack: Vec<Value>,
    pub return_depth: usize,
}

#[derive(Debug, Clone, Default)]
pub struct ExecutionStateInfo {
    pub stack_size: usize,
    pub return_stack_size: usize,
}

impl ExecutionState {
    #[must_use] 
    pub fn new(info: &ExecutionStateInfo) -> Self {
        let mut stack = Vec::with_capacity(info.stack_size);
        let mut return_stack = Vec::with_capacity(info.return_stack_size);

        // SAFETY: We manually manage liveness via `depth` and `return_depth`.
        // We set len to capacity to allow index access up to the limit.
        unsafe {
            stack.set_len(info.stack_size);
            return_stack.set_len(info.return_stack_size);
        };

        Self {
            stack,
            depth: 0,
            return_stack,
            return_depth: 0,
        }
    }

    /// Returns the active portion of the main stack
    #[must_use] 
    pub fn stack(&self) -> &[Value] {
        &self.stack[..self.depth]
    }

    /// Returns the active portion of the main stack (mutable)
    pub fn stack_mut(&mut self) -> &mut [Value] {
        &mut self.stack[..self.depth]
    }

    /// Returns the active portion of the return stack
    #[must_use] 
    pub fn return_stack(&self) -> &[Value] {
        &self.return_stack[..self.return_depth]
    }

    /// Returns the active portion of the return stack (mutable)
    pub fn return_stack_mut(&mut self) -> &mut [Value] {
        &mut self.return_stack[..self.return_depth]
    }

    /// Pushes a value onto the main stack
    pub fn push(&mut self, value: Value) {
        self.stack[self.depth] = value;
        self.depth += 1;
    }

    /// Pops a value from the main stack
    pub fn pop(&mut self) -> Option<Value> {
        if self.depth == 0 {
            return None;
        }
        self.depth -= 1;
        Some(self.stack[self.depth])
    }

    /// Pushes a value onto the return stack
    pub fn push_return(&mut self, value: Value) {
        self.return_stack[self.return_depth] = value;
        self.return_depth += 1;
    }

    /// Pops a value from the return stack
    pub fn pop_return(&mut self) -> Option<Value> {
        if self.return_depth == 0 {
            return None;
        }
        self.return_depth -= 1;
        Some(self.return_stack[self.return_depth])
    }

    /// Moves the top value of the stack to the return stack
    pub fn stack_to_return(&mut self) -> Option<()> {
        let value = self.pop()?;
        self.push_return(value);
        Some(())
    }

    /// Moves the top value of the return stack to the stack
    pub fn return_to_stack(&mut self) -> Option<()> {
        let value = self.pop_return()?;
        self.push(value);
        Some(())
    }

    /// Gets the nth value from the top of the stack (0-indexed)
    #[must_use] 
    pub fn stack_get_nth(&self, n: usize) -> Option<Value> {
        if self.depth == 0 || n >= self.depth {
            return None;
        }
        let top_idx = self.depth - 1;
        let idx = top_idx - n;
        self.stack.get(idx).copied()
    }

    /// Sets the value at n from the top of the stack
    pub fn stack_set_nth(&mut self, n: usize, value: Value) {
        if self.depth > n {
            let top_idx = self.depth - 1;
            let idx = top_idx - n;
            self.stack[idx] = value;
        }
    }

    /// Returns the current stack depth
    #[must_use] 
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// Returns the current return stack depth
    #[must_use] 
    pub fn return_depth(&self) -> usize {
        self.return_depth
    }

    /// # Safety
    /// caller must make sure that at least one element is in the stack
    pub unsafe fn pop_unchecked(&mut self) -> Value {
        self.depth -= 1;
        // SAFETY: caller guarantees depth > 0, so index is valid
        unsafe { *self.stack.get_unchecked(self.depth) }
    }

    /// # Safety
    /// caller must make sure that at least one element is in the stack
    pub unsafe fn peek_unchecked(&mut self) -> Value {
        // SAFETY: caller guarantees depth > 0, so index is valid
        unsafe { *self.stack.get_unchecked(self.depth - 1) }
    }

    /// get the n from the top of the stack
    /// # Safety
    /// caller must make sure that at least n elements are in the stack
    #[must_use] 
    pub unsafe fn stack_get_nth_unchecked(&self, n: usize) -> Value {
        let top_idx = self.depth - 1;
        let idx = top_idx - n;
        // SAFETY: caller guarantees depth > n, so index is valid
        unsafe { *self.stack.get_unchecked(idx) }
    }

    /// set the value at n from the top of the stack
    /// # Safety
    /// caller must make sure that at least n elements are in the stack
    pub unsafe fn stack_set_nth_unchecked(&mut self, n: usize, value: Value) {
        let top_idx = self.depth - 1;
        let idx = top_idx - n;
        // SAFETY: caller guarantees depth > n, so index is valid
        unsafe {
            *self.stack.get_unchecked_mut(idx) = value;
        }
    }

    /// # Safety
    /// caller must make sure that at least one element is in the return stack
    pub unsafe fn pop_return_unchecked(&mut self) -> Value {
        self.return_depth -= 1;
        // SAFETY: caller guarantees return_depth > 0, so index is valid
        unsafe { *self.return_stack.get_unchecked(self.return_depth) }
    }

    /// stack pop -> return push
    /// # Safety
    /// caller must make sure that at least 1 element is in the stack
    pub unsafe fn stack_to_return_unchecked(&mut self) {
        // SAFETY: caller guarantees stack depth > 0
        let value = unsafe { self.pop_unchecked() };
        self.push_return(value);
    }

    /// return pop -> stack push
    /// # Safety
    /// caller must make sure that at least 1 element is in the return stack
    pub unsafe fn return_to_stack_unchecked(&mut self) {
        // SAFETY: caller guarantees return stack depth > 0
        let value = unsafe { self.pop_return_unchecked() };
        self.push(value);
    }

    /// Returns a slice of the top n elements without removing them.
    /// The slice is ordered from bottom-of-slice to top-of-stack.
    #[must_use] 
    pub fn stack_peek_slice(&self, n: usize) -> Option<&[Value]> {
        if self.depth < n {
            return None;
        }
        let start = self.depth - n;
        let end = self.depth;
        Some(&self.stack[start..end])
    }

    /// Removes the top n elements and returns them as a new Vec.
    pub fn stack_pop_slice(&mut self, n: usize) -> Option<Vec<Value>> {
        if self.depth < n {
            return None;
        }
        let start = self.depth - n;
        let end = self.depth;

        let result = self.stack[start..end].to_vec();
        self.depth -= n;
        Some(result)
    }

    /// Pushes an entire slice onto the stack.
    /// Returns `None` if there isn't enough space.
    pub fn stack_push_slice(&mut self, slice: &[Value]) -> Option<()> {
        let n = slice.len();
        if self.depth + n > self.stack.len() {
            return None;
        }

        let start = self.depth;
        let end = start + n;

        self.stack[start..end].copy_from_slice(slice);
        self.depth = end;

        Some(())
    }

    /// Writes the slice at the top of the stack
    /// # Safety
    /// Caller must ensure the stack has enough space:
    /// `self.depth + slice.len() <= self.stack.len()`.
    pub unsafe fn stack_push_slice_unchecked(&mut self, slice: &[Value]) {
        let n = slice.len();
        // SAFETY: caller guarantees sufficient capacity
        let dst = unsafe { self.stack.as_mut_ptr().add(self.depth) };
        let src = slice.as_ptr();

        // SAFETY: caller guarantees sufficient capacity and non-overlapping memory
        unsafe {
            std::ptr::copy_nonoverlapping(src, dst, n);
        }
        self.depth += n;
    }

    /// Returns a slice of the top n elements.
    /// # Safety
    /// Caller must ensure that self.depth >= n.
    #[must_use] 
    pub unsafe fn stack_peek_slice_unchecked(&self, n: usize) -> &[Value] {
        let start = self.depth - n;
        // SAFETY: caller guarantees depth >= n, so range is valid
        unsafe { self.stack.get_unchecked(start..self.depth) }
    }

    /// Returns a slice of the top n elements and decrements the depth
    /// # Safety
    /// - Caller must ensure that self.depth >= n.
    /// - The values may get overridden on pushing to the stack
    pub unsafe fn stack_pop_slice_unchecked(&mut self, n: usize) -> &[Value] {
        let start = self.depth - n;
        let depth = self.depth;
        self.depth -= n;
        // SAFETY: caller guarantees depth >= n, so range is valid
        unsafe { self.stack.get_unchecked(start..depth) }
    }

    /// Removes the top n elements and returns them as a new Vec.
    /// # Safety
    /// Caller must ensure that self.depth >= n.
    pub unsafe fn stack_pop_unchecked(&mut self, n: usize) -> Vec<Value> {
        let start = self.depth - n;
        let end = self.depth;
        // SAFETY: caller guarantees depth >= n, so range is valid
        let result = unsafe { self.stack.get_unchecked(start..end).to_vec() };
        self.depth -= n;
        result
    }
}
