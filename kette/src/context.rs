use std::{mem, ptr};

use crate::object::{Object, ObjectRef};

pub struct Segment {
    start: *mut ObjectRef,
    size: usize,
    end: *mut ObjectRef,
}

impl Segment {
    pub const NULL: Self = Self {
        start: ptr::null_mut(),
        size: 0,
        end: ptr::null_mut(),
    };

    pub fn new(start: *mut ObjectRef, size: usize) -> Self {
        Self {
            start,
            size,
            end: unsafe { start.add(size) },
        }
    }

    pub fn in_bounds(&self, obj: *mut ObjectRef) -> bool {
        self.start <= obj && obj <= self.end
    }
}

pub struct Context {
    data_top: *mut ObjectRef,
    retain_top: *mut ObjectRef,
    call_top: *mut ObjectRef,

    data: Segment,
    retain: Segment,
    call: Segment,

    name: *mut Object,
    context: *mut Object,
}

impl Context {
    pub fn new_empty() -> Self {
        Self {
            data_top: ptr::null_mut(),
            retain_top: ptr::null_mut(),
            call_top: ptr::null_mut(),
            data: Segment::NULL,
            retain: Segment::NULL,
            call: Segment::NULL,
            name: ptr::null_mut(),
            context: ptr::null_mut(),
        }
    }

    pub unsafe fn push(&mut self, value: ObjectRef) {
        *self.data_top = value;
        self.data_top = self.data_top.add(1);
    }

    pub unsafe fn pop(&mut self) -> ObjectRef {
        self.data_top = self.data_top.sub(1);
        *self.data_top
    }

    pub unsafe fn retain_push(&mut self, value: ObjectRef) {
        *self.retain_top = value;
        self.retain_top = self.retain_top.add(1);
    }

    pub unsafe fn retain_pop(&mut self) -> ObjectRef {
        self.retain_top = self.retain_top.sub(1);
        *self.retain_top
    }

    pub unsafe fn call_push(&mut self, value: ObjectRef) {
        *self.call_top = value;
        self.call_top = self.call_top.add(1);
    }

    pub unsafe fn call_pop(&mut self) -> ObjectRef {
        self.call_top = self.call_top.sub(1);
        *self.call_top
    }

    pub fn is_full(&self) -> bool {
        self.data_top == self.data.end
    }

    pub fn is_empty(&self) -> bool {
        self.data_top == self.data.start
    }

    pub fn is_retain_full(&self) -> bool {
        self.retain_top == self.retain.end
    }

    pub fn is_retain_empty(&self) -> bool {
        self.retain_top == self.retain.start
    }

    pub fn is_call_full(&self) -> bool {
        self.call_top == self.call.end
    }

    pub fn is_call_empty(&self) -> bool {
        self.call_top == self.call.start
    }
}
