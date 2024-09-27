use std::{mem, ptr};

use crate::{gc::MarkAndSweep, object::{Object, ObjectHeader, ObjectRef, SpecialObjects}, VM};

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

    pub unsafe fn from_array(obj: ObjectRef) -> Self {
        let start = obj.array_data();
        let size = obj.array_data_len();
        let end = start.add(size);
        Self {
            start, size, end
        }
    }
}

pub struct Context {
    pub header: ObjectHeader,
    pub vm: *mut VM,
    pub gc: *mut MarkAndSweep,
    pub so: *mut SpecialObjects,

    pub data_top: *mut ObjectRef,
    pub retain_top: *mut ObjectRef,
    pub call_top: *mut ObjectRef,

    pub data_array: ObjectRef,
    pub retain_array: ObjectRef,
    pub call_array: ObjectRef,

    pub name: *mut Object,


    pub data: Segment,
    pub retain: Segment,
    pub call: Segment,



}

impl Context {
    pub fn new_empty() -> Self {
        Self {
            header: ObjectHeader { map: ObjectRef::null(), meta: 0},
            vm: ptr::null_mut(),
            gc: ptr::null_mut(),
            so: ptr::null_mut(),
            data_top: ptr::null_mut(),
            retain_top: ptr::null_mut(),
            call_top: ptr::null_mut(),
            data: Segment::NULL,
            retain: Segment::NULL,
            call: Segment::NULL,
            name: ptr::null_mut(),
            data_array: ObjectRef::null(),
            retain_array: ObjectRef::null(),
            call_array: ObjectRef::null(),
        }
    }

    pub fn reset(&mut self) {
        self.data_top = self.data.start;
        self.retain_top = self.retain.start;
        self.call_top = self.call_top;
    }

    pub unsafe fn len(&self) -> usize {
        (self.data_top as usize - self.data.start as usize) / mem::size_of::<ObjectRef>() 
    }

    pub unsafe fn push(&mut self, value: ObjectRef) {
        *self.data_top = value;
        self.data_top = self.data_top.add(1);
    }

    pub unsafe fn pop(&mut self) -> ObjectRef {
        self.data_top = self.data_top.sub(1);
        *self.data_top
    }

    pub unsafe fn peek(&mut self) -> ObjectRef {
        *self.data_top.sub(1)
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
