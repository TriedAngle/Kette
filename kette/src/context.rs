use std::mem;

use crate::object::{Object, ObjectRef};

pub struct Segment {
    start: *mut ObjectRef,
    size: usize,
    end: *mut ObjectRef,
}

impl Segment {
    pub unsafe fn from_vec(mut vec: Vec<ObjectRef>) -> Self {
        let start = vec.as_mut_ptr();
        let size = vec.len();
        let end = start.offset(size as isize);
        mem::forget(vec);
        Self { start, size, end }
    }
}

impl Drop for Segment {
    fn drop(&mut self) {
        let vec = unsafe {
            Vec::from_raw_parts(self.start, self.size, self.size)
        };
        mem::drop(vec);
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
    context: *mut Object
}

impl Context {

}

#[cfg(test)]
mod tests {
    use super::Segment;

    #[test]
    fn test_segment() {
        let vec = Vec::with_capacity(100);
        let segment = unsafe { Segment::from_vec(vec) };
    }
}