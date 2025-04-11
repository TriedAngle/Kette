use crate::{Array, Tagged};

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct MemoryRegion<T> {
    pub start: *mut T,
    pub end: *mut T,
    pub current: *mut T,
}

impl<T> MemoryRegion<T> {
    pub fn new(start: *mut T, size: usize) -> Self {
        let end = if size > 0 {
            unsafe { start.add(size - 1) }
        } else {
            start
        };
        let current = start;
        Self {
            start,
            end,
            current,
        }
    }

    pub fn increment(&mut self, by: usize) {
        unsafe { self.current = self.current.add(by) }
    }

    pub fn decrement(&mut self, by: usize) {
        unsafe { self.current = self.current.sub(by) }
    }

    pub fn offset(&mut self, by: isize) {
        unsafe { self.current = self.current.offset(by) }
    }

    pub fn percentage(&mut self) -> f64 {
        let size = unsafe { self.end.offset_from(self.start) } as f64;
        let offset = unsafe { self.current.offset_from(self.start) } as f64;
        offset / size
    }

    pub fn is_invalid(&self) -> bool {
        self.current < self.start || self.end < self.current
    }

    pub fn replace(&mut self, with: T) -> T {
        unsafe { std::mem::replace(&mut *self.current, with) }
    }
}

impl<T: Copy> MemoryRegion<T> {
    pub fn nth(&self, n: usize) -> T {
        unsafe { *self.current.sub(n + 1) }
    }
    pub fn set_nth(&mut self, n: usize, value: T) {
        unsafe {
            *self.current.sub(n + 1) = value;
        }
    }
}

impl From<*mut Array> for MemoryRegion<Tagged> {
    fn from(value: *mut Array) -> Self {
        let data_ptr = unsafe { (*value).data_ptr() };
        let size = unsafe { (*value).capacity() };
        Self::new(data_ptr, size)
    }
}

impl From<*mut Array> for MemoryRegion<(Tagged, Tagged)> {
    fn from(value: *mut Array) -> Self {
        let data_ptr = unsafe { (*value).data_ptr() } as _;
        let size = unsafe { (*value).capacity() };
        Self::new(data_ptr, size)
    }
}
