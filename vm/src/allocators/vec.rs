use std::{
    ops::{Index, IndexMut},
    ptr, slice,
};

pub struct LeakyVec<T> {
    pub ptr: ptr::NonNull<T>,
    pub size: usize,
}

impl<T> LeakyVec<T> {
    pub fn new(ptr: *mut T, size: usize) -> Option<Self> {
        ptr::NonNull::new(ptr).map(|ptr| Self { ptr, size })
    }

    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.size) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.size) }
    }
}

impl<T> Index<usize> for LeakyVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.size, "Index out of bounds");
        unsafe { &*self.ptr.as_ptr().add(index) }
    }
}

impl<T> IndexMut<usize> for LeakyVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < self.size, "Index out of bounds");
        unsafe { &mut *self.ptr.as_ptr().add(index) }
    }
}
