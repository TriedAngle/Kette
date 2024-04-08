use std::{
    ops::{Deref, DerefMut, Index, IndexMut},
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

pub struct LeakyBox<T> {
    pub ptr: ptr::NonNull<T>,
}

impl<T> LeakyBox<T> {
    pub unsafe fn new(ptr: *mut T) -> Self {
        Self {
            ptr: ptr::NonNull::new(ptr).unwrap(),
        }
    }
}

impl<T> Deref for LeakyBox<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> DerefMut for LeakyBox<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Drop for LeakyVec<T> {
    fn drop(&mut self) {}
}
impl<T> Drop for LeakyBox<T> {
    fn drop(&mut self) {}
}
