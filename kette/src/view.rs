use std::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

use crate::{TaggedPtr, TaggedValue};

#[derive(Debug, Clone, Copy)]
pub struct View<T>(NonNull<T>);

impl<T> View<T> {
    pub fn new(ptr: NonNull<T>) -> Self {
        Self(ptr)
    }

    pub fn from_ptr(ptr: *mut T) -> Option<Self> {
        let ptr = NonNull::new(ptr)?;
        Some(Self(ptr))
    }

    pub fn as_ptr(self) -> *mut T {
        self.0.as_ptr()
    }

    pub fn to_nonnull(self) -> NonNull<T> {
        self.0
    }

    pub fn to_tagged_ptr(self) -> TaggedPtr<T> {
        TaggedPtr::from_nonnull(self.0)
    }

    pub fn from_tagged(value: TaggedValue) -> Option<Self> {
        Some(Self(value.as_reference()?.to_nonnull()))
    }

    pub fn from_tagged_ptr(ptr: TaggedPtr<T>) -> Self {
        Self(ptr.to_nonnull())
    }
}

impl<T> Deref for View<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<T> DerefMut for View<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}

impl<T> From<TaggedPtr<T>> for View<T> {
    fn from(value: TaggedPtr<T>) -> Self {
        Self::from_tagged_ptr(value)
    }
}

impl<T> From<View<T>> for TaggedPtr<T> {
    fn from(value: View<T>) -> Self {
        value.to_tagged_ptr()
    }
}
