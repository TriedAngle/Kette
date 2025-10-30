use std::{
    alloc::{self, Layout},
    ptr::NonNull,
};

use crate::{GenericObject, Scheduler, TaggedPtr};

pub struct SpecialObjects {
    pub true_object: TaggedPtr<GenericObject>,
    pub false_object: TaggedPtr<GenericObject>,
}

pub struct Specials {
    pub specials: SpecialObjects,
}

#[allow(unused)]
pub struct VM {
    scheduler: Scheduler,
}

impl VM {
    pub fn allocate_off_heap(&self, layout: Layout) -> TaggedPtr<GenericObject> {
        let ptr = unsafe { alloc::alloc(layout) };
        let tagged = TaggedPtr::from_nonnull(NonNull::new(ptr).unwrap());
        unsafe { tagged.cast() }
    }
}
