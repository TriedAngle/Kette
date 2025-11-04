use std::{marker::PhantomData, sync::Arc};

use crate::{GenericObject, Heap, HeapProxy, TaggedPtr};
#[derive(Debug)]
pub struct SpecialObjects {
    pub true_object: TaggedPtr<GenericObject>,
    pub false_object: TaggedPtr<GenericObject>,
}
#[derive(Debug)]
pub struct VMShared {
    specials: SpecialObjects,
    _marker: PhantomData<*const ()>,
}

#[allow(unused)]
pub struct VM {
    inner: Arc<VMShared>,
    heap: Heap,
    _marker: PhantomData<*const ()>,
}

impl VM {}

#[derive(Debug)]
pub struct VMProxy {
    vm: Arc<VMShared>,
    heap: HeapProxy,
}

unsafe impl Send for VMProxy {}
unsafe impl Sync for VMProxy {}
