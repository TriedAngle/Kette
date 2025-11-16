use std::{marker::PhantomData, sync::Arc};

use crate::{Handle, Heap, HeapCreateInfo, HeapProxy, Value};

#[derive(Debug)]
pub struct SpecialObjects {
    pub bytearray_traits: Handle<Value>,
    pub array_traits: Handle<Value>,
    pub fixnum_traits: Handle<Value>,
    pub float_traits: Handle<Value>,
    pub true_object: Handle<Value>,
    pub false_object: Handle<Value>,
}

#[derive(Debug)]
pub struct VMShared {
    pub specials: SpecialObjects,
    pub heap: Heap,
}

unsafe impl Send for VMShared {}
unsafe impl Sync for VMShared {}

#[allow(unused)]
pub struct VM {
    inner: Arc<VMShared>,
    _marker: PhantomData<*const ()>,
}

#[derive(Debug)]
pub struct VMProxy {
    pub shared: Arc<VMShared>,
    pub heap: HeapProxy,
}

unsafe impl Send for VMProxy {}
unsafe impl Sync for VMProxy {}

#[derive(Debug)]
pub struct VMCreateInfo {
    pub heap: HeapCreateInfo,
    pub image: Option<String>,
}

impl VM {
    pub fn new(info: VMCreateInfo) -> Self {
        let heap = Heap::new(info.heap);

        let inner = VMShared {
            specials: SpecialObjects::null(),
            heap,
        };

        let new = Self {
            inner: Arc::new(inner),
            _marker: PhantomData,
        };

        match info.image {
            Some(image) => new.init_from_image(&image),
            None => new.init_new(),
        }

        new
    }

    pub fn new_proxy(&self) -> VMProxy {
        VMProxy {
            shared: self.inner.clone(),
            heap: self.inner.heap.create_proxy(),
        }
    }

    fn init_from_image(&self, _image_path: &str) {
        unimplemented!("TODO: images are not implemented yet")
    }

    // TODO: special objects should be allocated on a static/pinned region on the heap
    fn init_new(&self) {
        // let true_object = Arc::new(GenericObject::)
    }
}

impl VMShared {}

impl VMProxy {
    pub fn create_proxy(&self) -> Self {
        Self {
            shared: self.shared.clone(),
            heap: self.heap.create_proxy(),
        }
    }
}

impl SpecialObjects {
    pub fn null() -> Self {
        Self {
            bytearray_traits: unsafe { Value::zero().as_handle_unchecked() },
            array_traits: unsafe { Value::zero().as_handle_unchecked() },
            fixnum_traits: unsafe { Value::zero().as_handle_unchecked() },
            float_traits: unsafe { Value::zero().as_handle_unchecked() },
            true_object: unsafe { Value::zero().as_handle_unchecked() },
            false_object: unsafe { Value::zero().as_handle_unchecked() },
        }
    }
}
