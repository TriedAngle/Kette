use std::{marker::PhantomData, sync::Arc};

use crate::{ByteArray, Handle, Heap, HeapCreateInfo, HeapProxy, HeapValue, Strings, Value};

#[derive(Debug)]
pub struct SpecialObjects {
    pub bytearray_traits: Handle<HeapValue>,
    pub array_traits: Handle<HeapValue>,
    pub fixnum_traits: Handle<HeapValue>,
    pub float_traits: Handle<HeapValue>,
    pub true_object: Handle<HeapValue>,
    pub false_object: Handle<HeapValue>,
}

#[derive(Debug)]
pub struct VMShared {
    pub specials: SpecialObjects,
    pub heap: Heap,
    pub strings: Strings,
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

        // Safety: we initialize these right after
        let inner = VMShared {
            specials: unsafe { SpecialObjects::null() },
            heap,
            strings: Strings::new(),
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
        }
    }

    fn init_from_image(&self, _image_path: &str) {
        unimplemented!("TODO: images are not implemented yet")
    }

    // TODO: special objects should be allocated on the startup heap
    fn init_new(&self) {
        // let true_object = Arc::new(GenericObject::)
    }
}

impl VMProxy {
    pub fn create_proxy(&self) -> Self {
        Self {
            shared: self.shared.clone(),
        }
    }

    pub fn intern_string(&self, s: &str, heap: &mut HeapProxy) -> Handle<ByteArray> {
        self.shared.strings.get(s, heap)
    }
}

impl SpecialObjects {
    pub unsafe fn null() -> Self {
        Self {
            bytearray_traits: unsafe { Value::zero().as_heap_handle_unchecked() },
            array_traits: unsafe { Value::zero().as_heap_handle_unchecked() },
            fixnum_traits: unsafe { Value::zero().as_heap_handle_unchecked() },
            float_traits: unsafe { Value::zero().as_heap_handle_unchecked() },
            true_object: unsafe { Value::zero().as_heap_handle_unchecked() },
            false_object: unsafe { Value::zero().as_heap_handle_unchecked() },
        }
    }
}
