use std::{marker::PhantomData, sync::Arc};

use crate::{Handle, Heap, HeapCreateInfo, HeapProxy, Value};

#[derive(Debug)]
pub struct SpecialObjects {
    // pub bytearray_map: TaggedValue,
    // pub array_map: TaggedValue,
    pub true_object: Handle<Value>,
    pub false_object: Handle<Value>,
}

#[derive(Debug)]
pub struct VMShared {
    pub specials: SpecialObjects,
}

unsafe impl Send for VMShared {}
unsafe impl Sync for VMShared {}

#[allow(unused)]
pub struct VM {
    inner: Arc<VMShared>,
    heap: Heap,
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
        let inner = VMShared {
            specials: SpecialObjects::null(),
        };
        let heap = Heap::new(info.heap);

        let new = Self {
            inner: Arc::new(inner),
            heap,
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
            heap: self.heap.create_proxy(),
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

impl VMShared {
    // creates a map, then object, then links map in object, returns object
    // fn allocate_empty_object_with_map_off_heap<'a>(desc: &MapCreateInfo<'a>) -> Box<GenericObject> {
    //     let slots = desc.slots.iter().map(|&(name, kind, value)| {
    //         let name_size = name.len() + 1;
    //         let ba = Box::new(x)
    //     });
    //     unimplemented!()
    // }

    // fn off_heap_bytearray(&self, data: &[u8]) -> Box<ByteArray> {
    //     let total = size_of::<ByteArray>() + data.len();
    //
    //     let mut storage = vec![0u8; total].into_boxed_slice();
    //     let base = storage.as_mut_ptr();
    //
    //     unsafe {
    //         (base as *mut Header).write(Header::null());
    //         (base.add(size_of::<Header>()) as *mut TaggedUsize).write(bytes.len().into());
    //         let data_dst = base.add(size_of::<ByteArray>());
    //         ptr::copy_nonoverlapping(bytes.as_ptr(), data_dst, bytes.len());
    //     }
    //
    //     Self { storage }
    // }
    // }
}

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
            true_object: unsafe { Value::zero().as_handle_unchecked() },
            false_object: unsafe { Value::zero().as_handle_unchecked() },
        }
    }
}
