#![allow(dead_code, unused)]

use std::{
    collections::{HashMap, HashSet},
    mem,
    pin::Pin,
    ptr,
};

use allocators::{
    align_forward, Allocator, ChunkPool, FreeListPool, IntoAllocator, LeakyBox, PageAllocator,
};
use bytecode::Code;
use objects::{Float, Integer, Object, ToObject, VMString, Word};

mod allocators;
mod bytecode;
pub mod objects;

struct CodeHeap {
    pub new: HashSet<*const Word>,
    pub compiled: HashMap<*const Word, Code>,
}

impl CodeHeap {
    pub fn new() -> Self {
        Self {
            new: Default::default(),
            compiled: Default::default(),
        }
    }
}

pub struct VM {
    code: CodeHeap,
    pages: Box<PageAllocator>,
    freelist: Pin<Box<FreeListPool>>,
    chunks: Pin<Box<ChunkPool>>,

    stack: *mut Object,
    stack_top: *mut Object,
    stack_size: usize,

    retain_stack: *mut Object,
    retain_stack_size: usize,
}

impl VM {
    pub fn new() -> Self {
        let code = CodeHeap::new();
        let mut pages = Box::new(PageAllocator::new());
        let mut pa = pages.allocator();
        let mut freelist = unsafe { Pin::new_unchecked(Box::new(FreeListPool::new(pa))) };
        let fla = freelist.allocator();
        let mut chunks = unsafe { Pin::new_unchecked(Box::new(ChunkPool::new(pa))) };
        let cha = chunks.allocator();
        let stack = pa.alloc::<objects::Object>(1024);
        let stack_top = stack;
        let stack_size = 1024;
        Self {
            code,
            pages,
            freelist,
            chunks,
            stack,
            stack_top,
            stack_size,
            retain_stack: ptr::null_mut(),
            retain_stack_size: 0,
        }
    }

    pub fn alloc_int(&mut self, int_val: i64) -> Object {
        let mut int = self.chunks.alloc() as *mut Integer;
        unsafe {
            (*int).header.meta = 1;
            (*int).value = int_val;
            (*int).to_object_mut()
        }
    }

    pub fn alloc_float(&mut self, float_val: f64) -> Object {
        let mut float = self.chunks.alloc() as *mut Float;
        unsafe {
            (*float).header.meta = 1;
            (*float).value = float_val;
            (*float).to_object_mut()
        }
    }

    pub fn alloc_bytearray(
        &mut self,
        data: &[u8],
        override_size: Option<usize>,
    ) -> LeakyBox<objects::ByteArray> {
        let data_size = if let Some(ovrde) = override_size {
            ovrde
        } else {
            data.len()
        };
        let data_aligned_size = align_forward(data_size, 8);
        let ba_header_size = mem::size_of::<objects::ByteArray>();
        let size = data_aligned_size + ba_header_size;
        let ba_raw = self.freelist.alloc(size, 8);
        let ba = unsafe { LeakyBox::new(ba_raw as *mut objects::ByteArray) };
        let data_start =
            unsafe { (ba.ptr.as_ptr() as *mut u8).add(mem::size_of::<objects::ByteArray>()) };
        unsafe {
            ptr::write_bytes(data_start, 0, data_aligned_size);
            ptr::copy_nonoverlapping(data.as_ptr(), data_start, data.len());
        }
        ba
    }

    pub fn alloc_rust_string(&mut self, s: &str) -> Object {
        let bytes = s.as_bytes();
        // null temrinator
        let mut bytearray = self.alloc_bytearray(bytes, Some(bytes.len() + 1));
        let mut st = self.chunks.alloc() as *mut VMString;
        unsafe {
            (*st).data = bytearray.ptr.as_mut().to_object_mut();
            (*st).to_object_mut()
        }

        // return bytearray.to_object_mut()
    }

    pub fn push(&mut self, obj: Object) {
        unsafe {
            *self.stack_top = obj;
            self.stack_top = self.stack_top.add(1)
        }
    }

    pub fn pop(&mut self) -> Object {
        let obj = unsafe {
            self.stack_top = self.stack_top.sub(1);
            *self.stack_top
        };
        obj
    }

    // pub fn alloc_quoation()
}
