use std::ptr;

use super::{Allocator, IntoAllocator};

struct PoolNode {
    next: *mut PoolNode,
}

pub struct PoolAllocator {
    backing: Allocator,
    allocation: *mut u8,
    size: usize,
    chunk_size: usize,
    chunk_align: usize,

    head: *mut PoolNode,
}

impl PoolAllocator {
    pub fn new(backing: Allocator, chunk_size: usize, chunk_align: usize) -> Self {
        Self {
            backing,
            allocation: ptr::null_mut(),
            size: 0,
            chunk_size,
            chunk_align,
            head: ptr::null_mut(),
        }
    }

    pub fn new_with_capacity(
        backing: Allocator,
        chunk_size: usize,
        chunk_align: usize,
        cap: usize,
    ) -> Self {
        let mut pool = PoolAllocator::new(backing, chunk_size, chunk_align);
        pool.resize(cap);
        pool.free_all();
        pool
    }

    pub fn free_all(&mut self) {
        let count = self.size / self.chunk_size;

        for i in 0..count {
            let p = unsafe { self.allocation.add(i * self.chunk_size) };
            let node = p as *mut PoolNode;
            unsafe {
                (*node).next = self.head;
            }
            self.head = node;
        }
    }

    pub fn resize(&mut self, new_size: usize) {
        if self.allocation == ptr::null_mut() {
            let ptr = (self.backing.alloc_fn)(self.backing.backing, new_size, self.chunk_align);
            self.allocation = ptr;
            self.size = new_size;
            return;
        }

        self.allocation = self.backing.realloc(self.allocation, self.size, new_size);
        self.size = new_size;
    }

    pub fn alloc(&mut self) -> *mut u8 {
        let node = self.head;
        if (node == ptr::null_mut()) {
            return ptr::null_mut();
        }
        self.head = unsafe { (*self.head).next };
        let pointer = node as *mut u8;
        unsafe {
            ptr::write_bytes(pointer, 0, self.chunk_size);
        }
        pointer
    }

    pub fn free(&mut self, pointer: *mut u8) {
        let node = pointer as *mut PoolNode;
        unsafe { (*node).next = self.head };
        self.head = node;
    }

    pub fn generic_alloc(backing: *mut (), _size: usize, _align: usize) -> *mut u8 {
        let mut pool = backing as *mut PoolAllocator;
        unsafe { (*pool).alloc() }
    }

    pub fn generic_free(backing: *mut (), ptr: *mut u8, _size: usize) {
        let mut pool = backing as *mut PoolAllocator;
        unsafe { (*pool).free(ptr) }
    }

    pub fn generic_realloc(
        _backing: *mut (),
        ptr: *mut u8,
        _size: usize,
        _new_size: usize,
        _align: usize,
    ) -> *mut u8 {
        return ptr;
    }
}

impl Drop for PoolAllocator {
    fn drop(&mut self) {
        self.backing.free(self.allocation, self.size);
    }
}

impl IntoAllocator for PoolAllocator {
    fn allocator(&mut self) -> Allocator {
        Allocator {
            backing: self as *mut Self as *mut (),
            alloc_fn: Self::generic_alloc,
            free_fn: Self::generic_free,
            realloc_fn: Self::generic_realloc,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::allocators::{page::PAGE_SIZE, PageAllocator};

    #[test]
    fn arena_allocator() {
        let mut page_allocator = PageAllocator::new();
        let mut pager = page_allocator.allocator();
        let mut pool = PoolAllocator::new_with_capacity(pager, 32, 8, PAGE_SIZE);
        let mut pa = pool.allocator();

        {
            let mut a = pa.make::<i64>();
            let mut b = pa.make::<i64>();
            let mut c = pa.make::<i64>();
            *a = 69;
            assert_eq!(*a, 69);
            pa.unmake(&mut b);
            pa.unmake(&mut a);
            pa.unmake(&mut c);
        }

        let mut a = pa.make::<i64>();
        assert_eq!(*a, 0);
    }
}
