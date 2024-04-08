use std::ptr;

use super::{align_forward, Allocator, IntoAllocator};

pub struct ArenaAllocator {
    backing: Allocator,
    allocation: *mut u8,
    size: usize,
    offset: usize,
}

impl ArenaAllocator {
    pub fn new(backing: Allocator) -> Self {
        Self {
            backing,
            allocation: ptr::null_mut(),
            size: 0,
            offset: 0,
        }
    }

    pub fn new_with_capacity(backing: Allocator, cap: usize) -> Self {
        let mut arena = Self::new(backing);
        arena.resize(cap);
        arena
    }

    pub fn resize(&mut self, new_size: usize) {
        if (self.allocation == ptr::null_mut()) {
            self.allocation = self.backing.alloc(new_size);
            self.size = new_size;
            return;
        }

        self.allocation = self.backing.realloc(self.allocation, self.size, new_size);
        self.size = new_size;
    }

    pub fn alloc(&mut self, size: usize, align: usize) -> *mut u8 {
        let current = self.allocation as usize + self.offset;
        let aligned = align_forward(current, align);
        let relative = aligned - (self.allocation as usize);

        if (self.size < relative + size) {
            self.resize(self.size * 2);
        }

        let pointer = unsafe { self.allocation.add(relative) };
        self.offset = relative + size;
        unsafe {
            ptr::write_bytes(pointer, 0, size);
        }
        pointer
    }

    pub fn generic_alloc(backing: *mut (), size: usize, align: usize) -> *mut u8 {
        let mut arena = backing as *mut ArenaAllocator;
        unsafe { (*arena).alloc(size, align) }
    }

    pub fn generic_free(_backing: *mut (), _ptr: *mut u8, _size: usize) {}

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

impl Drop for ArenaAllocator {
    fn drop(&mut self) {
        self.backing.free(self.allocation, self.size);
    }
}

impl IntoAllocator for ArenaAllocator {
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
        let mut pa = page_allocator.allocator();
        let mut arena = ArenaAllocator::new_with_capacity(pa, PAGE_SIZE);
        let mut aa = arena.allocator();

        let mut array = aa.make::<[f32; 3]>();
        array[0] = 234.00;
        assert_eq!(array[0], 234.00);
        assert_eq!(array[1], 0.0);
        assert_eq!(array[1], 0.0);
        let mut value = aa.make::<f64>();
        assert_eq!(*value, 0.0);
        *value = 44.3;
        assert_eq!(*value, 44.3);
    }
}
