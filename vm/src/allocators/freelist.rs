use std::{mem, ptr};

use super::{align_forward, Allocator, IntoAllocator};

struct FreeHeader {
    size: usize,
    next: *mut FreeHeader,
}

pub struct FreeListAllocator {
    backing: Allocator,
    allocation: *mut u8,
    size: usize,
    head: *mut FreeHeader,
}

impl FreeListAllocator {
    pub fn new(backing: Allocator) -> Self {
        Self {
            backing,
            allocation: ptr::null_mut(),
            size: 0,
            head: ptr::null_mut(),
        }
    }

    pub fn new_with_capacity(backing: Allocator, cap: usize) -> Self {
        let mut freelist = Self::new(backing);
        freelist.allocation = (freelist.backing.alloc_fn)(freelist.backing.backing, cap, 16);
        freelist.size = cap;
        let head = freelist.allocation as *mut FreeHeader;
        unsafe {
            (*head).size = align_forward(cap, 16);
            (*head).next = ptr::null_mut();
        }
        freelist.head = head;

        freelist
    }

    fn alloc(&mut self, size: usize, align: usize) -> *mut u8 {
        let aligned_header_size =
            align_forward(mem::size_of::<FreeHeader>(), mem::align_of::<FreeHeader>());
        let aligned_size = align_forward(size, align);
        let required_size = aligned_header_size + aligned_size;

        let mut prev_header = ptr::null_mut::<FreeHeader>();
        let mut header = self.head;
        loop {
            let header_size = unsafe { (*header).size };
            let next = unsafe { (*header).next };
            if (next.is_null()) {
                if header_size < required_size {
                    return ptr::null_mut();
                }
                break;
            }

            if (header_size >= required_size) {
                break;
            }
            prev_header = header;
            header = next;
        }

        if !unsafe { (*header).next }.is_null() {
            if !prev_header.is_null() {
                unsafe {
                    (*prev_header).next = (*header).next;
                }
            } else {
                self.head = unsafe { (*header).next };
            }
        } else {
            unsafe {
                let raw_tail = (header as *mut u8).add(required_size);
                let offset = raw_tail.align_offset(mem::align_of::<FreeHeader>());
                let tail = raw_tail.add(offset) as *mut FreeHeader;

                (*tail).size = (*header).size - required_size;
                (*header).size = required_size;

                if !prev_header.is_null() {
                    (*prev_header).next = tail;
                } else {
                    self.head = tail;
                }
            }
        }

        let start_ptr = unsafe { (header as *mut u8).add(mem::size_of::<FreeHeader>()) };
        let offset = start_ptr.align_offset(align);
        let allocation = unsafe { start_ptr.add(offset) };

        allocation
    }

    fn free(&mut self, pointer: *mut u8, align: usize) {
        let header = unsafe { Self::get_header_from_allocation(pointer, align) };
        let block_size = unsafe { (*header).size };

        unsafe {
            ptr::write_bytes(header as *mut u8, 0, block_size);
        }

        let mut prev = ptr::null_mut::<FreeHeader>();
        let mut node = self.head;
        while (!node.is_null()) {
            if (pointer as usize) < (node as usize) {
                break;
            }
            prev = node;
            node = unsafe { (*node).next };
        }

        if (!node.is_null()) {
            if (self.head == node) {
                unsafe { (*header).next = node };
                self.head = header;
            } else {
                unsafe {
                    (*prev).next = header;
                }
                unsafe {
                    (*header).next = node;
                }
            }
        } else {
            self.head = header;
        }
    }

    unsafe fn get_header_from_allocation(allocation: *mut u8, align: usize) -> *mut FreeHeader {
        let max_possible_offset = align - 1;
        let possible_header_start = allocation.sub(mem::size_of::<FreeHeader>());
        let header_alignment = mem::align_of::<FreeHeader>();
        let misalignment = possible_header_start as usize % header_alignment;

        let header_start = if misalignment == 0 {
            possible_header_start
        } else {
            possible_header_start.sub(misalignment)
        };

        header_start as *mut FreeHeader
    }

    fn coalesce_free_blocks(&mut self) {
        // TODO implement this
    }

    pub fn generic_alloc(backing: *mut (), size: usize, align: usize) -> *mut u8 {
        let mut freelist = backing as *mut FreeListAllocator;
        unsafe { (*freelist).alloc(size, align) }
    }

    pub fn generic_free(backing: *mut (), ptr: *mut u8, _size: usize, align: usize) {
        let mut freelist = backing as *mut FreeListAllocator;
        unsafe { (*freelist).free(ptr, align) }
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

impl Drop for FreeListAllocator {
    fn drop(&mut self) {
        self.backing.free(self.allocation, self.size);
    }
}

impl IntoAllocator for FreeListAllocator {
    fn allocator(&mut self) -> Allocator {
        Allocator {
            backing: self as *mut Self as *mut (),
            alloc_fn: Self::generic_alloc,
            free_fn: Self::generic_free,
            realloc_fn: Self::generic_realloc,
        }
    }
}

mod tests {
    use std::arch::x86_64::__m512;

    use super::*;
    use crate::allocators::{page::PAGE_SIZE, PageAllocator};
    #[test]
    fn arena_allocator() {
        let mut page_allocator = PageAllocator::new();
        let mut pa = page_allocator.allocator();
        let mut freelist = FreeListAllocator::new_with_capacity(pa, PAGE_SIZE);
        let mut fl = freelist.allocator();

        let mut array = fl.make::<[f32; 3]>();
        array[0] = 234.00;
        assert_eq!(array[0], 234.00);
        let mut lel = fl.create::<__m512>(8);
        let mut value = fl.make::<f64>();
        assert_eq!(*value, 0.0);
        *value = 44.3;
        assert_eq!(*value, 44.3);
        fl.destroy(&mut lel);
        fl.unmake(&mut value);
        let mut lel = fl.create::<__m512>(3);
    }
}
