use std::ptr;

use super::{
    align_forward, freelist::FreeListAllocator, Allocator, ArenaAllocator, IntoAllocator,
    PageAllocator, PAGE_SIZE,
};

struct Allocation {
    size: usize,
    from: *mut u8,
    to: *mut u8,
}

struct FreeList {
    freelist: FreeListAllocator,
    from: *mut u8,
    to: *mut u8,
}

// TODO make this transparent to the language
// I don't care about that right now so I use rust vec
struct FreeListPool {
    backing: Allocator,
    lists: Vec<FreeList>,
}

impl FreeListPool {
    pub fn new(backing: Allocator) -> Self {
        Self {
            backing,
            lists: Vec::new(),
        }
    }

    pub fn alloc(&mut self, size: usize, align: usize) -> *mut u8 {
        for list in &mut self.lists {
            let a = list.freelist.alloc(size, align);
            if (!a.is_null()) {
                return a;
            }
        }

        let obj_size = align_forward(size, align);

        let fl_size = if obj_size > PAGE_SIZE * 8 {
            obj_size
        } else {
            PAGE_SIZE * 8
        };

        let mut fl = FreeListAllocator::new_with_capacity(self.backing, fl_size);
        let allocation = fl.alloc(size, align);
        let from = fl.allocation;
        let to = unsafe { fl.allocation.add(fl.size) };
        let freelist = FreeList {
            freelist: fl,
            from,
            to,
        };
        self.lists.push(freelist);
        allocation
    }

    pub fn free(&mut self, pointer: *mut u8, align: usize) {
        for list in &mut self.lists {
            if list.from < pointer && pointer < list.to {
                list.freelist.free(pointer, align);
                break;
            }
        }
    }

    pub fn generic_alloc(backing: *mut (), size: usize, align: usize) -> *mut u8 {
        let mut pool = backing as *mut FreeListPool;
        unsafe { (*pool).alloc(size, align) }
    }

    pub fn generic_free(backing: *mut (), ptr: *mut u8, _size: usize, align: usize) {
        let mut pool = backing as *mut FreeListPool;
        unsafe { (*pool).free(ptr, align) }
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

impl IntoAllocator for FreeListPool {
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
    fn freelist_pool_allocator() {
        let mut page_allocator = PageAllocator::new();
        let mut pa = page_allocator.allocator();
        let mut freelist_pool = FreeListPool::new(pa);
        let mut fl = freelist_pool.allocator();

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
