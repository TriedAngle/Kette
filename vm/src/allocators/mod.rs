use std::mem;

use self::vec::LeakyVec;

mod page;
mod vec;

type AllocFn = fn(backing: *mut (), size: usize, align: usize) -> *mut ();
type FreeFn = fn(backing: *mut (), ptr: *mut (), size: usize);

pub const fn is_power_of_two(x: usize) -> bool {
    x & (x - 1) == 0
}

pub const fn align_forward(mut ptr: usize, align: usize) -> usize {
    assert!(is_power_of_two(align));
    (ptr + align - 1) & !(align - 1)
}

pub trait IntoAllocator {
    fn allocator(&self) -> Allocator;
}

pub struct Allocator {
    backing: *mut (),
    alloc_fn: AllocFn,
    free_fn: FreeFn,
}

impl Allocator {
    pub fn new(backing: *mut (), alloc_fn: AllocFn, free_fn: FreeFn) -> Self {
        Self {
            backing,
            alloc_fn,
            free_fn,
        }
    }

    pub fn create<T: Clone>(&self, count: usize) -> LeakyVec<T> {
        let allocation = self.alloc::<T>(count);
        let vec = LeakyVec::new(allocation, count).unwrap();
        vec
    }

    pub fn make<T>(&self) -> Box<T> {
        let allocation = self.alloc::<T>(1);
        unsafe { Box::from_raw(allocation) }
    }

    pub fn alloc<T>(&self, count: usize) -> *mut T {
        let size = mem::size_of::<T>() * count;
        let align = mem::align_of::<T>();
        (self.alloc_fn)(self.backing, size, align) as *mut T
    }

    pub fn destroy<T>(&self, vec: &mut LeakyVec<T>) {
        self.free(vec.ptr.as_ptr(), vec.size);
    }

    pub fn free<T>(&self, ptr: *mut T, count: usize) {
        let size = mem::size_of::<T>() * count;
        (self.free_fn)(self.backing, ptr as *mut _, size)
    }
}
