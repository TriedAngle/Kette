use std::{mem, ptr};

mod arena;
mod chunk;
mod freelist;
mod leaky;
mod page;
mod pools;

pub use arena::ArenaAllocator;
pub use leaky::{LeakyBox, LeakyVec};
pub use page::{PageAllocator, PAGE_SIZE};
pub use pools::{ChunkPool, FreeListPool};

type AllocFn = fn(backing: *mut (), size: usize, align: usize) -> *mut u8;
type FreeFn = fn(backing: *mut (), ptr: *mut u8, size: usize, align: usize);
type ReallocFn =
    fn(backing: *mut (), ptr: *mut u8, size: usize, new_size: usize, align: usize) -> *mut u8;

pub const fn is_power_of_two(x: usize) -> bool {
    x & (x - 1) == 0
}

pub const fn align_forward(ptr: usize, align: usize) -> usize {
    assert!(is_power_of_two(align));
    (ptr + align - 1) & !(align - 1)
}

pub trait IntoAllocator {
    fn allocator(&mut self) -> Allocator;
}

#[derive(Clone, Copy)]
pub struct Allocator {
    backing: *mut (),
    alloc_fn: AllocFn,
    free_fn: FreeFn,
    realloc_fn: ReallocFn,
}

impl Allocator {
    pub fn new(
        backing: *mut (),
        alloc_fn: AllocFn,
        free_fn: FreeFn,
        realloc_fn: ReallocFn,
    ) -> Self {
        Self {
            backing,
            alloc_fn,
            free_fn,
            realloc_fn,
        }
    }

    pub fn create<T: Clone>(&mut self, size: usize) -> LeakyVec<T> {
        let allocation = self.alloc::<T>(size);
        let vec = LeakyVec::new(allocation, size).unwrap();
        vec
    }

    pub fn destroy<T>(&mut self, vec: &mut LeakyVec<T>) {
        self.free(vec.ptr.as_ptr(), vec.size);
    }

    pub fn resize<T>(&mut self, vec: &mut LeakyVec<T>, new_size: usize) {
        if (vec.size == new_size) {
            return;
        }

        let old = vec.ptr.as_ptr();
        let new = self.realloc(old, vec.size, new_size);
        vec.ptr = ptr::NonNull::new(new).unwrap();
        vec.size = new_size;
    }

    pub fn make<T>(&mut self) -> LeakyBox<T> {
        let allocation = self.alloc::<T>(1);
        unsafe { LeakyBox::new(allocation) }
    }

    pub fn unmake<T>(&mut self, boxx: &mut LeakyBox<T>) {
        self.free(boxx.ptr.as_ptr(), 1);
    }

    pub fn alloc<T>(&mut self, count: usize) -> *mut T {
        let size = mem::size_of::<T>() * count;
        let align = mem::align_of::<T>();
        (self.alloc_fn)(self.backing, size, align) as *mut T
    }

    pub fn free<T>(&mut self, ptr: *mut T, count: usize) {
        let size = mem::size_of::<T>() * count;
        (self.free_fn)(self.backing, ptr as *mut _, size, mem::align_of::<T>())
    }

    pub fn realloc<T>(&mut self, ptr: *mut T, count: usize, new_count: usize) -> *mut T {
        let size = mem::size_of::<T>() * count;
        let new_size = mem::size_of::<T>() * new_count;
        let align = mem::align_of::<T>();
        (self.realloc_fn)(self.backing, ptr as *mut _, size, new_size, align) as *mut T
    }
}
