use std::{ffi, mem, ptr};

use super::IntoAllocator;

#[cfg(target_os = "windows")]
extern "C" {
    fn VirtualAlloc(
        lpAddress: *mut ffi::c_void,
        dwSize: usize,
        flAllocationType: u32,
        flProtect: u32,
    ) -> *mut ffi::c_void;

    fn VirtualFree(lpAddress: *mut ffi::c_void, dwSize: usize, dwFreeType: u32) -> bool;
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
extern "C" {
    fn mmap(
        addr: *mut std::ffi::c_void,
        length: usize,
        prot: i32,
        flags: i32,
        fd: i32,
        offset: i64,
    ) -> *mut std::ffi::c_void;

    fn munmap(addr: *mut std::ffi::c_void, length: usize) -> i32;
}

unsafe fn memory(size: usize) -> *mut ffi::c_void {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    unsafe {
        const PROT_READ: i32 = 0x1;
        const PROT_WRITE: i32 = 0x2;
        const MAP_PRIVATE: i32 = 0x02;
        const MAP_ANONYMOUS: i32 = 0x20;
        return mmap(
            ptr::null_mut(),
            size,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            -1,
            0,
        );
    }
    #[cfg(target_os = "windows")]
    unsafe {
        const MEM_COMMIT: u32 = 0x00001000;
        const MEM_RESERVE: u32 = 0x00002000;
        const PAGE_READWRITE: u32 = 0x04;
        return VirtualAlloc(
            ptr::null_mut(),
            size,
            MEM_COMMIT | MEM_RESERVE,
            PAGE_READWRITE,
        );
    }
}

unsafe fn burn(address: *mut ffi::c_void, size: usize) {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    unsafe {
        munmap(address, size);
    }
    #[cfg(all(target_os = "windows", target_arch = "x86_64"))]
    unsafe {
        const MEM_RELEASE: u32 = 0x00008000;
        let _ = VirtualFree(address, size, MEM_RELEASE);
    }
}

struct PageAllocator {}

impl PageAllocator {
    pub fn new() -> Self {
        Self {}
    }

    pub fn alloc(&self, size: usize) -> *mut () {
        let allocation = unsafe { memory(size) as *mut _ };
        unsafe { ptr::write_bytes(allocation, 0, size) }
        allocation
    }

    pub fn free(&self, ptr: *mut (), size: usize) {
        unsafe { burn(ptr as *mut _, size) }
    }

    fn page_alloc(backing: *mut (), size: usize, _align: usize) -> *mut () {
        let allocator = backing as *mut PageAllocator;
        unsafe { (*allocator).alloc(size) }
    }

    fn page_free(backing: *mut (), ptr: *mut (), size: usize) {
        let allocator = backing as *mut PageAllocator;
        unsafe { (*allocator).free(ptr, size) }
    }
}

impl IntoAllocator for PageAllocator {
    fn allocator(&self) -> super::Allocator {
        super::Allocator {
            backing: self as *const Self as *mut Self as *mut (),
            alloc_fn: Self::page_alloc,
            free_fn: Self::page_free,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn page_allocator() {
        let page_allocator = PageAllocator::new();
        let allocator = page_allocator.allocator();
        let mut objects = allocator.create::<i64>(16);
        objects[3] = 333;

        assert_eq!(objects[0], 0);
        assert_eq!(objects[1], 0);
        assert_eq!(objects[2], 0);
        assert_eq!(objects[3], 333);
        assert_eq!(objects[4], 0);
        allocator.destroy(&mut objects)
    }
}
