use std::{ffi, ptr};
pub const PAGE_SIZE: usize = 4096;

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

pub unsafe fn memory(size: usize) -> *mut ffi::c_void {
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

pub unsafe fn burn(address: *mut ffi::c_void, size: usize) {
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
