use core::slice;
use std::{
    ffi,
    mem::{self, ManuallyDrop, MaybeUninit},
    panic, ptr,
};
pub const PAGE_SIZE: usize = 4096;

#[cfg(target_os = "windows")]
mod raw {
    use std::{ffi, ptr};
    extern "C" {
        pub fn VirtualAlloc(
            lpAddress: *mut ffi::c_void,
            dwSize: usize,
            flAllocationType: u32,
            flProtect: u32,
        ) -> *mut ffi::c_void;

        pub fn VirtualFree(lpAddress: *mut ffi::c_void, dwSize: usize, dwFreeType: u32) -> bool;

        fn LoadLibraryW(lpLibFileName: *const u16) -> *mut ffi::c_void;
        fn GetProcAddress(hModule: *mut ffi::c_void, lpProcName: *const i8) -> *mut ffi::c_void;
        fn FreeLibrary(hLibModule: *mut ffi::c_void) -> i32;
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod raw {
    use std::{ffi, ptr};
    extern "C" {
        pub fn mmap(
            addr: *mut ffi::c_void,
            length: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: i64,
        ) -> *mut ffi::c_void;

        pub fn munmap(addr: *mut ffi::c_void, length: usize) -> i32;

        pub fn dlopen(filename: *const ffi::c_char, flags: i32) -> *const ();
        pub fn dlclose(handle: *const ()) -> i32;
        pub fn dlsym(handle: *const (), symbol: *const ffi::c_char) -> *const ();
    }
}

pub unsafe fn memory(size: usize) -> *mut ffi::c_void {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    unsafe {
        const PROT_READ: i32 = 0x1;
        const PROT_WRITE: i32 = 0x2;
        const MAP_PRIVATE: i32 = 0x02;
        const MAP_ANONYMOUS: i32 = 0x20;
        return raw::mmap(
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
        return raw::VirtualAlloc(
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
        raw::munmap(address, size);
    }
    #[cfg(all(target_os = "windows", target_arch = "x86_64"))]
    unsafe {
        const MEM_RELEASE: u32 = 0x00008000;
        let _ = raw::VirtualFree(address, size, MEM_RELEASE);
    }
}

pub unsafe fn open_library(filename: &str) -> *const () {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    unsafe {
        const RTLD_LAZY: i32 = 0x00001; // Lazy function call binding.
        const RTLD_NOW: i32 = 0x00002; // Immediate function call binding.
        const RTLD_BINDING_MASK: i32 = 0x3; // Mask of binding time value.
        const RTLD_NOLOAD: i32 = 0x00004; // Do not load the object.
        const RTLD_DEEPBIND: i32 = 0x00008;
        let path = ffi::CString::new(filename).unwrap();
        let library = raw::dlopen(path.as_ptr(), RTLD_LAZY);
        library
    }
}

pub unsafe fn close_library(handle: *const ()) -> i32 {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    unsafe {
        raw::dlclose(handle)
    }
}

pub unsafe fn library_symbol(handle: *const (), symbol: &str) -> *const () {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    unsafe {
        let symbol = ffi::CString::new(symbol).unwrap();
        raw::dlsym(handle, symbol.as_ptr())
    }
}

type StackCallback = unsafe extern "C-unwind" fn(ptr: *mut u8, data: *mut ffi::c_void);

extern "C-unwind" {
    fn stack_allocate_callback(size: usize, callback: StackCallback, data: *mut ffi::c_void);
}

unsafe extern "C-unwind" fn trampoline<F: FnOnce(*mut u8)>(ptr: *mut u8, data: *mut ffi::c_void) {
    let f = mem::ManuallyDrop::take(&mut *(data as *mut ManuallyDrop<F>));
    f(ptr)
}

#[inline(always)]
fn get_trampoline<F: FnOnce(*mut u8)>(_closure: &F) -> StackCallback {
    trampoline::<F>
}

pub fn with_stack_alloc<T, F>(size: usize, cb: F) -> T
where
    F: FnOnce(&mut [u8]) -> T + panic::UnwindSafe + panic::RefUnwindSafe,
{
    let mut ret = MaybeUninit::uninit();

    let closure = |ptr| {
        let slice = unsafe { slice::from_raw_parts_mut(ptr, size) };
        let val = cb(slice);
        ret.write(val);
    };

    let trampoline = get_trampoline(&closure);
    let mut closure_data = mem::ManuallyDrop::new(closure);

    unsafe {
        stack_allocate_callback(
            size,
            trampoline,
            &mut closure_data as *mut _ as *mut ffi::c_void,
        );
        ret.assume_init()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_with_return() {
        let x = 1000;
        let res = with_stack_alloc(256, |mem| unsafe {
            let raw = mem.as_mut_ptr();
            let num = raw as *mut u64;
            let ptr = num.add(2);
            *ptr = x;
            let val = *ptr;
            println!("wooow mem: {:?}, val: {:?}", mem.len(), val);
            *ptr + 10
        });
        println!("wow res: {}", res)
    }
}
