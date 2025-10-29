#[cfg(unix)]
#[allow(unused)]
mod unix {
    use core::ffi::c_void;

    pub const PROT_NONE: i32 = 0x0;
    pub const PROT_READ: i32 = 0x1;
    pub const PROT_WRITE: i32 = 0x2;
    pub const PROT_EXEC: i32 = 0x4;

    pub const MAP_FILE: i32 = 0x0;
    pub const MAP_SHARED: i32 = 0x01;
    pub const MAP_PRIVATE: i32 = 0x02;

    #[cfg(target_os = "linux")]
    pub const MAP_ANON: i32 = 0x20;
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    pub const MAP_ANON: i32 = 0x1000;

    pub const MAP_FAILED: isize = -1;

    unsafe extern "C" {
        pub fn mmap(
            addr: *mut c_void,
            length: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: isize,
        ) -> *mut c_void;

        pub fn munmap(addr: *mut c_void, length: usize) -> i32;
    }

    #[inline]
    pub unsafe fn anonymous_mmap(len: usize) -> *mut u8 {
        let p = unsafe {
            mmap(
                core::ptr::null_mut(),
                len,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANON,
                -1,
                0,
            )
        };
        if (p as isize) == MAP_FAILED {
            core::ptr::null_mut()
        } else {
            p as *mut u8
        }
    }

    #[inline]
    pub unsafe fn anonymous_munmap(ptr: *mut u8, len: usize) {
        let _ = unsafe { munmap(ptr.cast(), len) };
    }
}
