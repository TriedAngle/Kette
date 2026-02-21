use std::ptr::NonNull;

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
    #[cfg(target_os = "linux")]
    pub const MAP_FIXED_NOREPLACE: i32 = 0x100000;
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    pub const MAP_ANON: i32 = 0x1000;

    pub const MAP_FAILED: isize = -1;

    /// posix mmap and munmap
    /// # Safety
    /// see valid mmap and munmap usage online
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

    /// posix memory allocation using mmap
    /// # Safety
    /// null must be checked
    #[inline]
    pub unsafe fn anonymous_mmap(len: usize) -> *mut u8 {
        // SAFETY: safe if contract holds
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

    /// posix memory deallocation using munmap
    /// # Safety
    /// must be allocated by mmmap
    #[inline]
    pub unsafe fn anonymous_munmap(ptr: *mut u8, len: usize) {
        // SAFETY: safe if contract holds
        let _ = unsafe { munmap(ptr.cast(), len) };
    }

    #[inline]
    pub unsafe fn anonymous_mmap_at(addr: *mut u8, len: usize) -> *mut u8 {
        #[cfg(target_os = "linux")]
        let flags = MAP_PRIVATE | MAP_ANON | MAP_FIXED_NOREPLACE;
        #[cfg(not(target_os = "linux"))]
        let flags = MAP_PRIVATE | MAP_ANON;

        let p = unsafe {
            mmap(addr.cast(), len, PROT_READ | PROT_WRITE, flags, -1, 0)
        };
        if (p as isize) == MAP_FAILED {
            core::ptr::null_mut()
        } else {
            p as *mut u8
        }
    }
}

#[cfg(windows)]
mod windows {
    use core::ffi::c_void;

    pub const MEM_COMMIT: u32 = 0x1000;
    pub const MEM_RESERVE: u32 = 0x2000;
    pub const MEM_RELEASE: u32 = 0x8000;
    pub const PAGE_READWRITE: u32 = 0x04;

    unsafe extern "system" {
        fn VirtualAlloc(
            lpAddress: *mut c_void,
            dwSize: usize,
            flAllocationType: u32,
            flProtect: u32,
        ) -> *mut c_void;

        fn VirtualFree(
            lpAddress: *mut c_void,
            dwSize: usize,
            dwFreeType: u32,
        ) -> i32;
    }

    #[inline]
    pub unsafe fn reserve_and_commit(len: usize) -> *mut u8 {
        // SAFETY: safe if contract holds
        let p = unsafe {
            VirtualAlloc(
                core::ptr::null_mut(),
                len,
                MEM_RESERVE | MEM_COMMIT,
                PAGE_READWRITE,
            )
        };
        p as *mut u8
    }

    #[inline]
    pub unsafe fn reserve_and_commit_at(addr: *mut u8, len: usize) -> *mut u8 {
        let p = unsafe {
            VirtualAlloc(
                addr.cast(),
                len,
                MEM_RESERVE | MEM_COMMIT,
                PAGE_READWRITE,
            )
        };
        p as *mut u8
    }

    #[inline]
    pub unsafe fn release(ptr: *mut u8) {
        // SAFETY: safe if contract holds
        let _ = unsafe { VirtualFree(ptr.cast(), 0, MEM_RELEASE) };
    }
}

pub const OS_PAGE_SIZE: usize = 4096;

#[must_use]
pub fn map_memory(size: usize) -> Option<NonNull<u8>> {
    #[cfg(unix)]
    // SAFETY: this is safe
    let ptr = unsafe { unix::anonymous_mmap(size) };
    #[cfg(windows)]
    // SAFETY: this is safe
    let ptr = unsafe { windows::reserve_and_commit(size) };
    NonNull::new(ptr)
}

#[must_use]
pub fn map_memory_at(addr: NonNull<u8>, size: usize) -> Option<NonNull<u8>> {
    #[cfg(unix)]
    let ptr = unsafe { unix::anonymous_mmap_at(addr.as_ptr(), size) };
    #[cfg(windows)]
    let ptr = unsafe { windows::reserve_and_commit_at(addr.as_ptr(), size) };

    let mapped = NonNull::new(ptr)?;
    if mapped.as_ptr() != addr.as_ptr() {
        unmap_memory(mapped, size);
        return None;
    }
    Some(mapped)
}

pub fn unmap_memory(ptr: NonNull<u8>, size: usize) {
    #[cfg(unix)]
    // SAFETY: ptr must be from mmap allocation
    unsafe {
        unix::anonymous_munmap(ptr.as_ptr(), size)
    };
    #[cfg(windows)]
    {
        let _ = size;
        // SAFETY: ptr must be from VirtualAlloc allocation
        unsafe { windows::release(ptr.as_ptr()) };
    }
}
