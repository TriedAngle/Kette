use std::{
    alloc::{self, Layout},
    marker::PhantomData,
    ptr::{self, NonNull},
};

use crate::{Header, Object};

/// A raw allocation region.
struct Region {
    start: *mut u8,
    end: *mut u8,
}
impl Region {
    fn contains(&self, p: *const u8) -> bool {
        p >= self.start && p < self.end
    }

    fn zeroed() -> Self {
        Self {
            start: std::ptr::null_mut(),
            end: std::ptr::null_mut(),
        }
    }
}

#[repr(C)]
struct FreeBlock {
    size: usize,
    next: *mut FreeBlock,
}

struct OldSpace {
    start: *mut u8,
    end: *mut u8,
    free_list: *mut FreeBlock,
    allocated: Vec<NonNull<Object>>,
}

impl OldSpace {
    unsafe fn new(capacity: usize) -> Self {
        let layout = Layout::from_size_align(capacity, align_of::<FreeBlock>()).unwrap();
        let start = unsafe { alloc::alloc(layout) };
        if start.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        let end = unsafe { start.add(capacity) };

        let fb = start as *mut FreeBlock;
        unsafe { (*fb).size = capacity };
        unsafe { (*fb).next = ptr::null_mut() };

        Self {
            start,
            end,
            free_list: fb,
            allocated: Vec::new(),
        }
    }

    unsafe fn drop_space(&mut self) {
        let capacity = unsafe { self.end.offset_from(self.start) } as usize;
        let layout = Layout::from_size_align(capacity, align_of::<FreeBlock>()).unwrap();
        unsafe { alloc::dealloc(self.start, layout) };
        self.start = ptr::null_mut();
        self.end = ptr::null_mut();
        self.free_list = ptr::null_mut();
        self.allocated.clear();
    }

    fn contains(&self, p: *const u8) -> bool {
        p >= self.start && p < self.end
    }

    pub fn zeroed() -> Self {
        Self {
            start: std::ptr::null_mut(),
            end: std::ptr::null_mut(),
            free_list: std::ptr::null_mut(),
            allocated: Vec::new(),
        }
    }
}

pub struct Heap {
    nur_a: Vec<u8>,
    nur_b: Vec<u8>,
    from: Region,
    to: Region,
    bump: *mut u8,
    bump_limit: *mut u8,

    old: OldSpace,

    remembered: Vec<NonNull<Object>>,

    large_threshold: usize,
    promote_age: u16,

    mark_stack: Vec<NonNull<Object>>,

    // make this !Send and !Sync
    _marker: PhantomData<*const ()>,
}

impl Heap {
    pub fn new(
        nursery_bytes: usize,
        old_bytes: usize,
        large_threshold: usize,
        promote_age: u16,
    ) -> Self {
        assert!(nursery_bytes >= 1024 && old_bytes >= 1024);
        let nur_a = vec![0u8; nursery_bytes];
        let nur_b = vec![0u8; nursery_bytes];

        let (a_start, a_end) = raw_range(&nur_a);
        let (b_start, b_end) = raw_range(&nur_b);

        let from = Region {
            start: a_start,
            end: a_end,
        };
        let to = Region {
            start: b_start,
            end: b_end,
        };

        let old = unsafe { OldSpace::new(old_bytes) };
        Self {
            nur_a,
            nur_b,
            from,
            to,
            bump: a_start,
            bump_limit: a_end,
            old,
            remembered: Vec::with_capacity(256),
            large_threshold,
            promote_age,
            mark_stack: Vec::with_capacity(1024),
            _marker: PhantomData,
        }
    }

    pub fn zeroed() -> Self {
        Self {
            nur_a: Vec::new(),
            nur_b: Vec::new(),
            from: Region::zeroed(),
            to: Region::zeroed(),
            bump: std::ptr::null_mut(),
            bump_limit: std::ptr::null_mut(),
            old: OldSpace::zeroed(),
            remembered: Vec::new(),
            large_threshold: 0,
            promote_age: 0,
            mark_stack: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// Is `p` inside the current nursery from-space?
    #[inline]
    pub fn in_nursery_from(&self, p: *const Object) -> bool {
        let q = p as *const u8;
        self.from.contains(q)
    }
    /// Is `p` inside either nursery space?
    #[inline]
    pub fn in_nursery_any(&self, p: *const Object) -> bool {
        let q = p as *const u8;
        self.from.contains(q) || self.to.contains(q)
    }
    /// Is `p` inside old space?
    #[inline]
    pub fn in_old(&self, p: *const Object) -> bool {
        let q = p as *const u8;
        self.old.contains(q)
    }
}

#[inline]
fn raw_range(buf: &Vec<u8>) -> (*mut u8, *mut u8) {
    let start = buf.as_ptr() as *mut u8;
    let end = unsafe { start.add(buf.len()) };
    (start, end)
}

#[inline]
fn align_up(n: usize, a: usize) -> usize {
    let mask = a - 1;
    (n + mask) & !mask
}

// unsafe fn init_header(
//     p: *mut Header,
//     type_id: u32,
//     vtable: *mut VTable,
//     total_size: usize,
//     large: bool,
// ) {
//     (*p).type_id = type_id;
//     (*p).flags = if large { F_LARGE } else { 0 };
//     (*p).age = 0;
//     (*p).vtable_or_fwd = vtable;
//     (*p).size = total_size as u32;
// }

#[inline]
fn oom(ctx: &str) -> ! {
    panic!("GC out of memory: {ctx}");
}
