use std::ptr;

use super::{Allocator, ArenaAllocator};

struct Allocation {
    size: usize,
    from: *mut u8,
    to: *mut u8,
}
