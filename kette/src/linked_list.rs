use std::{marker::PhantomData, ptr::NonNull, slice::from_raw_parts};

pub const DEFAULT_BLOCK_SIZE: usize = 4096; // 4KB blocks
pub const MIN_ALIGNMENT: usize = 8;

#[repr(C)]
pub struct Node {
    pub next: Option<NonNull<Node>>,
    pub prev: Option<NonNull<Node>>,
    pub data_size: usize,
    // code in memory here
}

impl Node {
    pub fn data_ptr(&self) -> *const u8 {
        let node_ptr = self as *const Self;
        unsafe { (node_ptr as *const u8).add(std::mem::size_of::<Self>()) }
    }

    pub fn get_data_slice(&self) -> &[u8] {
        unsafe { from_raw_parts(self.data_ptr(), self.data_size) }
    }

    pub fn data_as<T>(&self) -> &[T] {
        let data_ptr = self.data_ptr();

        let count = self.data_size / std::mem::size_of::<T>();

        unsafe { std::slice::from_raw_parts(data_ptr as *const T, count) }
    }
}

struct Block {
    ptr: NonNull<u8>,
    size: usize,
    used: usize,
    next: Option<NonNull<Block>>,
}

impl Block {
    fn new(size: usize) -> Self {
        let aligned_size = (size + MIN_ALIGNMENT - 1) & !(MIN_ALIGNMENT - 1);

        let layout =
            std::alloc::Layout::from_size_align(aligned_size, MIN_ALIGNMENT)
                .expect("Invalid layout");

        let ptr = unsafe {
            NonNull::new(std::alloc::alloc(layout))
                .expect("Memory allocation failed")
        };

        Block {
            ptr,
            size: aligned_size,
            used: 0,
            next: None,
        }
    }

    fn can_fit(&self, bytes: usize) -> bool {
        self.used + bytes <= self.size
    }

    fn allocate_node(&mut self, data_size: usize) -> Option<NonNull<Node>> {
        let total_size = std::mem::size_of::<Node>() + data_size;

        if !self.can_fit(total_size) {
            return None;
        }

        let node_ptr = unsafe { self.ptr.as_ptr().add(self.used) as *mut Node };
        let node = unsafe { &mut *node_ptr };

        node.next = None;
        node.prev = None;
        node.data_size = data_size;

        self.used += total_size;

        Some(unsafe { NonNull::new_unchecked(node_ptr) })
    }
}

impl Drop for Block {
    fn drop(&mut self) {
        unsafe {
            let layout =
                std::alloc::Layout::from_size_align(self.size, MIN_ALIGNMENT)
                    .expect("Invalid layout in drop");
            std::alloc::dealloc(self.ptr.as_ptr(), layout);
        }
    }
}

pub struct LinkedListAllocator {
    head: Option<NonNull<Node>>,
    tail: Option<NonNull<Node>>,
    head_block: Option<NonNull<Block>>,
    current_block: Option<NonNull<Block>>,
    _marker: PhantomData<Block>,
}

impl LinkedListAllocator {
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            head_block: None,
            current_block: None,
            _marker: PhantomData,
        }
    }

    fn allocate_block(&mut self, min_size: usize) -> NonNull<Block> {
        let block_size = if min_size > DEFAULT_BLOCK_SIZE {
            min_size
        } else {
            DEFAULT_BLOCK_SIZE
        };

        // Allocate Block struct on the heap
        let layout = std::alloc::Layout::new::<Block>();
        let block_ptr = unsafe {
            let ptr = std::alloc::alloc(layout) as *mut Block;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            // Initialize the Block using Block::new
            ptr.write(Block::new(block_size));
            NonNull::new_unchecked(ptr)
        };

        // Link it to the block list
        unsafe {
            if let Some(current_head) = self.head_block {
                (*block_ptr.as_ptr()).next = Some(current_head);
            }
            self.head_block = Some(block_ptr);
            self.current_block = Some(block_ptr);
        }

        block_ptr
    }

    fn get_or_create_block(&mut self, required_size: usize) -> NonNull<Block> {
        if let Some(block_ptr) = self.current_block {
            let can_fit = unsafe { block_ptr.as_ref().can_fit(required_size) };

            if can_fit {
                return block_ptr;
            }
        }

        self.allocate_block(required_size)
    }

    pub fn allocate(&mut self, data: &[u8]) -> NonNull<Node> {
        let data_size = data.len();
        let required_size = std::mem::size_of::<Node>() + data_size;

        let mut block_ptr = self.get_or_create_block(required_size);

        let mut node_ptr = unsafe {
            block_ptr.as_mut().allocate_node(data_size).expect(
                "Failed to allocate node in block that should have space",
            )
        };

        let data_dest = unsafe {
            let node = node_ptr.as_ref();
            std::slice::from_raw_parts_mut(
                node.data_ptr() as *mut u8,
                data_size,
            )
        };
        data_dest.copy_from_slice(data);

        match self.tail {
            None => {
                self.head = Some(node_ptr);
                self.tail = Some(node_ptr);
            }
            Some(mut tail_ptr) => {
                unsafe {
                    tail_ptr.as_mut().next = Some(node_ptr);
                    node_ptr.as_mut().prev = Some(tail_ptr);
                }
                self.tail = Some(node_ptr);
            }
        }

        node_ptr
    }
}

impl Drop for LinkedListAllocator {
    fn drop(&mut self) {
        let mut current_block = self.head_block;
        while let Some(block_ptr) = current_block {
            let block = unsafe { std::ptr::read(block_ptr.as_ptr()) };
            current_block = block.next;

            drop(block);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linkedlist_allocator_basic() {
        let mut allocator = LinkedListAllocator::new();

        let data1 = [1, 2, 3, 4, 5];
        let data2 = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100];

        let allocated_data1 =
            unsafe { allocator.allocate(&data1).as_ref().data_as::<u8>() };
        let allocated_data2 =
            unsafe { allocator.allocate(&data2).as_ref().data_as::<u8>() };

        assert_eq!(allocated_data1.len(), data1.len());
        assert_eq!(allocated_data2.len(), data2.len());

        assert_eq!(allocated_data1, &data1);
        assert_eq!(allocated_data2, &data2);
    }

    #[test]
    fn test_linkedlist_allocator_large_data() {
        let mut allocator = LinkedListAllocator::new();

        let large_data =
            vec![42; DEFAULT_BLOCK_SIZE - std::mem::size_of::<Node>()];

        let allocated_data =
            unsafe { allocator.allocate(&large_data).as_ref().data_as::<u8>() };

        assert_eq!(allocated_data.len(), large_data.len());

        assert_eq!(allocated_data, &large_data[..]);
    }

    #[test]
    fn test_linkedlist_allocator_multiple_allocations() {
        let mut allocator = LinkedListAllocator::new();

        let node_size = std::mem::size_of::<Node>();
        let item_size = 1024;
        let total_item_size = node_size + item_size;
        let items_per_block = DEFAULT_BLOCK_SIZE / total_item_size;
        let num_blocks = 3;
        let total_items = items_per_block * num_blocks + 1; // +1 to spill into another block

        let mut allocated_data = Vec::with_capacity(total_items);
        let mut original_data = Vec::with_capacity(total_items);

        for i in 0..total_items {
            let data = vec![(i % 256) as u8; item_size];
            original_data.push(data.clone());
            allocated_data.push(
                unsafe { allocator.allocate(&data).as_ref() }.data_as::<u8>(),
            );
        }

        for i in 0..total_items {
            assert_eq!(allocated_data[i], &original_data[i][..]);
        }
    }
}
