use crate::object::{self, Object};
use crate::object::ObjectRef;
use crate::VM;
use std::alloc;
use std::collections::HashMap;
use std::ptr;

pub enum GCResult<T> {
    Ok(T),
    OutOfMemory,
    InitializationError,
    ObjectDoesNotExist,
}

impl<T> GCResult<T> {
    pub fn unwrap(self) -> T {
        match self {
            GCResult::Ok(v) => v,
            _ => {
                panic!("unwrap on empty result")
            }
        }
    }
}

pub struct MSAllocation {
    object: *mut u8,
    layout: alloc::Layout,
    meta: usize, // tag, for example mark/sweep
}

impl MSAllocation {
    // Sets the nth bit of meta to 1
    #[inline]
    pub fn set_meta_bit(&mut self, n: usize) {
        self.meta |= 1 << n;
    }

    // Clears the nth bit of meta to 0
    #[inline]
    pub fn clear_meta_bit(&mut self, n: usize) {
        self.meta &= !(1 << n);
    }

    // Reads the nth bit of meta
    #[inline]
    pub fn get_meta_bit(&self, n: usize) -> bool {
        (self.meta & (1 << n)) != 0
    }

    #[inline]
    pub fn mark(&mut self) {
        self.set_meta_bit(0);
    }

    #[inline]
    pub fn unmark(&mut self) {
        self.clear_meta_bit(0);
    }

    #[inline]
    pub fn is_marked(&self) -> bool {
        self.get_meta_bit(0)
    }

    #[inline]
    pub fn root(&mut self) {
        self.set_meta_bit(8);
    }

    #[inline]
    pub fn unroot(&mut self) {
        self.clear_meta_bit(8);
    }

    #[inline]
    pub fn is_root(&self) -> bool {
        self.get_meta_bit(8)
    }
}

impl MSAllocation {
    pub fn new(object: *mut u8, layout: alloc::Layout) -> Self {
        Self {
            object,
            layout,
            meta: 0,
        }
    }
}

pub struct MarkAndSweep {
    allocations: HashMap<ObjectRef, MSAllocation>,
    worklist: Vec<ObjectRef>,
    paused: bool,
    vm: *const VM,
}

impl MarkAndSweep {
    pub fn new() -> Self {
        Self {
            allocations: HashMap::new(),
            worklist: Vec::new(),
            paused: false,
            vm: ptr::null(),
        }
    }

    pub fn link_vm(&mut self, vm: *const VM) {
        self.vm = vm;
    }

    pub fn allocate(
        &mut self,
        size: usize,
        align: usize,
        root: bool,
    ) -> GCResult<ObjectRef> {
        let layout = alloc::Layout::from_size_align(size, align).unwrap();
        let mut ptr = unsafe { alloc::alloc(layout) };
        if ptr.is_null() {
            self.mark_sweep();
            ptr = unsafe { alloc::alloc(layout) };
            if ptr.is_null() {
                return GCResult::OutOfMemory;
            }
        }
        let object = ObjectRef::new(ptr as *mut Object);

        let mut allocation = MSAllocation::new(ptr, layout);
        if root {
            allocation.root();
        }
        self.allocations.insert(object, allocation);
        GCResult::Ok(object)
    }

    pub fn deallocate(&mut self, object: ObjectRef) -> GCResult<()> {
        let allocation = self.allocations.remove(&object);

        if allocation.is_none() {
            return GCResult::ObjectDoesNotExist;
        }
        let allocation = allocation.unwrap();
        unsafe {
            alloc::dealloc(allocation.object, allocation.layout);
        }

        GCResult::Ok(())
    }

    pub fn allocation(&mut self, object: ObjectRef) -> Option<&MSAllocation> {
        self.allocations.get(&object)
    }

    pub fn allocation_mut(&mut self, object: ObjectRef) -> Option<&mut MSAllocation> {
        self.allocations.get_mut(&object)
    }

    pub fn reallocate(
        &mut self,
        object: ObjectRef,
        size: usize,
    ) -> GCResult<ObjectRef> {
        let allocation = self.allocations.get_mut(&object);
        if allocation.is_none() {
            return GCResult::ObjectDoesNotExist;
        }
        let allocation = allocation.unwrap();

        let ptr = unsafe { alloc::realloc(allocation.object, allocation.layout, size) };

        if ptr == allocation.object {
            allocation.layout =
                alloc::Layout::from_size_align(size, allocation.layout.align()).unwrap();
            return GCResult::Ok(object);
        }

        GCResult::Ok(ObjectRef::null())
    }

    pub fn mark_roots(&mut self) {
        let vm = unsafe { self.vm.as_ref().unwrap() };
        for root in vm.stack.iter() {
            if let Some(allocation) = self.allocations.get_mut(root) {
                allocation.mark();
                self.worklist.push(*root);
            }
        }
        for root in vm.words.values() {
            let obj = ObjectRef::from_word(*root);
            if let Some(allocation) = self.allocations.get_mut(&obj) {
                allocation.mark();
                self.worklist.push(obj);
            }
        }
        for (key, obj) in self.allocations.iter_mut() {
            if obj.is_root() {
                obj.mark();
                self.worklist.push(*key);
            }
        }
    }

    pub fn mark_sweep(&mut self) {
        self.mark_roots();
        unsafe {
            self.mark();
            self.sweep();
        }
    }

    pub unsafe fn mark(&mut self) {
        while let Some(obj) = self.worklist.pop() {
            let map = obj.get_map();

            // our object is a map
            if map == (*self.vm).special_objects.map_map {
                let mapp = obj.as_map();
                let name = (*mapp).name;
                if let Some(allocation) = self.allocations.get_mut(&name) {
                    allocation.mark();
                }

                let slots = (*mapp).slots();

                for slot in slots {
                    let refs = slot.reference_objects();
                    for ref_obj in refs {
                        if let Some(allocation) = self.allocations.get_mut(&ref_obj) {
                            if !allocation.is_marked() {
                                allocation.mark();
                                self.worklist.push(ref_obj)
                            }
                        }
                    }
                }
            } else if map == (*self.vm).special_objects.fixnum_map {
            } else if map == (*self.vm).special_objects.bytearray_map {
            } else {
                let slots = (*map).slots();
                for slot in slots {
                    if slot.kind == object::SLOT_DATA {
                        let field = obj.get_field(slot.index);
                        if let Some(allocation) = self.allocations.get_mut(&field) {
                            if !allocation.is_marked() {
                                allocation.mark();
                                self.worklist.push(field)
                            }
                        }
                    }
                }
            }
        }
    }

    pub unsafe fn sweep(&mut self) {
        let unmarked = self
            .allocations
            .iter()
            .filter(|(_k, v)| !v.is_marked())
            .map(|(k, _v)| *k)
            .collect::<Vec<_>>();

        unmarked
            .iter()
            .for_each(|obj| self.deallocate(*obj).unwrap());

        self.allocations.iter_mut().for_each(|(_k, v)| v.unmark());
    }

    pub fn pause(&mut self) {
        self.paused = true;
    }

    pub fn unpause(&mut self) {
        self.paused = false;
    }

    pub fn paused(&self) -> bool {
        self.paused
    }

    pub fn allocation_count(&self) -> usize {
        self.allocations.len()
    }

    pub fn print_all_objects(&self) {
        unsafe {
            for (key, _alloc) in self.allocations.iter() {
                println!("----");
                println!("address: {:?}", key);
                let map = key.get_map();
                let map_name = (*map).name.bytearray_as_str();
                println!("type: {:?}", map_name);
                if map == (*self.vm).special_objects.map_map {
                    let mapp = key.as_map();
                    let mapp_name = (*mapp).name.bytearray_as_str();
                    println!("map name: {:?}", mapp_name);
                    println!("object size: {:?}", (*mapp).object_size);
                    println!("slot count: {:?}", (*mapp).slot_count);
                } else if map == (*self.vm).special_objects.fixnum_map {
                    let intt = key.as_fixnum();
                    let value = (*intt).value;
                    println!("value: {:?}", value);
                } else if map == (*self.vm).special_objects.bytearray_map {
                    let ba = key.as_byte_array();
                    let bas = key.bytearray_as_str();
                    println!("value: {:?}", bas);
                } else {
                }
            }
        }
    }

    pub fn deallocate_all(&mut self) {
        let allocations = self
            .allocations
            .iter()
            .map(|(k, _v)| *k)
            .collect::<Vec<_>>();
        allocations
            .iter()
            .for_each(|obj| self.deallocate(*obj).unwrap());
    }

    pub fn set_object_root(&mut self, obj: ObjectRef) {
        if let Some(allocation) = self.allocations.get_mut(&obj) {
            allocation.root();
        }
    }

    pub fn unset_object_root(&mut self, obj: ObjectRef) {
        if let Some(allocation) = self.allocations.get_mut(&obj) {
            allocation.unroot();
        }
    }
}
