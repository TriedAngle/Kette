use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use object::{Tagged, Value};

use crate::VMProxy;

pub const HANDLESET_CAPACITY: usize = 20;
const HEAP_PTR_TAG: usize = 1;

struct OverflowChunk {
    // Tagged link:
    // - tag=1 => next OverflowChunk
    // - tag=0 => next HandleSet in VM chain (or null)
    next: *mut HandleSet,
    len: usize,
    slots: [Value; HANDLESET_CAPACITY],
}

#[inline(always)]
fn is_heap_tagged<T>(ptr: *mut T) -> bool {
    (ptr as usize & HEAP_PTR_TAG) != 0
}

#[inline(always)]
fn tag_heap_ptr<T>(ptr: *mut T) -> *mut T {
    debug_assert_eq!(ptr as usize & HEAP_PTR_TAG, 0, "unaligned pointer");
    ((ptr as usize) | HEAP_PTR_TAG) as *mut T
}

#[inline(always)]
fn untag_heap_ptr<T>(ptr: *mut T) -> *mut T {
    ((ptr as usize) & !HEAP_PTR_TAG) as *mut T
}

/// Stack-allocated set of GC roots.
///
/// Each `HandleSet` registers itself on a VM-local linked stack so
/// `VMProxy::visit_roots` can trace all active handle slots.
pub struct HandleSet {
    vm: *mut VMProxy,
    /// Tagged link:
    /// - tag=0 => next HandleSet in VM chain (or null)
    /// - tag=1 => head OverflowChunk (which itself eventually links to the
    ///            next HandleSet with tag=0)
    pub next: *mut HandleSet,
    linked: bool,
    len: usize,
    slots: [Value; HANDLESET_CAPACITY],
}

/// A copyable, scope-bounded rooted handle.
///
/// `Handle` is intentionally distinct from `object::Tagged`: this points to a
/// mutable root slot (indirection) while `Tagged` is a direct value wrapper.
pub struct Handle<'scope, T> {
    slot: *mut Value,
    _scope: PhantomData<&'scope HandleSet>,
    _type: PhantomData<*const T>,
}

impl<'scope, T> Clone for Handle<'scope, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'scope, T> Copy for Handle<'scope, T> {}

impl HandleSet {
    #[inline(always)]
    pub fn new_root(vm: &mut VMProxy) -> Self {
        Self {
            vm: vm as *mut VMProxy,
            next: core::ptr::null_mut(),
            linked: false,
            len: 0,
            slots: [Value::from_i64(0); HANDLESET_CAPACITY],
        }
    }

    #[inline(always)]
    pub fn child(&mut self) -> Self {
        self.ensure_linked();
        Self {
            vm: self.vm,
            next: core::ptr::null_mut(),
            linked: false,
            len: 0,
            slots: [Value::from_i64(0); HANDLESET_CAPACITY],
        }
    }

    #[inline(always)]
    fn ensure_linked(&mut self) {
        if self.linked {
            return;
        }
        let vm = unsafe { &mut *self.vm };
        self.next = vm.handle_roots_head;
        vm.handle_roots_head = self as *mut HandleSet;
        self.linked = true;
    }

    #[inline(always)]
    pub fn pin<'scope, T>(
        &'scope mut self,
        tagged: Tagged<T>,
    ) -> Handle<'scope, T> {
        self.pin_value(tagged.value())
    }

    #[inline(always)]
    pub fn pin_value<'scope, T>(
        &'scope mut self,
        value: Value,
    ) -> Handle<'scope, T> {
        self.ensure_linked();
        let slot = if self.len < HANDLESET_CAPACITY {
            let idx = self.len;
            self.len += 1;
            &mut self.slots[idx]
        } else {
            self.push_overflow_slot()
        };
        *slot = value;
        Handle {
            slot,
            _scope: PhantomData,
            _type: PhantomData,
        }
    }

    fn push_overflow_slot(&mut self) -> &mut Value {
        // First overflow chunk steals `self.next`, preserving VM linkage in
        // chunk.next. This merges overflow and normal link state into `next`.
        if !is_heap_tagged(self.next) {
            let chunk = Box::new(OverflowChunk {
                next: self.next,
                len: 0,
                slots: [Value::from_i64(0); HANDLESET_CAPACITY],
            });
            self.next = tag_heap_ptr(Box::into_raw(chunk) as *mut HandleSet);
        }

        let mut tagged = self.next;
        loop {
            debug_assert!(is_heap_tagged(tagged));
            let chunk_ptr =
                untag_heap_ptr(tagged as *mut OverflowChunk) as *mut OverflowChunk;
            let chunk = unsafe { &mut *chunk_ptr };

            if chunk.len < HANDLESET_CAPACITY {
                let idx = chunk.len;
                chunk.len += 1;
                return &mut chunk.slots[idx];
            }

            if !is_heap_tagged(chunk.next) {
                let next = Box::new(OverflowChunk {
                    next: chunk.next,
                    len: 0,
                    slots: [Value::from_i64(0); HANDLESET_CAPACITY],
                });
                chunk.next = tag_heap_ptr(Box::into_raw(next) as *mut HandleSet);
            }
            tagged = chunk.next;
        }
    }

    /// Return the VM chain successor for this handleset.
    pub fn vm_next(&self) -> *mut HandleSet {
        let mut link = self.next;
        while is_heap_tagged(link) {
            let chunk_ptr =
                untag_heap_ptr(link as *mut OverflowChunk) as *mut OverflowChunk;
            link = unsafe { (*chunk_ptr).next };
        }
        link
    }

    #[inline(always)]
    pub fn visit_roots(
        &mut self,
        visitor: &mut dyn FnMut(&mut Value),
    ) {
        for slot in &mut self.slots[..self.len] {
            visitor(slot);
        }

        let mut tagged = self.next;
        while is_heap_tagged(tagged) {
            let chunk_ptr =
                untag_heap_ptr(tagged as *mut OverflowChunk) as *mut OverflowChunk;
            let chunk = unsafe { &mut *chunk_ptr };
            for slot in &mut chunk.slots[..chunk.len] {
                visitor(slot);
            }
            tagged = chunk.next;
        }
    }

    fn drop_overflow_chain_and_restore_next(&mut self) {
        let mut tagged = self.next;
        if !is_heap_tagged(tagged) {
            return;
        }

        let mut vm_next = core::ptr::null_mut();
        while is_heap_tagged(tagged) {
            let chunk_ptr =
                untag_heap_ptr(tagged as *mut OverflowChunk) as *mut OverflowChunk;
            let next = unsafe { (*chunk_ptr).next };
            if !is_heap_tagged(next) {
                vm_next = next;
            }
            unsafe {
                drop(Box::from_raw(chunk_ptr));
            }
            tagged = next;
        }
        self.next = vm_next;
    }
}

impl Drop for HandleSet {
    fn drop(&mut self) {
        self.drop_overflow_chain_and_restore_next();

        if !self.linked {
            return;
        }
        let vm = unsafe { &mut *self.vm };
        let self_ptr = self as *mut HandleSet;
        debug_assert_eq!(
            vm.handle_roots_head, self_ptr,
            "HandleSet drop must follow LIFO scope order"
        );
        if vm.handle_roots_head == self_ptr {
            vm.handle_roots_head = self.next;
        }
    }
}

impl<'scope, T> Handle<'scope, T> {
    #[inline(always)]
    pub fn value(&self) -> Value {
        unsafe { *self.slot }
    }

    #[inline(always)]
    pub fn set(&self, value: Value) {
        unsafe {
            *self.slot = value;
        }
    }
}

impl<'scope, T> Deref for Handle<'scope, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe { (*self.slot).as_ref() }
    }
}

impl<'scope, T> DerefMut for Handle<'scope, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { (*self.slot).as_mut() }
    }
}

#[cfg(test)]
mod tests {
    use crate::special;
    use heap::{HeapSettings, RootProvider};
    use object::{Header, ObjectType, Tagged, Value};
    use std::alloc::Layout;

    #[test]
    fn handles_are_copyable_and_dereferenceable() {
        let mut vm = special::bootstrap(HeapSettings::default());
        let map_map = vm.special.map_map;
        let mut hs = vm.new_handleset();

        let a: super::Handle<'_, object::Map> = hs.pin(Tagged::from(map_map));
        let b = a;
        assert_eq!(a.value(), b.value());

        let object_type = a.header.object_type();
        assert_eq!(object_type, ObjectType::Map);
    }

    #[test]
    fn handles_are_updated_when_roots_are_rewritten_on_child_handleset() {
        let mut vm = special::bootstrap(HeapSettings::default());
        let layout = Layout::from_size_align(64, 8).expect("valid layout");

        let vm_ptr: *mut crate::VMProxy = &mut vm;
        let old_ptr = unsafe { (*vm_ptr).heap_proxy.allocate(layout, &mut *vm_ptr) };
        unsafe {
            old_ptr.as_ptr().write_bytes(0, layout.size());
            *(old_ptr.as_ptr() as *mut Header) = Header::new(ObjectType::Array);
        }

        let new_ptr = unsafe { (*vm_ptr).heap_proxy.allocate(layout, &mut *vm_ptr) };
        unsafe {
            new_ptr.as_ptr().write_bytes(0, layout.size());
            *(new_ptr.as_ptr() as *mut Header) = Header::new(ObjectType::Array);
        }

        let old_value = Value::from_ptr(old_ptr.as_ptr());
        let new_value = Value::from_ptr(new_ptr.as_ptr());

        let mut hs1 = vm.new_handleset();
        let mut hs2 = hs1.child();

        let h2: super::Handle<'_, Header> = hs2.pin_value(old_value);
        let old_addr_2 = h2.value().ref_bits();

        vm.visit_roots(&mut |root| {
            if *root == old_value {
                *root = new_value;
            }
        });

        let new_addr_2 = h2.value().ref_bits();
        assert_ne!(old_addr_2, new_addr_2, "inner handle slot should be updated");
        assert_eq!(h2.object_type(), ObjectType::Array);
    }

    #[test]
    fn handleset_overflow_slots_are_visited_and_rewritten() {
        let mut vm = special::bootstrap(HeapSettings::default());
        let layout = Layout::from_size_align(64, 8).expect("valid layout");

        let vm_ptr: *mut crate::VMProxy = &mut vm;
        let old_ptr = unsafe { (*vm_ptr).heap_proxy.allocate(layout, &mut *vm_ptr) };
        unsafe {
            old_ptr.as_ptr().write_bytes(0, layout.size());
            *(old_ptr.as_ptr() as *mut Header) = Header::new(ObjectType::Array);
        }

        let new_ptr = unsafe { (*vm_ptr).heap_proxy.allocate(layout, &mut *vm_ptr) };
        unsafe {
            new_ptr.as_ptr().write_bytes(0, layout.size());
            *(new_ptr.as_ptr() as *mut Header) = Header::new(ObjectType::Array);
        }

        let old_value = Value::from_ptr(old_ptr.as_ptr());
        let new_value = Value::from_ptr(new_ptr.as_ptr());

        let mut hs = vm.new_handleset();
        for i in 0..super::HANDLESET_CAPACITY {
            let _ = hs.pin_value::<Header>(Value::from_i64(i as i64));
        }

        let h_overflow: super::Handle<'_, Header> = hs.pin_value(old_value);
        let old_addr = h_overflow.value().ref_bits();

        vm.visit_roots(&mut |root| {
            if *root == old_value {
                *root = new_value;
            }
        });

        let new_addr = h_overflow.value().ref_bits();
        assert_ne!(old_addr, new_addr, "overflow handle slot should be updated");
        assert_eq!(h_overflow.object_type(), ObjectType::Array);
    }
}
