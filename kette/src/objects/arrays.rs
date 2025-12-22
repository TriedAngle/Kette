use std::{alloc::Layout, mem, ptr};

use crate::{
    Header, HeaderFlags, HeapObject, LookupResult, Object, ObjectType,
    Selector, Tagged, Value, Visitable, VisitedLink, Visitor,
};

// TODO: find a way to implement specific functions for arrays of some specific n
// we could introduce <size> as part of the the map.
// the question is, would that be good for the game? I am not sure yet
// keep it dynamically sized, and then figure out a nice way to have both dynamic and sized arrays.
// #[repr(C)]
// #[derive(Debug)]
// pub struct ArrayMap {
//     pub map: Map,
// }

#[repr(C)]
#[derive(Debug)]
pub struct Array {
    pub header: Header,
    pub size: Tagged<usize>,
    pub fields: [Value; 0],
}

impl Array {
    /// initialize array with data
    pub fn init_with_data(&mut self, data: &[Value]) {
        // SAFETY: safe if contract ok
        unsafe { self.init(data.len()) };
        // SAFETY: safe if contract ok
        unsafe {
            ptr::copy_nonoverlapping(
                data.as_ptr(),
                self.fields.as_mut_ptr(),
                data.len(),
            )
        };
    }
    /// Initialize a slot object
    /// # Safety
    /// must get initialized and allocated with correct size
    pub unsafe fn init(&mut self, size: usize) {
        self.header = Header::encode_object(
            ObjectType::Array,
            0,
            HeaderFlags::empty(),
            0,
        );
        self.size = size.into();
    }

    #[inline]
    fn fields_ptr(&self) -> *const Value {
        self.fields.as_ptr()
    }

    #[inline]
    fn fields_mut_ptr(&mut self) -> *mut Value {
        self.fields.as_mut_ptr()
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.size.into()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }

    #[inline]
    pub fn fields(&self) -> &[Value] {
        let len = self.size();
        // SAFETY: safe
        unsafe { std::slice::from_raw_parts(self.fields_ptr(), len) }
    }

    #[inline]
    pub fn fields_mut(&mut self) -> &mut [Value] {
        let len = self.size();
        // SAFETY: safe
        unsafe { std::slice::from_raw_parts_mut(self.fields_mut_ptr(), len) }
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<Value> {
        if index < self.size() {
            // SAFETY: checked
            Some(unsafe { self.fields_ptr().add(index).read() })
        } else {
            None
        }
    }

    #[inline]
    pub fn set(&mut self, index: usize, value: Value) -> bool {
        if index < self.size() {
            // SAFETY: checked
            unsafe { self.fields_mut_ptr().add(index).write(value) };
            true
        } else {
            false
        }
    }

    /// # Safety
    /// Caller must ensure `index < len()`.
    #[inline]
    pub unsafe fn get_unchecked(&self, index: usize) -> Value {
        // SAFETY: safe if contract holds
        unsafe { self.fields_ptr().add(index).read() }
    }

    /// # Safety
    /// Caller must ensure `index < len()`.
    #[inline]
    pub unsafe fn set_unchecked(&mut self, index: usize, value: Value) {
        // SAFETY: safe if contract holds
        unsafe { self.fields_mut_ptr().add(index).write(value) };
    }

    /// calculate the layout of an array with n fields
    pub fn required_layout(size: usize) -> Layout {
        let head = Layout::new::<Array>();
        let slots_layout =
            Layout::array::<Value>(size).expect("create valid layout");
        let (layout, _) =
            head.extend(slots_layout).expect("create valid layout");
        layout
    }
}

impl Object for Array {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.array_traits;
        traits.lookup(selector, link)
    }
}

impl HeapObject for Array {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>() + self.size() * mem::size_of::<Value>()
    }
}
impl Visitable for Array {
    #[inline]
    fn visit_edges_mut(&mut self, visitor: &mut impl Visitor) {
        self.fields().iter().for_each(|&obj| visitor.visit_mut(obj));
    }

    #[inline]
    fn visit_edges(&self, visitor: &impl Visitor) {
        self.fields().iter().for_each(|&obj| visitor.visit(obj));
    }
}

// impl Object for ArrayMap {}
// impl HeapObject for ArrayMap {}
//
// impl Visitable for ArrayMap {}
