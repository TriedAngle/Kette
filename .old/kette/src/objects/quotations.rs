use std::{alloc::Layout, mem};

use crate::{
    ActivationObject, Handle, Header, HeapObject, LookupResult, Map, Object,
    ObjectKind, ObjectType, Selector, Value, Visitable, VisitedLink,
};

#[repr(C)]
#[derive(Debug)]
pub struct Quotation {
    pub header: Header,
    pub map: Handle<Map>,
    pub parent: Handle<ActivationObject>,
    /// Captured values for lambdas with named parameters (`[| a . b | ... ]`).
    /// Empty (zero-length) for regular quotations.
    pub slots: [Value; 0],
}

impl Quotation {
    /// # Safety
    /// must be allocated with correct size
    pub fn init(&mut self, map: Handle<Map>, parent: Handle<ActivationObject>) {
        self.header = Header::new_object(ObjectType::Quotation);
        self.map = map;
        self.parent = parent;
    }

    /// Initialize a quotation with captured values (for lambdas).
    /// # Safety
    /// Must be allocated with `required_layout(captures.len())`.
    pub fn init_with_captures(
        &mut self,
        map: Handle<Map>,
        parent: Handle<ActivationObject>,
        captures: &[Value],
    ) {
        self.header = Header::new_object(ObjectType::Quotation);
        self.map = map;
        self.parent = parent;

        let ptr = self.slots.as_mut_ptr();
        // SAFETY: allocation was sized for captures.len() values
        unsafe {
            std::ptr::copy_nonoverlapping(
                captures.as_ptr(),
                ptr,
                captures.len(),
            );
        };
    }

    /// Returns the number of captured values.
    #[inline]
    #[must_use]
    pub fn capture_count(&self) -> usize {
        self.map.input_count()
    }

    /// Returns a slice of the captured values.
    #[inline]
    #[must_use]
    pub fn captured_slots(&self) -> &[Value] {
        let count = self.capture_count();
        // SAFETY: pointer and length must be valid by construction
        unsafe { std::slice::from_raw_parts(self.slots.as_ptr(), count) }
    }

    /// Calculate the layout of a Quotation with `captures` captured values.
    #[must_use]
    pub fn required_layout(captures: usize) -> Layout {
        let head = Layout::new::<Self>();
        let slots_layout =
            Layout::array::<Value>(captures).expect("create valid layout");
        let (layout, _) =
            head.extend(slots_layout).expect("create valid layout");
        layout
    }
}

impl Object for Quotation {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.quotation_traits;
        traits.lookup(selector, link)
    }
}

impl HeapObject for Quotation {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Quotation as u8;
    fn heap_size(&self) -> usize {
        let count = self.capture_count();
        mem::size_of::<Self>() + count * mem::size_of::<Value>()
    }
}

impl Visitable for Quotation {
    fn visit_edges(&self, visitor: &impl crate::Visitor) {
        visitor.visit(self.map.as_value_ref());
        if !self.parent.as_ptr().is_null() {
            visitor.visit(self.parent.as_value_ref());
        }
        // Visit captured values
        for slot in self.captured_slots() {
            visitor.visit(slot);
        }
    }

    fn visit_edges_mut(&mut self, visitor: &mut impl crate::Visitor) {
        visitor.visit_mut(self.map.as_value_mut());
        if !self.parent.as_ptr().is_null() {
            visitor.visit_mut(self.parent.as_value_mut());
        }
        // Visit captured values
        let count = self.capture_count();
        let ptr = self.slots.as_mut_ptr();
        for i in 0..count {
            // SAFETY: count is valid by construction
            unsafe { visitor.visit_mut(&mut *ptr.add(i)) };
        }
    }
}
