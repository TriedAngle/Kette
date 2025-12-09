use core::str;
use std::{mem, ptr};

use crate::{
    Header, HeaderFlags, HeapObject, LookupResult, Object, ObjectType,
    Selector, Tagged, Visitable, VisitedLink, Visitor,
};

#[repr(C)]
#[derive(Debug)]
pub struct ByteArray {
    pub header: Header,
    pub size: Tagged<usize>,
    pub data: [u8; 0],
}

impl ByteArray {
    /// Inititalize ByteArray with correct header and size
    /// # Safety
    /// this sets metadata, should only be called internally
    /// memory allocation must be at least size
    pub unsafe fn init(&mut self, size: usize) {
        self.header = Header::encode_object(
            ObjectType::ByteArray,
            0,
            HeaderFlags::empty(),
            0,
        );
        self.size = size.into();
    }

    /// Inititalize ByteArray with correct header, size and zeroed memory
    /// # Safety
    /// this sets metadata, should only be called internally
    /// memory allocation must be at least size
    pub unsafe fn init_zeroed(&mut self, size: usize) {
        // Safety: same contract as above
        unsafe { self.init(size) };
        let data = self.data.as_mut_ptr();
        // Safety: allocated with correct size
        unsafe { ptr::write_bytes(data, 0, size) };
    }

    /// Inititalize ByteArray with correct header, size and data
    /// # Safety
    /// this sets metadata, should only be called internally
    /// data must be same size as allocated
    pub unsafe fn init_data(&mut self, data: &[u8]) {
        let size = data.len();
        // Safety: same contract as above
        unsafe { self.init(size) };
        let own_data = self.data.as_mut_ptr();
        // Safety: allocated with correct size
        unsafe { ptr::copy_nonoverlapping(data.as_ptr(), own_data, size) };
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.size.into()
    }

    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        let len = self.size();
        // SAFETY: byterray must be correctly sized
        unsafe { std::slice::from_raw_parts(self.data.as_ptr(), len) }
    }

    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        let len = self.size();
        // SAFETY: byterray must be correctly sized
        unsafe { std::slice::from_raw_parts_mut(self.data.as_mut_ptr(), len) }
    }

    /// convert bytearray to utf8
    pub fn as_utf8(&self) -> Result<&str, str::Utf8Error> {
        str::from_utf8(self.as_bytes())
    }
}

impl Object for ByteArray {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.bytearray_traits;
        traits.lookup(selector, link)
    }
}
impl HeapObject for ByteArray {
    fn heap_size(&self) -> usize {
        mem::size_of::<Self>() + self.size()
    }
}

// nohting to visit in bytearray
impl Visitable for ByteArray {
    #[inline]
    fn visit_edges_mut(&mut self, _visitor: &mut impl Visitor) {}
    #[inline]
    fn visit_edges(&self, _visitor: &impl Visitor) {}
}
