use crate::{
    Header, HeaderFlags, HeapObject, LookupResult, Object, ObjectType,
    Selector, Visitable, VisitedLink,
};

#[derive(Debug)]
pub struct Float {
    pub header: Header,
    pub value: f64,
}

impl Float {
    /// # Safety
    /// internal function
    /// must be allocated with correct size and alignment
    pub unsafe fn init(&mut self, value: f64) {
        self.header = Header::encode_object(
            ObjectType::Float,
            0,
            HeaderFlags::empty(),
            0,
        );
        self.value = value;
    }
}

impl Visitable for Float {}
impl Object for Float {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.float_traits;
        traits.lookup(selector, link)
    }
}
impl HeapObject for Float {}
