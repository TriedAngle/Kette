use crate::{
    Header, HeapObject, LookupResult, Object, ObjectType, Selector, Visitable,
    VisitedLink,
};

#[derive(Debug)]
pub struct Float {
    pub header: Header,
    pub value: f64,
}

impl Float {
    pub fn init(&mut self, value: f64) {
        self.header = Header::new_object(ObjectType::Float);
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
