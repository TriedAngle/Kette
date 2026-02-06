use std::mem;

use crate::{
    Header, HeapObject, LookupResult, Object, ObjectKind, ObjectType, Selector,
    Tagged, Visitable, VisitedLink,
};

#[derive(Debug)]
pub struct Alien {
    pub header: Header,
    pub ptr: Tagged<usize>,
    pub library: Tagged<usize>,
}

impl Alien {
    pub fn init(&mut self, ptr: Tagged<usize>, library: Tagged<usize>) {
        self.header = Header::new_object(ObjectType::Alien);
        self.ptr = ptr;
        self.library = library;
    }
}

impl Visitable for Alien {
    #[inline]
    fn visit_edges(&self, _visitor: &impl crate::Visitor) {}

    #[inline]
    fn visit_edges_mut(&mut self, _visitor: &mut impl crate::Visitor) {}
}

impl Object for Alien {
    fn lookup(
        &self,
        selector: Selector,
        link: Option<&VisitedLink>,
    ) -> LookupResult {
        let traits = selector.vm.specials.alien_traits;
        traits.lookup(selector, link)
    }
}

impl HeapObject for Alien {
    const KIND: ObjectKind = ObjectKind::Object;
    const TYPE_BITS: u8 = ObjectType::Alien as u8;

    fn heap_size(&self) -> usize {
        mem::size_of::<Self>()
    }
}
