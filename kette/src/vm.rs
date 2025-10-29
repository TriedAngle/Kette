use crate::{GenericObject, Scheduler, TaggedPtr};

pub struct SpecialObjects {
    pub true_object: TaggedPtr<GenericObject>,
    pub false_object: TaggedPtr<GenericObject>,
}

pub struct Specials {
    pub specials: SpecialObjects,
}

pub struct VM {
    scheduler: Scheduler,
}
