use std::{cell::RefCell, rc::Rc, sync::Arc};

use crate::{Actor, Fiber, VM};

pub struct Interpreter {
    vm: Arc<VM>,
    actor: Arc<Actor>,
    fiber: Rc<RefCell<Fiber>>,
}

pub struct PrimitiveContext {
    vm: Arc<VM>,
    actor: Arc<Actor>,
    fiber: Rc<RefCell<Fiber>>,
}
