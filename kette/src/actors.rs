use std::ptr::NonNull;

use parking_lot::RwLock;

use crate::{Header, Heap, TaggedPtr, TaggedValue, WorkerId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ActorId(pub u64);

pub enum ActorState {
    Stale,
    Active,
    GcActive,
    Dead,
}

pub struct ActorInfo {
    pub pinned: Option<WorkerId>, // pin to worker (including main: WorkerId(0))
    pub dedicated: Option<WorkerId>, // a dedicated worker thread
    pub state: ActorState,
}

pub struct Actor {
    pub header: Header,
    pub id: ActorId,
    pub heap: Heap,
    pub info: RwLock<ActorInfo>,
    pub fibers: Vec<Fiber>,
}

pub struct Handler {
    pub header: Header,
    pub kind: TaggedValue,
    pub action: TaggedValue,
}

pub enum FiberState {
    Waiting,
    Running,
    Dead,
}

pub struct Fiber {
    pub header: Header,
    pub actor: NonNull<Actor>,
    pub state: FiberState,
    pub data: Vec<TaggedValue>,
    pub retain: Vec<TaggedValue>,
    pub activations: Vec<TaggedPtr<Activation>>,
    pub handlers: Vec<Handler>,
}

pub struct Message;

pub struct Activation {
    pub header: Header,
    pub parent: Option<NonNull<Activation>>,
    pub fiber: NonNull<Fiber>,
    pub receiver: TaggedValue,
    pub message: TaggedPtr<Message>,
    pub locals: Vec<TaggedValue>,
}

unsafe impl Send for Actor {}
unsafe impl Sync for Actor {}
