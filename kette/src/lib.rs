mod bytecode;
mod compiler;

mod allocator;
mod format;
mod interning;
mod interpreter;
mod lookup;
mod objects;
mod parker;
mod primitives;

mod barrier;
mod heap;
mod stack;
mod system;
mod tagged;
mod visitor;
mod vm;

pub use allocator::Allocator;
pub use barrier::SenseBarrier;
pub use bytecode::{BytecodeWriter, Code, OpCode};
pub use heap::{Heap, HeapProxy, HeapSettings};

pub use objects::activation::{
    Activation, ActivationObject, ActivationStack, ActivationType,
};
pub use objects::alien::Alien;
pub use objects::arrays::Array;
pub use objects::bignum::BigNum;
pub use objects::bytearrays::ByteArray;
pub use objects::feedback::FeedbackEntry;
pub use objects::floats::Float;
pub use objects::message::Message;
pub use objects::parser::{ParsedToken, Parser, Token};
pub use objects::quotations::Quotation;
pub use objects::slots::{
    Map, SlotDescriptor, SlotHelper, SlotObject, SlotTags,
};
pub use objects::threads::{
    NativeThread, ThreadInfo, ThreadObject, ThreadProxy, ThreadShared,
    ThreadState, VMThread,
};
pub use objects::{
    FLAG_REMEMBERED, Header, HeapObject, HeapValue, Object, ObjectKind,
    ObjectType, PtrSizedObject,
};

pub use primitives::Vector;

pub use compiler::BytecodeCompiler;
pub use interning::Strings;
pub use interpreter::{
    ExecutionResult, Interpreter, NumberError, execute_source_with_receiver,
};
pub use lookup::{LookupResult, ParentLookup, Selector, VisitedLink};
pub use parker::NativeParker;
pub use primitives::{
    PrimitiveContext, PrimitiveMessage, PrimitiveMessageIndex, get_primitive,
    primitive_index,
};

pub use stack::{ExecutionState, ExecutionStateInfo};
pub use system::{OS_PAGE_SIZE, PAGE_SIZE, map_memory, unmap_memory};
pub use tagged::{Handle, OBECT_TAG_MASK, Tagged, Value, ValueTag, transmute};

pub use visitor::{Visitable, Visitor};
pub use vm::{VM, VMCreateInfo, VMProxy, VMShared};
