mod bytecode;
mod compiler;

mod heap;
mod interning;
mod interpreter;
mod lookup;
mod objects;
mod parker;
mod primitives;

mod stack;
mod stack_effect;
mod system;
mod tagged;
mod visitor;
mod vm;

pub use objects::activation::{
    Activation, ActivationObject, ActivationStack, ActivationType,
};
pub use objects::arrays::Array;
pub use objects::bytearrays::ByteArray;
pub use objects::executable::{ExecutableMap, Method, MethodMap};
pub use objects::message::Message;
pub use objects::parser::{ParsedToken, Parser, Token};
pub use objects::quotations::{Quotation, QuotationMap};
pub use objects::slots::{
    SlotDescriptor, SlotHelper, SlotMap, SlotObject, SlotTags,
};
pub use objects::threads::{
    NativeThread, ThreadInfo, ThreadObject, ThreadProxy, ThreadShared,
    ThreadState, VMThread,
};
pub use objects::{
    HEADER_FREE, Header, HeaderFlags, HeapObject, HeapValue, Map, MapType,
    Object, ObjectKind, ObjectType, PtrSizedObject,
};

pub use bytecode::{Block, Instruction};
pub use compiler::BytecodeCompiler;
pub use heap::{Heap, HeapCreateInfo, HeapProxy, HeapSettings};
pub use interning::Strings;
pub use interpreter::{ExecutionResult, IntegerError, Interpreter};
pub use lookup::{LookupResult, Selector, VisitedLink};
pub use parker::NativeParker;
pub use primitives::{
    PrimitiveContext, PrimitiveMessage, PrimitiveMessageIndex, get_primitive,
    primitive_index,
};

pub use stack::{ExecutionState, ExecutionStateInfo};
pub use stack_effect::StackEffect;
pub use system::{PAGE_SIZE, map_memory, unmap_memory};
pub use tagged::{Handle, OBECT_TAG_MASK, Tagged, Value, ValueTag, transmute};

pub use visitor::{Visitable, Visitor};
pub use vm::{VM, VMCreateInfo, VMProxy, VMShared};
