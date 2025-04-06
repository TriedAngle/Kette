mod code;
mod context;
mod gc;
mod linked_list;
mod object;
mod primitives;
mod region;

pub use context::*;
pub use gc::*;
pub use linked_list::*;
pub use object::*;
pub use region::*;

pub type StackFn = fn(&mut Context);
