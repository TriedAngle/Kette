use crate::{ByteArray, ExecutionResult, PrimitiveContext, TaggedI64, TaggedPtr, View};

pub fn fixnum_to_utf8_bytes(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let _value = TaggedI64::from(ctx.message_receiver);
    unimplemented!("TODO: allocate bytearray, maybe also cache this");
}

pub fn bytearray_print(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let tagged: TaggedPtr<ByteArray> = TaggedPtr::from(ctx.receiver);
    let view = View::from_tagged_ptr(tagged);
    let data = view.as_bytes();
    let value = str::from_utf8(data).expect("valid utf8 encoding");
    print!("{}", value);
    ExecutionResult::Normal
}

pub fn bytearray_println(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let tagged: TaggedPtr<ByteArray> = TaggedPtr::from(ctx.receiver);
    let view = View::from_tagged_ptr(tagged);
    let data = view.as_bytes();
    let value = str::from_utf8(data).expect("valid utf8 encoding");
    println!("{}", value);
    ExecutionResult::Normal
}
