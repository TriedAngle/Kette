use crate::{ExecutionResult, PrimitiveContext};

/// x -- x x
pub fn dup(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 1 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let x = unsafe { s.stack_get_nth_unchecked(0) };
    s.push(x);

    ExecutionResult::Normal
}

/// x --
pub fn drop(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 1 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let _x = unsafe { s.pop_unchecked() };

    ExecutionResult::Normal
}

/// x y --
pub fn drop2(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 2 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let _x = unsafe { s.pop_unchecked() };
    let _y = unsafe { s.pop_unchecked() };

    ExecutionResult::Normal
}

/// x y z --
pub fn drop3(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 3 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let _z = unsafe { s.pop_unchecked() };
    let _y = unsafe { s.pop_unchecked() };
    let _x = unsafe { s.pop_unchecked() };

    ExecutionResult::Normal
}

/// x y -- y x
pub fn swap(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 2 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let y = unsafe { s.pop_unchecked() };
    let x = unsafe { s.pop_unchecked() };
    s.push(y);
    s.push(x);
    ExecutionResult::Normal
}

/// a b -- a b a
pub fn over(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 2 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let x = unsafe { s.stack_get_nth_unchecked(1) };
    s.push(x);

    ExecutionResult::Normal
}

/// x y z -- y z x
pub fn rot(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 3 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let x = unsafe { s.stack_get_nth_unchecked(2) };
    let y = unsafe { s.stack_get_nth_unchecked(1) };
    let z = unsafe { s.stack_get_nth_unchecked(0) };
    unsafe { s.stack_set_nth_unchecked(2, y) };
    unsafe { s.stack_set_nth_unchecked(1, z) };
    unsafe { s.stack_set_nth_unchecked(0, x) };

    ExecutionResult::Normal
}

/// x y z -- z x y
pub fn neg_rot(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 3 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let x = unsafe { s.stack_get_nth_unchecked(2) };
    let y = unsafe { s.stack_get_nth_unchecked(1) };
    let z = unsafe { s.stack_get_nth_unchecked(0) };
    unsafe { s.stack_set_nth_unchecked(2, z) };
    unsafe { s.stack_set_nth_unchecked(1, x) };
    unsafe { s.stack_set_nth_unchecked(0, y) };

    ExecutionResult::Normal
}

/// x y z -- z y x
pub fn spin(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 3 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let x = unsafe { s.stack_get_nth_unchecked(2) };
    let z = unsafe { s.stack_get_nth_unchecked(0) };
    unsafe { s.stack_set_nth_unchecked(2, z) };
    unsafe { s.stack_set_nth_unchecked(0, x) };

    ExecutionResult::Normal
}

/// x y -- x x y
pub fn dupd(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 2 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let y = unsafe { s.pop_unchecked() };
    let x = unsafe { s.stack_get_nth_unchecked(0) };

    s.push(x);
    s.push(y);

    ExecutionResult::Normal
}

/// x y -- y
pub fn dropd(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 2 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let y = unsafe { s.pop_unchecked() };
    let _x = unsafe { s.pop_unchecked() };

    s.push(y);

    ExecutionResult::Normal
}

/// x y z -- z
pub fn dropd2(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 3 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let z = unsafe { s.pop_unchecked() };
    let _y = unsafe { s.pop_unchecked() };
    let _x = unsafe { s.pop_unchecked() };

    s.push(z);

    ExecutionResult::Normal
}

/// x y z -- y x z
pub fn swapd(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 3 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // Safety: depth check
    let y = unsafe { s.stack_get_nth_unchecked(1) };
    let x = unsafe { s.stack_get_nth_unchecked(2) };
    unsafe { s.stack_set_nth_unchecked(1, x) };
    unsafe { s.stack_set_nth_unchecked(2, y) };
    ExecutionResult::Normal
}

/// removes x, calls q, puts x again
/// x q -- x
pub fn dip(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let s = &mut ctx.state;

    if s.depth() < 2 {
        return ExecutionResult::Panic("Datastack underflow");
    }

    // TODO: do executable map check and execute.
    // TODO: add callstack once added
    // Safety: depth check
    let _q = unsafe { s.pop_unchecked() };
    unsafe { s.stack_to_return_unchecked() };
    println!("CALL NOT IMPLEMENTED");
    unsafe { s.return_to_stack_unchecked() };
    ExecutionResult::Normal
}
