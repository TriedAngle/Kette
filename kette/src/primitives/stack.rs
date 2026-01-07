use super::{inputs, outputs};
use crate::{ExecutionResult, PrimitiveContext, Value};
macro_rules! shuffle {
    (
        $(
            $(#[$doc:meta])* $name:ident : $($in:ident)* -- $($out:ident)*
        );* $(;)?
    ) => {
        $(
            $(#[$doc])*
            pub fn $name(ctx: &mut PrimitiveContext) -> ExecutionResult {
                #[allow(unused)]
                let [$($in),*] = inputs(ctx);
                outputs(ctx, [$($out),*]);

                ExecutionResult::Normal
            }
        )*
    };
}

pub fn depth(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let depth = ctx.state.depth();
    // SAFETY: this is safe
    ctx.outputs[0] = unsafe { Value::from_usize(depth).as_handle_unchecked() };
    ExecutionResult::Normal
}

shuffle! {
    dup: x -- x x ;

    dup2: x y -- x y x y ;

    drop: x -- ;

    drop2: x y -- ;

    drop3: x y z -- ;

    swap: x y -- y x ;

    over: x y -- x y x ;

    pick: x y z -- x y z x ;

    /// rotates top three elements backwards
    rot: x y z -- y z x ;

    /// rotates top three elements forwards
    neg_rot: x y z -- z x y ;

    spin: x y z -- z y x;

    dupd: x y -- x x y ;

    dropd: x y -- y ;

    dropd2: x y z -- z ;

    swapd: x y z -- y x z ;

}
