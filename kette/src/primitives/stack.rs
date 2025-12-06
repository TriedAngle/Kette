use crate::{ExecutionResult, Handle, PrimitiveContext, Value};

/// TODO: change this all into input + output format

fn inputs<const N: usize>(ctx: &mut PrimitiveContext) -> [Handle<Value>; N] {
    // SAFETY: this requires a bounds check befor, but I am the boundcer
    unsafe { *(ctx.inputs.as_ptr() as *const [Handle<Value>; N]) }
}

fn outputs<const N: usize>(ctx: &mut PrimitiveContext, values: [Handle<Value>; N]) {
    // SAFETY: this requires a bounds check before, but I am the boundcer
    unsafe {
        std::ptr::copy_nonoverlapping(values.as_ptr(), ctx.outputs.as_mut_ptr(), N);
    }
}

macro_rules! shuffle {
    (
        $(
            $(#[$doc:meta])* $name:ident : $($in:ident)* -- $($out:ident)*
        );* $(;)?
    ) => {
        $(
            $(#[$doc])*
            pub fn $name(ctx: &mut PrimitiveContext) -> ExecutionResult {
                const N: usize = [$(stringify!($in)),*].len();

                #[allow(unused)]
                let [$($in),*] = inputs::<N>(ctx);
                outputs(ctx, [$($out),*]);

                ExecutionResult::Normal
            }
        )*
    };
}

shuffle! { 
    dup: x -- x x ;

    drop: x -- ;

    drop2: x y -- ;

    drop3: x y z -- ;

    swap: x y -- y x ;

    over: x y -- x y x ;

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


/// removes x, calls q, puts x again
/// x q -- x
pub fn dip(ctx: &mut PrimitiveContext) -> ExecutionResult {
    let [x, q] = inputs(ctx);


    // TODO: do executable map check and execute.
    // TODO: add callstack once added
    ctx.state.push_return(x.into());
    println!("TRYING TO CALL {q:?}, BUT CALL NOT IMPLEMENTED");
    let _ = ctx.state.pop_return();
    ExecutionResult::Normal
}
