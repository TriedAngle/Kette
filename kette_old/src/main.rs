use std::fs;
use std::io::{self, Write};
use std::path::Path;

use kette::ObjectRef;
use kette::{Context, ContextConfig};

fn execute_file(ctx: &mut Context, path: &Path) -> io::Result<()> {
    let content = fs::read_to_string(path)?;

    let text = unsafe {
        let bytearray = ctx.gc.allocate_string(&content);
        ObjectRef::from_bytearray_ptr(bytearray)
    };

    let quotation = ctx.compile_string(text);
    if !quotation.is_false() {
        let quot = quotation.as_quotation_ptr().unwrap();
        ctx.execute(quot);
    }

    Ok(())
}

fn main() -> io::Result<()> {
    let config = ContextConfig {
        datastack_size: 1024,
        retainstack_size: 1024,
        namestack_size: 1024,
    };

    let mut ctx = Context::new(&config);
    kette::add_primitives(&mut ctx);

    let _ = execute_file(&mut ctx, Path::new("std/bootstrap/stage0.ktt"));

    let mut input = String::new();
    loop {
        print!("> ");
        io::stdout().flush()?;

        input.clear();
        if io::stdin().read_line(&mut input)? == 0 {
            break;
        }

        if input.trim().is_empty() {
            continue;
        }

        unsafe {
            let text = {
                let bytearray = ctx.gc.allocate_string(&input);
                ObjectRef::from_bytearray_ptr(bytearray)
            };

            let quotation = ctx.compile_string(text);
            if !quotation.is_false() {
                let quot = quotation.as_quotation_ptr().unwrap();
                ctx.execute(quot);
            }
        }
    }

    Ok(())
}
