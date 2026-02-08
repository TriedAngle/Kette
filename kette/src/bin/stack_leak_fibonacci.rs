use std::io;

use kette::{
    Allocator, Array, BytecodeCompiler, BytecodeWriter, ExecutionResult,
    ExecutionState, ExecutionStateInfo, Handle, HeapSettings, Interpreter,
    ThreadProxy, VM, VMCreateInfo, VMThread,
};

/// Helper to execute Kette source code on an interpreter (full parse + compile + run).
fn execute_source(
    interpreter: &mut Interpreter,
    source: &str,
) -> Result<(), String> {
    let parser = interpreter.heap.allocate_parser(
        &interpreter.vm.shared.strings,
        interpreter.vm.shared.specials.universe,
        source.as_bytes(),
    );

    let parse_msg = interpreter
        .vm
        .intern_string_message("parse", &mut interpreter.heap);

    let constants = vec![parser.as_value(), parse_msg.as_value()];

    let mut writer = BytecodeWriter::new();
    writer.emit_push_constant(0);
    writer.emit_send(1, 0);
    writer.emit_return();

    let dummy_body = interpreter.heap.allocate_array(&[]);

    let boot_code = interpreter.heap.allocate_code(
        &constants,
        &writer.into_inner(),
        1,
        dummy_body,
        unsafe { Handle::null() },
    );

    let boot_map = interpreter.heap.allocate_executable_map(boot_code, 0, 0);

    let boot_quotation = interpreter
        .heap
        .allocate_quotation(boot_map, unsafe { Handle::null() });

    interpreter.add_quotation(boot_quotation);

    match interpreter.execute() {
        ExecutionResult::Normal => {}
        ExecutionResult::Panic(msg) => {
            return Err(format!("Parser Panic: {}", msg));
        }
        res => return Err(format!("Parser abnormal exit: {:?}", res)),
    }

    let body_val = match interpreter.state.pop() {
        Some(v) => v,
        None => {
            return Err("Parser did not return a value (Empty Stack)".into());
        }
    };

    if body_val == interpreter.vm.shared.specials.false_object.as_value() {
        return Err("Parsing failed (Syntax Error)".into());
    }

    let body_array = unsafe { body_val.as_handle_unchecked().cast::<Array>() };

    let code = BytecodeCompiler::compile(
        &interpreter.vm.shared,
        &mut interpreter.heap,
        body_array,
    );

    let code_map = interpreter.heap.allocate_executable_map(code, 0, 0);

    let quotation = interpreter
        .heap
        .allocate_quotation(code_map, unsafe { Handle::null() });

    interpreter.add_quotation(quotation);

    match interpreter.execute() {
        ExecutionResult::Normal => Ok(()),
        ExecutionResult::Panic(msg) => Err(format!("Panic: {}", msg)),
        res => Err(format!("Abnormal exit: {:?}", res)),
    }
}

/// Creates a fresh interpreter WITHOUT loading core library.
/// The caller MUST call `init_gc_roots()` and then load the core library.
fn create_interpreter() -> Interpreter {
    let mut heap_settings = HeapSettings::default();
    heap_settings.heap_size = 2 * 1024 * 1024 * 1024; // 2 GB

    let vm = VM::new(VMCreateInfo {
        image: None,
        heap: heap_settings,
    });

    let main_proxy = vm.proxy();
    let mut heap = main_proxy.shared.heap.proxy();
    heap.add_permanent_roots(main_proxy.specials().as_roots());

    let state = ExecutionState::new(&ExecutionStateInfo {
        stack_size: 8192,
        return_stack_size: 8192,
    });

    let main_thread = VMThread::new_main();
    let thread_proxy = ThreadProxy(main_thread.inner);
    let proxy = vm.proxy();

    let mut interpreter = Interpreter::new(proxy, thread_proxy, heap, state);
    interpreter.set_output(Box::new(io::sink()));

    interpreter
}

/// Initialize interpreter after it's in its final location.
/// This sets up GC roots and loads the core library.
fn init_interpreter(interpreter: &mut Interpreter) {
    interpreter.init_gc_roots();
    let core_content = include_str!("../../../core/init.ktt");
    execute_source(interpreter, core_content).expect("Failed to load core");
}

fn main() {
    let mut interpreter = create_interpreter();
    init_interpreter(&mut interpreter);

    let iterations = std::env::var("TEST_ITERATIONS")
        .ok()
        .and_then(|val| val.parse::<usize>().ok())
        .unwrap_or(0);
    let seconds = std::env::var("TEST_SECONDS")
        .ok()
        .and_then(|val| val.parse::<u64>().ok())
        .unwrap_or(0);

    let bench_code = r#"
(| 
    fib = (| n -- result |
        dup 2 < [
            /* base case: return n */
        ] [
            dup 1 - self fib
            swap 2 - self fib
            +
        ] if )
|) 
dup 12 swap fib
drop
"#;

    let mut executed = 0usize;
    if seconds > 0 {
        let start = std::time::Instant::now();
        while start.elapsed().as_secs() < seconds {
            execute_source(&mut interpreter, bench_code)
                .expect("Fibonacci execution failed");
            executed += 1;
        }
    } else {
        let count = if iterations == 0 { 200 } else { iterations };
        for _ in 0..count {
            execute_source(&mut interpreter, bench_code)
                .expect("Fibonacci execution failed");
            executed += 1;
        }
    }

    println!("iterations: {}", executed);
    println!("stack depth: {}", interpreter.state.depth());
    println!("return depth: {}", interpreter.state.return_depth());
}
