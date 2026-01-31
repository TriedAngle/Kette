//! Debug binary for benchmark issues
//!
//! CURRENTLY BROKEN: Hits OOM after ~200-300 iterations because major GC
//! is not yet implemented. The GC cannot reclaim old objects, so memory
//! fills up with each parse/compile cycle.
//!
//! Run in debug mode to catch precondition violations:
//!   cargo run --bin bench_test
//!
//! Run in release mode (like criterion):
//!   cargo run --bin bench_test --release

use std::io;

use kette::{
    Allocator, Array, BytecodeCompiler, BytecodeWriter, ExecutionResult,
    ExecutionState, ExecutionStateInfo, Handle, HeapSettings, Interpreter,
    ThreadProxy, VM, VMCreateInfo, VMThread,
};

fn execute_source(
    interpreter: &mut Interpreter,
    source: &str,
) -> Result<(), String> {
    // Allocate parser on the GC heap (not Rust heap via Box)
    let parser = interpreter
        .heap
        .allocate_parser(&interpreter.vm.shared.strings, source.as_bytes());

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

/// Run a benchmark pattern multiple times, similar to criterion
fn run_benchmark(
    interpreter: &mut Interpreter,
    name: &str,
    warmup_code: &str,
    bench_code: &str,
    iterations: usize,
) {
    eprintln!("\n=== Benchmark: {} ===", name);

    // Check state before warmup
    eprintln!(
        "  Before warmup - Stack: {}, Return: {}",
        interpreter.state.depth(),
        interpreter.state.return_depth()
    );

    // Warmup phase
    eprintln!("  Warming up...");
    if let Err(e) = execute_source(interpreter, warmup_code) {
        eprintln!("  WARMUP FAILED: {}", e);
        eprintln!("  Stack depth: {}", interpreter.state.depth());
        eprintln!("  Return stack depth: {}", interpreter.state.return_depth());
        std::process::exit(1);
    }

    // Check state after warmup
    eprintln!(
        "  After warmup - Stack: {}, Return: {}",
        interpreter.state.depth(),
        interpreter.state.return_depth()
    );

    // Benchmark iterations
    eprintln!("  Running {} iterations...", iterations);
    for i in 0..iterations {
        if i % 100 == 0 {
            eprintln!(
                "    Iteration {}/{} - Stack: {}, Return: {}",
                i,
                iterations,
                interpreter.state.depth(),
                interpreter.state.return_depth()
            );
        }

        if let Err(e) = execute_source(interpreter, bench_code) {
            eprintln!("  FAILED at iteration {}: {}", i, e);
            eprintln!("  Stack depth: {}", interpreter.state.depth());
            eprintln!(
                "  Return stack depth: {}",
                interpreter.state.return_depth()
            );
            std::process::exit(1);
        }
    }

    eprintln!(
        "  Final state - Stack: {}, Return: {}",
        interpreter.state.depth(),
        interpreter.state.return_depth()
    );
    eprintln!("  {} completed successfully!", name);
}

fn main() {
    let vm = VM::new(VMCreateInfo {
        image: None,
        heap: HeapSettings::default(),
    });

    let main_proxy = vm.proxy();
    let mut heap = main_proxy.shared.heap.proxy();

    // Add SpecialObjects as permanent GC roots
    heap.add_permanent_roots(main_proxy.specials().as_roots());

    // Use larger stack sizes to match criterion benchmark
    let state = ExecutionState::new(&ExecutionStateInfo {
        stack_size: 8192,
        return_stack_size: 8192,
    });

    let main_thread = VMThread::new_main();
    let thread_proxy = ThreadProxy(main_thread.inner);
    let proxy = vm.proxy();

    let mut interpreter = Interpreter::new(proxy, thread_proxy, heap, state);
    interpreter.init_gc_roots();
    interpreter.set_output(Box::new(io::sink()));

    // Load core library
    eprintln!("Loading core library...");
    let core_content = include_str!("../../../core/init.ktt");
    execute_source(&mut interpreter, core_content)
        .expect("Failed to load core");
    eprintln!("Core loaded successfully!");

    // ========================================
    // Benchmark 1: Recursive countdown
    // ========================================
    let countdown_warmup = r#"
(| 
    countdown = (| n -- |
        dup 0 > [
            1 - self countdown
        ] [ drop ] if )
|) 
dup 100 swap countdown
drop
"#;

    let countdown_bench = r#"
(| 
    countdown = (| n -- |
        dup 0 > [
            1 - self countdown
        ] [ drop ] if )
|) 
dup 500 swap countdown
drop
"#;

    run_benchmark(
        &mut interpreter,
        "recursive_countdown_500",
        countdown_warmup,
        countdown_bench,
        500, // Moderate count to avoid OOM while still testing
    );

    // ========================================
    // Benchmark 2: Counter increment loop
    // ========================================
    let counter_warmup = r#"
(| 
    counter := 0 .
    increment = (| -- | self counter 1 + self counter<< ) .
    runLoop = (| count -- |
        dup 0 > [
            self increment
            1 - self runLoop
        ] [ drop ] if )
|) 
dup 100 swap runLoop
drop
"#;

    let counter_bench = r#"
(| 
    counter := 0 .
    increment = (| -- | self counter 1 + self counter<< ) .
    runLoop = (| count -- |
        dup 0 > [
            self increment
            1 - self runLoop
        ] [ drop ] if )
|) 
dup 500 swap runLoop
drop
"#;

    run_benchmark(
        &mut interpreter,
        "counter_increment_500",
        counter_warmup,
        counter_bench,
        100,
    );

    // ========================================
    // Benchmark 3: Fibonacci
    // ========================================
    let fib_warmup = r#"
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
dup 10 swap fib
drop
"#;

    let fib_bench = r#"
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

    run_benchmark(
        &mut interpreter,
        "fibonacci_12",
        fib_warmup,
        fib_bench,
        20, // Reduced iterations due to high memory usage
    );

    eprintln!("\n=== All benchmarks completed successfully! ===");
}
