//! Run with inline-cache (default):
//!   cargo bench --bench vm_benchmark
//!
//! Run without inline-cache:
//!   cargo bench --bench vm_benchmark --no-default-features

use std::io;

use criterion::{Criterion, black_box, criterion_group, criterion_main};
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

/// Creates a fresh interpreter WITHOUT loading core library.
/// The caller MUST call `init_gc_roots()` and then load the core library.
fn create_interpreter() -> Interpreter {
    // Use a larger heap for benchmarks to avoid OOM during criterion's many iterations
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
    // NOTE: We don't call init_gc_roots() here because the interpreter will be
    // moved when returned, invalidating the pointers. The caller must call
    // init_gc_roots() after the interpreter is in its final location.
    interpreter.set_output(Box::new(io::sink()));

    interpreter
}

/// Initialize interpreter after it's in its final location.
/// This sets up GC roots and loads the core library.
fn init_interpreter(interpreter: &mut Interpreter) {
    interpreter.init_gc_roots();
    let core_content = include_str!("../../core/init.ktt");
    execute_source(interpreter, core_content).expect("Failed to load core");
}

/// Benchmark 1: Recursive countdown loop
/// Tests method dispatch and recursion performance.
fn bench_recursive_countdown(c: &mut Criterion) {
    let mut interpreter = create_interpreter();
    init_interpreter(&mut interpreter);

    let bench_code = r#"
(| 
    countdown = (| n -- |
        dup 0 > [
            1 - self countdown
        ] [ drop ] if )
|) 
dup 100 swap countdown
drop
"#;

    // Warm up - run a few times to populate IC
    for _ in 0..5 {
        execute_source(&mut interpreter, bench_code).expect("Warmup failed");
    }

    c.bench_function("recursive_countdown_100", |b| {
        b.iter(|| {
            execute_source(&mut interpreter, black_box(bench_code))
                .expect("Benchmark failed");
        });
    });
}

/// Benchmark 2: Object with counter and increment method
/// Tests slot access and mutation performance.
fn bench_counter_increment(c: &mut Criterion) {
    let mut interpreter = create_interpreter();
    init_interpreter(&mut interpreter);

    let bench_code = r#"
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

    // Warm up - run a few times to populate IC
    for _ in 0..5 {
        execute_source(&mut interpreter, bench_code).expect("Warmup failed");
    }

    c.bench_function("counter_increment_100", |b| {
        b.iter(|| {
            execute_source(&mut interpreter, black_box(bench_code))
                .expect("Benchmark failed");
        });
    });
}

/// Benchmark 3: Fibonacci (recursive, exponential complexity)
/// Tests deep recursion and multiple message sends per call.
fn bench_fibonacci(c: &mut Criterion) {
    let mut interpreter = create_interpreter();
    init_interpreter(&mut interpreter);

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

    // Warm up - run a few times to populate IC
    for _ in 0..5 {
        execute_source(&mut interpreter, bench_code).expect("Warmup failed");
    }

    c.bench_function("fibonacci_12", |b| {
        b.iter(|| {
            execute_source(&mut interpreter, black_box(bench_code))
                .expect("Benchmark failed");
        });
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(20);
    targets = bench_recursive_countdown, bench_counter_increment, bench_fibonacci
}

criterion_main!(benches);
