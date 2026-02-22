use criterion::{black_box, criterion_group, criterion_main, Criterion};
use heap::HeapSettings;
use object::Code;
use parser::{Lexer, Parser};
use vm::compiler0::Compiler;
use vm::interpreter::interpret;
use vm::materialize::materialize;
use vm::special::bootstrap;
use vm::{USER_MODULE, VM};

const BENCH_CODE_WITH_IC: &str = "__bench_code_with_ic";
const BENCH_CODE_WITHOUT_IC: &str = "__bench_code_without_ic";

fn test_settings() -> HeapSettings {
    HeapSettings {
        heap_size: 1024 * 1024,
        block_size: 8192,
        large_size: 4096 - 16,
        line_size: 64,
        bytes_before_gc: 0.1,
        nursery_fraction: 0.1,
        minor_recycle_threshold: 0.5,
        max_minor_before_major: 3,
    }
}

fn parse_source(src: &str) -> Vec<parser::ast::Expr> {
    let lexer = Lexer::from_str(src);
    Parser::new(lexer)
        .map(|r| r.expect("parse error"))
        .collect()
}

fn build_code_pair(src: &str) -> VM {
    let mut vm = bootstrap(test_settings());
    vm.open_module(USER_MODULE);

    let exprs = parse_source(src);
    let code_desc = Compiler::compile_for_vm(&vm, &exprs).expect("compile");

    let code_with_ic = materialize(&mut vm, &code_desc);
    let code_without_ic = materialize(&mut vm, &code_desc);
    unsafe {
        let code_ptr = code_without_ic.ref_bits() as *mut Code;
        (*code_ptr).feedback = vm.special.none;
    }

    let _ = vm.module_store_current(BENCH_CODE_WITH_IC, code_with_ic);
    let _ = vm.module_store_current(BENCH_CODE_WITHOUT_IC, code_without_ic);

    vm
}

fn run_case(c: &mut Criterion, name: &str, src: &str, iters_per_sample: usize) {
    let mut vm = build_code_pair(src);
    let warmup_code = vm
        .module_lookup_current(BENCH_CODE_WITH_IC)
        .expect("missing cached bench code");
    let warmup = interpret(&mut vm, warmup_code).expect("warmup");
    black_box(warmup);

    c.bench_function(&format!("{name}_with_ic_feedback"), |b| {
        b.iter(|| {
            for _ in 0..iters_per_sample {
                let code_with_ic = vm
                    .module_lookup_current(BENCH_CODE_WITH_IC)
                    .expect("missing cached bench code");
                let value =
                    interpret(&mut vm, code_with_ic).expect("interpret");
                black_box(value);
            }
        })
    });

    c.bench_function(&format!("{name}_without_ic_feedback"), |b| {
        b.iter(|| {
            for _ in 0..iters_per_sample {
                let code_without_ic = vm
                    .module_lookup_current(BENCH_CODE_WITHOUT_IC)
                    .expect("missing cached bench code");
                let value =
                    interpret(&mut vm, code_without_ic).expect("interpret");
                black_box(value);
            }
        })
    });
}

fn bench_ic_feedback(c: &mut Criterion) {
    let mut stress_dispatch = String::from("[ x := 0. ");
    for _ in 0..120 {
        stress_dispatch.push_str("x := x + 1. ");
    }
    stress_dispatch.push_str("x ] call");

    run_case(c, "stress_dispatch", &stress_dispatch, 1);
}

criterion_group!(benches, bench_ic_feedback);
criterion_main!(benches);
