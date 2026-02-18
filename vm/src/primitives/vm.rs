use object::Value;
use parser::{Lexer, Parser};

use crate::compiler0;
use crate::interpreter::{self, InterpreterState, RuntimeError};
use crate::materialize;
use crate::primitives::{expect_string, string::alloc_vm_string};
use crate::VM;

pub fn vm_eval(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let source_ptr = expect_string(args[0])?;
    let source = unsafe { (*source_ptr).as_str() };

    let parse_results: Vec<_> = Parser::new(Lexer::from_str(source)).collect();
    let parse_errors: Vec<String> = parse_results
        .iter()
        .filter_map(|r| r.as_ref().err())
        .map(|e| format!("Parse error: {e}"))
        .collect();
    if !parse_errors.is_empty() {
        let msg = parse_errors.join("\n");
        return alloc_vm_string(vm, state, msg.as_bytes());
    }

    let exprs: Vec<parser::ast::Expr> =
        parse_results.into_iter().map(|r| r.unwrap()).collect();

    let code_desc = match compiler0::Compiler::compile(&exprs) {
        Ok(code_desc) => code_desc,
        Err(err) => {
            let msg = format!("Compile error: {err}");
            return alloc_vm_string(vm, state, msg.as_bytes());
        }
    };

    let code = materialize::materialize(vm, &code_desc);
    match interpreter::interpret(vm, code) {
        Ok(value) => Ok(value),
        Err(err) => {
            let msg = format_runtime_error(&err);
            alloc_vm_string(vm, state, msg.as_bytes())
        }
    }
}

fn format_runtime_error(err: &interpreter::LocatedRuntimeError) -> String {
    match err.location {
        Some(loc) => {
            format!(
                "Runtime error: {:?} at {}..{}",
                err.error, loc.start, loc.end
            )
        }
        None => format!("Runtime error: {:?}", err.error),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use heap::HeapSettings;
    use object::{Header, ObjectType, VMString, Value};

    fn execute_source(vm: &mut VM, source: &str) -> Result<Value, String> {
        let parse_results: Vec<_> =
            Parser::new(Lexer::from_str(source)).collect();
        let parse_errors: Vec<String> = parse_results
            .iter()
            .filter_map(|r| r.as_ref().err())
            .map(|e| format!("Parse error: {e}"))
            .collect();
        if !parse_errors.is_empty() {
            return Err(parse_errors.join("\n"));
        }

        let exprs: Vec<parser::ast::Expr> =
            parse_results.into_iter().map(|r| r.unwrap()).collect();
        let code_desc = compiler0::Compiler::compile(&exprs)
            .map_err(|e| format!("Compile error: {e}"))?;
        let code = materialize::materialize(vm, &code_desc);
        interpreter::interpret(vm, code)
            .map(|v| v)
            .map_err(|e| format!("Runtime error: {:?}", e.error))
    }

    fn as_string(value: Value) -> Option<String> {
        if !value.is_ref() {
            return None;
        }
        let header: &Header = unsafe { value.as_ref() };
        if header.object_type() != ObjectType::Str {
            return None;
        }
        let s: &VMString = unsafe { value.as_ref() };
        Some(unsafe { s.as_str() }.to_string())
    }

    #[test]
    fn eval_computes_value_in_global_scope() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(&mut vm, "VM _Eval: \"40 _FixnumAdd: 2\"")
            .expect("evaluation should succeed");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn eval_updates_globals() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _Eval: \"EvalGlobal := 41.\". EvalGlobal _FixnumAdd: 1",
        )
        .expect("evaluation should succeed");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn eval_does_not_capture_caller_locals() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "{ test = { local := 99. VM _Eval: \"local\" }. } test",
        )
        .expect("evaluation should succeed");
        let text =
            as_string(value).expect("eval should return an error string");
        assert!(text.contains("UndefinedGlobal"));
        assert!(text.contains("local"));
    }

    #[test]
    fn eval_returns_parse_errors_as_string() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(&mut vm, "VM _Eval: \"(\"")
            .expect("eval call should succeed");
        let text =
            as_string(value).expect("eval should return an error string");
        assert!(text.contains("Parse error"));
    }
}
