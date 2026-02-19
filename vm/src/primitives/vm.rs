use std::collections::{HashMap, HashSet};

use object::Value;
use object::{Array, MapFlags, ObjectType, Slot, SlotFlags, SlotObject};
use parser::{Lexer, Parser};

use crate::compiler0;
use crate::interpreter::{self, with_roots, InterpreterState, RuntimeError};
use crate::materialize;
use crate::primitives::string::intern_symbol;
use crate::primitives::{
    expect_string, expect_symbol, string::alloc_vm_string,
};
use crate::{USER_MODULE, VM};

pub fn vm_eval(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    if vm.current_module.is_none() {
        vm.open_module(USER_MODULE);
    }

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

    let code_desc = match compiler0::Compiler::compile_for_vm(vm, &exprs) {
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

pub fn vm_module_open(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path = symbol_to_string(args[0])?;
    vm.open_module(&path);
    Ok(args[0])
}

pub fn vm_module_use(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path = symbol_to_string(args[0])?;
    vm.module_use(&path, &HashMap::new()).map_err(|msg| {
        RuntimeError::Unimplemented {
            message: Box::leak(msg.into_boxed_str()),
        }
    })?;
    Ok(vm.special.none)
}

pub fn vm_module_use_as(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path = symbol_to_string(args[0])?;
    let alias_map = parse_alias_map(args[1])?;
    vm.module_use(&path, &alias_map).map_err(|msg| {
        RuntimeError::Unimplemented {
            message: Box::leak(msg.into_boxed_str()),
        }
    })?;
    Ok(vm.special.none)
}

pub fn vm_module_use_only(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path = symbol_to_string(args[0])?;
    let names = parse_symbol_names(args[1])?;
    vm.module_use_only(&path, &names).map_err(|msg| {
        RuntimeError::Unimplemented {
            message: Box::leak(msg.into_boxed_str()),
        }
    })?;
    Ok(vm.special.none)
}

pub fn vm_module_export(
    vm: &mut VM,
    _state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let name = symbol_to_string(args[0])?;
    vm.module_export_current(&name).map_err(|msg| {
        RuntimeError::Unimplemented {
            message: Box::leak(msg.into_boxed_str()),
        }
    })?;
    Ok(vm.special.none)
}

pub fn vm_current_module(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    _args: &[Value],
) -> Result<Value, RuntimeError> {
    let Some(path) = vm.current_module.clone() else {
        return Ok(vm.special.none);
    };
    intern_symbol(vm, state, &path)
}

pub fn vm_module_at(
    vm: &mut VM,
    state: &mut InterpreterState,
    _receiver: Value,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    let path = symbol_to_string(args[0])?;
    let entries = vm.module_public_entries(&path).map_err(|msg| {
        RuntimeError::Unimplemented {
            message: Box::leak(msg.into_boxed_str()),
        }
    })?;

    let mut slot_data = Vec::with_capacity(entries.len());
    let mut scratch = Vec::with_capacity(entries.len() * 2);
    for (name, value) in &entries {
        let sym = intern_symbol(vm, state, name)?;
        slot_data.push((sym, *value));
        scratch.push(sym);
        scratch.push(*value);
    }

    let obj = with_roots(vm, state, &mut scratch, |proxy, roots| unsafe {
        let map_map = roots.special.map_map;
        let none = roots.special.none;
        let mut slots = Vec::with_capacity(slot_data.len());
        for (sym, value) in &slot_data {
            slots.push(Slot::new(
                SlotFlags::CONSTANT.with(SlotFlags::ENUMERABLE),
                *sym,
                *value,
            ));
        }

        let map = crate::alloc::alloc_map(
            proxy,
            roots,
            map_map,
            none,
            MapFlags::NONE,
            &slots,
            0,
        )
        .value();
        crate::alloc::alloc_slot_object(proxy, roots, map, &[]).value()
    });
    Ok(obj)
}

fn symbol_to_string(value: Value) -> Result<String, RuntimeError> {
    let ptr = expect_symbol(value)?;
    let s: &object::VMSymbol = unsafe { &*ptr };
    Ok(unsafe { s.as_str() }.to_string())
}

fn parse_alias_map(
    value: Value,
) -> Result<HashMap<String, String>, RuntimeError> {
    if !value.is_ref() {
        return Err(RuntimeError::TypeError {
            expected: "alias object",
            got: value,
        });
    }
    let header: &object::Header = unsafe { value.as_ref() };
    if header.object_type() != ObjectType::Slots {
        return Err(RuntimeError::TypeError {
            expected: "alias object",
            got: value,
        });
    }

    let obj: &SlotObject = unsafe { value.as_ref() };
    let map: &object::Map = unsafe { obj.map.as_ref() };
    let mut aliases = HashMap::new();
    unsafe {
        for slot in map.slots() {
            let from_name = symbol_to_string(slot.name)?;
            let to_value = if slot.is_assignable() {
                let offset = slot.value.to_i64() as u32;
                obj.read_value(offset)
            } else {
                slot.value
            };
            let to_name = symbol_to_string(to_value)?;
            aliases.insert(from_name, to_name);
        }
    }
    Ok(aliases)
}

fn parse_symbol_names(value: Value) -> Result<HashSet<String>, RuntimeError> {
    let mut names = HashSet::new();

    if value.is_ref() {
        let header: &object::Header = unsafe { value.as_ref() };
        if header.object_type() == ObjectType::Array {
            let array: &Array = unsafe { value.as_ref() };
            for element in unsafe { array.elements() } {
                names.insert(symbol_to_string(*element)?);
            }
            return Ok(names);
        }
    }

    names.insert(symbol_to_string(value)?);
    Ok(names)
}

#[cfg(test)]
mod tests {
    use super::*;
    use heap::HeapSettings;
    use object::{Header, ObjectType, VMString, Value};

    fn execute_source(vm: &mut VM, source: &str) -> Result<Value, String> {
        if vm.current_module.is_none() {
            vm.open_module(USER_MODULE);
        }

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
        let code_desc = compiler0::Compiler::compile_for_vm(vm, &exprs)
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

    fn compile_source(
        vm: &mut VM,
        source: &str,
    ) -> Result<compiler0::CodeDesc, String> {
        if vm.current_module.is_none() {
            vm.open_module(USER_MODULE);
        }

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
        compiler0::Compiler::compile_for_vm(vm, &exprs)
            .map_err(|e| format!("Compile error: {e}"))
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
            "EvalGlobal := 0. VM _Eval: \"EvalGlobal := 41.\". EvalGlobal _FixnumAdd: 1",
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
        assert!(text.contains("Compile error"));
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

    #[test]
    fn modules_isolate_bindings_without_global_fallback() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let err = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Shared. GlobalX := 9. VM _ModuleExport: 'GlobalX. VM _ModuleOpen: 'A. x := 1. VM _ModuleOpen: 'B. x := 2. VM _ModuleOpen: 'A. x _FixnumAdd: GlobalX",
        )
        .expect_err("cross-module global without import should fail");
        assert!(err.contains("unresolved global 'GlobalX'"));

        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Shared. GlobalX := 9. VM _ModuleExport: 'GlobalX. VM _ModuleOpen: 'A. x := 1. VM _ModuleUse: 'Shared. x _FixnumAdd: GlobalX",
        )
        .expect("explicit module import should succeed");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 10);
    }

    #[test]
    fn module_use_imports_only_exports() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. foo := 41. hidden := 7. VM _ModuleExport: 'foo. VM _ModuleOpen: 'App. VM _ModuleUse: 'Lib. foo _FixnumAdd: 1",
        )
        .expect("module use should import exported names");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);

        let err = execute_source(&mut vm, "VM _ModuleOpen: 'App. hidden")
            .expect_err("hidden must not be imported");
        assert!(err.contains("unresolved global 'hidden'"));
    }

    #[test]
    fn module_use_only_imports_requested_name() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. foo := 41. bar := 7. VM _ModuleExport: 'foo. VM _ModuleExport: 'bar. VM _ModuleOpen: 'App. VM _ModuleUseOnly: 'Lib Names: 'foo. foo _FixnumAdd: 1",
        )
        .expect("use only should import requested name");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);

        let err = execute_source(&mut vm, "VM _ModuleOpen: 'App. bar")
            .expect_err("non-selected export must not be imported");
        assert!(err.contains("unresolved global 'bar'"));
    }

    #[test]
    fn module_use_as_aliases_and_collisions_are_atomic() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'A. foo := 1. VM _ModuleExport: 'foo.",
        )
        .expect("setup A");
        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'B. foo := 2. VM _ModuleExport: 'foo.",
        )
        .expect("setup B");

        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'App. VM _ModuleUse: 'A As: { foo = 'fromA }. fromA",
        )
        .expect("first import should succeed");

        let err = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'App. VM _ModuleUse: 'B As: { foo = 'fromA }",
        )
        .expect_err("alias collision should fail");
        assert!(err.contains("import collision"));

        let value = execute_source(&mut vm, "VM _ModuleOpen: 'App. fromA")
            .expect("existing import must remain unchanged");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 1);
    }

    #[test]
    fn module_at_exposes_public_surface_only() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. pub := 3. hidden := 7. VM _ModuleExport: 'pub.",
        )
        .expect("setup lib module");

        let value = execute_source(&mut vm, "(VM _ModuleAt: 'Lib) pub")
            .expect("public lookup through module surface should work");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 3);

        let err = execute_source(&mut vm, "(VM _ModuleAt: 'Lib) hidden")
            .expect_err("hidden lookup must fail");
        assert!(err.contains("MessageNotUnderstood"));
    }

    #[test]
    fn module_reuse_with_same_source_is_idempotent() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Core::Math. pi := 3. answer := 42. VM _ModuleExport: 'pi. VM _ModuleExport: 'answer. VM _ModuleOpen: 'App. VM _ModuleUse: 'Core::Math. VM _ModuleUse: 'Core::Math As: { answer = 'mathAnswer }. VM _ModuleOpen: 'Core::Math. VM _ModuleOpen: 'App. pi _FixnumAdd: mathAnswer",
        )
        .expect("reusing module imports should succeed");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 45);
    }

    #[test]
    fn module_open_auto_uses_core_exports() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Core. Shared := 7. VM _ModuleExport: 'Shared. VM _ModuleOpen: 'App. Shared",
        )
        .expect("opening app should auto-use Core exports");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 7);
    }

    #[test]
    fn module_assignment_through_import_updates_source_binding() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. x := 1. VM _ModuleExport: 'x. VM _ModuleOpen: 'App. VM _ModuleUse: 'Lib. x := 9. VM _ModuleOpen: 'Lib. x",
        )
        .expect("assignment through imported symbol should write source");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 9);
    }

    #[test]
    fn methods_resolve_globals_in_defining_module() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. Posix := { O_RDONLY = 77 }. File := { open: path = { Posix O_RDONLY } }. VM _ModuleExport: 'File. VM _ModuleOpen: 'App. Posix := { O_RDONLY = 13 }. VM _ModuleUse: 'Lib. File open: \"x\"",
        )
        .expect("method global lookup should use defining module");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 77);
    }

    #[test]
    fn qualified_export_reference_works_without_use() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib::Nested. Greeter := { greet = { 41 _FixnumAdd: 1 }. }. VM _ModuleExport: 'Greeter. VM _ModuleOpen: 'App. Lib::Nested::Greeter greet",
        )
        .expect("qualified export reference should resolve");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn qualified_export_assignment_is_rejected() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let err = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib::Nested. x := 1. VM _ModuleExport: 'x. VM _ModuleOpen: 'App. Lib::Nested::x := 3",
        )
        .expect_err("assignment to qualified export should fail");
        assert!(err.contains("cannot assign to qualified export"));
    }

    #[test]
    fn export_before_define_in_same_unit_works() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let value = execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. VM _ModuleExport: 'Hello. Hello := 42. VM _ModuleOpen: 'App. VM _ModuleUse: 'Lib. Hello",
        )
        .expect("export before define should resolve");
        assert!(value.is_fixnum());
        assert_eq!(unsafe { value.to_i64() }, 42);
    }

    #[test]
    fn forward_global_reference_in_same_unit_compiles() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let code = compile_source(
            &mut vm,
            "VM _ModuleOpen: 'App. Holder := { get = { x } }. x := 41.",
        )
        .expect("forward global reference should compile");
        assert!(code.constants.iter().any(|c| matches!(
            c,
            compiler0::ConstEntry::ModuleAssoc { module, name }
                if module == "App" && name == "x"
        )));
    }

    #[test]
    fn unresolved_global_is_compile_error() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        let err = compile_source(&mut vm, "VM _ModuleOpen: 'App. missing")
            .expect_err("unresolved global should fail compile");
        assert!(err.contains("unresolved global 'missing'"));
    }

    #[test]
    fn module_compile_emits_module_assoc_constants() {
        let mut vm = crate::special::bootstrap(HeapSettings::default());
        execute_source(
            &mut vm,
            "VM _ModuleOpen: 'Lib. Hello := 1. VM _ModuleExport: 'Hello.",
        )
        .expect("setup lib module");

        let code = compile_source(
            &mut vm,
            "VM _ModuleOpen: 'App. VM _ModuleUse: 'Lib. Hello _FixnumAdd: 1",
        )
        .expect("compile should succeed");

        assert!(code.constants.iter().any(|c| matches!(
            c,
            compiler0::ConstEntry::ModuleAssoc { module, name }
                if module == "Lib" && name == "Hello"
        )));
    }
}
