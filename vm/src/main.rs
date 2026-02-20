use clap::Parser as ClapParser;
use std::{
    fs,
    io::{self, Write},
    process,
};

use heap::HeapSettings;
use parser::token::TokenKind;
use parser::{Lexer, Parser};

use vm::{compiler0, interpreter, materialize, special, USER_MODULE, VM};

const SLOT_PRINT_LIMIT: usize = 30;

#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Input source files to execute in order
    #[arg(required = false, help = "The .ktt files to execute")]
    files: Vec<String>,

    /// Start REPL after executing files (default if no files)
    #[arg(long, help = "Force REPL mode after file execution")]
    repl: bool,

    /// Print bytecode and constants instead of executing
    #[arg(long, help = "Dump bytecode + constant pool for inputs")]
    dump_bytecode: bool,

    /// Print receiver details for MessageNotUnderstood
    #[arg(long, help = "Trace MessageNotUnderstood receiver details")]
    #[cfg(debug_assertions)]
    trace_mnu: bool,

    /// Trace load/store for a specific global assoc
    #[cfg(debug_assertions)]
    #[arg(long, help = "Trace assoc load/store for global name")]
    trace_assoc: Option<String>,

    /// Trace sends for a specific selector
    #[cfg(debug_assertions)]
    #[arg(long, help = "Trace sends for selector name")]
    trace_send: Option<String>,
}

fn main() {
    let cli = Cli::parse();

    let mut vm = special::bootstrap(HeapSettings::default());
    #[cfg(debug_assertions)]
    {
        vm.trace_assoc_name = cli.trace_assoc.clone();
        vm.trace_send_name = cli.trace_send.clone();
    }

    if !cli.files.is_empty() {
        vm.open_module(USER_MODULE);
    }

    for filename in &cli.files {
        let source_code = match fs::read_to_string(filename) {
            Ok(content) => content,
            Err(err) => {
                eprintln!("Error reading file '{}': {}", filename, err);
                process::exit(1);
            }
        };

        if cli.dump_bytecode {
            match compile_source(&vm, &source_code) {
                Ok(code_desc) => {
                    println!("== {} ==", filename);
                    dump_code_desc(&code_desc);
                }
                Err(err) => {
                    eprintln!("Error compiling {}: {}", filename, err);
                    process::exit(1);
                }
            }
        } else {
            let trace_mnu = {
                #[cfg(debug_assertions)]
                {
                    cli.trace_mnu
                }
                #[cfg(not(debug_assertions))]
                {
                    false
                }
            };
            match execute_source(&mut vm, &source_code, trace_mnu) {
                Ok(value) => {
                    if should_print_last_expr(&source_code) {
                        print_value(&mut vm, value);
                    }
                }
                Err(err) => {
                    eprintln!("Error executing {}: {}", filename, err);
                    process::exit(1);
                }
            }
        }
    }

    if cli.dump_bytecode {
        return;
    }

    if cli.repl || cli.files.is_empty() {
        vm.open_module(USER_MODULE);
        let trace_mnu = {
            #[cfg(debug_assertions)]
            {
                cli.trace_mnu
            }
            #[cfg(not(debug_assertions))]
            {
                false
            }
        };
        run_repl(&mut vm, trace_mnu);
    }
}

fn run_repl(vm: &mut VM, trace_mnu: bool) {
    println!("Kette VM REPL");
    println!("Type 'exit' to quit.");

    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut input_buffer = String::new();

    loop {
        print!("> ");
        if let Err(err) = stdout.flush() {
            eprintln!("Error flushing stdout: {}", err);
            break;
        }

        input_buffer.clear();
        match stdin.read_line(&mut input_buffer) {
            Ok(0) => break,
            Ok(_) => {
                let input = input_buffer.trim();
                if input == "exit" {
                    break;
                }
                if input.is_empty() {
                    continue;
                }

                match execute_source(vm, &input_buffer, trace_mnu) {
                    Ok(value) => print_value(vm, value),
                    Err(err) => eprintln!("Error: {}", err),
                }
            }
            Err(err) => {
                eprintln!("Error reading input: {}", err);
                break;
            }
        }
    }
}

fn execute_source(
    vm: &mut VM,
    source: &str,
    trace_mnu: bool,
) -> Result<object::Value, String> {
    let code_desc = compile_source(vm, source)?;
    let code = materialize::materialize(vm, &code_desc);

    interpreter::interpret(vm, code)
        .map_err(|e| format_located_error(vm, source, &e, trace_mnu))
}

fn compile_source(
    vm: &VM,
    source: &str,
) -> Result<compiler0::CodeDesc, String> {
    let lexer = Lexer::from_str(source);

    let results: Vec<_> = Parser::new(lexer).collect();

    let errors: Vec<String> = results
        .iter()
        .filter_map(|r| r.as_ref().err())
        .map(|e| format_parse_error(source, e))
        .collect();

    if !errors.is_empty() {
        return Err(errors.join("\n"));
    }

    let exprs: Vec<parser::ast::Expr> =
        results.into_iter().map(|r| r.unwrap()).collect();

    compiler0::Compiler::compile_for_vm(vm, &exprs)
        .map_err(|e| format_compile_error(source, &e))
}

fn should_print_last_expr(source: &str) -> bool {
    let mut last_kind = None;
    for token in Lexer::from_str(source) {
        if token.kind.is_comment() {
            continue;
        }
        if matches!(token.kind, TokenKind::Eof) {
            break;
        }
        last_kind = Some(token.kind.clone());
    }

    match last_kind {
        None => false,
        Some(TokenKind::Dot) => false,
        _ => true,
    }
}

fn dump_code_desc(desc: &compiler0::CodeDesc) {
    dump_code_desc_inner(desc, 0);
}

fn dump_code_desc_inner(desc: &compiler0::CodeDesc, indent: usize) {
    let pad = " ".repeat(indent);
    println!("{pad}-- constants --");
    for (idx, entry) in desc.constants.iter().enumerate() {
        println!("{pad}[{idx}] {}", format_const_entry(entry));

        match entry {
            compiler0::ConstEntry::Code(code) => {
                println!("{pad}  >> code const {idx}");
                dump_code_desc_inner(code, indent + 4);
            }
            compiler0::ConstEntry::Map(map) => {
                println!("{pad}  >> map slots ({}):", map.slots.len());
                for slot in &map.slots {
                    let flags = format_slot_flags(slot.flags);
                    let value = match &slot.value {
                        compiler0::SlotValue::Constant(c) => {
                            format!("const {}", format_const_entry_short(c))
                        }
                        compiler0::SlotValue::Offset(o) => {
                            format!("offset {o}")
                        }
                    };
                    println!(
                        "{pad}    - {name} [{flags}] = {value}",
                        name = slot.name,
                        flags = flags,
                        value = value
                    );

                    if let compiler0::SlotValue::Constant(c) = &slot.value {
                        if let compiler0::ConstEntry::Code(code) = c {
                            println!("{pad}      >> slot code {}", slot.name);
                            dump_code_desc_inner(code, indent + 8);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    println!("{pad}-- bytecode --");
    let decoder = bytecode::BytecodeDecoder::new(&desc.bytecode);
    for (pc, instr) in decoder.enumerate() {
        println!("{pad}{pc:04}: {instr:?}");
    }
    println!(
        "{pad}-- meta --
{pad}regs={}
{pad}args={}
{pad}temps={}
{pad}feedback={}",
        desc.register_count,
        desc.arg_count,
        desc.temp_count,
        desc.feedback_count
    );
}

fn format_slot_flags(flags: u16) -> String {
    let mut parts = Vec::new();
    if flags & 1 != 0 {
        parts.push("assignable");
    }
    if flags & 2 != 0 {
        parts.push("assignment");
    }
    if flags & 4 != 0 {
        parts.push("constant");
    }
    if flags & 8 != 0 {
        parts.push("enumerable");
    }
    if flags & 16 != 0 {
        parts.push("parent");
    }
    if parts.is_empty() {
        return "none".to_string();
    }
    parts.join("|")
}

fn format_const_entry(entry: &compiler0::ConstEntry) -> String {
    match entry {
        compiler0::ConstEntry::Fixnum(v) => format!("Fixnum({v})"),
        compiler0::ConstEntry::BigInt(v) => format!("BigInt({v})"),
        compiler0::ConstEntry::Float(v) => format!("Float({v})"),
        compiler0::ConstEntry::String(s) => format!("String(\"{s}\")"),
        compiler0::ConstEntry::Value(v) => format!("Value({v:?})"),
        compiler0::ConstEntry::Symbol(s) => format!("Symbol({s})"),
        compiler0::ConstEntry::ModuleAssoc { module, name } => {
            format!("ModuleAssoc({module}::{name})")
        }
        compiler0::ConstEntry::Assoc(s) => format!("Assoc({s})"),
        compiler0::ConstEntry::AssocValue(s) => format!("AssocValue({s})"),
        compiler0::ConstEntry::Code(code) => {
            format!(
                "Code(regs={}, args={}, temps={}, consts={})",
                code.register_count,
                code.arg_count,
                code.temp_count,
                code.constants.len()
            )
        }
        compiler0::ConstEntry::Map(map) => {
            format!(
                "Map(slots={}, values={}, code={:?})",
                map.slots.len(),
                map.value_count,
                map.code
            )
        }
    }
}

fn format_const_entry_short(entry: &compiler0::ConstEntry) -> String {
    match entry {
        compiler0::ConstEntry::Fixnum(v) => format!("Fixnum({v})"),
        compiler0::ConstEntry::BigInt(v) => format!("BigInt({v})"),
        compiler0::ConstEntry::Float(v) => format!("Float({v})"),
        compiler0::ConstEntry::String(s) => format!("String(\"{s}\")"),
        compiler0::ConstEntry::Value(v) => format!("Value({v:?})"),
        compiler0::ConstEntry::Symbol(s) => format!("Symbol({s})"),
        compiler0::ConstEntry::ModuleAssoc { module, name } => {
            format!("ModuleAssoc({module}::{name})")
        }
        compiler0::ConstEntry::Assoc(s) => format!("Assoc({s})"),
        compiler0::ConstEntry::AssocValue(s) => format!("AssocValue({s})"),
        compiler0::ConstEntry::Code(code) => format!(
            "Code(regs={}, args={}, temps={})",
            code.register_count, code.arg_count, code.temp_count
        ),
        compiler0::ConstEntry::Map(map) => {
            format!(
                "Map(slots={}, values={})",
                map.slots.len(),
                map.value_count
            )
        }
    }
}

fn print_value(vm: &mut VM, value: object::Value) {
    if let Some(text) = value_to_string(value) {
        println!("{}", text);
        return;
    }

    if let Some(text) = try_to_string(vm, value) {
        println!("{}", text);
        return;
    }

    if let Some(text) = format_slot_object_shallow(vm, value) {
        println!("{}", text);
        return;
    }

    println!("{:?}", value);
}

fn try_to_string(vm: &mut VM, value: object::Value) -> Option<String> {
    let mut builder = bytecode::BytecodeBuilder::new();
    builder.load_constant(0);
    builder.send(1, 0, 0, 0);
    builder.local_return();

    let code_desc = compiler0::CodeDesc {
        bytecode: builder.into_bytes(),
        constants: vec![
            compiler0::ConstEntry::Value(value),
            compiler0::ConstEntry::Symbol("toString".to_string()),
        ],
        register_count: 1,
        arg_count: 0,
        temp_count: 0,
        feedback_count: 1,
        source_map: vec![],
    };

    let code = materialize::materialize(vm, &code_desc);
    let result = interpreter::interpret(vm, code).ok()?;
    value_to_string(result)
}

fn format_runtime_error(
    vm: &VM,
    err: &interpreter::RuntimeError,
    trace_mnu: bool,
) -> String {
    match err {
        interpreter::RuntimeError::MessageNotUnderstood {
            receiver,
            message,
        } => {
            let msg = value_to_string(*message)
                .unwrap_or_else(|| format!("{:?}", message));
            let recv = value_to_string(*receiver)
                .unwrap_or_else(|| format!("{:?}", receiver));
            if trace_mnu {
                let detail = format_receiver_debug(vm, *receiver);
                format!(
                    "MessageNotUnderstood {{ receiver: {recv}, message: {msg} }}\n{detail}"
                )
            } else {
                format!(
                    "MessageNotUnderstood {{ receiver: {recv}, message: {msg} }}"
                )
            }
        }
        interpreter::RuntimeError::UndefinedGlobal { name } => {
            format!("UndefinedGlobal {{ name: {name} }}")
        }
        other => format!("{:?}", other),
    }
}

fn format_located_error(
    vm: &VM,
    source: &str,
    err: &interpreter::LocatedRuntimeError,
    trace_mnu: bool,
) -> String {
    let error_msg = format_runtime_error(vm, &err.error, trace_mnu);

    let Some(loc) = &err.location else {
        return format!("Runtime error: {error_msg}");
    };

    format_diagnostic(
        source,
        "Runtime error",
        &error_msg,
        loc.start as usize,
        loc.end as usize,
    )
}

fn format_parse_error(source: &str, err: &parser::ParseError) -> String {
    format_diagnostic(
        source,
        "Parse error",
        &err.message,
        err.span.start.offset,
        err.span.end.offset,
    )
}

fn format_compile_error(source: &str, err: &compiler0::CompileError) -> String {
    match &err.span {
        Some(span) => format_diagnostic(
            source,
            "Compile error",
            &err.message,
            span.start.offset,
            span.end.offset,
        ),
        None => format!("Compile error: {}", err.message),
    }
}

fn format_receiver_debug(vm: &VM, receiver: object::Value) -> String {
    if !receiver.is_ref() {
        return format!("receiver_type=immediate value={receiver:?}");
    }

    let header: &object::Header = unsafe { receiver.as_ref() };
    let obj_type = header.object_type();
    let mut lines = vec![format!("receiver_type={:?}", obj_type)];

    match obj_type {
        object::ObjectType::Slots => unsafe {
            let obj: &object::SlotObject = receiver.as_ref();
            let map: &object::Map = obj.map.as_ref();
            lines.push(format!(
                "map_slots={} value_count={}",
                map.slot_count(),
                map.value_count()
            ));
            if obj.map.raw() == vm.assoc_map.raw() {
                lines.push("map_kind=assoc".to_string());
            }
            lines.push(format!("map_ptr={:?}", obj.map));
            if obj.map.is_ref() {
                let map_header: &object::Header = obj.map.as_ref();
                lines.push(format!(
                    "map_obj_type={:?}",
                    map_header.object_type()
                ));
            }
            let mut names = Vec::new();
            for slot in map.slots() {
                if let Some(name) = value_to_string(slot.name) {
                    names.push(name);
                } else {
                    names.push(format!("{:?}", slot.name));
                }
            }
            if !names.is_empty() {
                lines.push(format!("map_slot_names=[{}]", names.join(", ")));
            }
        },
        object::ObjectType::Map => unsafe {
            let map: &object::Map = receiver.as_ref();
            lines.push(format!(
                "map_slots={} value_count={}",
                map.slot_count(),
                map.value_count()
            ));
            let mut names = Vec::new();
            for slot in map.slots() {
                if let Some(name) = value_to_string(slot.name) {
                    names.push(name);
                } else {
                    names.push(format!("{:?}", slot.name));
                }
            }
            if !names.is_empty() {
                lines.push(format!("map_slot_names=[{}]", names.join(", ")));
            }
        },
        object::ObjectType::Array => unsafe {
            let arr: &object::Array = receiver.as_ref();
            lines.push(format!("array_len={}", arr.len()));
        },
        object::ObjectType::ByteArray => unsafe {
            let arr: &object::ByteArray = receiver.as_ref();
            lines.push(format!("bytearray_len={}", arr.len()));
        },
        object::ObjectType::Str => unsafe {
            let s: &object::VMString = receiver.as_ref();
            lines.push(format!("string=\"{}\"", s.as_str()));
        },
        object::ObjectType::Symbol => unsafe {
            let s: &object::VMSymbol = receiver.as_ref();
            lines.push(format!("symbol='{}", s.as_str()));
        },
        object::ObjectType::Float => unsafe {
            let f: &object::Float = receiver.as_ref();
            lines.push(format!("float_value={}", f.value));
        },
        object::ObjectType::Ratio => unsafe {
            let r: &object::Ratio = receiver.as_ref();
            lines.push(format!(
                "ratio=numer={:?} denom={:?}",
                r.numerator, r.denominator
            ));
        },
        object::ObjectType::BigNum => {}
        _ => {}
    }

    lines.join("\n")
}

fn format_diagnostic(
    source: &str,
    kind: &str,
    message: &str,
    start: usize,
    end: usize,
) -> String {
    let source_len = source.len();
    let start = start.min(source_len);
    let end = end.min(source_len);

    let (line, col, line_start) = offset_to_line_col(source, start);
    let line_end = source[line_start..]
        .find('\n')
        .map(|i| line_start + i)
        .unwrap_or(source.len());
    let source_line = &source[line_start..line_end];

    // Compute underline span (clamp to current line)
    let underline_start =
        start.saturating_sub(line_start).min(source_line.len());
    let underline_end = end.min(line_end).saturating_sub(line_start);
    let underline_len = underline_end.saturating_sub(underline_start).max(1);

    let line_num = format!("{}", line);
    let pad = " ".repeat(line_num.len());

    format!(
        "{kind}: {message} (offset {start})\n\
         {pad}--> {line}:{col}\n\
         {pad} |\n\
         {line_num} | {source_line}\n\
         {pad} | {}{}\n",
        " ".repeat(underline_start),
        "^".repeat(underline_len),
    )
}

fn offset_to_line_col(source: &str, offset: usize) -> (usize, usize, usize) {
    let mut line = 1;
    let mut line_start = 0;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            line_start = i + 1;
        }
    }
    let col = offset - line_start + 1;
    (line, col, line_start)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offset_to_line_col_first_line() {
        let (line, col, line_start) = offset_to_line_col("hello world", 6);
        assert_eq!(line, 1);
        assert_eq!(col, 7);
        assert_eq!(line_start, 0);
    }

    #[test]
    fn offset_to_line_col_second_line() {
        let (line, col, line_start) = offset_to_line_col("abc\ndef", 4);
        assert_eq!(line, 2);
        assert_eq!(col, 1);
        assert_eq!(line_start, 4);
    }

    #[test]
    fn offset_to_line_col_start() {
        let (line, col, _) = offset_to_line_col("x", 0);
        assert_eq!(line, 1);
        assert_eq!(col, 1);
    }

    #[test]
    fn diagnostic_single_digit_line() {
        let output = format_diagnostic("5 foo", "Test error", "oops", 0, 5);
        assert!(output.contains("Test error: oops (offset 0)"));
        assert!(output.contains("--> 1:1"));
        assert!(output.contains("1 | 5 foo"));
        assert!(output.contains("^^^^^"));
    }

    #[test]
    fn diagnostic_alignment() {
        // Verify the | characters are vertically aligned
        let output = format_diagnostic("hello", "E", "msg", 0, 5);
        let lines: Vec<&str> = output.lines().collect();
        // lines[1] = " --> 1:1"  (pad=" ")
        // lines[2] = "  |"       (pad + " |")
        // lines[3] = "1 | hello" (line_num + " | ")
        // lines[4] = "  | ^^^^^" (pad + " | ")
        let pipe_pos_2 = lines[2].find('|').unwrap();
        let pipe_pos_3 = lines[3].find('|').unwrap();
        let pipe_pos_4 = lines[4].find('|').unwrap();
        assert_eq!(pipe_pos_2, pipe_pos_3);
        assert_eq!(pipe_pos_3, pipe_pos_4);
    }

    #[test]
    fn diagnostic_multiline_source() {
        let src = "aaa\nbbb\nccc";
        let output = format_diagnostic(src, "E", "msg", 4, 7);
        assert!(output.contains("--> 2:1"));
        assert!(output.contains("2 | bbb"));
        assert!(output.contains("^^^"));
    }

    #[test]
    fn diagnostic_three_digit_line_alignment() {
        // Build a source with 100+ lines
        let mut src = String::new();
        for i in 1..=100 {
            src.push_str(&format!("line{}\n", i));
        }
        let offset = src.len() - 8; // somewhere on line 100
        let output = format_diagnostic(&src, "E", "msg", offset, offset + 3);
        assert!(output.contains("--> 100:"));
        // Check alignment
        let lines: Vec<&str> = output.lines().collect();
        let pipe_pos_blank = lines[2].find('|').unwrap();
        let pipe_pos_source = lines[3].find('|').unwrap();
        let pipe_pos_underline = lines[4].find('|').unwrap();
        assert_eq!(pipe_pos_blank, pipe_pos_source);
        assert_eq!(pipe_pos_source, pipe_pos_underline);
    }

    #[test]
    fn diagnostic_includes_offset() {
        let output = format_diagnostic("x blah", "E", "msg", 2, 6);
        assert!(output.contains("(offset 2)"));
    }

    #[test]
    fn diagnostic_clamps_out_of_range_offsets() {
        let output = format_diagnostic("x\n", "E", "msg", 99_999, 199_999);
        assert!(output.contains("(offset 2)"));
        assert!(output.contains("--> 2:1"));
    }

    #[test]
    fn parse_error_formatting() {
        let err = parser::ParseError::new(
            "unexpected token",
            parser::span::Span::new(
                parser::span::Pos {
                    offset: 3,
                    line: 1,
                    column: 4,
                },
                parser::span::Pos {
                    offset: 5,
                    line: 1,
                    column: 6,
                },
            ),
        );
        let output = format_parse_error("ab cde fg", &err);
        assert!(output.contains("Parse error: unexpected token"));
        assert!(output.contains("(offset 3)"));
        assert!(output.contains("--> 1:4"));
        assert!(output.contains("^^"));
    }

    #[test]
    fn compile_error_formatting() {
        let err = compiler0::CompileError {
            message: "cannot assign to constant".to_string(),
            span: Some(parser::span::Span::new(
                parser::span::Pos {
                    offset: 7,
                    line: 1,
                    column: 8,
                },
                parser::span::Pos {
                    offset: 12,
                    line: 1,
                    column: 13,
                },
            )),
        };
        let output = format_compile_error("x = 5. x := 2", &err);
        assert!(output.contains("Compile error: cannot assign to constant"));
        assert!(output.contains("(offset 7)"));
    }

    #[test]
    fn compile_error_no_span() {
        let err = compiler0::CompileError {
            message: "something wrong".to_string(),
            span: None,
        };
        let output = format_compile_error("code", &err);
        assert_eq!(output, "Compile error: something wrong");
    }
}

fn value_to_string(value: object::Value) -> Option<String> {
    if !value.is_ref() {
        if value.is_fixnum() {
            let n = unsafe { value.to_i64() };
            return Some(n.to_string());
        }
        return None;
    }

    let header: &object::Header = unsafe { value.as_ref() };
    if header.object_type() == object::ObjectType::Str {
        let s: &object::VMString = unsafe { value.as_ref() };
        return Some(unsafe { s.as_str() }.to_string());
    }

    if header.object_type() == object::ObjectType::Symbol {
        let s: &object::VMSymbol = unsafe { value.as_ref() };
        return Some(format!("'{}", unsafe { s.as_str() }));
    }

    None
}

fn format_slot_object_shallow(
    vm: &mut VM,
    value: object::Value,
) -> Option<String> {
    if !value.is_ref() {
        return None;
    }

    let header: &object::Header = unsafe { value.as_ref() };
    if header.object_type() != object::ObjectType::Slots {
        return None;
    }

    let obj: &object::SlotObject = unsafe { value.as_ref() };
    let map: &object::Map = unsafe { obj.map.as_ref() };
    let mut parts = Vec::new();
    unsafe {
        for slot in map.slots() {
            if slot.is_assignment() {
                continue;
            }
            if parts.len() == SLOT_PRINT_LIMIT {
                parts.push("...".to_string());
                break;
            }
            let name = value_to_string(slot.name)
                .unwrap_or_else(|| format!("{:?}", slot.name));
            let (op, val) = if slot.is_assignable() {
                let offset = slot.value.to_i64() as u32;
                let val = obj.read_value(offset);
                (":=", val)
            } else {
                ("=", slot.value)
            };
            let rendered = match format_value_shallow(vm, val) {
                Some(text) => text,
                None => format!("{:?}", val),
            };
            parts.push(format!("{name} {op} {rendered}"));
        }
    }

    let ptr = value.ref_bits() as usize;
    Some(format!("({ptr:#x}){{ {} }}", parts.join(". ")))
}

fn format_value_shallow(vm: &mut VM, value: object::Value) -> Option<String> {
    if let Some(text) = value_to_string(value) {
        return Some(text);
    }
    if let Some(text) = try_to_string(vm, value) {
        return Some(text);
    }
    if !value.is_ref() {
        return None;
    }
    let header: &object::Header = unsafe { value.as_ref() };
    if header.object_type() == object::ObjectType::Slots {
        return Some("{ ... }".to_string());
    }
    None
}
