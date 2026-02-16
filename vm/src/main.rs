use clap::Parser as ClapParser;
use std::{
    fs,
    io::{self, Write},
    process,
};

use heap::HeapSettings;
use parser::{Lexer, Parser};

use vm::{compiler0, interpreter, materialize, special, VM};

#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Input source files to execute in order
    #[arg(required = false, help = "The .ktt files to execute")]
    files: Vec<String>,

    /// Start REPL after executing files (default if no files)
    #[arg(long, help = "Force REPL mode after file execution")]
    repl: bool,
}

fn main() {
    let cli = Cli::parse();

    let mut vm = special::bootstrap(HeapSettings::default());

    for filename in &cli.files {
        let source_code = match fs::read_to_string(filename) {
            Ok(content) => content,
            Err(err) => {
                eprintln!("Error reading file '{}': {}", filename, err);
                process::exit(1);
            }
        };

        match execute_source(&mut vm, &source_code) {
            Ok(value) => {
                print_value(&mut vm, value);
            }
            Err(err) => {
                eprintln!("Error executing {}: {}", filename, err);
                process::exit(1);
            }
        }
    }

    if cli.repl || cli.files.is_empty() {
        run_repl(&mut vm);
    }
}

fn run_repl(vm: &mut VM) {
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

                match execute_source(vm, &input_buffer) {
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

fn execute_source(vm: &mut VM, source: &str) -> Result<object::Value, String> {
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

    let code_desc = compiler0::Compiler::compile(&exprs)
        .map_err(|e| format_compile_error(source, &e))?;
    let code = materialize::materialize(vm, &code_desc);

    interpreter::interpret(vm, code)
        .map_err(|e| format_located_error(source, &e))
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

fn format_runtime_error(err: &interpreter::RuntimeError) -> String {
    match err {
        interpreter::RuntimeError::MessageNotUnderstood {
            receiver,
            message,
        } => {
            let msg = value_to_string(*message)
                .unwrap_or_else(|| format!("{:?}", message));
            let recv = value_to_string(*receiver)
                .unwrap_or_else(|| format!("{:?}", receiver));
            format!(
                "MessageNotUnderstood {{ receiver: {recv}, message: {msg} }}"
            )
        }
        interpreter::RuntimeError::UndefinedGlobal { name } => {
            format!("UndefinedGlobal {{ name: {name} }}")
        }
        other => format!("{:?}", other),
    }
}

fn format_located_error(
    source: &str,
    err: &interpreter::LocatedRuntimeError,
) -> String {
    let error_msg = format_runtime_error(&err.error);

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

fn format_diagnostic(
    source: &str,
    kind: &str,
    message: &str,
    start: usize,
    end: usize,
) -> String {
    let (line, col, line_start) = offset_to_line_col(source, start);
    let line_end = source[line_start..]
        .find('\n')
        .map(|i| line_start + i)
        .unwrap_or(source.len());
    let source_line = &source[line_start..line_end];

    // Compute underline span (clamp to current line)
    let underline_start = start.saturating_sub(line_start);
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

    None
}
