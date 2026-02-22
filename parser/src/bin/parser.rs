use parser::ast::to_dot;
use parser::lexer::Lexer;
use parser::parser::Parser;
use std::env;
use std::fs;
use std::process::exit;

fn main() {
    let mut args = env::args().skip(1);
    let input = match args.next() {
        Some(v) => v,
        None => {
            eprintln!("usage: parser <input> [output]");
            exit(2);
        }
    };
    let output = args.next();
    if args.next().is_some() {
        eprintln!("usage: parser <input> [output]");
        exit(2);
    }

    let source = match fs::read_to_string(&input) {
        Ok(s) => s,
        Err(err) => {
            eprintln!("failed to read {}: {}", input, err);
            exit(1);
        }
    };

    let lexer = Lexer::from_str(&source);
    let mut parser = Parser::new(lexer);
    let mut exprs = Vec::new();
    let mut errors = Vec::new();
    for result in parser.by_ref() {
        match result {
            Ok(id) => exprs.push(id),
            Err(err) => errors.push(err),
        }
    }
    let arena = parser.into_arena();

    if !errors.is_empty() {
        for err in errors {
            eprintln!("Parse error: {}", err);
        }
        exit(1);
    }

    let dot = to_dot(&arena, &exprs);
    if let Some(output) = output {
        if let Err(err) = fs::write(&output, dot) {
            eprintln!("failed to write {}: {}", output, err);
            exit(1);
        }
    } else {
        print!("{}", dot);
    }
}
