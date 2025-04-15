module.exports = grammar({
    name: "kette",
    extras: ($) => [
        /\s+/,
    ],
    rules: {
        program: ($) => repeat(choice($.definition, $.expression, $.comment)),
        definition: ($) =>
            choice(
                $.syntax_definition,
                $.word_definition,
                $.type_definition,
                $.constant_definition,
                $.symbol_definition,
                $.todo_definition
            ),
        // Word: : <name> <stackeffect> <body> ;
        word_definition: ($) =>
            seq(
                ":",
                $.identifier,
                $.stack_effect,
                repeat(choice($.expression, $.comment)),
                ";",
            ),
        // Syntax: @: <name> <body> ;
        syntax_definition: ($) =>
            seq(
                "@:",
                $.identifier,
                repeat(choice($.expression, $.comment)),
                ";",
            ),
        // Type: type: <body> ;
        type_definition: ($) =>
            seq(
                "type:",
                $.identifier,
                repeat(choice($.expression, $.comment)),
                ";",
            ),
        // Symbol: $: <name>
        symbol_definition: ($) =>
            seq(
                "$:",
                $.identifier
            ),
        // Constant: !: <name> <expression>
        constant_definition: ($) =>
            seq(
                "!:",
                $.identifier,
                $.expression
            ),
        // Todo: TODO: <text> ;
        todo_definition: ($) =>
            seq(
                "TODO:",
                /[^;]*/,
                ";"
            ),
        // Stack effect: ( <inputs> -- <outputs> )
        stack_effect: ($) =>
            seq(
                "(",
                alias(repeat($.identifier), "inputs"), // Inputs are words
                "--",
                alias(repeat($.identifier), "outputs"), // Outputs are words
                ")",
            ),
        // Expression: number, word, string, quotation, array, t, or f
        expression: ($) =>
            choice(
                $.identifier,
                $.number,
                $.string,
                $.quotation,
                $.array,
            ),
        // Quotation: [ <body> ]
        quotation: ($) =>
            seq(
                "[",
                repeat($.expression), // Only expressions, no comments inside
                "]",
            ),
        // Array: { <body> }
        array: ($) =>
            seq(
                "{",
                repeat($.expression), // Only expressions, no comments inside
                "}",
            ),
        // String: s" <text>"
        string: ($) => token(/s"[^"]*"/),
        // Comment: line or block comment
        comment: ($) =>
            choice(
                $.line_comment,
                $.block_comment,
            ),
        // Line comment: // <space> <text> until newline
        line_comment: ($) => /\/\/ .*/,
        // Block comment: /* <space> <text> */
        block_comment: ($) => /\/\*.*?\*\//,
        // Number: integers, binary (0b), hex (0x), or floats with optional underscores
        number: ($) =>
            token(choice(
                /[0-9]+(_[0-9]+)*/, // Integer
                /0b[01]+(_[01]+)*/, // Binary
                /0x[0-9a-fA-F]+(_[0-9a-fA-F]+)*/, // Hexadecimal
                /[0-9]+(_[0-9]+)*\.[0-9]+(_[0-9]+)*/, // Float
            )),
        // Identifier: any non-whitespace sequence, includes words like t, f, //, etc.
        identifier: ($) => token(/[^ \t\n\r\f\v]+/),
    },
});
