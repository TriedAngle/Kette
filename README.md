# Kette

Kette is a message‑passing language with a compact object model and a custom
bytecode VM. The syntax is inspired by Self: everything is a message send,
objects are dictionaries of slots, and delegation is explicit via parent slots.

This README describes the current language shape and syntax as implemented in
the parser and core library.

## Core Concepts

- **Messages, not functions**: `receiver selector` is a message send.
- **Unary / binary / keyword messages**: precedence is Self‑style.
- **Objects are slot dictionaries**: slots can be constants, assignable, or
  parent links for delegation.
- **Blocks are closures**: `[ ... ]` with optional `| args |`.
- **None/true/false are objects**: `None` is the canonical empty value.
- **Globals at top level**: module-aware compile-time resolution is strict; an
  unresolved global is a compile error.

## Syntax Overview

### Literals

```
123
3.14
"hello"
true
false
None
```

### Message syntax

```
receiver unarySelector
receiver + argument
receiver key1: arg1 Key2: arg2
```

### Objects and slots

Objects are defined with `{ ... }`. Slots are separated by `.`.
If the body contains any expressions other than assignments, it is parsed as
an executable object (method body) rather than a pure slot dictionary.

Example (executable object body):

```
Log = {
    prefix = "[log] ".
    message = "ready".
    (prefix + message) println
}.
```

```
Point = {
    x := 0.
    y := 0.
    moveByX: dx Y: dy = { self x: (self x + dx). self y: (self y + dy) }.
    toString = { "(" + ((self x) toString) + ", " + ((self y) toString) + ")" }.
}.

Point moveByX: 10 Y: 20.
Point moveByX: 40 Y: 20.
Point x
```

- `=` defines a constant slot or method.
- `:=` defines an assignable slot.

### Delegation (parent slots)

```
Object extend: true With: {
    parent* = Boolean.
    toString = { "true" }.
}.
```

The `parent*` slot marks a delegation link. Any slot name ending with `*` is
treated as a parent slot by the runtime. The core library uses this to define
the inheritance structure (see `core/init.ktt`).

### Prototype objects and cloning

Objects are prototypes. You can use a prototype directly or clone it to create
an independent object with the same slots. Shared behavior is typically modeled
by adding a parent slot (e.g., `parent* = SomeTrait.`) so lookup delegates to a
common prototype.

### Slot accessors

- Getter: `self x`
- Setter: `self x: value`

Accessors are messages, so the receiver must be explicit.

### Blocks

```
[ 1 + ] call

[ | x y | x + y ] call: 2 With: 3
```

### Cascades

```
obj foo; bar; baz: 1
```

### Returns

```
^ expr
```

## Methods ("functions")

Kette does not have standalone functions. Behavior lives in object slots (methods)
and is invoked by sending messages.

```
Math = {
    double: x = { x + x }.
    fortyTwo = { 40 + 2 }.
}.

Math double: 21.
Math fortyTwo
```

- A unary method call is `receiver selector`.
- A keyword method call is `receiver name: arg ...`.
- Method execution keeps `self` as the receiver object.

## Modules and Global Resolution

The module system is designed to be CL-like in spirit: globals are resolved in
the module environment known at compile time, and imported names behave like
aliases to exported bindings.

### Module operations

```
Module open: 'Lib.
Module export: 'Hello.
Module use: 'Other.
Module use: 'Other As: { answer = 'otherAnswer }.
```

Equivalent low-level primitives are available on `VM`:

```
VM _ModuleOpen: 'Lib.
VM _ModuleExport: 'Hello.
VM _ModuleUse: 'Other.
VM _ModuleUse: 'Other As: { answer = 'otherAnswer }.
```

### Current semantics

- `Module export:` may appear before the definition; defining later in the same
  compilation unit works.
- `Module use:` imports exported names directly; `As:` is only needed for
  renaming or collision avoidance.
- Top-level unresolved globals in non-`user` modules are compile errors.
- Imported names are write-through aliases (assigning via an import updates the
  source module binding).
- Method global lookup uses the defining module context (not caller module).
- There is no legacy global fallback path: globals must resolve through module
  bindings/imports.

### Example

```
Module open: 'Lib.
Module export: 'Hello.
Hello := 41.

Greeter := {
    greet = { Hello _FixnumAdd: 1 }.
}.
Module export: 'Greeter.

Module open: 'App.
Module use: 'Lib.
Greeter greet
```

The full commented walkthrough is in `core/module_resolution_demo.ktt`.

## Running Script Tests

For strict module mode, load `core/init.ktt` first, then test scripts:

```bash
cargo run -p vm -- core/init.ktt tests/disposable_using.ktt
cargo run -p vm -- core/init.ktt tests/file_disposable.ktt
cargo run -p vm -- core/init.ktt tests/mitternacht.ktt
```

Extra output/file-loading demo previously in init lives in:

- `tests/init_runtime_demo.ktt`

## FizzBuzz Example

```
i := 1.

[ i <= 15 ] whileTrue: [
    (i % 15) == 0 ifTrue: [ "fizzbuzz" println ] IfFalse: [
        (i % 3) == 0 ifTrue: [ "fizz" println ] IfFalse: [
            (i % 5) == 0 ifTrue: [ "buzz" println ] IfFalse: [
                i toString println
            ]
        ]
    ].
    i := i + 1
].
```

## Where to Look Next

- VM design doc: `DESIGN.md`
- Core library: `core/init.ktt`
- Parser and AST: `parser/`
- Bytecode + interpreter: `bytecode/`, `vm/`
- Object model + lookup: `object/`
- GC/heap: `heap/`

## Editor Support

- Neovim integration: `editor/README.md`
- VSCode integration and extension packaging: `editor/vscode/README.md`

## Status

The VM and language are under active development. APIs and syntax may change.
