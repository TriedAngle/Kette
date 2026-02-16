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

## Status

The VM and language are under active development. APIs and syntax may change.
