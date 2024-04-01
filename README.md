# Kette

stack oriented language for modern systems

## Goals
- a live environment (lisp, smalltalk, SELF)
- lisp-like macros (parsing words)
- prototype based object system inspired by SELF
- gradual typing
- manual memory management with zig-style allocators and RAII
- opt-in garbage collection
- erlang inspired threading/process model (will take a while)
- most of the language written within the language (parsing words)

## Status (mostly ordered)
- small demo interpreter repl that can define new words and use builtin words but it can't do much else (lacks object system)
- [x] allocators
- [x] objects
- [ ] bytecode compiler
- [ ] rewrite VM for new object and allocator system
- [ ] interprete bytecode
- [ ] inlining and tail-call optimization
- [ ] images
- [ ] "selfhost"
- [ ] variables
- [ ] gradual typing
- [ ] proceses
- [ ] jit compile bytecode

## Building
Only requirement is the c11 gnu standard (including "threads.h") and make (nmake on windows).
Operating system is automatically detected (TODO crosscompile)
- building: `make`
- building with avx2: `make AVX2=1` (if you build normally before, clean first `make clean`)
- build and run `make run` (or `make && ./kette`)

## Basics
The language is stack based (variables will be supported) so expressions are written in reverse polish notation.
Whitespaces, tabs and `\n` separate words from each other.
### Addition
`5 5 + .` => prints `10` 
### Define a word
words start with `:` and end with `;`. After `:` comes the word name and after the name comes an optional stack effect. `( a b -- c )` is called a stack effect. this means the word takes `a` and `b` from the stack and pushes `c` onto it.

```
: +1 ( n -- n+1 ) 1 + ;`

5 +1 +1 +1 . // prints 8
```

### Quotations
Quotations are a powerful concept. They are basically lamdas or anonymous functions in other langauge. In Kette they are also used for control flow. A quotation starts with `[` and end with `]`.
Quotations just contain normal code or other quotations. Quotations can be called with `call` or other words like `dip` and `keep`. Quotations after being defined just leave a pointer on the stack where they are defined.
```
// prints 1 as `3 5 +` and 8 are equal
3 5 + 8 = [ 0 . ] [ 1 . ] if 

// prints 7 as 1 is taken from the stack 
// 2 3 * is executed, 1 is added back to the stack and 6 1 + is executed
2 1 [ 3 * ] dip + . 
```

### Builtin words
```
// Stack words
: drop ( a -- )
: dropd ( a b -- b )
: dup ( a -- a a ) 
: dupd ( a b -- a a b )
: over ( a b -- a b a )
: swap ( a b -- b a )
: swapd ( a b c -- b a c )
: rot ( a b c -- b c a )
: -rot ( a b c -- c a b )
: dip ( ... a q -- a ) // takes a from the stack, executes q (quotation) and puts a at the top of the stack
: call ( q -- ) calls a quotation

// arithmetic: + - * / %  
// logic: = and or not if
// bits: bit& bit| bit^ bit<< bit>> bit~

// OTHER
: . ( n -- ) prints a number to stdout
: .q ( q -- ) prints the quotation to stdout
: @ ( p -- v ) dereferences 8 byte pointer
: ! ( v p -- ) writes v to the location the pointer is pointing to
: let-me-cook ( -- vm ) returns a pointer to the actual VM
: LATEST ( -- ) pointer to the latest word
: word>quot ( w -- q ) takes a word pointer and pushes it's a quotation pointer of the word body onto the stack

// syscall0 up to syscall4 perform syscalls. n stands for the amount of parameters other than the syscall id
: syscall0 ( id -- res )
: syscall1 ( id p1 -- res )
: syscall2 ( id p1 p2 -- res )
: syscall3 ( id p1 p2 p3 -- res )
: syscall4 ( id p1 p2 p3 p4 -- res )
```