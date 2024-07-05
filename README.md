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

## Status (in order)
see src/preload for code
- [x] objects
- [x] garbage collector
- [x] repl
- [x] declare custom syntax/macros
- [x] implement arrays, comments, classes classes via macros
- [x] single dispatch
- [x] slot accessors and methods
- [ ] alien interface (c and rust wrapping)
- [ ] standard library and external library support
- [ ] variables
- [ ] gradual typing
- [ ] bytecode compiler
- [ ] inlining, tail-call and caching optimization
- [ ] rewrite garbage collector (one that supports threads, maybe allow different allocators and manual memory managemed?)
- [ ] images
- [ ] processes
- [ ] "selfhost"
- [ ] jit compilation

## Building
`cargo build`

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

### Define a macro
`@:` is used to define a macro/syntax word. they have to return a value. if they have "nothing to return", return `t`.
example: how comments are implemented:
```
@: !/ \ !/ @vm-skip-until drop t ;
!/ this is a commment !/
```
example: how arrays are implemented:
```
@: { \ } @vm-parse-until ;
{ 3 2 1 }
```

### Quotations
Quotations are a powerful concept. They are basically lamdas or anonymous functions in other langauge. In Kette they are also used for control flow. A quotation starts with `[` and end with `]`.
Quotations just contain normal code or other quotations. Quotations can be called with `call` or other words like `dip` and `keep`. Quotations after being defined just leave themselves on the stack where they are defined.
```
// prints 1 as `3 5 +` and 8 are equal
3 5 + 8 = [ 1 . ] [ 0 . ] if 

// prints 7 as 1 is taken from the stack 
// 2 3 * is executed, 1 is added back to the stack and 6 1 + is executed
2 1 [ 3 * ] dip + . 
```

Together with quotations and macros we have a very poweful framework to work with, for example `match` is just a word that iterates over arrays and executes its quotation.
```
: match ( ? array -- ) ... ; !/ implementation hidden for readability !/

: n| ( a n -- ? ) % 0 = ;

: fizzbuzz ( num -- ) 
    dup {
        { [ 15 n| ] [ s" FizzBuzz" utf8. ] }
        { [ 3 n| ] [ s" Fizz" utf8. ] }
        { [ 5 n| ] [ s" Buzz" utf8. ] }
        { [ drop t ] [ dup . ] }
    } match dup 0 > [ 1 - fizzbuzz ] [ drop ] if ;

30 fizzbuzz !/ does fizzbuzz for 30 to 0 !/
```

### Types
Types are data containers whose fields can be accessed accessors.
```
type: pos x y ;    !/ define tuple pos with slots x and y !/
10 5 pos boa        !/ construct a new object from the tuple class by "order of arguments"
dup x>> .           !/ prints 10 !/
dup 420 swap x<<
dup x>> .           !/ prints 420 !/
333 >>y y>> .       !/ prints 333 !/
```
Types can have methods
```
method: to-string ( obj -- string )

type: shape x y ;
m: shape to-string drop s" shape" ;

type: cat name ;
m: cat to-string [ s" cat with name " ] dip name>> bytearray-concat ;

420 69 shape boa to-string utf8. !/ prints: "shape" !/
s" Steve" cat boa to-string utf8. !/ prints "cat with name Steve" !/
```

### Common Stack Operations
```
: drop ( a -- )
: dropd ( a b -- b )
: dup ( a -- a a ) 
: dupd ( a b -- a a b )
: over ( a b -- a b a )
: swap ( a b -- b a )
: swapd ( a b c -- b a c )
: rot ( a b c -- b c a )
: -rot ( a b c -- c a b )
: dip ( x q -- x ) !/ takes x from the stack, executes q (quotation) and puts x at the top of the stack !/
: keep ( x q -- x ) !/ like dip but executes q with x too !/
: call ( q -- ) calls a quotation

!/
arithmetic: + - * / %  
logic: = and or not if when unless
bits: bit& bit| bit^ bit<< bit>> bit~
!/
```

see src/preload for more