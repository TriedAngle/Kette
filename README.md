# Kette
Concatenative Language with extreme Late binding and parallelism.

currently still in very early construction of the VM

## Intuition
### Stack Based
this langauge is stack based, things are written mostly in "reverse polish notation"
```
10 20 + 30 * >string println
```
there are many stack shuffle words to make this simpler.
all methods have a stack effect which should make stack modifications clear

for exmaple:
```
// stack effect ( -- x x ) every method takes "self" implicitly
// in other forths that don't do that, one would write ( x -- x x )
: dup ( -- x x ) self self ; 
```
common shuffle words are:
- dup `x -- x x`
- over `x -- x y x`
- swap `x y -- y x`

TODO: write more

### Dispatching
all "words" you see, are really just messages that dispatch on the top element on the stack
TODO: write more

## Examples
see `tests/` for small snippets and their output
most of them also run already, you can run `run_tests.py` to validate that.

### Fizzbuss
```
(| fizzbuzz = : ( count -- )
    dup [ 3 % 0 = ] [ 5 % 0 = ] bi && [ 
        "fizzbuzz" println
    ] [ 
        dup 3 % 0 = [ "fizz" println ] [
        dup 5 % 0 = [ "buzz" println ] [
        dup >string println
    ] if ] if ] if
    1 - dup 0 > [ self fizzbuzz ] [ drop ] if ;
|) 15 swap fizzbuzz
```

### Vec2
```
// this snippet will print
// vec2[x: 36.7, y: 81.3]
// magnitude: 89.199663676496

(| vec2 = (|  
    parent* = std traits clonable .
    x := 0.0 . y := 0.0 .
    + = : ( other -- new ) 
        self [ [ x ] bi@ + ] [ [ y ] bi@ + ] 2bi self clone! ; .
    mag = : ( -- magnitude )
        self [ x ] [ y ] bi  [ 2.0 ^ ] bi@ + sqrt ; .
    >string = : ( -- string ) 
       "vec2[x: " self [ x ] [ y ] bi [ >string ] bi@ ", y: " swap "]" + + + + ; .
|) |) universe addTraitSlots

6.7 11.3 vec2 clone! 
30.0 70.0 vec2 clone! 
+ [ >string println ] keep
"magnitude: " print mag >string println
```

## Roadmap
### Repl
should be easy, also an eval function that takes string or file would be nice
### CFFI
libffi and libloading look interesting, this is necessary to get anything done.
### Error handling
currently there is no error handling.
the standard library should return `value/f` in case of `Some/None` as much as possible.
throw and catch will also be implemented.
the throw should throw <values> and a message, so we can register handlers like this:
```
(| dividedByZero = : ( -- ) ... ; |) [ ... ] withHandler
// this handler takes time as well
(| timeout = : ( time -- ) ... ; |) [ ... ] withHandler
```
the stack should be reset to the state when `withHandler` was called

Another idea would be handlers that handle inplace without any stack unwinding.

### Multithreading
most things are already in place,
what is necessary is exposing the primitives to the language,
and making current primitives thread safe.
- add `synchronized`
- expose language primitives for threads
- make GC and primitives fully thread safe

### Lowhanging Bytecode Optimization Fruits
currently the language is slow.
some optimizations I consider that should be easy too:
- collecting all messages and allocating stack correctly
- inlining quotations (if, dip, etc.)
- inlining methods, also add a force inline property
- tailcall optimization
- inline the lookup, lets do very simple cache for that for now

### Named Parameters
stack based code is neat, but complex code is hard.
named parameters would simplify this a lot
```
3 5 (|
    add = :: ( x y -- z ) x y + z<< .
|) add >string println
```

### Concurrency
while multithreading is nice already, and a good optimization,
concurrency often makes computation possible.
Consider implementing this in a way later, probably via actors over a thread pool

### Register based virtual machine
stack based is cool and all but register will be faster
making an SSA form and allocating from that shouldn't be too hard
but its not an immediate priority

### Split Compilation
it is nice to compile the same code block once,
but it can be optimized further by inlining primitives etc.
a solution is to create guards and deoptimize if not same "type"
or splitting the code and compile "per type"

### JIT compilation
at one point we should get turbo fast
