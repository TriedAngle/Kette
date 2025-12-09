# Kette
Concatenative Language with extreme Late binding and actor concurrency.

currently still in very early construction of the VM

## Examples
see `tests/` for small snippets

## Roadmap
essentially which tests already work
not full in order of requirements but mostly.
a standard library getting build step by step is also necessary for most of these tests

**not much reason this is not there yet, Parser -> Bytecode compilation missing**
- [ ] repl
- [ ] tracing, a nice tracing library is needed, mostly stack based, should handle parallel stuff

**these would already work**, *but comment parsing is missing*
- [x] raw integers
- [x] raw printing

**requires nicer names**
- [ ] printing
- [ ] integers

**requires callstack**
- [ ] floats, float implementation is also not fully implemented yet, TODO: test missing
- [ ] big integers, not implemented yet, TODO: test missing,

**requires object parsing**
- [ ] printing
- [ ] assignables 
- [ ] constants
- [ ] custom parsers, TODO: test missing

**requires quotations**
- [ ] fizzbuzz
- [ ] flow

**requires parent mechanism**
- [ ] parent lookup, TODO: test missing
- [ ] assignable parent, TODO: test missing
- [ ] inheritance, TODO: test missing

**requires named parameters**
- [ ] named parameters

**mostly implemented, std and api missing**
- [ ] locking, TODO: test missing
- [ ] multithreading, TODO: test missing

**not fully implemented yet, object monitor and header missing**
- [ ] synchronized, TODO: test missing

