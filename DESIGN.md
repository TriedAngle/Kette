# Kette VM Design Notes (High-Level)

This document describes the current runtime architecture at a high level so a
new contributor can orient quickly and jump into the codebase. It is based on
the current Rust implementation, not the README.

## Big Picture

The project is a small object system + bytecode VM with a custom heap and
garbage collector. The core crates are:

- `object/`: tagged value representation, object layouts, maps/slots, lookup.
- `heap/`: Immix-style garbage collector and allocation.
- `vm/`: interpreter, compiler, materializer, bootstrap of special objects.
- `bytecode/`: bytecode encoding, decoding, and source map format.
- `parser/`: lexer/parser producing AST for the compiler.

## Quick Syntax Sketch

This document is runtime-focused, but new contributors usually need a minimal
syntax map to connect parser/compiler internals with source examples.

- **Everything is a message send**:
  - Unary: `receiver size`
  - Binary: `receiver + arg`
  - Keyword: `receiver at: 0 Put: 42`
- **Objects are slot dictionaries**: `{ ... }` with `.` between slots/exprs.
- **Slots**:
  - Constant slot: `name = expr`
  - Assignable slot: `name := expr`
  - Parent/delegation slot: `parent* = SomeProto`
- **Blocks/closures**: `[ ... ]` and `[ | x y | ... ]`.
- **Returns**: `^ expr`.
- **Cascades**: `obj foo; bar: 1; baz`.

Compilation notes:

- Top-level forms are compiled as module/global operations.
- Object literals with executable bodies compile as method objects.
- Methods are stored as code-bearing maps/objects; ordinary data objects are
  map-plus-inline-values.

## Tagged Values and Pointer Tagging

All values are 64-bit tagged words (`object/src/value.rs`). The low two bits
encode the tag, and all heap pointers are at least 4-byte aligned so the low
bits are free.

- Fixnum: low bit 0 (`...xxxxx0`), 63-bit signed integer.
- Reference: low bits `01`, points to heap object header.
- Header: low bits `11`, only used for the first word of a heap object.

```
Tagged 64-bit word (LSB on the right)

  [........ payload ........][t1 t0]

  t0=0            -> Fixnum (signed 63-bit)
  t1..t0 = 01     -> Reference (heap pointer, 4-byte aligned)
  t1..t0 = 11     -> Header word (object start only)
```

Key helpers:

- `Value::is_fixnum`, `Value::from_i64`, `Value::to_i64`.
- `Value::is_ref`, `Value::from_ptr`, `Value::as_ref`.
- `Value::is_header` is used by the GC to sanity-check object headers.

## Object Header and GC Flags

Every heap object starts with an 8-byte header (`object/src/header.rs`):

```
byte 0: [tag:2=0b11][object_type:6]
byte 1: flags (atomic) - remembered, pinned, escaping, escaped
byte 2: age (atomic)   - GC generation/epoch
bytes 3..7: reserved
```

The header encodes the object type and GC bookkeeping. The low two bits
match the `HEADER_TAG` so a header word can be detected from a `Value`.

## Object Layouts

Layouts are defined in `object/src/objects.rs` and `object/src/map.rs`.
Key types:

- `SlotObject`: ordinary object with a hidden map and inline assignable values.
- `Map`: a shape/descriptor containing slots and code metadata.
- `Array`, `ByteArray`, `Code`, `Block`, `BigNum`, `VMString`, `Ratio`, `Float`.

Examples (all are contiguous, header first):

```
SlotObject:
  [Header][map:Value][inline values...]

Map:
  [Header][map:Value][code:Value][flags:u64][slot_count:u32][value_count:u32]
  [Slot0][Slot1]...

Code:
  [Header][constant_count:u32][register_count:u16][arg_count:u16]
  [bytecode_len:u32][temp_count:u16][source_map_len:u16]
  [constants...][bytecode bytes...][source map bytes...]

Block (closure):
  [Header][map:Value][env:Value][self:Value]
```

Primitive-ish objects like `Array`, `ByteArray`, `VMString`, `Float` do not
carry a map pointer; method lookup is forwarded to special trait objects.

## Maps, Slots, and the Parenting System

Maps define the slot layout and behavior of objects (`object/src/map.rs`,
`object/src/slot.rs`). A `Slot` holds:

- `flags` (constant/assignable/assignment/enumerable/parent)
- `name` (symbol value)
- `value` (either constant value or byte offset into the object body)

Slots of interest:

- `CONSTANT`: value stored in the map directly.
- `ASSIGNABLE`: value is an offset where the real data lives.
- `ASSIGNMENT`: write access paired with `ASSIGNABLE`.
- `PARENT`: slot is used to walk parent links (prototype delegation).

Parenting is implemented by marking slots with `PARENT` and then walking those
links during lookup. Any slot name ending with `*` is treated as a parent slot
by the runtime. Parents can be constant (value stored in the slot) or
assignable (value stored inside the object body at an offset).

## Prototype Objects and Cloning

Objects are prototypes: behavior is shared by delegation rather than classes.
The common pattern is to define a prototype with methods and then:

- **Clone** it to get a fresh object with the same map and inline values.
- **Attach parents** via `PARENT` slots (often named `parent*`) so lookup
  delegates to shared behavior.

Cloning is implemented at the VM level by allocating a new `SlotObject` and
copying the inline values while keeping the same map. Parent slots are just
regular slots with the `PARENT` flag, so they participate naturally in lookup
and cache validity checks.

## Lookup and Message Dispatch

Lookup is in `object/src/lookup.rs`:

- For `SlotObject` and `Map`, it scans slots in the map and then follows any
  parent slots (with cycle detection).
- For primitive types without a map pointer, it forwards to the trait object
  stored in `SpecialObjects` (e.g., `array_traits`, `string_traits`).
- A `VisitedLink` stack list prevents infinite cycles when parents loop.

`LookupResult` returns the holder, slot, and slot index plus a flag indicating
whether a dynamic (assignable) parent was traversed, which is important for
inline caching correctness.

Message send and resend logic lives in `vm/src/interpreter.rs`:

- `Send` does a lookup on the receiver and dispatches the slot.
- `Resend` looks up via parent links from the current method holder.
- `DirectedResend` restricts parent traversal to a named parent slot.

If a slot value is a `Code` or a method object (map with code), it is invoked;
otherwise the slot value is returned.

## Special Objects and Traits

`object/src/special.rs` defines a struct of well-known objects and trait maps
used by lookup and primitives. These are created during bootstrap in
`vm/src/special.rs`:

- `map_map` is self-referential and describes maps themselves.
- `None`, `true`, `false`, and the root `Object` are allocated early.
- Trait objects for primitives (Array, ByteArray, String, Fixnum, etc.) are
  built by attaching primitive method objects to their maps.
- The global dictionary is a `SlotObject` whose map holds constant slots for
  globals.

## Compiler Pipeline (AST -> CodeDesc)

The compiler is in `vm/src/compiler0.rs`. It takes parser AST and produces
`CodeDesc` containing:

- Bytecode bytes
- Constant pool entries (values, strings, nested code, maps)
- Register count, argument count, temp count, feedback count
- Source map bytes

Key stages:

1. Prescan locals to discover variables.
2. Capture analysis to mark closed-over variables.
3. Emit bytecode and source map entries.

At top level, assignments always compile to global assoc stores (dictionary
entries), regardless of name casing.

Captures are assigned temp array indices (`temp_count`), and access is encoded
as `LoadTemp`/`StoreTemp` instructions.

## Bytecode and Source Maps

Bytecode is defined in `bytecode/src`:

- `Instruction` enumerates ops (load/store, send, create, jumps, temp access).
- `BytecodeBuilder` writes compact bytecode and auto-emits `Wide`/`ExtraWide`
  prefixes when operands exceed 8-bit.
- `SourceMapBuilder` emits a delta-encoded VLQ stream that maps bytecode PCs
  to source character ranges. The interpreter uses `source_map_lookup` to
  report error locations.

## Interpreter Runtime Model

The interpreter is in `vm/src/interpreter.rs`.

- A `Frame` holds `code`, `pc`, registers, and a `temp_array` for captured vars.
- The accumulator (`acc`) is the implicit operand/result register.
- Registers are in a `Vec<Value>`; register 0 is `self`.

Instruction execution uses helpers like `dispatch_send`, `dispatch_resend`,
`create_object`, and `create_block`.

## Tail-Recursive Self Calls

Kette has a targeted tail-call optimization for **simple self-recursive
methods**.

- The compiler marks method maps as tail-call-eligible when it can detect a
  tail-position send to the same selector on `self`
  (`vm/src/compiler0.rs`, `method_tail_call_eligible`).
- `_EnsureTailCall` can be used to require that a method is eligible; otherwise
  compilation fails with `"method is not tail-call eligible"`.
- At runtime, the interpreter reuses the existing method frame instead of
  pushing a new one when the guard conditions hold
  (`vm/src/interpreter.rs`, `try_tail_recursive_self_call`).
- This optimization is intentionally conservative: it is not a general proper
  tail-call implementation for arbitrary call graphs.

## Temp Arrays and Runtime Capturing

Captured variables are stored in heap-allocated temp arrays. Temp arrays are
regular `Array` objects with a special layout:

- Index 0 holds the parent temp array (or `None`).
- Indices 1..N are the actual captured values.

This supports nested closures: `array_idx` in bytecode selects which temp array
in the chain to access (0 = current, 1 = parent, ...). Access helpers:

- `alloc_temp_array` allocates an `Array` with parent link and None-initialized
  slots.
- `get_temp_array` walks the parent chain based on `array_idx`.
- `LoadTemp` and `StoreTemp` read/write `idx + 1` within the array.

Blocks (`object::Block`) capture the temp array (`env`) and receiver (`self`).

## Allocation and Materialization

Runtime allocation wrappers are in `vm/src/alloc.rs`. These allocate objects
on the heap and initialize their headers and inline fields.

The compiler output (`CodeDesc`) is converted into real heap objects by the
materializer (`vm/src/materialize.rs`):

- Recursively materializes constants and nested code/maps.
- Interns strings to `VMString` objects.
- Resolves globals (`Assoc`) via the dictionary, creating new assocs on demand.
- Writes a `Code` object with constants, bytecode, and source map.

The materializer uses a local root set to keep intermediate values live across
allocations.

## Image Save/Load (Heap Snapshotting)

The VM can persist and restore a full runtime image (`vm/src/image.rs`, wired
through CLI flags in `vm/src/main.rs` as `--save-image` / `--load-image`).

What is saved:

- Heap settings and full heap byte range.
- Block/line allocator metadata and GC tracking counters.
- Large-object allocations and bytes.
- Special object roots, assoc map, dictionary, current module.
- Interned symbol table, module states/imports/exports.
- Next platform-thread id.

Save/load contract and safety checks:

- Save forces a major GC first, then validates preconditions again.
- Save is rejected unless GC is idle and exactly one VM thread is active.
- Save is rejected when platform thread handles are still registered.
- Load validates image magic/version and primitive ABI hash.
- Heap and large-object memory are mapped back at their recorded addresses.

Practical implication: image files are runtime-coupled artifacts (same primitive
set/ABI, compatible memory mapping environment), not a portable interchange
format.

## Garbage Collector (Sticky Immix)

The GC is a sticky Immix-style allocator in `heap/src/heap.rs`:

- Heap is split into blocks and lines (coarse + fine-grained).
- Bump allocation happens in free or recycled blocks; line marks track liveness.
- Large objects are mmap'd and tracked separately.
- Minor GC marks young objects; major GC scans all objects.

Pinning and defragmentation:

- Pinning is "free" in the sense that minor collections do not relocate
  objects; a pinned flag just tells the collector to keep an object at its
  current address when relocation is attempted.
- Major GC performs opportunistic evacuation (not fully implemented yet),
  so objects can be relocated then, while pinned objects remain in place.
- Sticky Immix still defragments because it can recycle or evacuate whole
  lines/blocks around pinned objects; the allocator then prefers clean lines
  and free blocks, compacting around pinned islands.

Important pieces:

- `TraceFn`: a VM-provided function that visits all `Value` fields of an object.
- `RootProvider`: VM-specific root enumeration at safepoints.
- `HeapProxy`: thread-local allocator with a remembered set and write barrier.
- `Header::age` is used to mark objects during the current GC epoch.

Minor GC:

- Only objects with age 0 are considered young.
- Remembered set tracks old objects that reference young ones.
- Marking sets line epoch; sweeping recycles or frees blocks based on live lines.

Major GC:

- Advances the global epoch.
- Marks all reachable objects with opportunistic evacuation (see below).
- Sweeps all blocks; records live line count per block for the next cycle.
- Large objects are retained or unmapped based on header age.

### Epoch Wraparound

The epoch counter is a `u8` starting at 1 (0 is reserved as "uninitialized").
When the counter wraps from 255 back to 1 the coordinator thread resets the
entire line bytemap to zero with a non-atomic `memset` — safe because all
mutator threads are stopped at this point.  Subsequent marking from the root
set rebuilds the bytemap from scratch under the new epoch.

```
Heap layout (Immix)

  Heap
  +-----------------------------------------------------------+
  | Block 0 | Block 1 | Block 2 | ...                         |
  +-----------------------------------------------------------+

  Each Block is split into Lines:
  +-----------------------------------------------------------+
  | line | line | line | line | ...                           |
  +-----------------------------------------------------------+
  ^ mark bitmap stores epoch per line (0 = dead/unvisited)
```

### Opportunistic Evacuation (Defragmentation)

During every major GC the coordinator identifies *sparse* blocks (blocks whose
live line count from the previous cycle is greater than zero but below 25% of
the block's capacity) and marks them as **evacuation candidates**.  GC threads
then evacuate live objects out of candidate blocks into fresh to-space, leaving
the old locations dead so the sweep naturally frees entire candidate blocks.

**Per-thread to-space (`EvacBuf`).**  Each GC thread owns a private bump
allocator (`EvacBuf`).  When the current block fills it claims a new one
directly from the heap with `request_block()` (thread-safe CAS on the fresh
cursor).  No two threads ever write into the same block.

**`SizeFn`.**  Alongside `TraceFn`, the VM provides a `SizeFn` pointer
(`vm/src/lib.rs :: object_size`) that returns the total byte size of any heap
object.  Returning 0 signals "skip evacuation" (used for `Alien` objects whose
ownership semantics are opaque).

**ESCAPING / ESCAPED handshake.**  When a thread decides to evacuate an object
it uses the header flags to coordinate with any other thread that may reach the
same object concurrently:

```
thread that wins:                       thread that loses:

pre-alloc to-space                      fetch_or(ESCAPING) → already set
fetch_or_acqrel(ESCAPING) → was clear   undo pre-alloc (if any)
copy bytes to new location              spin until ESCAPED is observed
stamp new copy with current epoch       read forwarding ptr from old+8
clear ESCAPING|ESCAPED on new copy      update own *value reference
mark_object_lines(new copy)
write fwd ptr at old_ptr + 8
fence(Release)
fetch_or(ESCAPED)
update own *value reference
push new copy to worklist
```

Pre-allocating to-space *before* claiming ESCAPING is the key invariant: once
ESCAPING is visible any spinning thread is guaranteed that ESCAPED will follow
— no fallback path is needed.

**Forwarding pointer.**  The forwarding address is stored at
`old_ptr + size_of::<Header>()` (offset 8).  All heap objects are at least
16 bytes, so this word is always available.

**Field and root fixup.**  Inter-object references are fixed up during marking:
`trace_fn` visits the *new copy's* fields while draining the worklist, so any
field that points to another evacuated object is updated via the normal
`visit` closure (`*value = Value::from_ptr(fwd)`).  Root pointers (stack
roots, VM globals, interned symbols) are fixed up in a dedicated pass in
`HeapProxy::execute_gc_with_reason` immediately after the parallel marking
phase completes: every root is inspected for the `ESCAPED` flag and forwarded
if set.

**Line marking.**  Only the *new copy's* lines are marked with the current
epoch.  The old location's lines are never marked, so after the sweep the
candidate block shows zero live lines and is returned to the free list
automatically — no explicit "unmark" step is needed.

**Pinned objects.**  Objects with the `PINNED` flag are never evacuated; they
fall through to the ordinary in-place marking path regardless of whether their
block is a candidate.

The VM integrates with GC via `vm/src/lib.rs`:

- `trace_object` describes object graph edges for each object type.
- `object_size` returns the byte size of each object type (0 for Alien).
- `VM` implements `RootProvider` for global roots and interned symbols.

## Multithreading Model

Threading is shared-heap, multi-VM-proxy:

- `SharedVMData` owns heap, module table, intern table, and global runtime
  state.
- Each OS thread gets a `VMProxy` with its own `HeapProxy` and interpreter
  state, all pointing at the same `SharedVMData`.
- `VM _SpawnPlatform: [ ... ]` creates an OS thread and runs a compiled block;
  `VM _ThreadJoin:` waits and returns its value.

Thread coordination primitives:

- Thread tokens: `VM _ThreadCurrent`.
- Parking API: `VM _ThreadPark`, `VM _ThreadParkForMillis:`,
  `VM _ThreadUnpark:`.
- Cooperative yield: `VM _ThreadYield`.

Synchronization/monitors:

- Object monitors are re-entrant and tied to object headers.
- Fast uncontended path uses thin-lock states in header flags.
- Contention inflates to monitor records (`Mutex + Condvar`) with owner token +
  recursion depth.
- Language-level helpers route through these primitives (`synchronized:` and
  monitor ops in core/init + vm primitives).

## FFI and Proxy Model

The VM provides low-level FFI primitives on `Alien` objects plus `libffi`-backed
dynamic calls.  The key pieces are:

- `Alien` wraps raw pointer + optional size metadata.
- Shared libraries and symbols are loaded with `_LibraryOpen:` and `_LibrarySym:`.
- Dynamic foreign calls use `_AlienCallWithTypes:Args:ReturnType:` where
  parameter and return types are protocol descriptor objects.
- CType descriptors are ordinary user-space objects with ordered slots:
  `impl`, `size`, `align`, then optional field descriptors (for struct layout).
  Scalar descriptors start with a scalar tag in `impl`; struct descriptors use
  `impl = None` and place field CType descriptors after `align`.
- The VM lazily caches libffi type metadata by writing an internal cache handle
  into the descriptor's `impl` slot.
- Struct-by-value interop is supported through descriptors: struct arguments are
  supplied from `ByteArray`/`Alien` backing bytes; struct returns are materialized
  as `ByteArray` values.
- User-space code can wrap either `Alien` or `ByteArray` in a single `Proxy`
  object and dispatch through a shared typed memory API.

### Stale pointer safety (not implemented)

The current design does **not** implement stale-pointer liveness checks for
foreign pointers.  A stored `Alien` pointer may become invalid if external code
frees or unloads the underlying resource.

This is an explicit current limitation. A future design could add an optional
liveness mechanism (for example: generation/epoch handles, indirection tables,
or explicit proxy kill-state similar to Self's dead/live proxy model), but no
such mechanism is required by the current runtime contract.

## Where to Start in the Code

Suggested entry points:

- Value tagging and header: `object/src/value.rs`, `object/src/header.rs`.
- Object layouts and maps: `object/src/objects.rs`, `object/src/map.rs`.
- Lookup and parent traversal: `object/src/lookup.rs`.
- Interpreter: `vm/src/interpreter.rs`.
- Compiler: `vm/src/compiler0.rs`.
- GC/heap: `heap/src/heap.rs` and `vm/src/lib.rs` (`trace_object`).
- Bootstrap of special objects: `vm/src/special.rs`.
