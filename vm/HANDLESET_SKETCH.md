# HandleSet / Handle design sketch for `VM` (revised)

This revises the initial sketch with the following constraints:

- `Handle` and `Tagged` stay **separate** types.
- `Handle` has an extra indirection but is **safe to dereference**.
- Handles are **copyable**, but only within the lifetime/scope of their `HandleSet`.
- Clarify overflow policy for stack-allocated sets.
- Clarify whether `next` is sufficient for disjoint handle-set trees.

## Goals

- Keep temporary object references safe across allocation + GC points.
- Make handle scopes cheap to create on the stack.
- Support nested scopes linked together.
- Let `VM` expose active handle roots to GC via `RootProvider::visit_roots`.

## Key type split: `Tagged` vs `Handle`

- `Tagged<T>` remains a plain typed `Value` wrapper (no rooting).
- `Handle<T>` is a rooted, indirect reference to a slot in a live `HandleSet`.
- They should not be unified.

`Handle<T>` is for values that must survive safepoints/GC relocation while remaining ergonomic to access.

## Runtime model

### 1) VM owns **multiple** handle-set roots

To support potentially disjoint trees, store root heads in the VM:

```rust
pub struct VMProxy {
    // ...existing fields...
    handleset_roots: Vec<*mut HandleSet>,
}
```

Why a vector:

- A single `next` pointer only encodes one linked chain.
- If you allow creating top-level handle sets independently (not strictly nested from one active top), you can form multiple disjoint trees/chains.
- VM root scanning should iterate all root heads.

### 2) Stack-allocated `HandleSet`

```rust
const HANDLESET_CAPACITY: usize = 20;

pub struct HandleSet<'vm> {
    vm: &'vm mut VMProxy,
    parent: Option<*mut HandleSet<'vm>>,
    len: u8,
    slots: [Value; HANDLESET_CAPACITY],
}
```

Notes:

- `parent` links a child scope to its parent scope.
- A top-level scope created directly from VM has `parent = None` and is registered in `vm.handleset_roots`.
- A child scope created from an existing scope is linked via `parent = Some(...)` and does not need to be added as a separate VM root head.

### 3) Copyable, scope-bounded `Handle<T>`

```rust
#[derive(Clone, Copy)]
pub struct Handle<'hs, T> {
    slot: *mut Value,
    _scope: PhantomData<&'hs HandleSet<'hs>>,
    _type: PhantomData<*const T>,
}
```

- `Clone + Copy`: yes.
- `'hs` ties the handle lifetime to the originating handle scope.
- This allows copying handles freely **within scope**, while preventing escape.

## API shape

### Creating scopes

Two entry points:

1. Top-level scope from VM:
   - `let mut hs = vm.new_handleset();`
   - registers `hs` in `vm.handleset_roots`.
2. Child scope from existing scope:
   - `let mut child = hs.child();`
   - links child to parent via `parent`.

Both are stack values with RAII drop behavior.

### Inserting handles

```rust
impl<'vm> HandleSet<'vm> {
    pub fn pin<'hs, T>(&'hs mut self, value: Value) -> Handle<'hs, T>;
}
```

- Stores value in next free slot.
- Returns copyable handle to that slot.

### Safe handle operations

```rust
impl<'hs, T> Handle<'hs, T> {
    pub fn get(self) -> Value;
    pub fn set(self, value: Value);

    // typed safe accessors
    pub fn as_ref(self) -> Option<&'hs T>;
    pub fn as_mut(self) -> Option<&'hs mut T>;
}
```

Design intent:

- No `unsafe` required by callers for normal dereference/access.
- Internally, `Handle` may use unsafe pointer operations, but API checks tag/kind and returns `Option` (or `Result`) for invalid type/tag.

## Overflow policy (stack allocated sets)

For v1: **no overflow chaining**.

- Each `HandleSet` has hard capacity 20.
- On overflow, return an error or panic in debug builds.
- Users needing more than 20 simultaneously can explicitly open child scopes.

Why:

- True overflow chaining usually implies dynamically allocated extra chunks.
- If we require purely stack allocation, dynamic overflow chunks contradict that model.
- A fixed-capacity + nested-scope strategy is simpler and predictable.

Possible future option (if desired): allow VM-managed heap chunks for overflow, but that is a different design tradeoff and can be deferred.

## GC integration

`VMProxy::visit_roots` additions:

1. Iterate `vm.handleset_roots`.
2. For each root head, traverse its parent-chain/tree links.
3. For every active set, visit `slots[..len]` with `visitor(&mut slot)`.

This ensures all values referenced by active handles are traced and fixed up.

## Safety / invariants

- Handle sets unregister from VM root list on drop.
- Parent/child scope drop must remain LIFO per chain.
- Handles cannot outlive their scope (`'hs` lifetime).
- VM proxy remains thread-confined while scopes are active.
- `Handle` and `Tagged` remain distinct concepts and APIs.

## Suggested implementation plan

1. Add `vm/src/handles.rs` with `HandleSet`, `Handle`, and scope registration.
2. Add `handleset_roots` storage + helper methods on `VMProxy`.
3. Extend `RootProvider::visit_roots` to include all active handle sets.
4. Add tests for:
   - handle copyability within scope;
   - compile-time prevention of escape;
   - nested scope registration/unregistration;
   - GC fixup through handle slots.
5. Incrementally migrate GC-sensitive temporary values to handles.

