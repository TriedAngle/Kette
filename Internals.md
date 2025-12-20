# Kette VM Internals
THIS IS MOSTLY OUTDATED
TODO: UPDATE THIS
Overview of the internals of the virtual machine

## Hidden Maps
- objects use a prototype system with hidden maps.
- these maps describe the objects shape and methods and parent objects.

## VM-aware objects
the objects are builtin or the VM is aware of them (in the future these might be moved outside of the VM initialization, and the VM loads them instead)
- true `t`
- false/null `f` right now false and null is the same, **every** value in the VM evaluates to true **except** `f` which is the **only** false value
- different SlotTypes, the type of the slot descriptor in hidden classes / maps.

## Pointer Types
### `TaggedValue`
very generic value that is on the heap, can be:
- integer (63 bit) `X0`
- reference `01`
- header `11`

### `GenericObject`
represents a very generic object, (reference), it is not an integer and not a header, but any heap allocated object.
It is ofted used with `TaggedPtr<GenericObject>`, it implements "dispatching" to specific object implementations

### `TaggedPtr<T>`
pointer to a heap allocated object that is also heap compliant, meaning the heap/gc would understand what this is.

### `View<T>`
pointer wrapper over just a normal pointer to a heap allocated object. it's easier to work with (also impls Deref and DerefMut) but the heap would not understand it.

## Concurrency
short: M fibers on N actors on P threads, but allows quite fine control 

### Actor
- an actor is a object and also a green thread.
- communicate via mail box messages, which are just normal methods
- can be pinned to physical threads if necessary (including main)
- actors can also given a dedicated thread
- currently support for snapshotting actors is not not fully planned but intended later or dropped if too hard/impossible/too many edge cases. 
- every actor has their own GC 
- every actor also has their own Heap, but it is intended to have only one heap later maybe.

### Fibers
- on every actor there is multiple fibers
- fibers run cooperatively on the same actor
