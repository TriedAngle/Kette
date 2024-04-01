#ifndef VM_H
#define VM_H

#include "defaults.h"
#include "allocators.h"
#include "hashmap.h"
#include "objects.h"

typedef struct {
    cell* owner; // word or quotation
    cell* parameters;
    cell* compiled;
} CodeBlock;

typedef struct {
    GeneralAllocator ga;
    HashMap code;
    HashMap compiled;
} CodeHeap;

CodeHeap initCodeHeap();
void deinitCodeHeap(CodeHeap* ch);

void chCompile(CodeHeap* ch, word* word);
void chFree(CodeHeap* ch, word* word);

// must be kept in sync
typedef struct {
    PageAllocator pa;
    GeneralAllocator ga;

    cell* dataStack;
    cell dataStackIndex;
    cell dataStackSize;

    cell* retainStack;
    cell retainStackIndex;
    cell retainStackSize;

    cell* callStack;
    cell callStackIndex;
    cell callStackSize;

    HashMap dictionary;
    word* lastWord;

    CodeHeap code;

    byte* activeStream;
    cell activeStreamLength;
    cell activeStreamOffset;
} VM;

typedef struct {
    cell dataStackSize;
    cell retainStackSize;
    cell callStackSize;
} VMConfig;

VM initVM(VMConfig config);
void deinitVM(VM* vm);

void vm_push(VM* vm, cell value);
cell vm_pop(VM* vm);


void vm_bind_code(VM* vm, byte* stream, cell length);

#endif