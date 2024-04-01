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

    // pointers not tagged, but tagged for VM
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

    // this is only for initializing vm
    // maybe remove them later or remove them once images are there
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

void vmPush(VM* vm, cell value);
cell vmPop(VM* vm);


word* vmAllocateWord(VM* vm, cell name, cell vocab);
word* vmFindWord(VM* vm, cell name, cell vocab);
word* vmChangeWordVocab(VM* vm, cell word, cell newVocab);


void vmBindCode(VM* vm, byte* stream, cell length);

cell vmReadNumber(VM* vm, byte* word, cell length);
cell vmPeekWord(VM* vm, byte** word);
cell vmReadWord(VM* vm, byte** word);
cell vmReadUntil(VM* vm, byte* ident, cell identLength);
void vmReadStackEffect(VM* vm);
void vmReadWordDef(VM* vm);

void primitiveSyntax(VM* vm);

void primitiveCall(VM* vm);
void primitiveDrop(VM* vm);
void primitiveDropd(VM* vm);
void primitive2Drop(VM* vm);
void primitive3Drop(VM* vm);
void primitiveDup(VM* vm);
void primitiveDupd(VM* vm);
void primitive2Dup(VM* vm);
void primitive3Dup(VM* vm);
void primitiveOver(VM* vm);
void primitiveSwap(VM* vm);
void primitiveSwapd(VM* vm);
void primitiveRot(VM* vm);
void primitiveRRot(VM* vm);
void primitiveDip(VM* vm);

cell primitiveFixnumAdd(VM* vm, cell n1, cell n2);
cell primitiveFixnumSub(VM* vm, cell n1, cell n2);
cell primitiveFixnumMul(VM* vm, cell n1, cell n2);
cell primitiveFixnumDiv(VM* vm, cell n1, cell n2);
cell primitiveFixnumMod(VM* vm, cell n1, cell n2);

cell primitiveFixnumBitOr(VM* vm, cell n1, cell n2);
cell primitiveFixnumBitAnd(VM* vm, cell n1, cell n2);
cell primitiveFixnumBitXor(VM* vm, cell n1, cell n2);
cell primitiveFixnumBitLShift(VM* vm, cell n1, cell n2);
cell primitiveFixnumBitRShift(VM* vm, cell n1, cell n2);
cell primitiveFixnumBitNot(VM* vm, cell n1);


void primitiveFixnumPrint(VM* vm, cell n1);


cell primitiveEq(VM* vm, cell n1, cell n2);
cell primitiveFixnumLT(VM* vm, cell n1, cell n2);
cell primitiveFixnumGT(VM* vm, cell n1, cell n2);
cell primitiveFixnumLTEq(VM* vm, cell n1, cell n2);
cell primitiveFixnumGTEq(VM* vm, cell n1, cell n2);
void primitiveIf(VM* vm);


#endif