#ifndef CODE_H
#define CODE_H
#include "defaults.h"
#include "allocators.h"
#include "hashmap.h"


// 8 bit size -> 256 basic opcodes
typedef enum {
    bcNoop, // does nothing, mainly there to have no 0 in mem
    bcSelf, // push  64bit pointer to self
    bcLiteral, // push value
    bcSend, // starts with self, goes up the parents
    bcSendSelf, // only take self, no parents
    bcSendSuper, // ingore self, go to parents
    bcSendDelegate, // specific parent
    bcEnter, // enter a word or quotation
    bcReturn, // return from a word or quotation
    bcLocalJump, // 64bit
    bcPrimitive,
} BYTECODE ;


typedef struct {
    // TAGGED POINTER
    cell owner; // word or quotation
    // TAGGED POINTER
    cell parameters;
    GrowableArray bytecode;
} CodeBlock;

typedef struct {
    Allocator ga;
    HashMap code;
    HashMap compiled;
} CodeHeap;

CodeHeap initCodeHeap(Allocator allocator);
void deinitCodeHeap(CodeHeap* ch);
// KEY: TAGGED POINTER
CodeBlock* chAllocateCodeBlock(CodeHeap* ch, cell key);
void chDeallocateCodeBlock(CodeHeap* ch, cell key);

void chCompile(CodeHeap* ch, word* word);
void chFree(CodeHeap* ch, word* word);

void printCodeBlock(CodeBlock* cb);

void bcPushInteger(CodeBlock* cb, i64 integer);
void bcPushFloat(CodeBlock* cb, f64 num);

void bcPushObject(CodeBlock* cb, cell obj);
void bcPushSelf(CodeBlock* cb);
void bcPushSend(CodeBlock* cb);
void bcPushSendSelf(CodeBlock* cb);
void bcPushSendSuper(CodeBlock* cb);
void bcPushSendDelegate(CodeBlock* cb);
void bcPushSendEnter(CodeBlock* cb);
void bcPushSendReturn(CodeBlock* cb);
void bcPushLocalJump(CodeBlock* cb, cell to);
void bcPushPrimitive(CodeBlock* cb, i32 index, i32 inout);

i32 codeCreateInOut(i16 in, i16 out);
i16 codeGetIn(i32 inout);
i16 codeGetOut(i32 inout);

#endif
