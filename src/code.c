#include "code.h"
#include "vm.h"

CodeHeap initCodeHeap(Allocator allocator) {
    CodeHeap ch;
    ch.ga = allocator;
    ch.code = initHashMap(ch.ga, 165); // almost 1 page
    ch.compiled = initHashMap(ch.ga, 165); // almost 1 page 
    return ch;
}

void deinitCodeHeap(CodeHeap* ch) {
    deinitHashMap(&ch->compiled);
    deinitHashMap(&ch->code);
}

void pushInstruction(GrowableArray* ga, byte instr) {
    gaPush(ga, (void*)&instr);
}

void pushCell(GrowableArray* ga, cell c) {
    for (int i = 0; i < 8; i++) {
        byte b = (c >> (8 * i)) & 0xFF;
        gaPush(ga, (void*)&b);
    }
}

void pushInteger(GrowableArray* ga, i64 integer) {
    pushInstruction(ga, (byte)bcLiteral);
    cell fixnum = tag_num(integer);
    pushCell(ga, fixnum);
}

void pushSelf(GrowableArray* ga) {
    pushInstruction(ga, (byte)bcSelf);
}
void pushSend(GrowableArray* ga) {
    pushInstruction(ga, (byte)bcSend);
}
void pushSendSelf(GrowableArray* ga) {
    pushInstruction(ga, (byte)bcSendSelf);
}
void pushSendSuper(GrowableArray* ga) {
    pushInstruction(ga, (byte)bcSendSuper);
}
void pushSendDelegate(GrowableArray* ga) {
    pushInstruction(ga, (byte)bcSendDelegate);
}
void pushSendEnter(GrowableArray* ga) {
    pushInstruction(ga, (byte)bcEnter);
}
void pushSendReturn(GrowableArray* ga) {
    pushInstruction(ga, (byte)bcReturn);
}
void pushPrimitive(GrowableArray* ga) {
    pushInstruction(ga, (byte)bcPrimitive);
}

void chCompile(CodeHeap* ch, word* word);