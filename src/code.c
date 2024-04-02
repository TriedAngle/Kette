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