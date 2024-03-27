#include "tryangle.h"

// clears the upper 12 bits of a pointer
// intel 5 level 52bit paging, is this even a concern ?
void* clear_pointer_tags(void* ptr) {
    i64 mask = 0x000FFFFFFFFFFFFF;
    return (void*)((i64)ptr & mask);
}

void* set_pointer_tag_bit(void* ptr, i32 nth) {
    i64 mask = 1ULL << nth;
    return (void*)((i64)ptr | mask);
}

i64 set_nth_bit(i64 val, i32 nth, byte tf) {
    if(tf == 0) {
        return val & ~(1LL << nth);
    } else {
        return val | (1LL << nth);
    }
}

byte read_nth_bit(i64 val, i32 nth) {
    i64 mask = 1ULL << nth;
    return (val & mask) ? 1 : 0;
}