#ifndef HASHMAP_H
#define HASHMAP_H

#include "defaults.h"
#include "allocators.h"

u64 hashFunction(byte* str, i32 length);

// TODO change to bytearray
typedef struct {
    byte* key;
    i32 length;
    i32 state;
    cell value;
} HashItem;

typedef struct {
    Allocator allocator;
    HashItem* items;
    u32 size;
    u32 count;
    u32 sizeMin;
    u32 increaseDelta100;
    u32 decreaseDelta100;
    u16 expandFactor;
    u16 shrinkFactor;
} HashMap;

HashMap initHashMap(Allocator allocator, u32 size);
void deinitHashMap(HashMap* map);
void hmInsert(HashMap* map, byte* key, i32 length, cell value);
cell hmGet(HashMap* map, byte* key, i32 length);
cell hmDelete(HashMap* map, byte* key, i32 length);
void hmResize(HashMap* map, u32 newSize);



#endif