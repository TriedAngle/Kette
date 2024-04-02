#ifndef HASHMAP_H
#define HASHMAP_H

#include "defaults.h"
#include "allocators.h"
#include "objects.h"

u64 hashFunction(byte* str, i32 length);

u64 hashByteArray(bytearray* ba);
u64 hashFixnum(cell fixnum);

// TODO change to bytearray
typedef struct {
    cell key; // bytearray or fixnum (tagged)
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
void hmResize(HashMap* map, u32 newSize);

// automatically checks for fixnum or bytearray
void hmInsert(HashMap* map, cell key, cell value);
cell hmGet(HashMap* map, cell key);
cell hmDelete(HashMap* map, cell key);

#endif