#ifndef ALLOCATORS_H
#define ALLOCATORS_H

#include "defaults.h"
#include <stdio.h>
#include <string.h>
#ifdef LINUX
    #define PAGE_SIZE 4096
#elif WINDOWS
    #define PAGE_SIZE 4096
#endif

#ifdef X64
    #include <immintrin.h>
#endif

typedef void* (*ALLOCATE_FN)(void* allocator, usize length, u8 align, usize retAddr);
typedef u64 (*RESIZE_FN)(void* allocator, void** buffer, usize length, u8 align, usize newLength, usize retAddr);
typedef void (*FREE_FN)(void* allocator, void* buffer, usize length, u8 align, usize retAddr);

usize alignForward(usize value, usize alignment);
i32 findFirstBit(i64 bitset[4]);

typedef struct {
    void* ptr; // allocator implementation
    ALLOCATE_FN alloc;
    RESIZE_FN resize;
    FREE_FN free;
} Allocator;

typedef struct {
    
} PageAllocator ;
PageAllocator initPageAllocator();

Allocator allocatorFromPageAllocator(PageAllocator* allocator);


typedef struct {
    Allocator allocator;
    void* allocation;
    i32 capacity;
    i32 length;
} ArenaAllocator;

ArenaAllocator initArenaAllocator(Allocator allocator, i32 capacity);
Allocator allocatorFromArenaAllocator(ArenaAllocator* allocator);

typedef struct Bucket {
    struct Bucket* next;
    i32 blockSize;
    i32 blockCount;
    i64 freelist[4];
    void* allocation;
} Bucket;

typedef struct {
    PageAllocator pageAllocator;
    ArenaAllocator arenaAllocator;
    Bucket buckets[8];
} GeneralAllocator;

GeneralAllocator initGeneralAllocator();

Allocator allocatorFromGeneralAllocator(GeneralAllocator* allocator);


#endif