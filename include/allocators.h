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

typedef struct {
    void* ptr; // allocator implementation
    ALLOCATE_FN alloc;
    RESIZE_FN resize;
    FREE_FN free;
} Allocator;

typedef struct {
    
} PageAlloctor ;

Allocator allocatorFromPageAllocator(PageAlloctor* allocator);

usize alignForward(usize value, usize alignment);

typedef struct Bucket {
    struct Bucket* next;
    usize block_size;
} Bucket;

typedef struct {
    Allocator backing;
} GeneralAllocator;

i32 findFirstBit(i64 bitset[4]);

#endif