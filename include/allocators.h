#ifndef ALLOCATORS_H
#define ALLOCATORS_H

#include "defaults.h"

#ifdef LINUX
    #include <sys/mman.h>
    #define PAGE_SIZE 4096
#elif WINDOWS
    #include <windows.h>
    #define PAGE_SIZE 4096
#endif

#ifdef X64
    #include <immintrin.h>
#endif

typedef void* (*ALLOCATE_FN)(void* allocator, usize length,i32 align, usize retAddr);
typedef u64 (*RESIZE_FN)(void* allocator, void** buffer, usize length, i32 align, usize newLength, usize retAddr);
typedef void (*FREE_FN)(void* allocator, void* buffer, usize length, i32 align, usize retAddr);

usize alignForward(usize value, usize alignment);
i32 bitsetfindFirst1Bit(i64 bitset[4]);
void bitsetToggleNthBit(i64 bitset[4], i32 nth);

typedef struct {
    void* ptr; // allocator implementation
    ALLOCATE_FN alloc;
    RESIZE_FN resize;
    FREE_FN free;
} Allocator;

void* tcreate(Allocator* allocator, usize size);
void tdelete(Allocator* allocator, void* buffer, usize size);

void* talloc(Allocator* allocator, usize length, i32 align);
u64 tresize(Allocator* allocator, void** buffer, usize length, usize newLength, i32 align);
void tfree(Allocator* allocator, void* buffer, usize length, i32 align);

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
void deinitArenaAllocator(ArenaAllocator* allocator);
Allocator allocatorFromArenaAllocator(ArenaAllocator* allocator);

typedef struct Bucket {
    struct Bucket* next;
    i32 blockSize;
    i32 blockCount;
    u32 freeCount;
    i64 freelist[4];
    void* allocation;
} Bucket;

typedef struct LargeAllocation {
    struct LargeAllocation* next;
    struct LargeAllocation* prior;
    i32 size;
    i32 explicitPadding; 
    byte data[];
} LargeAllocation;

typedef struct {
    i32 zeroMem;
} GeneralAllocatorConfig;

typedef struct {
    GeneralAllocatorConfig config;
    PageAllocator pageAllocator;
    ArenaAllocator arenaAllocator;
    Bucket* buckets[8];
    mtx_t locks[8];
    u16 blockSizes[8];
    u16 blockCounts[8];
    LargeAllocation* larges;
    mtx_t large_lock;
} GeneralAllocator;

GeneralAllocator initGeneralAllocator(GeneralAllocatorConfig config);
void deinitGeneralAllocator(GeneralAllocator* allocator);

Allocator allocatorFromGeneralAllocator(GeneralAllocator* allocator);


typedef struct {
    Allocator ac;
    void* allocation;
    i32 capacity;
    i32 length; 
    i32 elementSize;
} GrowableArray;

GrowableArray initGrowableArray(Allocator ac, i32 initCapacity, i32 elementSize);
void deinitGrowableArray(GrowableArray* ga);
i32 gaPush(GrowableArray* ga, void* element);
void* gaPop(GrowableArray* ga);
void* gaAt(GrowableArray* ga, i32 index);

#endif