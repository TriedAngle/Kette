#include "allocators.h"

usize alignForward(usize value, usize alignment) {
    return (value + alignment - 1) & ~(alignment - 1);
}

i32 bitsetfindFirst1Bit(i64 bitset[4]) {
    #ifdef SIMD
    __m256i data = _mm256_loadu_si256((__m256i*)bitset);

    if (_mm256_testz_si256(data, data)) {
        return -1; // All bits are 0.
    }

    i64 part0 = _mm256_extract_epi64(data, 0);
    if (part0 != 0) {
        return 0 * 64 + __builtin_ctzll(part0);
    }
    i64 part1 = _mm256_extract_epi64(data, 1);
    if (part1 != 0) {
        return 1 * 64 + __builtin_ctzll(part1);
    }
    i64 part2 = _mm256_extract_epi64(data, 2);
    if (part2 != 0) {
        return 2 * 64 + __builtin_ctzll(part2);
    }
    i64 part3 = _mm256_extract_epi64(data, 3);
    if (part3 != 0) {
        return 3 * 64 + __builtin_ctzll(part3);
    }

    return -1;
    #else
    for (int i = 0; i < 4; ++i) {
        if (bitset[i] != 0) {
            for (int j = 0; j < 64; ++j) {
                if (bitset[i] & ((i64)1 << j)) {
                    return i * 64 + j;
                }
            }
        }
    }
    return -1;
    #endif
}

void bitsetToggleNthBit(i64 bitset[4], i32 nth) {
    i32 arrayIdx = nth / 64;
    i32 bitIdx = nth % 64;
    bitset[arrayIdx] ^= (1LL << bitIdx);
}

void* pageAlloc(void* allocator, usize length, u8 align, usize retAddr) {
    assert(length > 0);
    int alignedLength = alignForward(length, PAGE_SIZE);
    void* addr;

    #ifdef LINUX
        addr = mmap(NULL,  alignedLength, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    #elif WINDOWS
        addr = VirtualAlloc(NULL, alignedLength, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    #endif

    return addr;
}

void pageFree(void* allocator, void* buffer, usize length, u8 align, usize retAddr) {
    #ifdef LINUX
        munmap(buffer, length);
    #elif WINDOWS
        VirtualFree(buffer, 0, MEM_RELEASE);
    #endif
}

u64 pageResize(void* allocator, void** buffer, usize length, u8 align, usize newLength, usize retAddr) {
    assert(newLength > 0);
    usize oldAlignedLength = alignForward(length, PAGE_SIZE);
    usize newAlignedLength = alignForward(newLength, PAGE_SIZE);

    if(oldAlignedLength == newAlignedLength) {
        return 0;
    }

    void* newAddr = pageAlloc(allocator, oldAlignedLength, align, retAddr);
    memcpy(newAddr, *buffer, length < newLength ? length : newLength);
    pageFree(allocator, *buffer, oldAlignedLength, align, retAddr);
    *buffer = newAddr;
    return 1;
}

PageAllocator initPageAllocator() {
    PageAllocator allocator = {};
    return allocator;
}

Allocator allocatorFromPageAllocator(PageAllocator* allocator) {
    Allocator alloc = {
        .ptr = (void*)allocator,
        .alloc = pageAlloc,
        .resize = pageResize,
        .free = pageFree,
    };
    return alloc;
}

ArenaAllocator initArenaAllocator(Allocator allocator, i32 capacity) {
    void* allocation = allocator.alloc((void*)&allocator, capacity, 8, 0);
    ArenaAllocator arena = {
        .allocator = allocator,
        .allocation = allocation,
        .capacity = capacity,
        .length = 0,
    };

    return arena;
}

void* arenaAlloc(void* allocator, usize length, u8 align, usize retAddr) {
    ArenaAllocator* alloc = (ArenaAllocator*) alloc;
    i32 alignedLength = alignForward(length, align);
    Allocator inner = alloc->allocator;
    void* allocation;
    if (alloc->allocation == NULL) {
        allocation = inner.alloc((void*)&inner, alignedLength, align, retAddr);
        alloc->capacity = alignedLength;
        alloc->length = 0;
    } else if (alloc->length + length >= alloc->capacity) {
        i32 newCapacity = alloc->capacity * 2;
        inner.resize(
            (void*)&alloc->allocator, 
            &alloc->allocation, 
            alloc->capacity, 
            align, 
            newCapacity, 
            0
        );
        alloc->capacity = newCapacity;
        allocation = alloc->allocation + alloc->length;
    } else {
        allocation = alloc->allocation + alloc->length;
    }

    alloc->length += alignedLength;
    return allocation;
}

u64 arenaResize(void* allocator, void** buffer, usize length, u8 align, usize newLength, usize retAddr) {
    return 0;
}

void arenaFree(void* allocator, void* buffer, usize length, u8 align, usize retAddr) {
    ArenaAllocator* alloc = (ArenaAllocator*) alloc;
    Allocator inner = alloc->allocator;
    inner.free((void*)&inner, alloc->allocation, alloc->capacity, align, retAddr);
}

Allocator allocatorFromArenaAllocator(ArenaAllocator* allocator) {
    Allocator alloc = {
        .ptr = (void*)allocator,
        .alloc = arenaAlloc,
        .resize = arenaResize,
        .free = arenaFree,
    };
    return alloc;
}


i32 bucketFreeIndex(Bucket* bucket) {
    i32 index = bitsetfindFirst1Bit(bucket->freelist);
    if (index == -1) return -1;
    if (index > bucket->blockCount) return -1;
    return index;
}

void bucketToggleFree(Bucket* bucket, i32 index) {
    bitsetToggleNthBit(bucket->freelist, index);
}

Bucket newEmptyBucket(i32 blockSize, i32 blockCount) {
    Bucket bucket = {
        .blockSize = blockSize,
        .blockCount = blockCount,
        .allocation = NULL,
    };
    return bucket;
}

GeneralAllocator initGeneralAllocator() {
    PageAllocator pageAllocator = initPageAllocator();
    Allocator pageAlloc = allocatorFromPageAllocator(&pageAllocator);
    ArenaAllocator arenaAllocator = initArenaAllocator(pageAlloc, PAGE_SIZE);
    
    GeneralAllocator ga = {
        .pageAllocator = pageAllocator,
        .arenaAllocator = arenaAllocator,
    };
    
    ga.buckets[0] = newEmptyBucket(16, 256); // 1 page
    ga.buckets[1] = newEmptyBucket(32, 256); // 2 pages
    ga.buckets[2] = newEmptyBucket(64, 256); // 4 pages
    ga.buckets[3] = newEmptyBucket(128, 128); // 4 pages
    ga.buckets[4] = newEmptyBucket(256, 64); // 4 pages
    ga.buckets[5] = newEmptyBucket(512, 32); // 4 pages
    ga.buckets[6] = newEmptyBucket(1024, 16); // 4 pages
    ga.buckets[7] = newEmptyBucket(2048, 4); // 4 pages
    

    return ga;
}

Bucket* findBucketCategory(GeneralAllocator* allocator, i32 size) {
    for (int i = 0; i < 8; i++) {
        if (size <= allocator->buckets[i].blockSize) {
            return &allocator->buckets[i];
        }
    }
    return NULL;
}

// Bucket* findAvailableBucket(GeneralAllocator* allocator, i32 size) {
//     Bucket* bucket = findBucketCategory(allocator, size);
//     if (bucket == NULL) {
//         return NULL;
//     }

//     do {

//     } while(bucket != NULL)

// }