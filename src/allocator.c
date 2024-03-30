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

void* tcreate(Allocator* a, usize size) {
    return talloc(a, size, 8);
}

void tdelete(Allocator* a, void* buffer, usize size) {
    return tfree(a, buffer, size, 8);
}

void* talloc(Allocator* a, usize length, i32 align) {
    return a->alloc(a->ptr, length, align, 0);
}

u64 tresize(Allocator* a, void** buffer, usize length, usize newLength, i32 align) {
    return a->resize(a->ptr, buffer, length, align, newLength, 0);
}

void tfree(Allocator* a, void* buffer, usize length, i32 align) {
    a->free(a->ptr, buffer, length, align, 0);
}


void* pageAlloc(void* allocator, usize length, i32 align, usize retAddr) {
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

void pageFree(void* allocator, void* buffer, usize length, i32 align, usize retAddr) {
    #ifdef LINUX
        munmap(buffer, length);
    #elif WINDOWS
        VirtualFree(buffer, 0, MEM_RELEASE);
    #endif
}

u64 pageResize(void* allocator, void** buffer, usize length, i32 align, usize newLength, usize retAddr) {
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

void* arenaAlloc(void* allocator, usize length, i32 align, usize retAddr) {
    ArenaAllocator* alloc = (ArenaAllocator*) allocator;
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

u64 arenaResize(void* allocator, void** buffer, usize length, i32 align, usize newLength, usize retAddr) {
    return 0;
}

void arenaFree(void* allocator, void* buffer, usize length, i32 align, usize retAddr) {
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

void* bucketPtrFromIndex(Bucket* bucket, i32 index) {
    void* ptr = bucket->allocation + (bucket->blockSize * index);

    return ptr;
}

i32 bucketIndexFromPtr(Bucket* bucket, void* ptr) {
    usize start = (usize)bucket->allocation;
    usize p = (usize)ptr;
    i32 index = (p - start) / bucket->blockSize;
    return index;
}

Bucket newEmptyBucket(i32 blockSize, i32 blockCount) {
    Bucket bucket = {
        .blockSize = blockSize,
        .blockCount = blockCount,
        .freelist = {-1, -1, -1, -1}, // 2 complement -> full 1 array
        .allocation = NULL,
    };
    return bucket;
}

GeneralAllocator initGeneralAllocator(GeneralAllocatorConfig config) {
    GeneralAllocator ga;
    ga.pageAllocator = initPageAllocator();
    Allocator pageAlloc = allocatorFromPageAllocator(&ga.pageAllocator);
    ga.arenaAllocator = initArenaAllocator(pageAlloc, PAGE_SIZE);

    ga.buckets[0] = NULL;
    ga.buckets[1] = NULL;
    ga.buckets[2] = NULL;
    ga.buckets[3] = NULL;
    ga.buckets[4] = NULL;
    ga.buckets[5] = NULL;
    ga.buckets[6] = NULL;
    ga.buckets[7] = NULL;

    ga.blockSizes[0] = 16;
    ga.blockSizes[1] = 32;
    ga.blockSizes[2] = 64;
    ga.blockSizes[3] = 128;
    ga.blockSizes[4] = 256;
    ga.blockSizes[5] = 512;
    ga.blockSizes[6] = 1024;
    ga.blockSizes[7] = 2048;

    ga.blockCounts[0] = 256;
    ga.blockCounts[1] = 256;
    ga.blockCounts[2] = 256;
    ga.blockCounts[3] = 128;
    ga.blockCounts[4] = 64;
    ga.blockCounts[5] = 32;
    ga.blockCounts[6] = 16;
    ga.blockCounts[7] = 4;

    mtx_init(&ga.locks[0], mtx_plain);
    mtx_init(&ga.locks[1], mtx_plain);
    mtx_init(&ga.locks[2], mtx_plain);
    mtx_init(&ga.locks[3], mtx_plain);
    mtx_init(&ga.locks[4], mtx_plain);
    mtx_init(&ga.locks[5], mtx_plain);
    mtx_init(&ga.locks[6], mtx_plain);
    mtx_init(&ga.locks[7], mtx_plain);

    return ga;
}

void allocateBucketMemory(GeneralAllocator* ga, Bucket* bucket) {
    usize allocSize = bucket->blockSize * bucket->blockCount;
    bucket->allocation = pageAlloc((void*)&ga->pageAllocator, allocSize, PAGE_SIZE, 0);
    if(ga->config.zeroMem) {
        memset(bucket->allocation, 0, allocSize);
    }
}

Bucket* allocateGABucket(GeneralAllocator* ga, u32 category) {
    Bucket* bucket = arenaAlloc((void*)&ga->arenaAllocator, sizeof(Bucket), sizeof(Bucket), 0);
    bucket->blockSize = ga->blockSizes[category];
    bucket->blockCount = ga->blockCounts[category];
    bucket->freeCount = bucket->blockCount;
    bucket->freelist[0] = -1;
    bucket->freelist[1] = -1;
    bucket->freelist[2] = -1;
    bucket->freelist[3] = -1;
    allocateBucketMemory(ga, bucket);
    return bucket;
}


u32 findBucketCategory(GeneralAllocator* ga, i32 size) {
    if (size <= ga->blockSizes[0]) {
        return 0;
    } else if (size <= ga->blockSizes[1]) {
        return 1;
    } else if (size <= ga->blockSizes[2]) {
        return 2;
    } else if (size <= ga->blockSizes[3]) {
        return 3;
    } else if (size <= ga->blockSizes[4]) {
        return 4;
    } else if (size <= ga->blockSizes[5]) {
        return 5;
    } else if (size <= ga->blockSizes[6]) {
        return 6;
    } else if (size <= ga->blockSizes[7]) {
        return 7;
    }
    return 8;
}

Bucket* findAvailableBucket(GeneralAllocator* ga, i32 size, u32 category) {
    Bucket* bucket = ga->buckets[category];
    if (bucket == NULL) {
        bucket = allocateGABucket(ga, category);
        ga->buckets[category] = bucket;
    }
    for(;;) {
        if (bucket->freeCount > 0) {
            break;
        }
        if (bucket->next == NULL) {
            Bucket* new = allocateGABucket(ga, category);
            bucket->next = new;
            bucket = new;
            break;
        }
        bucket = bucket->next;
    }
    return bucket;
}

void* generalAlloc(void* allocator, usize length, i32 align, usize retAddr) {
    GeneralAllocator* ga = (GeneralAllocator*) allocator;
    usize size = alignForward(length, align);

    u32 category = findBucketCategory(ga, size);
    if (category > 7) {
        // TODO HANDLE LARGER ALLOCATIONS
        exit(1);
    }

    mtx_lock(&ga->locks[category]);
    Bucket* bucket = findAvailableBucket(ga, size, category);
    if (bucket == NULL) {
        // TODO HANDLE ERROR
        exit(1);
    }
    i32 index = bucketFreeIndex(bucket);
    index = bucketFreeIndex(bucket);
    bucketToggleFree(bucket, index);
    mtx_unlock(&ga->locks[category]);

    return bucketPtrFromIndex(bucket, index);
}

void generalFree(void* allocator, void* buffer, usize length, i32 align, usize retAddr) {
    GeneralAllocator* ga = (GeneralAllocator*) allocator;
    usize size = alignForward(length, align);

    u32 category = findBucketCategory(ga, size);
    if (category > 7) {
        // TODO HANDLE LARGER ALLOCATIONS
        return;
    }

    Bucket* bucket = ga->buckets[category];
    usize addr = (usize)buffer;
    usize minAddr;
    usize maxAddr;
    for(;;) {
        minAddr = (usize)bucket->allocation;
        maxAddr = minAddr + (bucket->blockSize * bucket->blockCount);
        if (minAddr <= addr && addr < maxAddr) {
            break;
        }
        if (bucket->next == NULL) {
            // TODO HANDLE ERROR
            return;
        }
        bucket = bucket->next;
    }

    // TODO maybe we don't need locks here? 
    mtx_lock(&ga->locks[category]);
    i32 index = bucketIndexFromPtr(bucket, buffer);
    bucketToggleFree(bucket, index);
    if(ga->config.zeroMem) {
        memset(buffer, 0, bucket->blockSize);
    }
    mtx_unlock(&ga->locks[category]);
}


u64 generalResize(void* allocator, void** buffer, usize length, i32 align, usize newLength, usize retAddr) {
    usize size = alignForward(length, align);
    usize newSize = alignForward(newLength, align);

    if(size == newSize) {
        return 0;
    }

    void* newBuffer = generalAlloc(allocator, newSize, align, retAddr);
    memcpy(newBuffer, *buffer, size < newSize ? size : newSize);
    generalFree(allocator, *buffer, size, align, retAddr);
    *buffer = newBuffer;
    return 1;
}

Allocator allocatorFromGeneralAllocator(GeneralAllocator* allocator) {
    Allocator alloc = {
        .ptr = (void*)allocator,
        .alloc = generalAlloc,
        .resize = generalResize,
        .free = generalFree,
    };
    return alloc;
}