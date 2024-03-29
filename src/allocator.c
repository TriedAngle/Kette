#include "allocators.h"

usize alignForward(usize value, usize alignment) {
    return (value + alignment - 1) & ~(alignment - 1);
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

Allocator allocatorFromPageAllocator(PageAlloctor* allocator) {
    Allocator alloc = {
        .ptr = (void*)allocator,
        .alloc = pageAlloc,
        .resize = pageResize,
        .free = pageFree,
    };
    return alloc;
}


#ifdef SIMD
i32 findFirstBit(i64 bits[4]) {
    __m256i data = _mm256_loadu_si256((__m256i*)bits);

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
}
#else
i32 findFirstBit(i64 bitset[4]) {
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
}
#endif





// 16 32 64 128 256 512 1024 2048 4096