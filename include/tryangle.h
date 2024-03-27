#ifndef TRYANGLE_H
#define TRYANGLE_H

#include <stdint.h>

typedef uint8_t byte;
typedef char str;
typedef uint8_t u8;
typedef int8_t i8;
typedef int16_t i16;
typedef uint16_t u16;
typedef int32_t i32;
typedef uint32_t u32;
// printf("The value of myInt is: %" PRId64 "\n", myInt); HAHAHHAHAHAHA
typedef long long i64; 
typedef unsigned long long u64;
typedef i64 isize;
typedef u64 usize;


void* clear_pointer_tags(void* ptr);
void* set_pointer_tag_bit(void* ptr, i32 nth);

i64 set_nth_bit(i64 val, i32 nth, byte tf);
byte read_nth_bit(i64 val, i32 nth);


#define DEFAULT_ARRAY_LIST_CAPACITY 16

typedef struct {
    byte* allocation;
    u32 len;
    u32 capacity;
    u32 stride;
} ArrayList;

#endif