#ifndef INTEGERS_H
#define INTEGERS_H

#ifdef LINUX
#elif WINDOWS
#elif ANDROID
#elif DARWIN
#endif

#ifdef __x86_64__
    #define X64
#elif __aarch64__
    #define A64
#endif

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <threads.h>

typedef unsigned char byte;
typedef char str;
typedef char i8;
typedef unsigned char u8;
typedef short i16;
typedef unsigned short u16;
typedef int i32;
typedef unsigned int u32;
typedef long long i64; 
typedef unsigned long long u64;
typedef i64 isize;
typedef u64 usize;
typedef float f32;
typedef double f64;


typedef i64 cell;


int string_eq(const byte* str1, i32 length1, const byte* str2, i32 length2);


#endif