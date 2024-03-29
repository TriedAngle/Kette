#ifndef INTEGERS_H
#define INTEGERS_H

#define __USE_GNU
#ifdef LINUX
    #include <sys/mman.h>
    #include <sys/syscall.h>
#elif WINDOWS
    #include <windows.h>
#elif ANDROID
#elif DARWIN
#endif

#ifdef __x86_64__
    #define X64
#elif __aarch64__
    #define A64
#endif

#include <stdlib.h>
#include <assert.h>

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

typedef i64 cell;

#endif