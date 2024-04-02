#ifndef OBJECTS_H
#define OBJECTS_H

#include "defaults.h"

#define TAG_MASK 0b111LL

typedef enum TAG {
    FIXNUM_TAG, // fixnum 0 is the only false, everything else true
    FLOAT_TAG,
    QUOTATION_TAG,
    BIGNUM_TAG, // TODO implement this, probably use library
    ARRAY_TAG,
    BYTEARRAY_TAG,
    WRAPPER_TAG,
    OBJECT_TAG,
} TAG;

cell tag_value(cell value, TAG tag);
TAG read_tag(cell tagged);
cell remove_tag(cell tagged);

cell tag_num(i64 fixnum);
i64 untag_num(cell fixnum);

cell fixnum_eq(cell fn1, cell fn2);
cell bytearray_eq(cell ba1, cell ba2);

cell generic_eq(cell a, cell b);

// hypothetically special objects don't require parent pointers
// but to keep it unified we add them
// + on 32bit hardware, we need to remove some tags

typedef struct {
    // TAGGED POINTER
    cell parent;
    // TAGGED POINTER
    cell name; //  bytearray
    // TAGGED POINTER
    cell vocabulary; // vocabulary, probably just hashmap
    // TAGGED POINTER
    cell properties; // array
    // TAGGED POINTER
    cell effect; // effect
    // TAGGED POINTER
    cell definition;
    // TAGGED POINTER
    cell entry;
} word;

typedef struct {
    // TAGGED POINTER
    cell parent;
    // TAGGED POINTER
    cell effect;
    // TAGGED POINTER
    cell defintion;
    // TAGGED POINTER
    cell entry;
} quotation;

typedef struct {
    // TAGGED POINTER
    cell parent;
    // TAGGED POINTER
    cell inout; // fixnum 0-30bits in 30-60bits out
    // TAGGED POINTER
    cell def; // array  
} effect;

typedef struct {
    cell parent;
    double value;
} boxedfloat;

typedef struct {
    // TAGGED POINTER
    cell parent;
    // TAGGED FIXNUM
    cell size;
    // ALLOCATED DATA AFTER STRUCT
    cell data[];
} array;

typedef struct {
    // TAGGED POINTER
    cell parent;
    // TAGGED FIXNUM
    cell size;
    // ALLOCATED DATA AFTER STRUCT
    byte data[];
} bytearray;

typedef struct {
    // TAGGED POINTER
    cell parent;
    // TAGGED POINTER
    cell object;
} wrapper;

#endif