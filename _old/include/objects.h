#ifndef OBJECTS_H
#define OBJECTS_H

#include "defaults.h"

#define TAG_MASK 0b11LL

typedef enum {
    FIXNUM_TAG, // fixnum 0 is the only false, everything else true
    FLOAT_TAG, // uhm akschaully you are breaking IEEE754 :nerd:
    OBJECT_TAG,
    BYTEARRAY_TAG,
} TAG;


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
    // this is basically properties but some special ones
    // properties must also contain the flags
    // the VM can deduce some important properties way faster with this.
    cell flags;
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

typedef struct {
    // TAGGED POINTER
    cell parent;
    // TAGGED FIXNUM
    cell expired;
    // TAGGED POINTER
    cell base;
    // TAGGED POINTER
    cell displacement; // if -1, base is absolute address
} alien;

cell tag_value(cell value, TAG tag);
TAG read_tag(cell tagged);
cell remove_tag(cell tagged);

cell tag_num(i64 fixnum);
i64 untag_num(cell fixnum);

cell tag_float(f64 num);
f64 untag_float(cell num);

cell tag_object(cell obj);
cell tag_bytearray(bytearray* ba);

cell generic_eq(cell a, cell b);

#endif