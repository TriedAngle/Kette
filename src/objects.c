#include "objects.h"


cell tag_value(cell value, TAG tag) {
    return value | tag;
}

TAG read_tag(cell tagged) {
    return tagged & TAG_MASK;
}

cell remove_tag(cell tagged) {
    return tagged & ~TAG_MASK;
}

cell tag_num(i64 num) {
    return tag_value((cell)(num << 3), FIXNUM_TAG);
}

i64 untag_num(cell fixnum) {
    return (i64)(fixnum >> 3);
}

cell fixnum_eq(cell fn1, cell fn2) {
    return fn1 == fn2;
}

cell bytearray_eq(cell bytearray1, cell bytearray2) {
    bytearray* ba1 = (bytearray*)remove_tag(bytearray1);
    bytearray* ba2 = (bytearray*)remove_tag(bytearray2);
    if (ba1->size != ba2->size) return 0;
    for (int i = 0; i < ba1->size; i++) {
        if (ba1->data[i] != ba2->data[i]) {
            return 0;
        }
    }
    return 1;
}

cell generic_eq(cell a, cell b) {
    if (read_tag(a) == OBJECT_TAG && read_tag(b) == OBJECT_TAG) {
        return a == b; 
    } else if (read_tag(a) == FIXNUM_TAG && read_tag(b) == FIXNUM_TAG) {
        return fixnum_eq(a, b);
    } else if (read_tag(a) == BYTEARRAY_TAG && read_tag(b) == BYTEARRAY_TAG) {
        return bytearray_eq(a, b);
    }
    return 0;
}