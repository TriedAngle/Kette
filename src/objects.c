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

