#include "defaults.h"

int string_eq(const byte* str1, i32 length1, const byte* str2, i32 length2) {
    if (length1 != length2) return 0;
    for (int i = 0; i < length1; i++) {
        if (str1[i] != str2[i]) {
            return 0;
        }
    }
    return 1;
}

