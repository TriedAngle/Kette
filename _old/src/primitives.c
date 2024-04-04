#include "vm.h"
#include "code.h"

void* primitivePointers[40];
word* primitiveWords[40];
i32 primitiveInOut[40];
cell primitiveIndex = 0;

void* GET_PRIMITIVE_FN(cell index) {
    return primitivePointers[index];
}

word* GET_PRIMITIVE_WORD(cell index) {
    return primitiveWords[index];
}

i32 GET_PRIMITIVE_INOUTS(cell index) {
    return primitiveInOut[index];
}

word* vmAllocatePrimitiveWord(VM* vm, cell isParse, i16 in, i16 out, char* word_name, void* ptr) {
    cell index = primitiveIndex++;
    cell length = strlen(word_name);
    bytearray* name = vmAllocateString(vm, (byte*)word_name, length);
    cell name_ptr = tag_bytearray(name); 
    word* word = vmAllocateWord(vm, name_ptr, 0);
    word->flags = isParse ? tag_num(0b11) : tag_num(0b1);
    word->entry = tag_num(index);

    primitivePointers[index] = ptr;
    primitiveWords[index] = word;
    primitiveInOut[index] = codeCreateInOut(in, out);

    return word;
}

void vmAllocatePrimitives(VM* vm) {
    vmAllocatePrimitiveWord(vm, 0, 2, 1, "fixnum+", (void*)primitiveFixnumAdd);

    vmAllocatePrimitiveWord(vm, 0, 1, 1, "fixnum.", (void*)primitiveFixnumPrint);
}

cell primitiveFixnumAdd(VM* vm, cell n1, cell n2) {
    return n1 + n2;
}

void primitiveFixnumPrint(VM* vm, cell n1) {
    printf("%lld\n", n1);
}