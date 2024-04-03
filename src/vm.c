#include "vm.h"



VM initVM(VMConfig config) {
    VM vm;
    vm.pageAllocator = initPageAllocator();
    vm.generalAllocator = initGeneralAllocator((GeneralAllocatorConfig){.zeroMem = 1});
    vm.pa = allocatorFromPageAllocator(&vm.pageAllocator);
    vm.ga = allocatorFromGeneralAllocator(&vm.generalAllocator);
    
    vm.dataStack = (cell*)tcreate(&vm.pa, config.dataStackSize);
    vm.dataStackTop = vm.dataStack;
    vm.retainStack = (cell*)tcreate(&vm.pa, config.retainStackSize);
    vm.callStack = (cell*)tcreate(&vm.pa, config.callStackSize);
    
    vm.dataStackSize = config.dataStackSize;
    vm.retainStackSize = config.retainStackSize;
    vm.callStackSize = config.callStackSize;

    vm.dataStackIndex = 0;
    vm.retainStackIndex = 0;
    vm.callStackIndex = 0;

    vm.dictionary = initHashMap(vm.ga, 32);
    vm.lastWord = NULL;

    vm.codeHeap = initCodeHeap(vm.pa);
    return vm;
}

void deinitVM(VM* vm) {
    deinitCodeHeap(&vm->codeHeap);
    deinitHashMap(&vm->dictionary);

    tdelete(&vm->pa, vm->callStack, vm->callStackIndex);
    tdelete(&vm->pa, vm->retainStack, vm->retainStackSize);
    tdelete(&vm->pa, vm->dataStack, vm->dataStackSize);
    deinitGeneralAllocator(&vm->generalAllocator);
}

void vmPush(VM* vm, cell value) {
    if (vm->dataStackIndex >= vm->dataStackSize) {
        // TODO handle this
    }
    vm->dataStackIndex++;
    *(vm->dataStackTop++) = value;
}

cell vmPop(VM* vm) {
    if (vm->dataStackTop == vm->dataStack) {
        // TODO handle this
    }
    vm->dataStackIndex--;
    return *(--vm->dataStackTop);
}


bytearray* vmAllocateBytearray(VM* vm, cell size) {
    bytearray* ba = tcreate(&vm->ga, sizeof(bytearray) + size);
    ba->parent = 0;
    ba->size = tag_num(size);
    return ba;
}

bytearray* vmAllocateString(VM* vm, byte* ptr, cell size) {
    bytearray* ba = vmAllocateBytearray(vm, size);
    memcpy(&ba->data, ptr, size);
    return ba;
}

word* vmAllocateWord(VM* vm, cell name, cell vocab) {
    word* word = tcreate(&vm->ga, sizeof(word));
    word->name = name;
    word->vocabulary = vocab;
    word->flags = 0;
    return word;
}
