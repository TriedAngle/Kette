#include "vm.h"

VM initVM(VMConfig config) {
    VM vm;
    vm.pageAllocator = initPageAllocator();
    vm.generalAllocator = initGeneralAllocator((GeneralAllocatorConfig){.zeroMem = 1});
    vm.pa = allocatorFromPageAllocator(&vm.pageAllocator);
    vm.ga = allocatorFromGeneralAllocator(&vm.generalAllocator);
    
    vm.dataStack = (cell*)tcreate(&vm.pa, config.dataStackSize);
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