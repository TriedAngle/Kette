#ifndef CODE_H
#define CODE_H
#include "defaults.h"


// 8 bit size -> 256 basic opcodes
typedef enum BYTECODE {
    bcNoop, // does nothing, mainly there to have no 0 in mem
    bcSelf, // push  64bit pointer to self
    bcLiteral, // push 64bit pointer to object or special object (fixnum, boxed float) (tagged)
    bcSend, // starts with self, goes up the parents
    bcSendSelf, // only take self, no parents
    bcSendSuper, // ingore self, go to parents
    bcSendDelegate, // specific parent
    bcEnter, // enter a word or quotation
    bcReturn, // return from a word or quotation
} BYTECODE ;



#endif
