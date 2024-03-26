#define _GNU_SOURCE
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <sys/mman.h>
#include <limits.h>
#include <stddef.h>

#include "utilities.h"

#define DEFAULT_STACK_SIZE 8192

typedef struct {
    cell data_size, retrain_size, call_size; 
    cell quotation_size, dictionary_size;
} VMInitConfig;

typedef struct {
    cell* data_stack;
    cell data_stack_pointer;
    cell data_stack_size;

    cell* retrain_stack;
    cell retrain_stack_pointer;
    cell retrain_stack_size;

    cell* call_stack;
    cell call_stack_pointer;
    cell call_stack_size;

    byte* quotations;
    cell quotations_length;
    cell quotation_size;

    byte* dictionary;
    cell dictionary_length;
    cell dictionary_size;
    cell* latest_word;
} VM;

typedef void (*BUILTIN_FUN)(VM*);

void init_VM(VM* vm, VMInitConfig config) {
    vm->data_stack_size = config.data_size;
    vm->data_stack = mmap(NULL,  config.data_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->data_stack_pointer = 0;

    vm->retrain_stack_size = config.retrain_size;
    vm->retrain_stack = mmap(NULL, config.retrain_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->retrain_stack_pointer = 0;

    vm->call_stack_size = config.call_size;
    vm->call_stack = mmap(NULL, config.call_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->call_stack_pointer = 0;

    vm->quotation_size = config.quotation_size;
    vm->quotations = mmap(NULL, config.quotation_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->quotations_length = 0;

    vm->dictionary_size = config.dictionary_size;
    vm->dictionary = mmap(NULL, config.dictionary_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->dictionary_length = 0;
    vm->latest_word = NULL;
}


void deinit_VM(VM* vm) {
    munmap(vm->data_stack, vm->data_stack_size);
    munmap(vm->retrain_stack, vm->retrain_stack_size);
    munmap(vm->call_stack, vm->call_stack_size);

    munmap(vm->dictionary, vm->dictionary_size);
    munmap(vm->quotations, vm->quotation_size);
}

cell pop(VM* vm) {
    return vm->data_stack[--(vm->data_stack_pointer)];
}

void push(VM* vm, cell data) {
    cell* point = vm->data_stack + vm->data_stack_pointer;
    *point = data;
    vm->data_stack_pointer++;
}

cell rpop(VM* vm) {
    return vm->retrain_stack[--(vm->retrain_stack_pointer)];
}

void rpush(VM* vm, cell data) {
    vm->retrain_stack[(vm->retrain_stack_pointer)++] = data;
}

cell cpop(VM* vm) {
    return vm->call_stack[--(vm->call_stack_pointer)];
}

void cpush(VM* vm, cell data) {
    vm->call_stack[(vm->call_stack_pointer)++] = data;
}


int string_eq(byte* str1, i32 length1, byte* str2, i32 length2) {
    if (length1 != length2) return 0;
    for (int i = 0; i < length1; i++) {
        if (str1[i] != str2[i]) {
            return 0;
        }
    }
    return 1;
}


/*
    link: 64bit pointer to next Word
    name: pointer to name
    length: size of the name in bytes
    codeword: 8 bytes
    body: variable sized pointer list with size of size, pointing to words (can be 0)
*/
typedef struct {
    cell* link;
    byte* name;
    i32 length;
    i32 flags;
    cell codeword;
    cell* data[];
} Word;

void alloc_word(VM* vm, byte* name, i32 length, i32 flags, cell codeword, cell* data) {
    Word* word = (Word*)(vm->dictionary + vm->dictionary_length);
    word->link = vm->latest_word;
    word->name = name; 
    word->length = length;
    word->flags = flags;
    word->codeword = codeword;
    vm->latest_word = (cell*) word;

    if ((flags >> 31) & 1 == 1)  {
        
    } else {
        memcpy(word->data, data, codeword * sizeof(cell*));
        vm->dictionary_length += codeword * sizeof(cell*);
    }
    
    vm->dictionary_length += sizeof(Word);
}

// out: pointer to start of word (at link) (0 if no word)
// in: pointer utf8 name of word
// in: length in bytes of name
cell* find(VM* vm, byte* name, cell length) {
    Word* word = (Word*) vm->latest_word;
    while(!string_eq(word->name, word->length, name, length)) {
        if (word == NULL) {
            return 0;
        }
        word = (Word*) word->link;
    }
    return (cell*) word;
}

byte* read_word(byte* stream, cell stream_length, cell* offset, cell* length) {
    if (*offset >= stream_length) return NULL;

    *length = 0;

    byte c = stream[*offset];
    while (*offset < stream_length && (c == ' ' || c == '\t' || c == '\n')) {
        (*offset)++;
        c = stream[*offset];
    }

    if (*offset >= stream_length) return NULL;

    c = stream[*offset + *length];
    while(*offset + *length < stream_length) {
        if (c == ' ' || c == '\t' || c == '\n') {
            break;
        }
        (*length)++;
        c = stream[*offset + *length];
    }
    byte* result = stream + *offset;
    *offset += *length;
    return result;
}

cell read_number(byte* word, cell length, cell* isNum) {
    cell result = 0;
    int sign = 1;
    cell i = 0;

    *isNum = 0;
    if (length == 0) {
        return 0;
    }

    if(word[0] == '-') {
        sign = -1;
        i = 1;
    } else if(word[0] == '+') {
        i = 1;
    }

    if(i == 1 && length == 1) {
        return 0;
    }

    for (; i < length; i++) {
        if (word[i] == '_') {
            continue;
        }
        if (word[i] < '0' || word[i] > '9') {
            return 0;
        }
        if (result > LLONG_MAX / 10 || (result == LLONG_MAX / 10 && (word[i] - '0') > LLONG_MAX % 10)) {
            return (sign == 1) ? LLONG_MAX : LLONG_MIN;
        }
        result = result * 10 + (word[i] - '0');
    }
    *isNum = 1;
    return result * sign;
}

void builtin_dup(VM* vm) {
    cell val = pop(vm);
    push(vm, val);
    push(vm, val);
}

void builtin_drop(VM* vm) {
    cell _ = pop(vm);
}

void builtin_swap(VM* vm) {
    cell y = pop(vm);
    cell x = pop(vm);
    push(vm, y);
    push(vm, x);
}

void builtin_rot(VM* vm) {
    cell z = pop(vm);
    cell y = pop(vm);
    cell x = pop(vm);
    push(vm, y);
    push(vm, z);
    push(vm, x);
}

void builtin_add(VM* vm) {
    cell n2 = pop(vm);
    cell n1 = pop(vm);
    push(vm, n1 + n2);
}

void builtin_syscall0(VM* vm) {
    cell id = pop(vm);
    push(vm, syscall(id));
}

void builtin_syscall1(VM* vm) {
    cell v1 = pop(vm);
    cell id = pop(vm);
    push(vm, syscall(id, v1));
}

void builtin_syscall2(VM* vm) {
    cell v2 = pop(vm);
    cell v1 = pop(vm);
    cell id = pop(vm);
    push(vm, syscall(id, v1, v2));
}

void builtin_syscall3(VM* vm) {
    cell v3 = pop(vm);
    cell v2 = pop(vm);
    cell v1 = pop(vm);
    cell id = pop(vm);
    push(vm, syscall(id, v1, v2, v3));
}

void builtin_print_string(VM* vm) {
    cell length = pop(vm);
    byte* string = (byte*)pop(vm);
    printf("%.*s\n", (i32)length, string);
}

void builtin_print_integer(VM* vm) {
    cell val = pop(vm);
    printf("%lld\n", val);
}

void execute_builtin_word(VM* vm, Word* word) {
    BUILTIN_FUN fun = (BUILTIN_FUN) word->codeword;
    fun(vm);
}

void execute_word(VM* vm, Word* word) {
    execute_builtin_word(vm, word);
}

void add_builtin(VM* vm, byte* name, void* fn) {
    i32 length = strlen(name);
    i32 flags = 1 << 31;
    alloc_word(vm, name, length, flags, (cell)fn, NULL);
}

void add_builtins(VM* vm) {
    add_builtin(vm, "dup", builtin_dup);
    add_builtin(vm, ".", builtin_print_integer);
    add_builtin(vm, "drop", builtin_drop);
    add_builtin(vm, "swap", builtin_swap);
    add_builtin(vm, "rot", builtin_rot);
    add_builtin(vm, "+", builtin_add);
    add_builtin(vm, "syscall0", builtin_syscall0);
    add_builtin(vm, "syscall1", builtin_syscall0);
    add_builtin(vm, "syscall2", builtin_syscall0);
    add_builtin(vm, "syscall3", builtin_syscall0);
}

int main() {
    VM vm;
    VMInitConfig vm_config = {
        .data_size = DEFAULT_STACK_SIZE,
        .retrain_size = DEFAULT_STACK_SIZE,
        .call_size = DEFAULT_STACK_SIZE,
        .dictionary_size = DEFAULT_STACK_SIZE * 4,
        .quotation_size = DEFAULT_STACK_SIZE * 4,
    };
    init_VM(&vm, vm_config);
    
    add_builtins(&vm);

    byte* stream = "10 3 dup + + .";
    cell stream_length = strlen(stream);
    cell offset = 0;
    cell length = 0;

    byte* word;
    while(1) {
        word = read_word(stream, stream_length, &offset, &length);
        if (word == NULL) break;
        // printf("DEBUG READ: %.*s\n", (int)length, word);

        cell isNum = 0;
        cell num = read_number(word, length, &isNum);
        
        if (isNum) {
            // printf("DEBUG NUM: %lld\n", num);
            push(&vm, num);
            continue;
        }

        Word* dic_word = (Word*) find(&vm, word, length);
        // printf("DEBUG EXEC: %.*s\n", (int)dic_word->length, dic_word->name);
        execute_word(&vm, dic_word);
    }

    deinit_VM(&vm);

    return 0;
}