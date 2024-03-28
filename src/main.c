#define _GNU_SOURCE
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <sys/mman.h>
#include <limits.h>
#include <stddef.h>
#include <assert.h>

// #include "utilities.h"
#include "tryangle.h"

#define DEFAULT_STACK_SIZE 8192
#define QUOTE_HEADER 0x20011217

typedef i64 cell;

typedef struct {
    cell* link;
    byte* name;
    i32 length;
    i32 flags;
    cell* quotation; // function pointer for builtins not a value pointer
} Word;

void print_word(const char* left, Word* word, const char* right) {
    printf("%s%.*s%s", left, word->length, word->name, right);
}

Word* BUILTINS[32] = {};

typedef struct {
    cell data_size, retain_size, call_size; 
    cell quotation_size, dictionary_size;
} VMInitConfig;

typedef struct {
    cell* data_stack;
    cell data_stack_pointer;
    cell data_stack_size;

    cell* retain_stack;
    cell retain_stack_pointer;
    cell retain_stack_size;

    cell* call_stack;
    cell call_stack_pointer;
    cell call_stack_size;

    cell* quotations;
    cell quotations_pointer;
    cell quotation_size;

    Word* dictionary;
    cell dictionary_pointer;
    cell dictionary_size;
    cell* latest_word;

    byte* code;
    cell code_length;
    cell code_offset;

    cell sate;
    cell* current;
    cell* next;
} VM;

typedef void (*VM_FUN)(VM*);

void VM_init(VM* vm, VMInitConfig config) {
    vm->data_stack_size = config.data_size;
    vm->data_stack = mmap(NULL,  config.data_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->data_stack_pointer = 0;

    vm->retain_stack_size = config.retain_size;
    vm->retain_stack = mmap(NULL, config.retain_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->retain_stack_pointer = 0;

    vm->call_stack_size = config.call_size;
    vm->call_stack = mmap(NULL, config.call_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->call_stack_pointer = 0;

    vm->quotation_size = config.quotation_size;
    vm->quotations = mmap(NULL, config.quotation_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->quotations_pointer = 0;

    vm->dictionary_size = config.dictionary_size;
    vm->dictionary = mmap(NULL, config.dictionary_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->dictionary_pointer = 0;
    vm->latest_word = NULL;
}


void VM_deinit(VM* vm) {
    munmap(vm->data_stack, vm->data_stack_size);
    munmap(vm->retain_stack, vm->retain_stack_size);
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

cell* data_stack_top(VM* vm) {
    return vm->data_stack + vm->data_stack_pointer;
}

cell rpop(VM* vm) {
    return vm->retain_stack[--(vm->retain_stack_pointer)];
}

void rpush(VM* vm, cell data) {
    vm->retain_stack[(vm->retain_stack_pointer)++] = data;
}

cell cpop(VM* vm) {
    return vm->call_stack[--(vm->call_stack_pointer)];
}

void cpush(VM* vm, cell data) {
    vm->call_stack[(vm->call_stack_pointer)++] = data;
}

void qpush(VM* vm, cell data) {
    vm->quotations[(vm->quotations_pointer)++] = data;
}


void VM_bind_code(VM* vm, byte* code, cell length) {
    vm->code = code;
    vm->code_length = length;
    vm->code_offset = 0;
}

void VM_execute_builtin(VM* vm, Word* word) {
    VM_FUN fun = (VM_FUN) word->quotation;
    fun(vm);
}

void VM_return(VM* vm) {
    cpop(vm);
    // TODO implement
}

cell VM_next(VM* vm) {
    cell value = *vm->current;
    vm->current = vm->next;
    vm->next += 1;
    return value;
}


void VM_enter(VM* vm, cell* quot) {
    // cpush(vm, vm->current);
    vm->next = quot;
    VM_next(vm);
    cell val = VM_next(vm);
    assert(val == QUOTE_HEADER);
}


int string_eq(const byte* str1, i32 length1, const byte* str2, i32 length2) {
    if (length1 != length2) return 0;
    for (int i = 0; i < length1; i++) {
        if (str1[i] != str2[i]) {
            return 0;
        }
    }
    return 1;
}

Word* alloc_word(VM* vm, byte* name, i32 length, i32 flags, cell* quotation) {
    Word* word = vm->dictionary + vm->dictionary_pointer;
    word->link = vm->latest_word;
    word->name = name; 
    word->length = length;
    word->flags = flags;
    word->quotation = quotation;
    vm->latest_word = (cell*) word;
    vm->dictionary_pointer++;
    return word;
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

void builtin_quot(VM*);
void builtin_ret(VM*);
void builtin_quot_end(VM*);
void builtin_lit(VM*);

void start_quotation(VM* vm) {
    qpush(vm, QUOTE_HEADER);
}

void end_quotation(VM* vm) {
    cell* word = find(vm, (byte*)"return", 6);
    qpush(vm, (cell)word);
}

cell* alloc_quotation(VM* vm, cell size, cell* body) {
    cell* start = vm->quotations + vm->quotations_pointer;
    start_quotation(vm);
    for(cell i = 0; i < size; i++) {
        qpush(vm, body[i]);
    }
    end_quotation(vm);
    return start;
}

byte* read_word(VM* vm, cell* length) {
    byte* stream = vm->code;
    cell stream_length = vm->code_length;
    cell* offset = &vm->code_offset;

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

cell* read_until(VM* vm, cell *word_count, byte* ident, cell ident_length) {
    cell length;
    byte* word;
    cell number;
    cell is_number;
    cell* start = data_stack_top(vm);
    Word* found_word;
    while(1) {
        word = read_word(vm, &length);
        if (word == NULL) {
            break;
        }

        number = read_number(word, length, &is_number);
        if (string_eq(ident, ident_length, word, length)) {
            break;
        } else if (is_number) {
            push(vm, (cell)BUILTINS[13]);
            push(vm, number);
            *word_count += 2;
            continue;
        } 
        
        found_word = (Word*)find(vm, word, length);
        if (found_word == NULL) {
            // TODO HANDLE ERROR
        }
        if (read_nth_bit(found_word->flags, 30)) {
            if (read_nth_bit(found_word->flags, 31)) {
                VM_execute_builtin(vm, found_word);
                continue;
            } else {

            }
        }
        push(vm, (cell)found_word);
        *word_count += 1;
    }
    
    return start;    
}


void clear_mem(cell* start, cell count) {
    for (cell i = 0; i < count; i++){
        start[i] = (cell)0;
    }
}

void builtin_quot(VM* vm) {
    byte* end = (byte*)"]";
    cell word_count = 0;
    cell* start = read_until(vm, &word_count, end, 1);
    if (start == NULL) {
        // TODO ERROR;
    }
    cell* quot = alloc_quotation(vm, word_count, start);
    clear_mem(start, word_count);
    vm->call_stack_pointer -= word_count;
    push(vm, (cell)quot);
}


void builtin_lit(VM* vm) {
    cell value = VM_next(vm);
    push(vm, value);
}

void builtin_ret(VM* vm) {
    printf("shouldn't be called");
}

void builtin_call(VM* vm) {
    cell* quot = (cell*)pop(vm);
    quot += 1;
}

void builtin_dup(VM* vm) {
    cell val = pop(vm);
    push(vm, val);
    push(vm, val);
}

void builtin_drop(VM* vm) {
    pop(vm);
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

void builtin_unsafe_vm(VM* vm) {
    push(vm, (cell) vm);
}

void add_builtin(VM* vm, cell id, const str* name, void* fn) {
    i32 length = strlen(name);
    i32 flags = (i32)set_nth_bit(0, 31, 1);
    Word* word = alloc_word(vm, (byte*)name, length, flags, (cell*)fn);
    BUILTINS[id] = word;
}

void add_parsing_builtin(VM* vm, cell id, const str* name, void* fn) {
    i32 length = strlen(name);
    i32 flags = (i32)set_nth_bit(set_nth_bit(0, 31, 1), 30, 1);
    Word* word = alloc_word(vm, (byte*)name, length, flags, (cell*)fn);
    BUILTINS[id] = word;
}

void add_builtins(VM* vm) {
    add_builtin(vm, 0, "dup", builtin_dup);
    add_builtin(vm, 1, ".", builtin_print_integer);
    add_builtin(vm, 2, "drop", builtin_drop);
    add_builtin(vm, 3, "swap", builtin_swap);
    add_builtin(vm, 4, "rot", builtin_rot);
    add_builtin(vm, 5, "+", builtin_add);
    add_parsing_builtin(vm, 6, "[", builtin_quot);
    add_builtin(vm, 7, "syscall0", builtin_syscall0);
    add_builtin(vm, 8, "syscall1", builtin_syscall1);
    add_builtin(vm, 9, "syscall2", builtin_syscall2);
    add_builtin(vm, 10, "syscall3", builtin_syscall3);
    add_builtin(vm, 11, "let-me-cook", builtin_unsafe_vm);
    add_builtin(vm, 12, "call", builtin_call);
    add_builtin(vm, 13, "LITERAL", builtin_lit);
    add_builtin(vm, 14, "return", builtin_ret);
}

cell* VM_read_until_end(VM* vm) {
    cell word_count = 0;
    cell* quot;
    cell* start = read_until(vm, &word_count, NULL, -1);
    quot = alloc_quotation(vm, word_count, start);
    clear_mem(start, word_count);
    vm->data_stack_pointer -= word_count;
    push(vm, (cell)quot);
    return quot;
}

int main() {
    VM vm;
    VMInitConfig vm_config = {
        .data_size = DEFAULT_STACK_SIZE,
        .retain_size = DEFAULT_STACK_SIZE,
        .call_size = DEFAULT_STACK_SIZE,
        .dictionary_size = DEFAULT_STACK_SIZE * 4,
        .quotation_size = DEFAULT_STACK_SIZE * 4,
    };
    VM_init(&vm, vm_config);
    
    add_builtins(&vm);

    str* stream = "10 3 dup + + .";
    cell stream_length = strlen(stream);

    VM_bind_code(&vm, (byte*)stream, stream_length);

    cell* entry = VM_read_until_end(&vm);
    VM_enter(&vm, entry);
    
    while(1) {
        cell current = VM_next(&vm);
        Word* word = (Word*)current;
        
        if(word == BUILTINS[14]) {
            break;
        }

        if(read_nth_bit(word->flags, 31)) {
            VM_execute_builtin(&vm, word);
        }
    }

    VM_deinit(&vm);

    return 0;
}