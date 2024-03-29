#include <stdio.h>

#include <string.h>
#include <unistd.h>

#include <limits.h>
#include <stddef.h>
#include <assert.h>

// #include "utilities.h"
#include "defaults.h"
#include "allocators.h"

#define DEFAULT_STACK_SIZE 8192
#define QUOTE_HEADER 0x20011217
#define QUOTE_END_HEADER 0x20050801


i64 set_nth_bit(i64 val, i32 nth, byte tf) {
    if(tf == 0) {
        return val & ~(1LL << nth);
    } else {
        return val | (1LL << nth);
    }
}

byte read_nth_bit(i64 val, i32 nth) {
    i64 mask = 1ULL << nth;
    return (val & mask) ? 1 : 0;
}

typedef struct {
    cell* link;
    byte* name;
    i32 length;
    i32 flags;
    cell* quotation; // function pointer for builtins not a value pointer
} Word;

cell BUILTIN_COUNT = 0;
Word* BUILTINS[64] = {};

void print_word(const char* left, Word* word, const char* right) {
    printf("%s%.*s%s", left, word->length, word->name, right);
}

void print_quotation(cell* entry) {
    assert(*entry == QUOTE_HEADER);
    printf("[");
    while(1) {
        entry += 1;
        if(*entry == QUOTE_END_HEADER) break;
        
        Word* word = (Word*) *entry;
        if (word == BUILTINS[0]) {
            entry += 1;
            cell num = *entry;
            print_word(" ", word, "");
            printf("(%lld)", num);
        } else {
            print_word(" ", word, "");
        }
    }
    printf(" ]\n");
}



typedef struct {
    cell data_size, retain_size, call_size; 
    cell quotation_size, dictionary_size;
    cell strings_size;
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

    byte* strings;
    cell strings_offset;
    cell strings_size;

    cell state;
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

    vm->strings_size = config.strings_size;
    vm->strings = mmap(NULL, config.strings_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    vm->strings_offset = 0;
}


void VM_deinit(VM* vm) {
    munmap(vm->data_stack, vm->data_stack_size);
    munmap(vm->retain_stack, vm->retain_stack_size);
    munmap(vm->call_stack, vm->call_stack_size);

    munmap(vm->dictionary, vm->dictionary_size);
    munmap(vm->quotations, vm->quotation_size);
    munmap(vm->strings, vm->strings_size);
}

cell* VM_data_stack_top(VM* vm) {
    return vm->data_stack + vm->data_stack_pointer;
}

cell pop(VM* vm) {
    return vm->data_stack[--(vm->data_stack_pointer)];
}

void push(VM* vm, cell data) {
    vm->data_stack[vm->data_stack_pointer++] = data;
}

cell rpop(VM* vm) {
    return vm->retain_stack[--(vm->retain_stack_pointer)];
}

void rpush(VM* vm, cell data) {
    vm->retain_stack[vm->retain_stack_pointer++] = data;
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
    // lol this is needed because VM_next could deref segment fault error otherwise
    vm->current = quot; 
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

byte* alloc_string(VM* vm, byte* string, cell length) {
    byte* location = vm->strings + vm->strings_offset;
    for(int i = 0; i<length; i++) {
        location[i] = string[i];
    }
    location[length] = '\0';
    vm->strings_offset += length + 1;
    return location;
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

void start_quotation(VM* vm) {
    qpush(vm, QUOTE_HEADER);
}

void end_quotation(VM* vm) {
    qpush(vm, (cell)BUILTINS[1]);
    qpush(vm, QUOTE_END_HEADER);
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

// out: pointer to start of word (at link) (0 if no word)
// in: pointer utf8 name of word
// in: length in bytes of name
cell* find(VM* vm, byte* name, cell length) {
    Word* word = (Word*) vm->latest_word;
    for(;;) {
        if (word == NULL) {
            return NULL;
        }
        if (string_eq(word->name, word->length, name, length)) {
            break;
        }
        word = (Word*) word->link;
    }
    return (cell*) word;
}

void builtin_quot(VM*);
void builtin_ret(VM*);
void builtin_quot_end(VM*);
void builtin_lit(VM*);
void builtin_call(VM*);
void builtin_word2quot(VM*);

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

// like read_word but doesn't consume the word
byte* peek_word(VM* vm, cell* length) {
    cell offset = vm->code_offset;
    byte* word = read_word(vm, length);
    vm->code_offset = offset;
    return word;
}

cell read_number(byte* word, cell length) {
    cell result = 0;
    
    for (int i = 0; i < length; ++i) {
        if (word[i] >= '0' && word[i] <= '9') {
            result = result * 10 + (word[i] - '0');
        } else if (word[i] == '_') {
            continue;
        } else {
            return -1;
        }
    }
    
    return result;
}

cell read_until(VM* vm, byte* ident, cell ident_length) {
    cell word_count = 0;
    cell length;
    byte* word;
    
    Word* found_word;
    while(1) {
        word = read_word(vm, &length);
        
        if (word == NULL) {
            break;
        }

        if (string_eq(ident, ident_length, word, length)) {
            break;
        }

        cell number = read_number(word, length);

        if (number != -1) {
            push(vm, (cell)BUILTINS[0]);
            push(vm, number);
            word_count += 2;
            continue;
        } 
        
        found_word = (Word*)find(vm, word, length);
        
        if (found_word == NULL) {

            // TODO HANDLE ERROR
        }
        if (read_nth_bit(found_word->flags, 30)) {
            if (read_nth_bit(found_word->flags, 31)) {
                VM_execute_builtin(vm, found_word);
                // this is kind of a hack, maybe find better solution?
                // essentially this expects every parser word to tell push
                // how many things they added to the stack
                word_count += pop(vm); 
                continue;
            } else {
                push(vm, (cell)found_word->quotation);
                builtin_call(vm);
                word_count += pop(vm); 
                continue;
            }
        }
        push(vm, (cell)found_word);
        word_count += 1;
    }
    
    return word_count;    
}


void clear_mem(cell* start, cell count) {
    for (cell i = 0; i < count; i++){
        start[i] = (cell)0;
    }
}

void builtin_quot(VM* vm) {
    cell* start = VM_data_stack_top(vm);
    cell word_count = read_until(vm, (byte*)"]", 1);
    if (start == NULL) {
        // TODO ERROR;
    }
    cell* quot = alloc_quotation(vm, word_count, start);
    clear_mem(start, word_count);
    vm->data_stack_pointer -= word_count;
    push(vm, (cell)BUILTINS[0]);
    push(vm, (cell)quot);
    push(vm, (cell)2);
}

void parse_stack_effect(VM* vm) {
    // let's just ignore stack effects for now lol
    cell paren_length;
    byte* paren_name = read_word(vm, &paren_length);
    assert(string_eq(paren_name, paren_length, (byte*)"(", 1));

    cell length;
    byte* word;
    while(1) {
        word = read_word(vm, &length);
        if (string_eq(word, length, (byte*)")", 1)) {
            break;
        }
    }
}

void builtin_colon(VM* vm) {
    cell name_length;
    byte* name_read = read_word(vm, &name_length);
    byte* name = alloc_string(vm, name_read, name_length);
    cell maybe_se_length;
    byte* maybe_se = peek_word(vm, &maybe_se_length);
    if(string_eq(maybe_se, maybe_se_length, (byte*)"(", 1)) {
        parse_stack_effect(vm);
    }

    cell* start = VM_data_stack_top(vm);
    cell word_count = read_until(vm, (byte*)";", 1);
    if (start == NULL) {
        // TODO ERROR;
    }
    cell* quot = alloc_quotation(vm, word_count, start);
    alloc_word(vm, name, name_length, 0, quot);

    clear_mem(start, word_count);
    vm->data_stack_pointer -= word_count;
    
    push(vm, 0);
}

void builtin_syntax(VM* vm) {
    builtin_colon(vm);
    Word* word = (Word*)vm->latest_word;
    word->flags = (i32)set_nth_bit(word->flags, 30, 1);
}


void builtin_lit(VM* vm) {
    cell value = VM_next(vm);
    push(vm, value);
}

void builtin_ret(VM* vm) {
    printf("shouldn't be called");
}

void builtin_interpret(VM* vm) {
    while(1) {
        cell current = VM_next(vm);
        Word* word = (Word*)current;

        if(word == BUILTINS[1]) {
            break;
        }

        if(read_nth_bit(word->flags, 31) == 1) {
            VM_execute_builtin(vm, word);
            continue;
        }

        push(vm, (cell)word->quotation);
        builtin_call(vm);
    }
}

void builtin_call(VM* vm) {
    cpush(vm, (cell)vm->current);
    cell* quot = (cell*) pop(vm);
    VM_enter(vm, quot);

    builtin_interpret(vm);

    vm->current = (cell*)cpop(vm);
    vm->next = vm->current + 1;
}

void builtin_load(VM* vm) {
    cell* address = (cell*)pop(vm);
    cell value = *address;
    push(vm, value);
}

void builtin_store(VM* vm) {
    cell* address = (cell*)pop(vm);
    cell value = pop(vm);
    *address = value;
}

void builtin_dup(VM* vm) {
    cell val = pop(vm);
    push(vm, val);
    push(vm, val);
}

void builtin_dupd(VM* vm) {
    cell top = pop(vm);
    cell val = pop(vm);
    push(vm, val);
    push(vm, val);
    push(vm, top);
}

void builtin_2dup(VM* vm) {
    cell y = pop(vm);
    cell x = pop(vm);
    push(vm, x);
    push(vm, y);
    push(vm, x);
    push(vm, y);
}

void builtin_drop(VM* vm) {
    pop(vm);
}

void builtin_dropd(VM* vm) {
    cell y = pop(vm);
    pop(vm);
    push(vm, y);
}

void builtin_swap(VM* vm) {
    cell y = pop(vm);
    cell x = pop(vm);
    push(vm, y);
    push(vm, x);
}

void builtin_swapd(VM* vm) {
    cell z = pop(vm);
    cell y = pop(vm);
    cell x = pop(vm);
    push(vm, y);
    push(vm, x);
    push(vm, z);
}

void builtin_over(VM* vm) {
    cell val = vm->data_stack[vm->data_stack_pointer - 2];
    push(vm, val);
}

void builtin_pick(VM* vm) {
    cell val = vm->data_stack[vm->data_stack_pointer - 3];
    push(vm, val);
}

void builtin_rot(VM* vm) {
    cell z = pop(vm);
    cell y = pop(vm);
    cell x = pop(vm);
    push(vm, y);
    push(vm, z);
    push(vm, x);
}

void builtin_rrot(VM* vm) {
    cell z = pop(vm);
    cell y = pop(vm);
    cell x = pop(vm);
    push(vm, z);
    push(vm, x);
    push(vm, y);
}

void builtin_dip(VM* vm) {
    builtin_swap(vm);
    rpush(vm, pop(vm));
    builtin_call(vm);
    push(vm, rpop(vm));
}

void builtin_neg(VM* vm) {
    push(vm, -pop(vm));
}

void builtin_add(VM* vm) {
    cell n2 = pop(vm);
    cell n1 = pop(vm);
    push(vm, n1 + n2);
}

void builtin_sub(VM* vm) {
    cell n2 = pop(vm);
    cell n1 = pop(vm);
    push(vm, n1 - n2);
}

void builtin_mul(VM* vm) {
    cell n2 = pop(vm);
    cell n1 = pop(vm);
    push(vm, n1 * n2);
}

void builtin_div(VM* vm) {
    cell n2 = pop(vm);
    cell n1 = pop(vm);
    push(vm, n1 / n2);
}

void builtin_mod(VM* vm) {
    cell n2 = pop(vm);
    cell n1 = pop(vm);
    push(vm, n1 % n2);
}

void builtin_if(VM* vm) {
    cell f = pop(vm);
    cell t = pop(vm);
    cell b = pop(vm);
    if(b) {
        push(vm, t);
    } else {
        push (vm, f);
    }
    builtin_call(vm);
}

void builtin_eq(VM* vm) {
    cell b = pop(vm);
    cell a = pop(vm);
    push(vm, a == b);
}

void builtin_and(VM* vm) {
    cell b = pop(vm);
    cell a = pop(vm);
    push(vm, a && b);
}

void builtin_or(VM* vm) {
    cell b = pop(vm);
    cell a = pop(vm);
    push(vm, a || b);
}

void builtin_not(VM* vm) {
    cell a = pop(vm);
    push(vm, !a);
}

void builtin_bitand(VM* vm) {
    cell b = pop(vm);
    cell a = pop(vm);
    push(vm, a & b);
}

void builtin_bitor(VM* vm) {
    cell b = pop(vm);
    cell a = pop(vm);
    push(vm, a | b);
}

void builtin_bitxor(VM* vm) {
    cell b = pop(vm);
    cell a = pop(vm);
    push(vm, a ^ b);
}

void builtin_lshift(VM* vm) {
    cell b = pop(vm);
    cell a = pop(vm);
    push(vm, a << b);
}

void builtin_rshift(VM* vm) {
    cell b = pop(vm);
    cell a = pop(vm);
    push(vm, a >> b);
}

void builtin_bitnot(VM* vm) {
    cell a = pop(vm);
    push(vm, ~a);
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

void builtin_syscall4(VM* vm) {
    cell v4 = pop(vm);
    cell v3 = pop(vm);
    cell v2 = pop(vm);
    cell v1 = pop(vm);
    cell id = pop(vm);
    push(vm, syscall(id, v1, v2, v3, v4));
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

void builtin_print_quot(VM* vm) {
    cell val = pop(vm);
    print_quotation((cell*)val);
}

void builtin_unsafe_vm(VM* vm) {
    push(vm, (cell) vm);
}

void builtin_LATEST(VM* vm) {
    push(vm, (cell)vm->latest_word);
}

void builtin_word2quot(VM* vm) {
    Word* word = (Word*)pop(vm);
    push(vm, (cell)word->quotation);
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
    int c = 0;
    add_builtin(vm, c++, "LITERAL", builtin_lit);
    add_builtin(vm, c++, "return", builtin_ret);

    add_parsing_builtin(vm, c++, "[", builtin_quot);
    add_parsing_builtin(vm, c++, ":", builtin_colon);
    add_parsing_builtin(vm, c++, "syn:", builtin_syntax);
    
    add_builtin(vm, c++, "call", builtin_call);
    add_builtin(vm, c++, "@", builtin_load);
    add_builtin(vm, c++, "!", builtin_store);
    add_builtin(vm, c++, ".", builtin_print_integer);
    add_builtin(vm, c++, ".q", builtin_print_quot);
    add_builtin(vm, c++, "drop", builtin_drop);
    add_builtin(vm, c++, "dropd", builtin_dropd);
    add_builtin(vm, c++, "dup", builtin_dup);
    add_builtin(vm, c++, "dupd", builtin_dupd);
    add_builtin(vm, c++, "over", builtin_over);
    add_builtin(vm, c++, "swap", builtin_swap);
    add_builtin(vm, c++, "swapd", builtin_swap);
    add_builtin(vm, c++, "rot", builtin_rot);
    add_builtin(vm, c++, "-rot", builtin_rrot);
    add_builtin(vm, c++, "dip", builtin_dip);
    add_builtin(vm, c++, "neg", builtin_neg);
    add_builtin(vm, c++, "+", builtin_add);
    add_builtin(vm, c++, "-", builtin_sub);
    add_builtin(vm, c++, "*", builtin_mul);
    add_builtin(vm, c++, "/", builtin_div);
    add_builtin(vm, c++, "%", builtin_mod);
    add_builtin(vm, c++, "/", builtin_div);
    add_builtin(vm, c++, "if", builtin_if);
    add_builtin(vm, c++, "=", builtin_eq);
    add_builtin(vm, c++, "and", builtin_and);
    add_builtin(vm, c++, "or", builtin_or);
    add_builtin(vm, c++, "not", builtin_not);
    add_builtin(vm, c++, "bit&", builtin_bitand);
    add_builtin(vm, c++, "bit|", builtin_bitor);
    add_builtin(vm, c++, "bit^", builtin_bitxor);
    add_builtin(vm, c++, "bit<<", builtin_lshift);
    add_builtin(vm, c++, "bit>>", builtin_rshift);
    add_builtin(vm, c++, "bit~", builtin_bitnot);
    add_builtin(vm, c++, "syscall0", builtin_syscall0);
    add_builtin(vm, c++, "syscall1", builtin_syscall1);
    add_builtin(vm, c++, "syscall2", builtin_syscall2);
    add_builtin(vm, c++, "syscall3", builtin_syscall3);
    add_builtin(vm, c++, "syscall4", builtin_syscall4);
    add_builtin(vm, c++, "let-me-cook", builtin_unsafe_vm);
    add_builtin(vm, c++, "LATEST", builtin_LATEST); // todo impl in lang
    add_builtin(vm, c++, "word>quot", builtin_word2quot); // todo impl in lang
}

cell* VM_compile(VM* vm) {
    cell* quot;
    cell* start = VM_data_stack_top(vm);
    cell word_count = read_until(vm, NULL, -1);
    quot = alloc_quotation(vm, word_count, start);
    clear_mem(start, word_count);
    vm->data_stack_pointer -= word_count;
    return quot;
}

int main() {
    i64 arr[4] = {0};
    arr[3] = 1LL << 21;
    int index = findFirstBit(arr);
    printf("First 1 bit is at position: %d\n", index);
    return 0; 
}

// int main(int argc, char* argv[]) {
//     VM vm;
//     VMInitConfig vm_config = {
//         .data_size = DEFAULT_STACK_SIZE,
//         .retain_size = DEFAULT_STACK_SIZE,
//         .call_size = DEFAULT_STACK_SIZE,
//         .dictionary_size = DEFAULT_STACK_SIZE * 4,
//         .quotation_size = DEFAULT_STACK_SIZE * 4,
//         .strings_size = DEFAULT_STACK_SIZE * 4,
//     };
//     VM_init(&vm, vm_config);
    
//     add_builtins(&vm);

//     int mode = 0;
//     // TODO: files
//     // byte buffer[100] = {};

//     for (int i = 1; i < argc; i++) {
//         if (strcmp(argv[i], "--manual") == 0) {
//             mode = 1;
//         }
//     }


//     if (mode == 1) {
//         str* stream = "[ 10 [ 5 + ] call . ] dup .q call";
//         cell stream_length = strlen(stream);

//         VM_bind_code(&vm, (byte*)stream, stream_length);
//         cell* entry = VM_compile(&vm);

//         VM_enter(&vm, entry);
//         builtin_interpret(&vm);

        
//     } else {
//         str* input_buffer = (str*)malloc(1000 * sizeof(str)); 
//         cell input_size = 0;
//         while(1) {
//             printf("> ");
//             fgets(input_buffer, 1000, stdin);
//             if (strcmp(input_buffer, "quit\n") == 0) {
//                 break;
//             }
            
//             input_size = strlen(input_buffer);
//             VM_bind_code(&vm, (byte*)input_buffer, input_size);
//             cell* entry = VM_compile(&vm);
//             VM_enter(&vm, entry);
//             builtin_interpret(&vm);
//         }
//     }

//     VM_deinit(&vm);
//     return 0;
// }