#include <stdio.h>
#include "utilities.h"


byte* data_stack;
cell data_stack_size;
cell* stack_pointer;

byte* return_stack;
cell return_stack_size;
cell* return_pointer; // is actually just an offset/index

cell* dictionary;
cell* latest_word;
cell* dictionary_size;

/*
    link: 64bit pointer to next Word
    length: size of the name in bytes
    name: utf8 string
    padding: 0-8 bytes long, padding name to 8 bytes
    codeword: 8 bytes
    body: variable sized pointer list with size of size, pointing to words (can be 0)
*/
typedef struct {
    cell* link;
    int length; // length of the string
    byte data[];
} Word;

// out: pointer to start of word (at link)
// in: pointer utf8 name of word
// in: length in bytes of name
cell find_word(cell name, cell length) {
    return 0;
} 

cell pop() {
    return data_stack[--(*stack_pointer)];
}

void push(cell data) {
    data_stack[(*stack_pointer)++] = data;
}

void swap() {
    cell y = pop();
    cell x = pop();
    push(y);
    push(x);
}

void rot() {
    cell z = pop();
    cell y = pop();
    cell x = pop();
    push(y);
    push(z);
    push(x);
}

void add() {
    cell n1 = pop();
    cell n2 = pop();
    push(n1 + n2);
}


int main() {
    return 0;
}