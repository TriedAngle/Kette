#include "code.h"
#include "vm.h"

CodeHeap initCodeHeap(Allocator allocator) {
    CodeHeap ch;
    ch.ga = allocator;
    ch.code = initHashMap(ch.ga, 165); // almost 1 page
    ch.compiled = initHashMap(ch.ga, 165); // almost 1 page 
    return ch;
}

void deinitCodeHeap(CodeHeap* ch) {
    deinitHashMap(&ch->compiled);
    deinitHashMap(&ch->code);
}

void write_string_len_into(char* buffer, char* str, int length) {
    for (int i = 0; i < length; i++) {
        buffer[i] = str[i];
    }
}

void write_string_into(char* buffer, char* str) {
    for (int i = 0; str[i] != 0; i++) {
        buffer[i] = str[i];
    }
}

void write_push(char* buffer) {
    write_string_into(buffer, "PUSH");
}
void write_fixnum(char* buffer) {
    write_string_into(buffer, "PUSH FIXNUM");
}
void write_fixfloat(char* buffer) {
    write_string_into(buffer, "PUSH FIXFLOAT");
}
void write_self(char* buffer) {
    write_string_into(buffer, "PUSH SELF");
}
void write_object(char* buffer) {
    write_string_into(buffer, "PUSH OBJECT");
}
void write_byte(char* buffer, byte b) {
    int neededSize = snprintf(NULL, 0, "%02X", b) + 1;
    char* buf = (char*)malloc(neededSize);

    snprintf(buf, neededSize, "%02X", b);
    memcpy(buffer, buf, neededSize-1);
    free(buf);
}
void write_i64(char* buffer, i64 num) {
    int neededSize = snprintf(NULL, 0, "%lld", num) + 1;
    char* buf = (char*)malloc(neededSize);

    snprintf(buf, neededSize, "%lld", num);
    memcpy(buffer, buf, neededSize);
    free(buf);
}

void write_f64(char* buffer, f64 num) {
    int neededSize = snprintf(NULL, 0, "%f", num) + 1;
    char* buf = (char*)malloc(neededSize);

    snprintf(buf, neededSize, "%f", num);
    memcpy(buffer, buf, neededSize);
    free(buf);
}

void write_ptr(char* buffer, void* num) {
    int neededSize = snprintf(NULL, 0, "%p", num) + 1;
    char* buf = (char*)malloc(neededSize);

    snprintf(buf, neededSize, "%p", num);
    memcpy(buffer, buf, neededSize);
    free(buf);
}


void printCodeBlock(CodeBlock* cb) {
    byte* start = (byte*)cb->bytecode.allocation;
    char buffer[100];
    memset(buffer, ' ', sizeof(char)*100);
    int offset = 0;
    word* w;
    bytearray* s;
    while(offset < cb->bytecode.length) {
        byte instr = *(start + offset);
        memset(buffer, ' ', 100);
        write_byte(buffer, instr);
        offset += 1;
        switch(instr) {
            case bcNoop:
                break;
            case bcSelf:
                write_self(buffer + 6);
                break;
            case bcLiteral:
                cell literal = *(cell*)(start + offset);
                offset += 8;
                switch ((byte)read_tag(literal)) {
                    case FIXNUM_TAG:
                        i64 num = untag_num(literal);
                        write_fixnum(buffer + 5);
                        write_i64(buffer + 32, num);
                        break;
                    case FLOAT_TAG:
                        f64 fnum = untag_float(literal);
                        write_fixfloat(buffer + 5);
                        write_f64(buffer + 32, fnum);
                        break;
                    case OBJECT_TAG:
                        cell ptr = remove_tag(literal);
                        write_object(buffer + 5);
                        write_ptr(buffer + 32, (void*)ptr);
                        break;
                }
                break;
            case bcSend:
                // w = (word*)instr;
                // s = (bytearray*)w->name;
                // instr += 8;
                // sprintf(&buffer[6], "SEND SELF");
                // sprintf(&buffer[32], "%.*s", (int)s->size, (char*)s->data);
                break;
            case bcPrimitive:
                cell prim = *(cell*)(start + offset);
                offset += 8;
                i32 index = prim >> 32;
                i32 inout = (i32)prim;
                i16 in = codeGetIn(inout);
                i16 out = codeGetOut(inout);
                w = GET_PRIMITIVE_WORD(index);
                s = (bytearray*)remove_tag(w->name);
                write_string_into(buffer + 5, "SEND PRIMITIVE");
                write_byte(buffer + 22, in);
                write_byte(buffer + 27, out);
                write_string_len_into(buffer + 32, (char*)s->data, (int)untag_num(s->size));
                break;
            case bcReturn:
                return;
            default: 
                return;
        }

        buffer[99] = '\0';
        printf("%s\n", buffer);
    }
}

void pushInstruction(CodeBlock* cb, byte instr) {
    gaPush(&cb->bytecode, (void*)&instr);
}

void pushCell(CodeBlock* cb, cell c) {
    for (int i = 0; i < 8; i++) {
        byte b = (c >> (8 * i)) & 0xFF;
        gaPush(&cb->bytecode, (void*)&b);
    }
}

void bcPushInteger(CodeBlock* cb, i64 integer) {
    pushInstruction(cb, (byte)bcLiteral);
    cell fixnum = tag_num(integer);
    pushCell(cb, fixnum);
}

void bcPushFloat(CodeBlock* cb, f64 num) {
    pushInstruction(cb, (byte)bcLiteral);
    cell fixfloat = tag_float(num);
    pushCell(cb, fixfloat);
}

void bcPushObject(CodeBlock* cb, cell obj) {
    pushInstruction(cb, (byte)bcLiteral);
    pushCell(cb, obj);
}

void bcPushSelf(CodeBlock* cb) {
    pushInstruction(cb, (byte)bcSelf);
}
void bcPushSend(CodeBlock* cb) {
    pushInstruction(cb, (byte)bcSend);
}
void bcPushSendSelf(CodeBlock* cb) {
    pushInstruction(cb, (byte)bcSendSelf);
}
void bcPushSendSuper(CodeBlock* cb) {
    pushInstruction(cb, (byte)bcSendSuper);
}
void bcPushSendDelegate(CodeBlock* cb) {
    pushInstruction(cb, (byte)bcSendDelegate);
}
void bcPushSendEnter(CodeBlock* cb) {
    pushInstruction(cb, (byte)bcEnter);
}
void bcPushSendReturn(CodeBlock* cb)  {
    pushInstruction(cb, (byte)bcReturn);
}
void bcPushLocalJump(CodeBlock* cb, cell to) {
    cell dest = (to << 1) + 1;
    pushInstruction(cb, (byte)bcLocalJump);
    pushCell(cb, dest);
}
void bcPushPrimitive(CodeBlock* cb, i32 index, i32 inout) {
    pushInstruction(cb, (byte)bcPrimitive);
    cell instr = ((cell)index << 32) | inout;
    pushCell(cb, instr);
}

CodeBlock* chAllocateCodeBlock(CodeHeap* ch, cell key) {
    CodeBlock* cb = tcreate(&ch->ga, sizeof(CodeBlock));
    cb->owner = key;
    cb->bytecode = initGrowableArray(ch->ga, 128, 1);
    hmInsert(&ch->compiled, key, (cell)cb);
    return cb;
}

void chDeallocateCodeBlock(CodeHeap* ch, cell key) {
    CodeBlock* cb = (CodeBlock*)hmDelete(&ch->compiled, key);
    deinitGrowableArray(&cb->bytecode);
    tdelete(&ch->ga, (void*)cb, sizeof(CodeBlock));
}

void chCompile(CodeHeap* ch, word* word);


i32 codeCreateInOut(i16 in, i16 out) {
    return in << 16 | out;
}

i16 codeGetIn(i32 inout) {
    return inout >> 16;
}

i16 codeGetOut(i32 inout) {
    return (i16)inout;
}