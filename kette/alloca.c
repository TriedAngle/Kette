#include <stddef.h>
#include <stdint.h>
#include <alloca.h>

typedef uint8_t u8;
typedef size_t usize;

void stack_allocate_callback(usize size, void (*callback)(u8*, void*), void* data) {
    u8 *buffer = alloca(size);
    return callback(&buffer[0], data);
}