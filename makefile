CC=gcc
CFLAGS=-Iinclude -std=gnu11 -masm=intel -Wall -Werror -O2
SRC_DIR=src
BUILD_DIR=build
SOURCES=$(shell find $(SRC_DIR) -type f -name '*.c')
OBJECTS=$(patsubst $(SRC_DIR)/%.c,$(BUILD_DIR)/%.o,$(SOURCES))
DEPS=$(wildcard include/*.h)

# run with make AVX2=1
# clean before changing
ifdef AVX2
CFLAGS += -mavx2 -D SIMD
endif

# Detect operating system
# link platform specific libraries
ifeq ($(OS),Windows_NT)
    CFLAGS += -D WINDOWS
    ifeq ($(CC),gcc)
        LDFLAGS += -lpthread
    endif
else
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Linux)
        CFLAGS += -D LINUX
        LDFLAGS += -pthread
    endif
	ifeq ($(UNAME_S),Darwin) 
        CFLAGS += -D DARWIN
        LDFLAGS += -pthread
    endif
endif


$(BUILD_DIR)/%.o: $(SRC_DIR)/%.c $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

kette: $(OBJECTS)
	$(CC) -o $@ $^ $(CFLAGS) $(LDFLAGS)

clean:
	rm -f $(BUILD_DIR)/*.o kette

run: kette
	./kette

.PHONY: clean