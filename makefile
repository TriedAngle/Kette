CC=gcc
CFLAGS=-Iinclude -std=gnu11 -masm=intel -Wall -O2
SRC_DIR=src
BUILD_DIR=build
SOURCES=$(wildcard $(SRC_DIR)/*.c)
OBJECTS=$(patsubst $(SRC_DIR)/%.c,$(BUILD_DIR)/%.o,$(SOURCES))
DEPS=$(wildcard include/*.h)

# run with make AVX2=1
# clean before changing
ifdef AVX2
CFLAGS += -mavx2 -D SIMD
endif

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.c $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

kette: $(OBJECTS)
	$(CC) -o $@ $^ $(CFLAGS)

clean:
	rm -f $(BUILD_DIR)/*.o kette

run: kette
	./kette

.PHONY: clean