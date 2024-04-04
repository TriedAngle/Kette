CXX=clang++-18
CXXFLAGS= -std=c++20 -Wall -Werror -O2
LDFLAGS = -pthread
SRC_DIR=src
INCLUDE_DIR = include
SOURCES=$(wildcard $(SRC_DIR)/*.cpp)

BUILD_DIR_BASE=build
RELEASE_DIR=$(BUILD_DIR_BASE)/release
DEBUG_DIR=$(BUILD_DIR_BASE)/debug
EXECUTABLE_BASE = kette
EXECUTABLE_RELEASE=$(EXECUTABLE_BASE)
EXECUTABLE_DEBUG=$(EXECUTABLE_BASE)_debug

ifeq ($(MAKECMDGOALS),debug)
	BUILD_DIR=$(DEBUG_DIR)
	CXXFLAGS += -g
	EXECUTABLE=$(EXECUTABLE_DEBUG)
else
	BUILD_DIR=$(RELEASE_DIR)
	EXECUTABLE=$(EXECUTABLE_RELEASE)
endif

OBJECTS=$(patsubst $(SRC_DIR)/%.cpp,$(BUILD_DIR)/%.o,$(SOURCES))


ifeq ($(OS),Windows_NT)
    LDFLAGS = -lpthread
endif

$(EXECUTABLE): $(OBJECTS)
	$(CXX) $(CXXFLAGS) -I$(INCLUDE_DIR) -o $@ $^ $(LDFLAGS)

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp | $(BUILD_DIR)
	$(CXX) $(CXXFLAGS) -I$(INCLUDE_DIR) -c $< -o $@

$(BUILD_DIR):
	mkdir -p $@

run: $(EXECUTABLE_RELEASE)
	./$(EXECUTABLE_RELEASE)

valgrind: $(EXECUTABLE_RELEASE)
	valgrind ./$(EXECUTABLE_RELEASE)

debug: $(EXECUTABLE_DEBUG)

debugrun: debug
	gdb ./$(EXECUTABLE_DEBUG)

clean:
	rm -rf $(BUILD_DIR_BASE) $(EXECUTABLE_RELEASE) $(EXECUTABLE_DEBUG)

.PHONY: run gdbbuild gdbrun valgrind clean