CXX=clang++-18
CXXFLAGS= -std=c++20 -Wall -Werror -O2
LDFLAGS = -pthread
SRC_DIR=src
BUILD_DIR=build
INCLUDE_DIR = include
SOURCES=$(wildcard $(SRC_DIR)/*.cpp)
OBJECTS=$(patsubst $(SRC_DIR)/%.cpp,$(BUILD_DIR)/%.o,$(SOURCES))
EXECUTABLE = kette



ifeq ($(OS),Windows_NT)
    LDFLAGS = -lpthread
endif

$(EXECUTABLE): $(OBJECTS)
	$(CXX) $(CXXFLAGS) -I$(INCLUDE_DIR) -o $@ $^ $(LDFLAGS)

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp | $(BUILD_DIR)
	$(CXX) $(CXXFLAGS) -I$(INCLUDE_DIR) -c $< -o $@

$(BUILD_DIR):
	mkdir -p $@

gdbbuild: CXXFLAGS += -g
gdbbuild: $(EXECUTABLE)

run: $(EXECUTABLE)
	./$(EXECUTABLE)

valgrind: $(EXECUTABLE)
	valgrind ./$(EXECUTABLE)

gdbrun: gdbbuild
	gdb ./$(EXECUTABLE)

clean:
	rm -rf $(BUILD_DIR) $(EXECUTABLE)

.PHONY: all run gdb valgrind clean