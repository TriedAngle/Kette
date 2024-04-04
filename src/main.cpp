#include "sanity.h"
#include "vm.h"
#include "test.h"
#include <format>
#include <iostream>

int main() {
    std::string name = "John";
    i32 age = 30;

    auto lol = age * age / 3;
    std::string message = std::format("Name: {}, Age: {}", name, lol);

    std::cout << message << std::endl;
    
    return 0;
}