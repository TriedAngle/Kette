#include "vm.h"
#include "test.h"
#include <format>
#include <iostream>

int main() {
    std::string name = "John";
    int age = 30;

    std::string message = std::format("Name: {}, Age: {}", name, age);

    std::cout << message << std::endl;
    
    return 0;
}