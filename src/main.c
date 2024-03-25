#include <stdio.h>
#include "utilities.h"

int main() {
    print_welcome_message();
    int sum = add(5, 3);
    printf("Sum of 5 and 3 is: %d\n", sum);
    
    Fraction fraction = {10, 2};
    double division = divide(fraction);
    printf("Division of 10 by 2 is: %.2f\n", division);
    return 0;
}