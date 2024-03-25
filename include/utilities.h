#ifndef UTILITIES_H
#define UTILITIES_H

typedef struct {
    int numerator;
    int denominator;
} Fraction;

void print_welcome_message();
int add(int a, int b);
double divide(Fraction fraction);

#endif // UTILITIES_H