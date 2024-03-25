#include "utilities.h"

double divide(Fraction fraction) {
    if (fraction.denominator == 0) {
        return 0;
    }
    return (double)fraction.numerator / fraction.denominator;
}