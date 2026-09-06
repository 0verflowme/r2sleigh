#include <stdint.h>
#include <stddef.h>
/* setcc: a boolean materialised from a comparison */
int gt(int a, int b) { return a > b; }
/* adc: carry consumed by arithmetic */
uint64_t addc(uint64_t a, uint64_t b, uint64_t c) {
    uint64_t lo = a + b;
    return lo + (lo < a) + c;
}
/* a chain of comparisons feeding a branch */
int classify(int x) {
    if (x < 0) return -1;
    if (x == 0) return 0;
    if (x > 100) return 2;
    return 1;
}
/* carry propagated across a loop */
uint64_t sum_carry(const uint64_t *v, size_t n) {
    uint64_t acc = 0, carry = 0;
    for (size_t i = 0; i < n; i++) { uint64_t t = acc + v[i]; carry += (t < acc); acc = t; }
    return acc + carry;
}
