#include <stddef.h>
#include <stdlib.h>
#include <string.h>

// Simple test function for end-to-end testing
int add(int a, int b) {
    return a + b;
}

int factorial(int n) {
    if (n <= 1) {
        return 1;
    }
    return n * factorial(n - 1);
}

int sum_array(int *arr, int len) {
    int sum = 0;
    for (int i = 0; i < len; i++) {
        sum += arr[i];
    }
    return sum;
}

void *alloc_wrapper(size_t n) {
    return malloc(n);
}

void *alloc_wrapper2(size_t n) {
    return alloc_wrapper(n);
}

char *memcpy_wrapper(char *dst, const char *src, size_t n) {
    return memcpy(dst, src, n);
}

// Keep a long linear prologue in one basic block so plugin lifting must not
// truncate large blocks before the terminating branch.
__attribute__((noinline)) int large_basic_block_guard(int x) {
    volatile int acc = x;

    acc += 1;
    acc += 2;
    acc += 3;
    acc += 4;
    acc += 5;
    acc += 6;
    acc += 7;
    acc += 8;
    acc += 9;
    acc += 10;
    acc += 11;
    acc += 12;
    acc += 13;
    acc += 14;
    acc += 15;
    acc += 16;
    acc += 17;
    acc += 18;
    acc += 19;
    acc += 20;
    acc += 21;
    acc += 22;
    acc += 23;
    acc += 24;
    acc += 25;
    acc += 26;
    acc += 27;
    acc += 28;
    acc += 29;
    acc += 30;
    acc += 31;
    acc += 32;
    acc += 33;
    acc += 34;
    acc += 35;
    acc += 36;
    acc += 37;
    acc += 38;
    acc += 39;
    acc += 40;
    acc += 41;
    acc += 42;
    acc += 43;
    acc += 44;
    acc += 45;
    acc += 46;
    acc += 47;
    acc += 48;
    acc += 49;
    acc += 50;
    acc += 51;
    acc += 52;
    acc += 53;
    acc += 54;
    acc += 55;
    acc += 56;
    acc += 57;
    acc += 58;
    acc += 59;
    acc += 60;
    if (acc == 1830) {
        return acc - 7;
    }
    return acc + 3;
}

int main() {
    int result = add(5, 3);
    result = factorial(5);
    int arr[] = {1, 2, 3, 4, 5};
    result = sum_array(arr, 5);
    char *buf = alloc_wrapper2(16);
    if (buf) {
        memcpy_wrapper(buf, "ok", 3);
        free(buf);
    }
    result += large_basic_block_guard(result);
    return result;
}
