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
    return result;
}
