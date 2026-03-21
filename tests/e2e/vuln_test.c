// Vulnerability test cases for r2sleigh integration tests
// Compile with: gcc -O0 -g -fno-stack-protector -no-pie -o vuln_test vuln_test.c
//
// This binary is used by tests/e2e/integration_tests.rs to test all plugin features.
// When adding a new feature that needs a specific binary pattern:
// 1. Add a test function here that exercises the feature
// 2. Add it to the main() switch statement
// 3. Add an integration test in tests/e2e/integration_tests.rs
//
// Current test functions:
// - check_secret: Simple condition (symbolic execution, path exploration)
// - unlock: Multi-condition path explosion
// - vuln_memcpy: Buffer overflow (taint analysis)
// - solve_equation: Arithmetic constraint solving
// - bitwise_check: Bitwise operations
// - (others available for future test cases)

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <locale.h>

volatile int global_counter = 0;
volatile int global_limit = 10;
volatile int global_tail = 0;

// Test 1: Simple password check (symbolic should find 0xDEAD)
int check_secret(int x) {
    if (x == 0xDEAD) {
        return 1;  // win
    }
    return 0;
}

// Test 2: Multi-condition unlock (tests path explosion)
int unlock(int a, int b, int c) {
    if (a == 10) {
        if (b == 20) {
            if (c == 30) {
                return 1;  // unlocked
            }
        }
    }
    return 0;
}

// Test 3: Buffer overflow (taint should track user input to memcpy size)
void vuln_memcpy(char *user_input, int user_len) {
    char buf[64];
    // VULN: user-controlled length in memcpy
    memcpy(buf, user_input, user_len);
    printf("Copied: %s\n", buf);
}

// Test 4: Format string (taint should track user input to printf)
void vuln_printf(char *user_input) {
    // VULN: user input directly in format string
    printf(user_input);
}

// Test 5: strlen on user input (tests sim layer)
int process_string(char *s) {
    size_t len = strlen(s);
    if (len > 100) {
        return -1;  // too long
    }
    if (len < 5) {
        return -2;  // too short
    }
    return (int)len;
}

// Test 6: strcmp for authentication (tests sim layer)
int authenticate(char *password) {
    if (strcmp(password, "secret123") == 0) {
        return 1;  // auth success
    }
    return 0;  // auth failed
}

// Test 7: malloc + use (tests sim layer)
char* alloc_and_copy(char *src, size_t len) {
    char *buf = malloc(len + 1);
    if (!buf) {
        return NULL;
    }
    memcpy(buf, src, len);
    buf[len] = '\0';
    return buf;
}

// Test 8: Integer overflow before allocation
void* vuln_alloc(int count, int size) {
    // VULN: integer overflow in multiplication
    int total = count * size;
    return malloc(total);
}

// Test 9: Simple arithmetic for constraint solving
int solve_equation(int x) {
    // x * 2 + 5 == 25 => x == 10
    int result = x * 2 + 5;
    if (result == 25) {
        return 1;
    }
    return 0;
}

// Test 10: Nested conditions with arithmetic
int complex_check(int a, int b) {
    int sum = a + b;
    int diff = a - b;
    
    if (sum == 100) {
        if (diff == 20) {
            // a + b = 100, a - b = 20 => a = 60, b = 40
            return 1;
        }
    }
    return 0;
}

// Test 11: Bitwise operations
int bitwise_check(unsigned int x) {
    if ((x & 0xF0) == 0x50) {
        if ((x & 0x0F) == 0x0A) {
            // x == 0x5A
            return 1;
        }
    }
    return 0;
}

// Test 12: Array bounds check
int safe_array_access(int *arr, int idx, int len) {
    if (idx >= 0 && idx < len) {
        return arr[idx];
    }
    return -1;
}

// Test 13: CPUID instruction (tests CallOther/userop naming)
__attribute__((naked)) void test_cpuid(void) {
#if defined(__x86_64__) || defined(__i386__)
    __asm__ volatile(
        "xor %eax, %eax\n\t"
        "cpuid\n\t"
        "ret\n\t"
    );
#else
    __asm__ volatile("ret");
#endif
}

// Test 14: Subpiece/cast from 64-bit to 32-bit
uint32_t test_subpiece(uint64_t x) {
    return (uint32_t)x;
}

// Test 15: Piece (concatenate hi/lo)
uint64_t test_piece(uint32_t hi, uint32_t lo) {
    return ((uint64_t)hi << 32) | lo;
}

// Test 16: Boolean XOR
int test_boolxor(int a, int b) {
    return (a > 0) ^ (b > 0);
}

// Test 17: Pointer add (array indexing)
int test_array_index(int *arr, int idx) {
    return arr[idx];
}

// Test 18: Pointer sub (negative index)
int test_array_index_neg(int *arr, int idx) {
    return arr[-idx];
}

// Test 19: Explicit cast to uint8_t
uint8_t test_cast_u8(int x) {
    return (uint8_t)x;
}

// Test 20: Guarded loop + switch recovery
int test_loop_switch(int x) {
    int i = 0;
    int sum = 0;

    while (1) {
        if (i >= x) {
            break;
        }

        switch (i & 7) {
            case 0:
                sum += 1;
                break;
            case 1:
                sum += 2;
                break;
            case 2:
                sum += 3;
                break;
            case 3:
                sum += 4;
                break;
            case 4:
                sum += 5;
                break;
            case 5:
                sum += 6;
                break;
            case 6:
                sum += 7;
                break;
            case 7:
                sum += 8;
                break;
            default:
                sum += 9;
                break;
        }

        i = i + 1;
    }

    return sum;
}

typedef struct {
    int first;
    int second;
    int third;
    int fourth;
    int fifth;
    int sixth;
    int seventh;
    int eighth;
    int ninth;
    int tenth;
    int eleventh;
    int twelfth;
    int thirteenth;
    int fourteenth;
} DemoStruct;

// Test 21: Struct-like fixed-offset access
int test_struct_field(DemoStruct *obj, int v) {
    obj->thirteenth = v;
    return obj->thirteenth + obj->first;
}

// Test 22: API signature propagation (setlocale returns char*)
int test_setlocale_wrapper(void) {
    char *loc = setlocale(LC_ALL, "C");
    if (!loc) {
        return 0;
    }
    return (int)loc[0];
}

// Test 23: Multi-use simple temporary (x + 1 reused)
int test_multi_use_temp(int x) {
    int y = x + 1;
    return y + y + y;
}

// Test 24: Arithmetic identity elimination patterns
int test_identity_ops(int x) {
    volatile int sub0 = x - 0;
    volatile int add0 = x + 0;
    volatile int or0 = x | 0;
    volatile int xor0 = x ^ 0;
    volatile int mul1 = x * 1;
    volatile int div1 = x / 1;
    volatile unsigned int and_all_ones = ((unsigned int)x) & 0xffffffffU;
    volatile int keep_sub = x - 1;
    volatile int keep_add = x + 2;
    volatile int keep_or = x | 1;
    return sub0 + add0 + or0 + xor0 + mul1 + div1 + (int)and_all_ones + keep_sub + keep_add + keep_or;
}

// Test 25: Global symbol flow in non-call contexts (load/store/compare)
int test_global_symbol_flow(int x) {
    global_counter = x;
    int current = global_counter;
    if (current == global_limit) {
        global_counter = current + global_limit;
    } else {
        global_counter = current - global_limit;
    }
    return global_counter;
}

// Test 26: Mixed struct offsets from same base pointer
int test_struct_mixed_offsets(DemoStruct *obj, int x) {
    obj->first = x;
    obj->fifth = x + 5;
    obj->thirteenth = obj->fifth + 1;
    return obj->thirteenth + obj->first;
}

// Test 27: Non-4-byte stride array indexing
uint16_t test_u16_stride(uint16_t *arr, int idx) {
    return arr[idx];
}

// Test 28: Pointer-to-struct-array indexing pattern
int test_struct_array_index(DemoStruct *arr, int idx, int v) {
    arr[idx].third = v;
    return arr[idx].third + arr[idx].fourteenth;
}

typedef struct {
    char pad[0x100];
    int marker;
} LargeOffsetStruct;

// Test 29: Large constant offset should remain 0x100 (hex) in recovered access patterns
int test_struct_offset_0x100(LargeOffsetStruct *obj, int v) {
    obj->marker = v;
    return obj->marker + 1;
}

// Test 30: SCCP should eliminate dead branch and dead sink store path
int test_sccp_dead_branch(int x) {
    int flag = 1;
    if (flag) {
        return x + 10;
    } else {
        global_tail = x * 100;
        return global_tail;
    }
}

// Test 31: Nested if-chain for short-circuit && reconstruction
int test_short_circuit_chain(int a, int b) {
    if (a) {
        if (b) {
            return 1;
        }
    }
    return 0;
}

// Test 32: Else-terminator pattern for guard inversion
int test_guard_inversion(int x) {
    if (x > 5) {
        global_tail = x + 1;
    } else {
        return -1;
    }
    return global_tail;
}

// Test 33: Nested if with side effects for short-circuit rewrite coverage
void test_short_circuit_side_effect(int a, int b) {
    if (a) {
        if (b) {
            global_tail = 1;
        }
    }
}

// Test 34: Void guard inversion pattern (else return)
void test_guard_inversion_void(int x) {
    if (x > 5) {
        global_tail = x;
    } else {
        return;
    }
    global_counter = x;
}

// Test 35: Loop guard with else-break for condition inversion coverage
int test_guard_inversion_loop(int x) {
    int sum = 0;
    while (x > 0) {
        if (x & 1) {
            sum += x;
        } else {
            break;
        }
        x--;
    }
    return sum;
}

// Test 36: Else-goto terminator pattern for guard inversion coverage
int test_guard_inversion_goto(int x) {
    if (x > 5) {
        global_tail = x;
    } else {
        goto out;
    }
    global_counter = x;
out:
    return global_tail;
}

// Test 37: Trailing-return guard inversion with multi-statement then-body
int test_guard_tail_return(int x) {
    if (x > 5) {
        global_tail = x + 10;
        global_counter = x - 1;
    }
    return 0;
}

// Test 38: Constant address add-chain for data-xref recovery (base + offset)
int test_const_addr_chain(void) {
    volatile uintptr_t base = 0x404d00ULL;
    volatile uintptr_t target = base + 0x108ULL;
    return (target == 0x404e08ULL) ? 1 : 0;
}

typedef struct {
    int tag;
    int len;
    long marker;
} TypeChainObj;

// Test 39: Leaf in a multi-hop caller/callee chain with struct field accesses.
__attribute__((noinline)) int test_type_leaf(TypeChainObj *obj, int v) {
    obj->tag = v;
    obj->len = v + 1;
    return obj->tag + obj->len;
}

// Test 40: Mid-level call propagates and adds another field write.
__attribute__((noinline)) int test_type_mid(TypeChainObj *obj, int v) {
    int acc = test_type_leaf(obj, v);
    obj->marker = (long)&global_counter;
    return acc + (int)(obj->marker != 0);
}

// Test 41: Top-level caller used to validate multi-hop interproc propagation.
__attribute__((noinline)) int test_type_top(int v) {
    TypeChainObj obj = {0};
    return test_type_mid(&obj, v) + obj.tag;
}

typedef struct {
    int first;
    int second;
} GlobalTypeA;

typedef struct {
    short lo;
    short hi;
    int tail;
} GlobalTypeB;

volatile GlobalTypeA g_type_a = {0};
volatile GlobalTypeB g_type_b = {0};

// Test 42: Competing global access shapes for global type-link ranking.
int test_global_type_compete(int x) {
    g_type_a.first = x;
    g_type_a.second = x + 7;
    g_type_b.lo = (short)x;
    g_type_b.hi = (short)(x + 1);
    g_type_b.tail = g_type_a.second;
    return g_type_b.tail + g_type_a.first;
}

// Test 43: Predicate carrier through cast/bool-not chain for decompiler normalization
int test_bool_carrier_chain(int x, int y) {
    int neq = x != y;
    unsigned long widened = (unsigned long)neq;
    if (!widened) {
        return y;
    }
    return x;
}

int main(int argc, char *argv[]) {
    if (argc < 2) {
        printf("Usage: %s <test_num> [args...]\n", argv[0]);
        return 1;
    }
    
    int test = atoi(argv[1]);
    
    switch (test) {
        case 1:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf("check_secret(%d) = %d\n", x, check_secret(x));
            }
            break;
        case 2:
            if (argc > 4) {
                int a = atoi(argv[2]);
                int b = atoi(argv[3]);
                int c = atoi(argv[4]);
                printf("unlock(%d, %d, %d) = %d\n", a, b, c, unlock(a, b, c));
            }
            break;
        case 3:
            if (argc > 3) {
                int len = atoi(argv[3]);
                vuln_memcpy(argv[2], len);
            }
            break;
        case 4:
            if (argc > 2) {
                vuln_printf(argv[2]);
            }
            break;
        case 5:
            if (argc > 2) {
                printf("process_string = %d\n", process_string(argv[2]));
            }
            break;
        case 6:
            if (argc > 2) {
                printf("authenticate = %d\n", authenticate(argv[2]));
            }
            break;
        case 7:
            if (argc > 3) {
                size_t len = atoi(argv[3]);
                char *copy = alloc_and_copy(argv[2], len);
                if (copy) {
                    printf("Copied: %s\n", copy);
                    free(copy);
                }
            }
            break;
        case 8:
            if (argc > 3) {
                int count = atoi(argv[2]);
                int size = atoi(argv[3]);
                void *p = vuln_alloc(count, size);
                printf("vuln_alloc(%d, %d) = %p\n", count, size, p);
                free(p);
            }
            break;
        case 9:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf("solve_equation(%d) = %d\n", x, solve_equation(x));
            }
            break;
        case 10:
            if (argc > 3) {
                int a = atoi(argv[2]);
                int b = atoi(argv[3]);
                printf("complex_check(%d, %d) = %d\n", a, b, complex_check(a, b));
            }
            break;
        case 11:
            if (argc > 2) {
                unsigned int x = strtoul(argv[2], NULL, 0);
                printf("bitwise_check(0x%x) = %d\n", x, bitwise_check(x));
            }
            break;
        case 12: {
            int arr[] = {10, 20, 30, 40, 50};
            if (argc > 2) {
                int idx = atoi(argv[2]);
                printf("safe_array_access(arr, %d, 5) = %d\n", idx, safe_array_access(arr, idx, 5));
            }
            break;
        }
        case 13:
            test_cpuid();
            printf("test_cpuid() = ok\n");
            break;
        case 14:
            if (argc > 2) {
                uint64_t x = strtoull(argv[2], NULL, 0);
                printf(
                    "test_subpiece(0x%llx) = 0x%x\n",
                    (unsigned long long)x,
                    test_subpiece(x)
                );
            }
            break;
        case 15:
            if (argc > 3) {
                uint32_t hi = strtoul(argv[2], NULL, 0);
                uint32_t lo = strtoul(argv[3], NULL, 0);
                printf(
                    "test_piece(0x%x, 0x%x) = 0x%llx\n",
                    hi,
                    lo,
                    (unsigned long long)test_piece(hi, lo)
                );
            }
            break;
        case 16:
            if (argc > 3) {
                int a = atoi(argv[2]);
                int b = atoi(argv[3]);
                printf("test_boolxor(%d, %d) = %d\n", a, b, test_boolxor(a, b));
            }
            break;
        case 17: {
            int arr[] = {10, 20, 30, 40, 50};
            if (argc > 2) {
                int idx = atoi(argv[2]);
                printf("test_array_index(arr, %d) = %d\n", idx, test_array_index(arr, idx));
            }
            break;
        }
        case 18: {
            int arr[] = {10, 20, 30, 40, 50};
            if (argc > 2) {
                int idx = atoi(argv[2]);
                printf(
                    "test_array_index_neg(arr, %d) = %d\n",
                    idx,
                    test_array_index_neg(arr, idx)
                );
            }
            break;
        }
        case 19:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf("test_cast_u8(%d) = %u\n", x, test_cast_u8(x));
            }
            break;
        case 20:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf("test_loop_switch(%d) = %d\n", x, test_loop_switch(x));
            }
            break;
        case 21: {
            DemoStruct obj = {0};
            if (argc > 2) {
                int v = atoi(argv[2]);
                printf("test_struct_field(&obj, %d) = %d\n", v, test_struct_field(&obj, v));
            }
            break;
        }
        case 22:
            printf("test_setlocale_wrapper() = %d\n", test_setlocale_wrapper());
            break;
        case 23:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf("test_multi_use_temp(%d) = %d\n", x, test_multi_use_temp(x));
            }
            break;
        case 24:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf("test_identity_ops(%d) = %d\n", x, test_identity_ops(x));
            }
            break;
        case 25:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf("test_global_symbol_flow(%d) = %d\n", x, test_global_symbol_flow(x));
            }
            break;
        case 26: {
            DemoStruct obj = {0};
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf(
                    "test_struct_mixed_offsets(&obj, %d) = %d\n",
                    x,
                    test_struct_mixed_offsets(&obj, x)
                );
            }
            break;
        }
        case 27: {
            uint16_t arr[] = {10, 20, 30, 40, 50};
            if (argc > 2) {
                int idx = atoi(argv[2]);
                printf(
                    "test_u16_stride(arr, %d) = %u\n",
                    idx,
                    (unsigned int)test_u16_stride(arr, idx)
                );
            }
            break;
        }
        case 28: {
            DemoStruct arr[4] = {0};
            if (argc > 3) {
                int idx = atoi(argv[2]);
                int v = atoi(argv[3]);
                printf(
                    "test_struct_array_index(arr, %d, %d) = %d\n",
                    idx,
                    v,
                    test_struct_array_index(arr, idx, v)
                );
            }
            break;
        }
        case 29: {
            LargeOffsetStruct obj = {0};
            if (argc > 2) {
                int v = atoi(argv[2]);
                printf(
                    "test_struct_offset_0x100(&obj, %d) = %d\n",
                    v,
                    test_struct_offset_0x100(&obj, v)
                );
            }
            break;
        }
        case 30:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf("test_sccp_dead_branch(%d) = %d\n", x, test_sccp_dead_branch(x));
            }
            break;
        case 31:
            if (argc > 3) {
                int a = atoi(argv[2]);
                int b = atoi(argv[3]);
                printf(
                    "test_short_circuit_chain(%d, %d) = %d\n",
                    a,
                    b,
                    test_short_circuit_chain(a, b)
                );
            }
            break;
        case 32:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf("test_guard_inversion(%d) = %d\n", x, test_guard_inversion(x));
            }
            break;
        case 33:
            if (argc > 3) {
                int a = atoi(argv[2]);
                int b = atoi(argv[3]);
                test_short_circuit_side_effect(a, b);
                printf("test_short_circuit_side_effect(%d, %d) done\n", a, b);
            }
            break;
        case 34:
            if (argc > 2) {
                int x = atoi(argv[2]);
                test_guard_inversion_void(x);
                printf("test_guard_inversion_void(%d) done\n", x);
            }
            break;
        case 35:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf(
                    "test_guard_inversion_loop(%d) = %d\n",
                    x,
                    test_guard_inversion_loop(x)
                );
            }
            break;
        case 36:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf(
                    "test_guard_inversion_goto(%d) = %d\n",
                    x,
                    test_guard_inversion_goto(x)
                );
            }
            break;
        case 37:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf(
                    "test_guard_tail_return(%d) = %d\n",
                    x,
                    test_guard_tail_return(x)
                );
            }
            break;
        case 38:
            printf("test_const_addr_chain() = %d\n", test_const_addr_chain());
            break;
        case 39: {
            TypeChainObj obj = {0};
            if (argc > 2) {
                int v = atoi(argv[2]);
                printf("test_type_leaf(&obj, %d) = %d\n", v, test_type_leaf(&obj, v));
            }
            break;
        }
        case 40: {
            TypeChainObj obj = {0};
            if (argc > 2) {
                int v = atoi(argv[2]);
                printf("test_type_mid(&obj, %d) = %d\n", v, test_type_mid(&obj, v));
            }
            break;
        }
        case 41:
            if (argc > 2) {
                int v = atoi(argv[2]);
                printf("test_type_top(%d) = %d\n", v, test_type_top(v));
            }
            break;
        case 42:
            if (argc > 2) {
                int x = atoi(argv[2]);
                printf("test_global_type_compete(%d) = %d\n", x, test_global_type_compete(x));
            }
            break;
        case 43:
            if (argc > 3) {
                int x = atoi(argv[2]);
                int y = atoi(argv[3]);
                printf(
                    "test_bool_carrier_chain(%d, %d) = %d\n",
                    x,
                    y,
                    test_bool_carrier_chain(x, y)
                );
            }
            break;
        default:
            printf("Unknown test: %d\n", test);
            return 1;
    }
    
    return 0;
}
