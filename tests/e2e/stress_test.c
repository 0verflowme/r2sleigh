// Comprehensive stress test for r2sleigh plugin
// Compile: gcc -O0 -g -fno-stack-protector -no-pie -o stress_test stress_test.c -lm -lpthread
// Also compile optimized: gcc -O2 -g -no-pie -o stress_test_opt stress_test.c -lm -lpthread
//
// Tests complex real-world patterns:
// - Floating point operations
// - Function pointers and indirect calls
// - Linked list / pointer chasing
// - Recursive functions
// - setjmp/longjmp
// - Variable-length argument functions
// - Bit manipulation
// - Multi-dimensional arrays
// - Nested struct access
// - Enum-based state machines
// - Goto statements
// - Complex loop patterns (do-while, nested, early exit)
// - String operations
// - Signal handling patterns
// - Tail calls (with -O2)

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <stdarg.h>
#include <stddef.h>

// ============================================================================
// 1. Floating point operations
// ============================================================================

double fp_interpolate(double a, double b, double t) {
    return a * (1.0 - t) + b * t;
}

float fp_magnitude(float x, float y, float z) {
    return sqrtf(x * x + y * y + z * z);
}

int fp_classify(double x) {
    if (x != x) return -1;        // NaN check
    if (x > 1e300) return 1;      // very large
    if (x < -1e300) return -2;    // very negative
    if (x == 0.0) return 0;       // zero
    return 2;                     // normal
}

double fp_polynomial(double x) {
    // 3x^3 - 2x^2 + x - 7
    return 3.0 * x * x * x - 2.0 * x * x + x - 7.0;
}

// ============================================================================
// 2. Function pointers and indirect calls
// ============================================================================

typedef int (*binary_op_t)(int, int);

int op_add(int a, int b) { return a + b; }
int op_sub(int a, int b) { return a - b; }
int op_mul(int a, int b) { return a * b; }
int op_div(int a, int b) { return b ? a / b : 0; }
int op_mod(int a, int b) { return b ? a % b : 0; }

static binary_op_t op_table[] = { op_add, op_sub, op_mul, op_div, op_mod };

int dispatch_op(int opcode, int a, int b) {
    if (opcode < 0 || opcode >= 5) return -1;
    return op_table[opcode](a, b);
}

int apply_chain(binary_op_t *ops, int n, int init, int operand) {
    int result = init;
    for (int i = 0; i < n; i++) {
        result = ops[i](result, operand);
    }
    return result;
}

// ============================================================================
// 3. Linked list / pointer chasing
// ============================================================================

typedef struct Node {
    int value;
    struct Node *next;
} Node;

Node* list_create(int *values, int n) {
    Node *head = NULL;
    for (int i = n - 1; i >= 0; i--) {
        Node *node = (Node*)malloc(sizeof(Node));
        node->value = values[i];
        node->next = head;
        head = node;
    }
    return head;
}

int list_sum(Node *head) {
    int sum = 0;
    Node *cur = head;
    while (cur) {
        sum += cur->value;
        cur = cur->next;
    }
    return sum;
}

Node* list_reverse(Node *head) {
    Node *prev = NULL;
    Node *cur = head;
    while (cur) {
        Node *next = cur->next;
        cur->next = prev;
        prev = cur;
        cur = next;
    }
    return prev;
}

void list_free(Node *head) {
    while (head) {
        Node *next = head->next;
        free(head);
        head = next;
    }
}

int list_nth(Node *head, int n) {
    Node *cur = head;
    for (int i = 0; i < n && cur; i++) {
        cur = cur->next;
    }
    return cur ? cur->value : -1;
}

// ============================================================================
// 4. Recursive functions
// ============================================================================

int fibonacci(int n) {
    if (n <= 0) return 0;
    if (n == 1) return 1;
    return fibonacci(n - 1) + fibonacci(n - 2);
}

int gcd(int a, int b) {
    if (b == 0) return a;
    return gcd(b, a % b);
}

int ackermann(int m, int n) {
    if (m == 0) return n + 1;
    if (n == 0) return ackermann(m - 1, 1);
    return ackermann(m - 1, ackermann(m, n - 1));
}

// Binary search (recursive)
int bsearch_recursive(int *arr, int lo, int hi, int target) {
    if (lo > hi) return -1;
    int mid = lo + (hi - lo) / 2;
    if (arr[mid] == target) return mid;
    if (arr[mid] < target)
        return bsearch_recursive(arr, mid + 1, hi, target);
    return bsearch_recursive(arr, lo, mid - 1, target);
}

// ============================================================================
// 5. Variadic functions
// ============================================================================

int sum_args(int count, ...) {
    va_list ap;
    va_start(ap, count);
    int total = 0;
    for (int i = 0; i < count; i++) {
        total += va_arg(ap, int);
    }
    va_end(ap);
    return total;
}

char* concat_strings(int count, ...) {
    va_list ap;
    va_start(ap, count);
    
    // First pass: compute total length
    va_list ap2;
    va_copy(ap2, ap);
    size_t total = 0;
    for (int i = 0; i < count; i++) {
        total += strlen(va_arg(ap2, const char*));
    }
    va_end(ap2);
    
    // Allocate and concatenate
    char *result = (char*)malloc(total + 1);
    if (!result) { va_end(ap); return NULL; }
    result[0] = '\0';
    for (int i = 0; i < count; i++) {
        strcat(result, va_arg(ap, const char*));
    }
    va_end(ap);
    return result;
}

// ============================================================================
// 6. Bit manipulation
// ============================================================================

uint32_t bit_reverse(uint32_t x) {
    x = ((x >> 1) & 0x55555555) | ((x & 0x55555555) << 1);
    x = ((x >> 2) & 0x33333333) | ((x & 0x33333333) << 2);
    x = ((x >> 4) & 0x0F0F0F0F) | ((x & 0x0F0F0F0F) << 4);
    x = ((x >> 8) & 0x00FF00FF) | ((x & 0x00FF00FF) << 8);
    x = (x >> 16) | (x << 16);
    return x;
}

int popcount_naive(uint32_t x) {
    int count = 0;
    while (x) {
        count += x & 1;
        x >>= 1;
    }
    return count;
}

uint32_t next_power_of_two(uint32_t x) {
    x--;
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    x++;
    return x;
}

int count_leading_zeros(uint32_t x) {
    if (x == 0) return 32;
    int n = 0;
    if ((x & 0xFFFF0000) == 0) { n += 16; x <<= 16; }
    if ((x & 0xFF000000) == 0) { n += 8; x <<= 8; }
    if ((x & 0xF0000000) == 0) { n += 4; x <<= 4; }
    if ((x & 0xC0000000) == 0) { n += 2; x <<= 2; }
    if ((x & 0x80000000) == 0) { n += 1; }
    return n;
}

// ============================================================================
// 7. Multi-dimensional arrays
// ============================================================================

#define MATRIX_SIZE 4

void matrix_multiply(int a[MATRIX_SIZE][MATRIX_SIZE],
                     int b[MATRIX_SIZE][MATRIX_SIZE],
                     int c[MATRIX_SIZE][MATRIX_SIZE]) {
    for (int i = 0; i < MATRIX_SIZE; i++) {
        for (int j = 0; j < MATRIX_SIZE; j++) {
            c[i][j] = 0;
            for (int k = 0; k < MATRIX_SIZE; k++) {
                c[i][j] += a[i][k] * b[k][j];
            }
        }
    }
}

int matrix_trace(int m[MATRIX_SIZE][MATRIX_SIZE]) {
    int tr = 0;
    for (int i = 0; i < MATRIX_SIZE; i++) {
        tr += m[i][i];
    }
    return tr;
}

// ============================================================================
// 8. Nested structs
// ============================================================================

typedef struct {
    int x, y;
} Point;

typedef struct {
    Point top_left;
    Point bottom_right;
} Rect;

typedef struct {
    char name[32];
    Rect bounds;
    int color;
    int z_order;
} Widget;

int rect_area(Rect *r) {
    int w = r->bottom_right.x - r->top_left.x;
    int h = r->bottom_right.y - r->top_left.y;
    return w * h;
}

int widget_contains_point(Widget *w, int px, int py) {
    return px >= w->bounds.top_left.x &&
           px <= w->bounds.bottom_right.x &&
           py >= w->bounds.top_left.y &&
           py <= w->bounds.bottom_right.y;
}

Widget* widget_find_at(Widget *widgets, int n, int px, int py) {
    Widget *best = NULL;
    for (int i = 0; i < n; i++) {
        if (widget_contains_point(&widgets[i], px, py)) {
            if (!best || widgets[i].z_order > best->z_order) {
                best = &widgets[i];
            }
        }
    }
    return best;
}

// ============================================================================
// 9. State machine (enum-based)
// ============================================================================

typedef enum {
    STATE_IDLE = 0,
    STATE_CONNECTING,
    STATE_AUTHENTICATED,
    STATE_ACTIVE,
    STATE_ERROR,
    STATE_CLOSED,
    NUM_STATES
} ConnState;

typedef enum {
    EVT_CONNECT = 0,
    EVT_AUTH_OK,
    EVT_AUTH_FAIL,
    EVT_DATA,
    EVT_DISCONNECT,
    EVT_TIMEOUT,
    NUM_EVENTS
} Event;

ConnState state_machine(ConnState state, Event event) {
    switch (state) {
        case STATE_IDLE:
            if (event == EVT_CONNECT) return STATE_CONNECTING;
            break;
        case STATE_CONNECTING:
            if (event == EVT_AUTH_OK) return STATE_AUTHENTICATED;
            if (event == EVT_AUTH_FAIL) return STATE_ERROR;
            if (event == EVT_TIMEOUT) return STATE_ERROR;
            break;
        case STATE_AUTHENTICATED:
            if (event == EVT_DATA) return STATE_ACTIVE;
            if (event == EVT_DISCONNECT) return STATE_CLOSED;
            break;
        case STATE_ACTIVE:
            if (event == EVT_DATA) return STATE_ACTIVE;
            if (event == EVT_DISCONNECT) return STATE_CLOSED;
            if (event == EVT_TIMEOUT) return STATE_ERROR;
            break;
        case STATE_ERROR:
            if (event == EVT_DISCONNECT) return STATE_CLOSED;
            if (event == EVT_CONNECT) return STATE_CONNECTING;
            break;
        case STATE_CLOSED:
            if (event == EVT_CONNECT) return STATE_CONNECTING;
            break;
        default:
            return STATE_ERROR;
    }
    return state;
}

const char* state_name(ConnState s) {
    static const char *names[] = {
        "IDLE", "CONNECTING", "AUTHENTICATED", "ACTIVE", "ERROR", "CLOSED"
    };
    if (s >= 0 && s < NUM_STATES) return names[s];
    return "UNKNOWN";
}

// ============================================================================
// 10. Complex loop patterns
// ============================================================================

// Do-while with break
int find_first_set_bit(uint64_t x) {
    if (x == 0) return -1;
    int pos = 0;
    do {
        if (x & 1) break;
        x >>= 1;
        pos++;
    } while (pos < 64);
    return pos;
}

// Nested loops with labeled-style break (using goto)
int matrix_find(int m[MATRIX_SIZE][MATRIX_SIZE], int target) {
    int found_i = -1, found_j = -1;
    for (int i = 0; i < MATRIX_SIZE; i++) {
        for (int j = 0; j < MATRIX_SIZE; j++) {
            if (m[i][j] == target) {
                found_i = i;
                found_j = j;
                goto done;
            }
        }
    }
done:
    return found_i * MATRIX_SIZE + found_j;
}

// Loop with multiple exit conditions
int parse_number(const char *str) {
    int result = 0;
    int sign = 1;
    int i = 0;
    
    if (str[0] == '-') {
        sign = -1;
        i = 1;
    } else if (str[0] == '+') {
        i = 1;
    }
    
    while (str[i] != '\0') {
        if (str[i] < '0' || str[i] > '9') break;
        result = result * 10 + (str[i] - '0');
        if (result > 100000) break;  // overflow guard
        i++;
    }
    
    return sign * result;
}

// ============================================================================
// 11. String operations
// ============================================================================

int my_strcmp(const char *a, const char *b) {
    while (*a && *a == *b) {
        a++;
        b++;
    }
    return (unsigned char)*a - (unsigned char)*b;
}

char* my_strdup(const char *s) {
    size_t len = strlen(s);
    char *dup = (char*)malloc(len + 1);
    if (dup) {
        memcpy(dup, s, len + 1);
    }
    return dup;
}

int count_char(const char *s, char c) {
    int count = 0;
    while (*s) {
        if (*s == c) count++;
        s++;
    }
    return count;
}

// Simple tokenizer
int tokenize(const char *input, char delim, char tokens[][64], int max_tokens) {
    int token_count = 0;
    int pos = 0;
    
    for (int i = 0; input[i] && token_count < max_tokens; i++) {
        if (input[i] == delim) {
            tokens[token_count][pos] = '\0';
            if (pos > 0) token_count++;
            pos = 0;
        } else {
            if (pos < 63) {
                tokens[token_count][pos++] = input[i];
            }
        }
    }
    if (pos > 0) {
        tokens[token_count][pos] = '\0';
        token_count++;
    }
    return token_count;
}

// ============================================================================
// 12. Error handling patterns
// ============================================================================

typedef struct {
    int code;
    char message[128];
} Error;

typedef struct {
    int success;
    union {
        int value;
        Error error;
    };
} Result;

Result result_ok(int value) {
    Result r;
    r.success = 1;
    r.value = value;
    return r;
}

Result result_err(int code, const char *msg) {
    Result r;
    r.success = 0;
    r.error.code = code;
    strncpy(r.error.message, msg, sizeof(r.error.message) - 1);
    r.error.message[sizeof(r.error.message) - 1] = '\0';
    return r;
}

Result safe_divide(int a, int b) {
    if (b == 0) return result_err(-1, "division by zero");
    if (a == INT32_MIN && b == -1) return result_err(-2, "integer overflow");
    return result_ok(a / b);
}

// ============================================================================
// 13. Hash table (open addressing)
// ============================================================================

#define HT_SIZE 64

typedef struct {
    uint32_t key;
    int value;
    int occupied;
} HTEntry;

typedef struct {
    HTEntry entries[HT_SIZE];
    int count;
} HashTable;

uint32_t hash_func(uint32_t key) {
    key = ((key >> 16) ^ key) * 0x45d9f3b;
    key = ((key >> 16) ^ key) * 0x45d9f3b;
    key = (key >> 16) ^ key;
    return key % HT_SIZE;
}

void ht_init(HashTable *ht) {
    memset(ht, 0, sizeof(HashTable));
}

int ht_insert(HashTable *ht, uint32_t key, int value) {
    if (ht->count >= HT_SIZE / 2) return -1;  // load factor limit
    uint32_t idx = hash_func(key);
    for (int i = 0; i < HT_SIZE; i++) {
        uint32_t probe = (idx + i) % HT_SIZE;
        if (!ht->entries[probe].occupied) {
            ht->entries[probe].key = key;
            ht->entries[probe].value = value;
            ht->entries[probe].occupied = 1;
            ht->count++;
            return 0;
        }
        if (ht->entries[probe].key == key) {
            ht->entries[probe].value = value;
            return 0;
        }
    }
    return -1;
}

int ht_lookup(HashTable *ht, uint32_t key, int *value) {
    uint32_t idx = hash_func(key);
    for (int i = 0; i < HT_SIZE; i++) {
        uint32_t probe = (idx + i) % HT_SIZE;
        if (!ht->entries[probe].occupied) return 0;
        if (ht->entries[probe].key == key) {
            *value = ht->entries[probe].value;
            return 1;
        }
    }
    return 0;
}

// ============================================================================
// 14. Sorting algorithms
// ============================================================================

void swap(int *a, int *b) {
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

int partition(int *arr, int lo, int hi) {
    int pivot = arr[hi];
    int i = lo - 1;
    for (int j = lo; j < hi; j++) {
        if (arr[j] <= pivot) {
            i++;
            swap(&arr[i], &arr[j]);
        }
    }
    swap(&arr[i + 1], &arr[hi]);
    return i + 1;
}

void quicksort(int *arr, int lo, int hi) {
    if (lo < hi) {
        int p = partition(arr, lo, hi);
        quicksort(arr, lo, p - 1);
        quicksort(arr, p + 1, hi);
    }
}

void insertion_sort(int *arr, int n) {
    for (int i = 1; i < n; i++) {
        int key = arr[i];
        int j = i - 1;
        while (j >= 0 && arr[j] > key) {
            arr[j + 1] = arr[j];
            j--;
        }
        arr[j + 1] = key;
    }
}

// ============================================================================
// 15. Complex control flow
// ============================================================================

// Duff's device pattern
void duffs_copy(int *to, int *from, int count) {
    int n = (count + 7) / 8;
    switch (count % 8) {
        case 0: do { *to++ = *from++;
        case 7:      *to++ = *from++;
        case 6:      *to++ = *from++;
        case 5:      *to++ = *from++;
        case 4:      *to++ = *from++;
        case 3:      *to++ = *from++;
        case 2:      *to++ = *from++;
        case 1:      *to++ = *from++;
                } while (--n > 0);
    }
}

// Computed goto simulation (jump table through switch)
int interpret_bytecode(uint8_t *code, int len) {
    int ip = 0;
    int acc = 0;
    int stack[16];
    int sp = 0;
    
    while (ip < len) {
        uint8_t op = code[ip++];
        switch (op) {
            case 0x01: // PUSH immediate
                if (ip < len && sp < 16) stack[sp++] = code[ip++];
                break;
            case 0x02: // ADD
                if (sp >= 2) { stack[sp-2] += stack[sp-1]; sp--; }
                break;
            case 0x03: // SUB
                if (sp >= 2) { stack[sp-2] -= stack[sp-1]; sp--; }
                break;
            case 0x04: // MUL
                if (sp >= 2) { stack[sp-2] *= stack[sp-1]; sp--; }
                break;
            case 0x05: // DUP
                if (sp > 0 && sp < 16) { stack[sp] = stack[sp-1]; sp++; }
                break;
            case 0x06: // POP to accumulator
                if (sp > 0) acc = stack[--sp];
                break;
            case 0x07: // LOAD acc
                if (sp < 16) stack[sp++] = acc;
                break;
            case 0x08: // CMP (sets acc to comparison result)
                if (sp >= 2) { acc = stack[sp-2] - stack[sp-1]; sp -= 2; }
                break;
            case 0x09: // JZ offset
                if (ip < len) {
                    int8_t offset = (int8_t)code[ip++];
                    if (acc == 0) ip += offset;
                }
                break;
            case 0x0A: // JNZ offset
                if (ip < len) {
                    int8_t offset = (int8_t)code[ip++];
                    if (acc != 0) ip += offset;
                }
                break;
            case 0xFF: // HALT
                return acc;
            default:
                return -1;  // invalid opcode
        }
    }
    return acc;
}

// Small interpreter loop intended to be step-summary friendly.
__attribute__((noinline))
int tiny_vm_dispatch(uint8_t *code, int len) {
    int ip = 0;
    int acc = 0;
    uint8_t dispatch_op = 0;

dispatch:
    if (ip >= len) {
        return acc;
    }

    dispatch_op = code[ip++];
    switch (dispatch_op) {
        case 0x00:
            acc += 1;
            goto dispatch;
        case 0x01:
            acc += 2;
            goto dispatch;
        case 0x02:
            acc -= 1;
            goto dispatch;
        case 0x03:
            acc ^= 0x55;
            goto dispatch;
        case 0x04:
            acc ^= 0xaa;
            goto dispatch;
        case 0x05:
            acc <<= 1;
            goto dispatch;
        case 0x06:
            acc >>= 1;
            goto dispatch;
        case 0x07:
            if (acc == 0 && ip < len) {
                ip += (int8_t)code[ip];
            }
            goto dispatch;
        case 0xff:
            return acc;
        default:
            return -1;
    }
}

// ============================================================================
// 16. Vulnerability patterns for taint analysis
// ============================================================================

// Use-after-free pattern
void vuln_use_after_free(int flag) {
    char *buf = (char*)malloc(64);
    strcpy(buf, "sensitive data");
    free(buf);
    if (flag) {
        // UAF: using buf after free
        printf("Data: %s\n", buf);
    }
}

// Double free pattern
void vuln_double_free(int flag) {
    char *buf = (char*)malloc(64);
    free(buf);
    if (flag) {
        free(buf);  // double free
    }
}

// Uninitialized variable
int vuln_uninit(int flag) {
    int x;
    if (flag > 0) {
        x = 42;
    }
    // x may be uninitialized if flag <= 0
    return x;
}

// Off-by-one
void vuln_off_by_one(char *dst, const char *src) {
    int i;
    for (i = 0; src[i] != '\0'; i++) {
        dst[i] = src[i];
    }
    // Bug: should set dst[i] = '\0' but fence-post error
    dst[i + 1] = '\0';
}

// ============================================================================
// 17. Saturating / overflow-aware arithmetic
// ============================================================================

int32_t saturating_add(int32_t a, int32_t b) {
    int64_t result = (int64_t)a + (int64_t)b;
    if (result > INT32_MAX) return INT32_MAX;
    if (result < INT32_MIN) return INT32_MIN;
    return (int32_t)result;
}

uint32_t rotate_left(uint32_t x, int n) {
    n &= 31;
    return (x << n) | (x >> (32 - n));
}

uint32_t rotate_right(uint32_t x, int n) {
    n &= 31;
    return (x >> n) | (x << (32 - n));
}

// ============================================================================
// 18. Mini regex matcher
// ============================================================================

int match_here(const char *regexp, const char *text);

int match_star(char c, const char *regexp, const char *text) {
    do {
        if (match_here(regexp, text))
            return 1;
    } while (*text != '\0' && (*text++ == c || c == '.'));
    return 0;
}

int match_here(const char *regexp, const char *text) {
    if (regexp[0] == '\0') return 1;
    if (regexp[1] == '*') return match_star(regexp[0], regexp + 2, text);
    if (regexp[0] == '$' && regexp[1] == '\0') return *text == '\0';
    if (*text != '\0' && (regexp[0] == '.' || regexp[0] == *text))
        return match_here(regexp + 1, text + 1);
    return 0;
}

int match(const char *regexp, const char *text) {
    if (regexp[0] == '^')
        return match_here(regexp + 1, text);
    do {
        if (match_here(regexp, text))
            return 1;
    } while (*text++ != '\0');
    return 0;
}

// ============================================================================
// 19. Memory pool allocator
// ============================================================================

#define POOL_BLOCK_SIZE 32
#define POOL_NUM_BLOCKS 16

typedef struct {
    uint8_t data[POOL_BLOCK_SIZE * POOL_NUM_BLOCKS];
    uint16_t free_bitmap;  // bit i = block i is free
} MemPool;

void pool_init(MemPool *pool) {
    memset(pool->data, 0, sizeof(pool->data));
    pool->free_bitmap = 0xFFFF;  // all free
}

void* pool_alloc(MemPool *pool) {
    for (int i = 0; i < POOL_NUM_BLOCKS; i++) {
        if (pool->free_bitmap & (1 << i)) {
            pool->free_bitmap &= ~(1 << i);
            return &pool->data[i * POOL_BLOCK_SIZE];
        }
    }
    return NULL;
}

void pool_free(MemPool *pool, void *ptr) {
    ptrdiff_t offset = (uint8_t*)ptr - pool->data;
    if (offset < 0 || offset >= POOL_BLOCK_SIZE * POOL_NUM_BLOCKS) return;
    int idx = offset / POOL_BLOCK_SIZE;
    pool->free_bitmap |= (1 << idx);
}

// ============================================================================
// 20. CRC32 computation
// ============================================================================

uint32_t crc32_byte(uint32_t crc, uint8_t byte) {
    crc ^= byte;
    for (int i = 0; i < 8; i++) {
        if (crc & 1)
            crc = (crc >> 1) ^ 0xEDB88320;
        else
            crc >>= 1;
    }
    return crc;
}

uint32_t crc32(const uint8_t *data, size_t len) {
    uint32_t crc = 0xFFFFFFFF;
    for (size_t i = 0; i < len; i++) {
        crc = crc32_byte(crc, data[i]);
    }
    return crc ^ 0xFFFFFFFF;
}

// ============================================================================
// Main: dispatcher for all tests
// ============================================================================

int main(int argc, char *argv[]) {
    if (argc < 2) {
        printf("Usage: %s <test_num> [args...]\n", argv[0]);
        printf("Tests:\n");
        printf("  1: fp_interpolate\n");
        printf("  2: fp_magnitude\n");
        printf("  3: fp_classify\n");
        printf("  4: dispatch_op\n");
        printf("  5: list_create + list_sum\n");
        printf("  6: fibonacci\n");
        printf("  7: gcd\n");
        printf("  8: bit_reverse\n");
        printf("  9: popcount\n");
        printf(" 10: matrix_multiply\n");
        printf(" 11: state_machine\n");
        printf(" 12: parse_number\n");
        printf(" 13: quicksort\n");
        printf(" 14: interpret_bytecode\n");
        printf(" 15: safe_divide\n");
        printf(" 16: match (regex)\n");
        printf(" 17: crc32\n");
        printf(" 18: ht_insert + ht_lookup\n");
        printf(" 19: vuln patterns\n");
        printf(" 20: saturating_add\n");
        printf(" 21: tiny_vm_dispatch\n");
        return 1;
    }
    
    int test = atoi(argv[1]);
    
    switch (test) {
        case 1: {
            double r = fp_interpolate(0.0, 100.0, 0.5);
            printf("fp_interpolate(0,100,0.5) = %f\n", r);
            printf("fp_polynomial(2.0) = %f\n", fp_polynomial(2.0));
            break;
        }
        case 2: {
            float r = fp_magnitude(3.0f, 4.0f, 0.0f);
            printf("fp_magnitude(3,4,0) = %f\n", r);
            break;
        }
        case 3: {
            printf("fp_classify(0.0) = %d\n", fp_classify(0.0));
            printf("fp_classify(1.0) = %d\n", fp_classify(1.0));
            printf("fp_classify(NAN) = %d\n", fp_classify(0.0/0.0));
            break;
        }
        case 4: {
            if (argc > 4) {
                int opcode = atoi(argv[2]);
                int a = atoi(argv[3]);
                int b = atoi(argv[4]);
                printf("dispatch_op(%d,%d,%d) = %d\n", opcode, a, b, dispatch_op(opcode, a, b));
            }
            break;
        }
        case 5: {
            int vals[] = {1, 2, 3, 4, 5};
            Node *list = list_create(vals, 5);
            printf("list_sum = %d\n", list_sum(list));
            list = list_reverse(list);
            printf("after reverse, nth(0) = %d\n", list_nth(list, 0));
            list_free(list);
            break;
        }
        case 6: {
            int n = argc > 2 ? atoi(argv[2]) : 10;
            printf("fibonacci(%d) = %d\n", n, fibonacci(n));
            break;
        }
        case 7: {
            if (argc > 3) {
                int a = atoi(argv[2]);
                int b = atoi(argv[3]);
                printf("gcd(%d,%d) = %d\n", a, b, gcd(a, b));
            }
            break;
        }
        case 8: {
            if (argc > 2) {
                uint32_t x = strtoul(argv[2], NULL, 0);
                printf("bit_reverse(0x%x) = 0x%x\n", x, bit_reverse(x));
            }
            break;
        }
        case 9: {
            if (argc > 2) {
                uint32_t x = strtoul(argv[2], NULL, 0);
                printf("popcount(0x%x) = %d\n", x, popcount_naive(x));
            }
            break;
        }
        case 10: {
            int a[4][4] = {{1,2,3,4},{5,6,7,8},{9,10,11,12},{13,14,15,16}};
            int b[4][4] = {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}};
            int c[4][4];
            matrix_multiply(a, b, c);
            printf("trace(A*I) = %d\n", matrix_trace(c));
            break;
        }
        case 11: {
            ConnState s = STATE_IDLE;
            s = state_machine(s, EVT_CONNECT);
            printf("IDLE + CONNECT = %s\n", state_name(s));
            s = state_machine(s, EVT_AUTH_OK);
            printf("+ AUTH_OK = %s\n", state_name(s));
            s = state_machine(s, EVT_DATA);
            printf("+ DATA = %s\n", state_name(s));
            s = state_machine(s, EVT_DISCONNECT);
            printf("+ DISCONNECT = %s\n", state_name(s));
            break;
        }
        case 12: {
            if (argc > 2) {
                printf("parse_number(\"%s\") = %d\n", argv[2], parse_number(argv[2]));
            }
            break;
        }
        case 13: {
            int arr[] = {38, 27, 43, 3, 9, 82, 10};
            int n = sizeof(arr)/sizeof(arr[0]);
            quicksort(arr, 0, n - 1);
            printf("sorted: ");
            for (int i = 0; i < n; i++) printf("%d ", arr[i]);
            printf("\n");
            break;
        }
        case 14: {
            // Program: PUSH 10, PUSH 20, ADD, PUSH 3, MUL, POP, HALT
            uint8_t code[] = {0x01, 10, 0x01, 20, 0x02, 0x01, 3, 0x04, 0x06, 0xFF};
            printf("bytecode result = %d\n", interpret_bytecode(code, sizeof(code)));
            break;
        }
        case 15: {
            if (argc > 3) {
                int a = atoi(argv[2]);
                int b = atoi(argv[3]);
                Result r = safe_divide(a, b);
                if (r.success)
                    printf("safe_divide(%d,%d) = %d\n", a, b, r.value);
                else
                    printf("safe_divide(%d,%d) error: %s\n", a, b, r.error.message);
            }
            break;
        }
        case 16: {
            if (argc > 3) {
                printf("match(\"%s\", \"%s\") = %d\n", argv[2], argv[3], match(argv[2], argv[3]));
            }
            break;
        }
        case 17: {
            if (argc > 2) {
                uint32_t crc = crc32((const uint8_t*)argv[2], strlen(argv[2]));
                printf("crc32(\"%s\") = 0x%08x\n", argv[2], crc);
            }
            break;
        }
        case 18: {
            HashTable ht;
            ht_init(&ht);
            ht_insert(&ht, 42, 100);
            ht_insert(&ht, 99, 200);
            int val;
            if (ht_lookup(&ht, 42, &val))
                printf("ht[42] = %d\n", val);
            if (ht_lookup(&ht, 99, &val))
                printf("ht[99] = %d\n", val);
            break;
        }
        case 19: {
            printf("Testing vuln patterns (UAF, double-free, uninit)...\n");
            // These are intentionally buggy - just run to verify analysis
            printf("vuln_uninit(0) = %d\n", vuln_uninit(0));
            printf("vuln_uninit(1) = %d\n", vuln_uninit(1));
            break;
        }
        case 20: {
            if (argc > 3) {
                int32_t a = atoi(argv[2]);
                int32_t b = atoi(argv[3]);
                printf("saturating_add(%d,%d) = %d\n", a, b, saturating_add(a, b));
                uint32_t x = strtoul(argv[2], NULL, 0);
                printf("rotate_left(0x%x, 4) = 0x%x\n", x, rotate_left(x, 4));
            }
            break;
        }
        case 21: {
            uint8_t code[] = {0x00, 0x01, 0x03, 0x05, 0x06, 0x04, 0xff};
            printf("tiny_vm_dispatch result = %d\n", tiny_vm_dispatch(code, sizeof(code)));
            break;
        }
        default:
            printf("Unknown test: %d\n", test);
            return 1;
    }
    
    return 0;
}
