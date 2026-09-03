/* Shape corpus for r2sleigh rendering evaluation.

   The hash corpus proves one program shape: a loop over bytes accumulating an
   integer.  Nine functions, nine variations on that shape, and nothing else.
   Three defects found by an external benchmark were invisible to it because
   none of them can occur in that shape -- a variadic call losing arguments, a
   stack pointer that never recovers the eight bytes an x86-64 `call` pushes,
   and a call rendered with no arguments at all.

   Every function scored here is `uint64_t shape_*(uint64_t, uint64_t)`, so the
   harness hands it two integers and compares one integer back.  The shape under
   test lives inside the body and in the noinline helpers it calls, which the
   verifier pulls in from their own renderings.  Each result is a pure function
   of the two arguments: no output, no clock, and no address ever reaches the
   returned value, because an address would differ between the oracle and the
   rendering for reasons that are not defects.

   Every helper is noinline so it survives -O2 as its own symbol and the call is
   still a call at every optimization level. */

#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define NOINL __attribute__((noinline))

/* ---- 1. A variadic libc callee reached with one, two, three and five
        variable arguments.  `snprintf` returns the length it would have
        written, which is a value an oracle can compare, so a dropped argument
        changes the answer instead of only changing what was printed. ---- */
NOINL uint64_t shape_variadic(uint64_t a, uint64_t b) {
    char buffer[160];
    uint64_t total = 0;

    int one = snprintf(buffer, sizeof buffer, "%llu", (unsigned long long)a);
    total = total * 131u + (uint64_t)one + (uint64_t)(uint8_t)buffer[0];

    int two = snprintf(buffer, sizeof buffer, "%llu:%llu",
                       (unsigned long long)a, (unsigned long long)b);
    total = total * 131u + (uint64_t)two + (uint64_t)(uint8_t)buffer[1];

    int three = snprintf(buffer, sizeof buffer, "%llu:%llu:%llu",
                         (unsigned long long)a, (unsigned long long)b,
                         (unsigned long long)(a ^ b));
    total = total * 131u + (uint64_t)three + (uint64_t)(uint8_t)buffer[2];

    int five = snprintf(buffer, sizeof buffer, "%llu-%llu-%llu-%llu-%llu",
                        (unsigned long long)a, (unsigned long long)b,
                        (unsigned long long)(a ^ b), (unsigned long long)(a + b),
                        (unsigned long long)(a | b));
    total = total * 131u + (uint64_t)five + (uint64_t)(uint8_t)buffer[3];

    return total;
}

/* ---- 2. A variadic callee of our own, so the argument area is built by this
        translation unit rather than by libc's prototype. ---- */
NOINL uint64_t vfold(unsigned count, ...) {
    va_list arguments;
    uint64_t accumulator = 0x1234u;
    va_start(arguments, count);
    for (unsigned index = 0; index < count; index++) {
        accumulator = accumulator * 131u + va_arg(arguments, uint64_t);
    }
    va_end(arguments);
    return accumulator;
}

NOINL uint64_t shape_variadic_local(uint64_t a, uint64_t b) {
    uint64_t result = 0;
    result = result * 7u + vfold(1u, a);
    result = result * 7u + vfold(2u, a, b);
    result = result * 7u + vfold(3u, a, b, a ^ b);
    result = result * 7u + vfold(5u, a, b, a ^ b, a + b, a | b);
    return result;
}

/* ---- 3. Calls in sequence with stack locals read after each.  The locals have
        their addresses taken so they are frame objects at every optimization
        level, and the answer depends on reading them back after the calls: a
        frame slot resolved eight bytes low changes the value rather than only
        looking odd. ---- */
NOINL uint64_t shape_step(uint64_t value) {
    return value * 6364136223846793005ull + 1442695040888963407ull;
}

NOINL void shape_stash(uint64_t *slot, uint64_t value) { *slot = value; }

NOINL uint64_t shape_call_chain(uint64_t a, uint64_t b) {
    uint64_t first = 0;
    uint64_t second = 0;
    uint64_t third = 0;

    shape_stash(&first, a ^ 0x0123456789abcdefull);
    uint64_t stepped_first = shape_step(first);
    shape_stash(&second, first + b);
    uint64_t stepped_second = shape_step(second);
    shape_stash(&third, second ^ stepped_first);
    uint64_t stepped_third = shape_step(third);

    return (first + second * 3u + third * 7u)
         ^ (stepped_first + stepped_second * 5u + stepped_third * 11u);
}

/* ---- 4 and 5. One struct with fields of four widths, passed by pointer and by
        value.  Sixteen bytes of integers is two registers under both ABIs, so
        the by-value call also exercises a multi-register argument. ---- */
struct mixed {
    uint8_t byte;
    uint16_t half;
    uint32_t word;
    uint64_t quad;
};

NOINL void mixed_touch(struct mixed *value) {
    value->byte = (uint8_t)(value->byte + 3u);
    value->half = (uint16_t)(value->half ^ 0xbeefu);
    value->word = value->word * 2654435761u;
    value->quad = value->quad + value->word + value->half + value->byte;
}

NOINL uint64_t mixed_fold(struct mixed value) {
    return ((uint64_t)value.byte << 56)
         ^ ((uint64_t)value.half << 40)
         ^ ((uint64_t)value.word << 8)
         ^ value.quad;
}

static struct mixed mixed_from(uint64_t a, uint64_t b) {
    struct mixed value;
    value.byte = (uint8_t)a;
    value.half = (uint16_t)(a >> 8);
    value.word = (uint32_t)b;
    value.quad = a ^ b;
    return value;
}

NOINL uint64_t shape_struct_pointer(uint64_t a, uint64_t b) {
    struct mixed value = mixed_from(a, b);
    mixed_touch(&value);
    mixed_touch(&value);
    return ((uint64_t)value.byte * 3u)
         + ((uint64_t)value.half * 5u)
         + ((uint64_t)value.word * 7u)
         + value.quad;
}

NOINL uint64_t shape_struct_value(uint64_t a, uint64_t b) {
    struct mixed value = mixed_from(a, b);
    uint64_t folded = mixed_fold(value);
    value.quad ^= folded;
    value.word = (uint32_t)(folded >> 32);
    return folded * 31u + mixed_fold(value);
}

/* ---- 6. An array of structs indexed by a loop counter. ---- */
struct pair {
    uint32_t low;
    uint32_t high;
};

NOINL uint64_t shape_struct_array(uint64_t a, uint64_t b) {
    struct pair table[8];
    for (unsigned index = 0; index < 8u; index++) {
        table[index].low = (uint32_t)(a + index * 2654435761u);
        table[index].high = (uint32_t)(b ^ (index * 0x9e3779b9u));
    }
    uint64_t accumulator = 0;
    for (unsigned index = 0; index < 8u; index++) {
        accumulator = accumulator * 1099511628211ull + table[index].low;
        accumulator ^= (uint64_t)table[(index + 3u) & 7u].high << 16;
    }
    return accumulator;
}

/* ---- 7. A stack buffer written and read back, out of order so the read
        cannot be folded into the write. ---- */
NOINL uint64_t shape_stack_buffer(uint64_t a, uint64_t b) {
    uint8_t buffer[64];
    for (unsigned index = 0; index < 64u; index++) {
        buffer[index] = (uint8_t)((a >> (index & 7u)) + b * index);
    }
    uint64_t hash = 0xcbf29ce484222325ull;
    for (unsigned index = 0; index < 64u; index++) {
        hash ^= buffer[(index * 5u) & 63u];
        hash *= 0x100000001b3ull;
    }
    return hash;
}

/* ---- 8. Direct recursion.  The count is masked so any argument terminates. */
NOINL uint64_t shape_recurse_direct(uint64_t a, uint64_t b) {
    uint64_t depth = a & 15u;
    if (depth == 0) {
        return b | 1u;
    }
    return shape_recurse_direct(depth - 1u, b * 3u + depth) ^ (depth << 3);
}

/* ---- 9. Mutual recursion. ---- */
NOINL uint64_t shape_mutual_odd(uint64_t depth, uint64_t accumulator);

NOINL uint64_t shape_mutual_even(uint64_t depth, uint64_t accumulator) {
    if (depth == 0) {
        return accumulator ^ 0xa5a5a5a5u;
    }
    return shape_mutual_odd(depth - 1u, accumulator * 31u + depth);
}

NOINL uint64_t shape_mutual_odd(uint64_t depth, uint64_t accumulator) {
    if (depth == 0) {
        return accumulator ^ 0x5a5a5a5au;
    }
    return shape_mutual_even(depth - 1u, accumulator * 17u + (depth << 2));
}

NOINL uint64_t shape_recurse_mutual(uint64_t a, uint64_t b) {
    return shape_mutual_even(a & 15u, b) + shape_mutual_odd(a & 7u, b ^ 0xffffu);
}

/* ---- 10. Signed division and remainder at two widths, with negative operands.
        The divisor is moved off the two values that are undefined rather than
        merely surprising, so every case has one right answer. ---- */
NOINL uint64_t shape_signed_divmod(uint64_t a, uint64_t b) {
    int64_t wide_numerator = (int64_t)a;
    int64_t wide_divisor = (int64_t)b;
    if (wide_divisor == 0) {
        wide_divisor = -7;
    }
    if (wide_divisor == -1 && wide_numerator == INT64_MIN) {
        wide_divisor = 3;
    }
    int64_t wide_quotient = wide_numerator / wide_divisor;
    int64_t wide_remainder = wide_numerator % wide_divisor;

    int32_t narrow_numerator = (int32_t)(uint32_t)a;
    int32_t narrow_divisor = (int32_t)(uint32_t)b;
    if (narrow_divisor == 0) {
        narrow_divisor = -3;
    }
    if (narrow_divisor == -1 && narrow_numerator == INT32_MIN) {
        narrow_divisor = 5;
    }
    int32_t narrow_quotient = narrow_numerator / narrow_divisor;
    int32_t narrow_remainder = narrow_numerator % narrow_divisor;

    uint64_t folded = ((uint64_t)wide_quotient * 1000003u) + (uint64_t)wide_remainder;
    folded ^= (uint64_t)(uint32_t)narrow_quotient << 32;
    folded ^= (uint64_t)(uint32_t)narrow_remainder;
    folded += (wide_numerator < 0) ? 0x11u : 0x22u;
    folded += (narrow_quotient < narrow_remainder) ? 0x3300u : 0x4400u;
    return folded;
}

/* ---- 11. A struct returned by value that the ABI splits across two
        registers. ---- */
struct wide {
    uint64_t low;
    uint64_t high;
};

NOINL struct wide wide_make(uint64_t a, uint64_t b) {
    struct wide value;
    value.low = a * 0x9e3779b97f4a7c15ull + b;
    value.high = (a ^ b) * 0xc2b2ae3d27d4eb4full;
    return value;
}

NOINL uint64_t shape_multiword_return(uint64_t a, uint64_t b) {
    struct wide first = wide_make(a, b);
    struct wide second = wide_make(first.high, first.low);
    return (first.low ^ second.high) + (first.high ^ second.low);
}

/* ---- 12. A pointer to a pointer, written and read through two levels. ---- */
NOINL uint64_t indirect_load(uint64_t **rows, unsigned index) {
    return *rows[index];
}

NOINL void indirect_store(uint64_t **rows, unsigned index, uint64_t value) {
    *rows[index] = value;
}

NOINL uint64_t shape_pointer_to_pointer(uint64_t a, uint64_t b) {
    uint64_t zero = a;
    uint64_t one = b;
    uint64_t two = a ^ b;
    uint64_t three = a + b;
    uint64_t *rows[4] = {&zero, &one, &two, &three};
    uint64_t **cursor = rows;

    uint64_t accumulator = 0;
    for (unsigned index = 0; index < 4u; index++) {
        accumulator = accumulator * 1000003u + indirect_load(cursor, index);
    }
    indirect_store(cursor, 1u, accumulator);
    indirect_store(cursor, 3u, accumulator ^ zero);
    for (unsigned index = 0; index < 4u; index++) {
        accumulator ^= indirect_load(cursor, index) << (index * 3u);
    }
    return accumulator;
}

/* ---- 13. A call through a function pointer held in a variable. ---- */
NOINL uint64_t op_add(uint64_t x, uint64_t y) { return x + y; }
NOINL uint64_t op_xor(uint64_t x, uint64_t y) { return (x ^ y) * 3u; }
NOINL uint64_t op_mul(uint64_t x, uint64_t y) { return x * (y | 1u); }

typedef uint64_t (*binary_operation)(uint64_t, uint64_t);

NOINL uint64_t shape_function_pointer(uint64_t a, uint64_t b) {
    binary_operation table[3] = {op_add, op_xor, op_mul};
    uint64_t accumulator = a;
    for (unsigned index = 0; index < 6u; index++) {
        binary_operation chosen = table[(a + index) % 3u];
        accumulator = chosen(accumulator, b + index);
    }
    return accumulator;
}

/* A main so the corpus binary links, and so nothing is dead-stripped. */
int main(void) {
    uint64_t a = 0x0123456789abcdefull;
    uint64_t b = 0xfedcba9876543210ull;
    printf("%016llx\n", (unsigned long long)shape_variadic(a, b));
    printf("%016llx\n", (unsigned long long)shape_variadic_local(a, b));
    printf("%016llx\n", (unsigned long long)shape_call_chain(a, b));
    printf("%016llx\n", (unsigned long long)shape_struct_pointer(a, b));
    printf("%016llx\n", (unsigned long long)shape_struct_value(a, b));
    printf("%016llx\n", (unsigned long long)shape_struct_array(a, b));
    printf("%016llx\n", (unsigned long long)shape_stack_buffer(a, b));
    printf("%016llx\n", (unsigned long long)shape_recurse_direct(a, b));
    printf("%016llx\n", (unsigned long long)shape_recurse_mutual(a, b));
    printf("%016llx\n", (unsigned long long)shape_signed_divmod(a, b));
    printf("%016llx\n", (unsigned long long)shape_multiword_return(a, b));
    printf("%016llx\n", (unsigned long long)shape_pointer_to_pointer(a, b));
    printf("%016llx\n", (unsigned long long)shape_function_pointer(a, b));
    return 0;
}
