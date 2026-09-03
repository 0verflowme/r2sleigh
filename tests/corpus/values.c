/* Value-hazard corpus for r2sleigh rendering evaluation.

   shapes.c asked whether the decompiler can render a program shape at all, and
   the answer was mostly no: eleven of its thirteen functions refuse, naming the
   rule that declined. A refusal is the honest outcome and it is not the
   dangerous one. The one shape that rendered and was wrong -- a variadic call
   losing its arguments on arm64 while refusing correctly on x64 -- taught more
   than the other twelve together, because a confident wrong answer is the
   failure this project treats as worse than declining.

   So these functions are built to fail open. Every one is a leaf: no calls, no
   address-taken locals, no arrays, no aggregates. There is no call boundary to
   refuse at and no frame object to decline, so the renderer has nothing to
   stop on and must commit to an answer. What is left is arithmetic, and each
   function isolates one place where the machine's arithmetic and C's differ in
   a way a reader cannot see: sign versus zero extension, arithmetic versus
   logical shift, signed versus unsigned comparison, the bias a compiler adds
   before dividing a negative number by a power of two, the high half of a
   multiply, carry, overflow, byte order.

   Getting any of them wrong produces a plausible number rather than a refusal.
   That is the point.

   Every function is a pure function of its two arguments, is defined for every
   possible pair -- shift counts are masked, counts of leading zeros guard the
   zero case, and negation is done in unsigned arithmetic so INT64_MIN has an
   answer -- and uses both arguments. */

#include <stdint.h>
#include <stdio.h>

#define NOINL __attribute__((noinline))

/* ---- 1. Sign extension versus zero extension on narrow loads. ----
   A byte read as signed and a byte read as unsigned differ for exactly half
   the inputs, and the rendered C looks equally reasonable either way. */
NOINL uint64_t value_sign_extend(uint64_t a, uint64_t b) {
    int64_t signed_total = 0;
    uint64_t unsigned_total = 0;
    for (unsigned index = 0; index < 8u; index++) {
        int8_t narrow = (int8_t)(uint8_t)(a >> (index * 8u));
        signed_total += (int64_t)narrow;
        unsigned_total += (uint64_t)(uint8_t)(a >> (index * 8u));
    }
    for (unsigned index = 0; index < 4u; index++) {
        int16_t half = (int16_t)(uint16_t)(b >> (index * 16u));
        signed_total = signed_total * 3 + (int64_t)half;
    }
    int32_t word = (int32_t)(uint32_t)b;
    signed_total += (int64_t)word;
    return (uint64_t)signed_total ^ (unsigned_total * 0x9e3779b97f4a7c15ull);
}

/* ---- 2. Arithmetic versus logical right shift. ----
   `sar` and `shr` differ only when the value is negative, so a run that never
   tries a negative operand cannot tell them apart. */
NOINL uint64_t value_arith_shift(uint64_t a, uint64_t b) {
    int64_t wide = (int64_t)a;
    uint64_t folded = 0;
    for (unsigned index = 0; index < 8u; index++) {
        unsigned count = (unsigned)((b >> (index * 3u)) & 63u);
        folded = folded * 31u + (uint64_t)(wide >> count);
        folded ^= a >> count;
    }
    int32_t narrow = (int32_t)(uint32_t)a;
    for (unsigned index = 0; index < 4u; index++) {
        unsigned count = (unsigned)((b >> (index * 2u)) & 31u);
        folded = folded * 17u + (uint64_t)(uint32_t)(narrow >> count);
        folded ^= (uint64_t)((uint32_t)a >> count);
    }
    /* Left shifts stay in unsigned arithmetic, where overflow is defined. */
    folded ^= a << (b & 63u);
    return folded;
}

/* ---- 3. Signed versus unsigned comparison. ----
   The condition codes differ; the C reads the same. The operands are chosen so
   the two orderings disagree. */
NOINL uint64_t value_signed_compare(uint64_t a, uint64_t b) {
    uint64_t folded = 0;
    int64_t signed_a = (int64_t)a;
    int64_t signed_b = (int64_t)b;
    folded = folded * 7u + (signed_a < signed_b ? 1u : 2u);
    folded = folded * 7u + (a < b ? 1u : 2u);
    folded = folded * 7u + (signed_a <= signed_b ? 3u : 4u);
    folded = folded * 7u + (a <= b ? 3u : 4u);
    folded = folded * 7u + (signed_a > 0 ? 5u : 6u);
    folded = folded * 7u + (a > 0u ? 5u : 6u);
    int32_t narrow_a = (int32_t)(uint32_t)a;
    int32_t narrow_b = (int32_t)(uint32_t)b;
    folded = folded * 7u + (narrow_a < narrow_b ? 8u : 9u);
    folded = folded * 7u + ((uint32_t)a < (uint32_t)b ? 8u : 9u);
    folded = folded * 7u + (narrow_a >= narrow_b ? 10u : 11u);
    int16_t half_a = (int16_t)(uint16_t)a;
    int16_t half_b = (int16_t)(uint16_t)b;
    folded = folded * 7u + (half_a < half_b ? 12u : 13u);
    return folded;
}

/* ---- 4. Truncation width. ----
   Wraparound at 8 and 16 bits, then widened. A rendering that keeps the wrong
   width carries bits that should have been discarded. */
NOINL uint64_t value_narrow_wrap(uint64_t a, uint64_t b) {
    uint8_t byte = (uint8_t)a;
    uint16_t half = (uint16_t)b;
    uint32_t word = (uint32_t)(a ^ b);
    for (unsigned index = 0; index < 6u; index++) {
        byte = (uint8_t)(byte * 251u + (uint8_t)(b >> index));
        half = (uint16_t)(half * 65521u + (uint16_t)(a >> index));
        word = word * 2654435761u + (uint32_t)(a >> index);
    }
    return ((uint64_t)byte << 48) ^ ((uint64_t)half << 24) ^ (uint64_t)word;
}

/* ---- 5. Signed division by a power of two. ----
   The compiler emits an add-the-bias-then-shift sequence rather than a divide,
   and the bias only matters when the numerator is negative. Getting it wrong is
   off by one for exactly the negative inputs. A constant divisor also avoids
   the conflicting-use refusal that a variable divisor produces. */
NOINL uint64_t value_div_pow2(uint64_t a, uint64_t b) {
    int64_t wide = (int64_t)a;
    int32_t narrow = (int32_t)(uint32_t)b;
    uint64_t folded = 0;
    folded = folded * 31u + (uint64_t)(wide / 2);
    folded = folded * 31u + (uint64_t)(wide % 2);
    folded = folded * 31u + (uint64_t)(wide / 8);
    folded = folded * 31u + (uint64_t)(wide % 8);
    folded = folded * 31u + (uint64_t)(wide / 1024);
    folded = folded * 31u + (uint64_t)(wide % 1024);
    folded = folded * 31u + (uint64_t)(uint32_t)(narrow / 4);
    folded = folded * 31u + (uint64_t)(uint32_t)(narrow % 4);
    folded = folded * 31u + (uint64_t)(uint32_t)(narrow / 256);
    /* Unsigned by the same powers, where no bias belongs at all. */
    folded = folded * 31u + (a / 8u);
    folded = folded * 31u + (a % 8u);
    folded = folded * 31u + (uint64_t)((uint32_t)b / 256u);
    return folded;
}

/* ---- 6. Rotate versus shift-or, and the rotate amount's mask. ---- */
NOINL uint64_t value_rotate(uint64_t a, uint64_t b) {
    uint64_t folded = a;
    for (unsigned index = 0; index < 6u; index++) {
        unsigned count = (unsigned)((b >> (index * 4u)) & 63u);
        unsigned wide_left = count & 63u;
        unsigned wide_right = (64u - wide_left) & 63u;
        folded ^= (a << wide_left) | (a >> wide_right);
        uint32_t narrow = (uint32_t)(a >> index);
        unsigned short_left = count & 31u;
        unsigned short_right = (32u - short_left) & 31u;
        folded = folded * 5u
               + (uint64_t)((narrow << short_left) | (narrow >> short_right));
    }
    return folded;
}

/* ---- 7. Carry across a word boundary. ----
   The carry-out of an addition is a flag on the machine and a comparison in C.
   A rendering that loses it is wrong only when the addition wraps. */
NOINL uint64_t value_carry_chain(uint64_t a, uint64_t b) {
    uint64_t low = 0;
    uint64_t high = 0;
    for (unsigned index = 0; index < 8u; index++) {
        uint64_t addend = (a * (index + 1u)) ^ (b << index);
        uint64_t sum = low + addend;
        uint64_t carry = (sum < low) ? 1u : 0u;
        low = sum;
        high = high + carry + (addend >> 32);
        uint64_t difference = low - b;
        uint64_t borrow = (low < b) ? 1u : 0u;
        low = difference;
        high = high - borrow;
    }
    return (high * 0x100000001b3ull) ^ low;
}

/* ---- 8. High half of a multiply, unsigned and signed. ----
   Two different instructions whose low halves agree. */
NOINL uint64_t value_mul_high(uint64_t a, uint64_t b) {
    __uint128_t unsigned_product = (__uint128_t)a * (__uint128_t)b;
    __int128 signed_product = (__int128)(int64_t)a * (__int128)(int64_t)b;
    uint64_t unsigned_high = (uint64_t)(unsigned_product >> 64);
    uint64_t signed_high = (uint64_t)((__uint128_t)signed_product >> 64);
    uint64_t low = (uint64_t)unsigned_product;
    uint32_t narrow_unsigned_high =
        (uint32_t)(((uint64_t)(uint32_t)a * (uint64_t)(uint32_t)b) >> 32);
    uint32_t narrow_signed_high = (uint32_t)((uint64_t)(
        (int64_t)(int32_t)(uint32_t)a * (int64_t)(int32_t)(uint32_t)b) >> 32);
    return (unsigned_high * 31u) ^ (signed_high * 17u) ^ low
         ^ ((uint64_t)narrow_unsigned_high << 16)
         ^ ((uint64_t)narrow_signed_high << 32);
}

/* ---- 9. Byte order. ----
   Assembling a word from bytes both ways, so a rendering that swaps them
   returns a different number rather than an obviously broken one. */
NOINL uint64_t value_byte_order(uint64_t a, uint64_t b) {
    uint32_t big = 0;
    uint32_t little = 0;
    for (unsigned index = 0; index < 4u; index++) {
        uint8_t byte = (uint8_t)(a >> (index * 8u));
        big = (big << 8) | byte;
        little |= (uint32_t)byte << (index * 8u);
    }
    uint64_t swapped = 0;
    for (unsigned index = 0; index < 8u; index++) {
        swapped |= (uint64_t)(uint8_t)(b >> (index * 8u)) << ((7u - index) * 8u);
    }
    return ((uint64_t)big << 32) ^ (uint64_t)little ^ swapped;
}

/* ---- 10. Bit counting. ----
   `clz`, `ctz` and `popcount` are single instructions whose results no reader
   can check by eye. The zero cases are guarded, so every input has an answer. */
NOINL uint64_t value_count_bits(uint64_t a, uint64_t b) {
    uint64_t folded = 0;
    uint64_t nonzero_a = a | 1u;
    uint64_t nonzero_b = b | 0x8000000000000000ull;
    folded = folded * 67u + (uint64_t)__builtin_popcountll(a);
    folded = folded * 67u + (uint64_t)__builtin_popcountll(b);
    folded = folded * 67u + (uint64_t)__builtin_clzll(nonzero_a);
    folded = folded * 67u + (uint64_t)__builtin_ctzll(nonzero_a);
    folded = folded * 67u + (uint64_t)__builtin_clzll(nonzero_b);
    folded = folded * 67u + (uint64_t)__builtin_ctzll(nonzero_b);
    folded = folded * 67u + (uint64_t)__builtin_popcount((uint32_t)(a ^ b));
    folded = folded * 67u + (uint64_t)__builtin_clz((uint32_t)a | 1u);
    folded = folded * 67u + (uint64_t)__builtin_parityll(a ^ b);
    return folded;
}

/* ---- 11. Overflow flags. ----
   Signed overflow sets a different flag from unsigned carry, and the two
   disagree for a large share of operand pairs. */
NOINL uint64_t value_overflow_flags(uint64_t a, uint64_t b) {
    uint64_t folded = 0;
    int64_t signed_result = 0;
    uint64_t unsigned_result = 0;
    int32_t narrow_result = 0;

    folded = folded * 13u
           + (__builtin_add_overflow((int64_t)a, (int64_t)b, &signed_result) ? 1u : 2u);
    folded = folded * 13u + (uint64_t)signed_result;
    folded = folded * 13u
           + (__builtin_add_overflow(a, b, &unsigned_result) ? 3u : 4u);
    folded = folded * 13u + unsigned_result;
    folded = folded * 13u
           + (__builtin_sub_overflow((int64_t)a, (int64_t)b, &signed_result) ? 5u : 6u);
    folded = folded * 13u + (uint64_t)signed_result;
    folded = folded * 13u
           + (__builtin_mul_overflow((int32_t)(uint32_t)a, (int32_t)(uint32_t)b,
                                     &narrow_result)
                  ? 7u
                  : 8u);
    folded = folded * 13u + (uint64_t)(uint32_t)narrow_result;
    return folded;
}

/* ---- 12. Absolute value, minimum and maximum. ----
   The abs idiom is a sign mask, an exclusive-or and a subtract, and it has no
   correct answer at INT_MIN, so the negation is done in unsigned arithmetic
   where it does. Signed and unsigned min disagree across the sign boundary. */
NOINL uint64_t value_abs_minmax(uint64_t a, uint64_t b) {
    int64_t signed_a = (int64_t)a;
    int64_t signed_b = (int64_t)b;
    uint64_t magnitude_a = signed_a < 0 ? (uint64_t)0 - a : a;
    uint64_t magnitude_b = signed_b < 0 ? (uint64_t)0 - b : b;
    uint64_t folded = magnitude_a * 31u + magnitude_b;
    folded = folded * 11u + (uint64_t)(signed_a < signed_b ? signed_a : signed_b);
    folded = folded * 11u + (uint64_t)(signed_a > signed_b ? signed_a : signed_b);
    folded = folded * 11u + (a < b ? a : b);
    folded = folded * 11u + (a > b ? a : b);
    int32_t narrow_a = (int32_t)(uint32_t)a;
    int32_t narrow_b = (int32_t)(uint32_t)b;
    folded = folded * 11u
           + (uint64_t)(uint32_t)(narrow_a < narrow_b ? narrow_a : narrow_b);
    uint32_t narrow_magnitude =
        narrow_a < 0 ? (uint32_t)0 - (uint32_t)narrow_a : (uint32_t)narrow_a;
    folded = folded * 11u + (uint64_t)narrow_magnitude;
    return folded;
}

/* A main so the corpus binary links, and so nothing is dead-stripped. */
int main(void) {
    uint64_t a = 0x0123456789abcdefull;
    uint64_t b = 0xfedcba9876543210ull;
    printf("%016llx\n", (unsigned long long)value_sign_extend(a, b));
    printf("%016llx\n", (unsigned long long)value_arith_shift(a, b));
    printf("%016llx\n", (unsigned long long)value_signed_compare(a, b));
    printf("%016llx\n", (unsigned long long)value_narrow_wrap(a, b));
    printf("%016llx\n", (unsigned long long)value_div_pow2(a, b));
    printf("%016llx\n", (unsigned long long)value_rotate(a, b));
    printf("%016llx\n", (unsigned long long)value_carry_chain(a, b));
    printf("%016llx\n", (unsigned long long)value_mul_high(a, b));
    printf("%016llx\n", (unsigned long long)value_byte_order(a, b));
    printf("%016llx\n", (unsigned long long)value_count_bits(a, b));
    printf("%016llx\n", (unsigned long long)value_overflow_flags(a, b));
    printf("%016llx\n", (unsigned long long)value_abs_minmax(a, b));
    return 0;
}
