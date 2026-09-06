#ifndef R2SLEIGH_BITVECTORS_H
#define R2SLEIGH_BITVECTORS_H

/*
 * External C11 representation for machine carriers wider than 128 bits.
 *
 * Limbs are least-significant first.  The generated helpers implement exact
 * bit coordinates, including fields that cross a limb boundary.  They are the
 * only operations r2dec currently emits for wide carriers; unsupported vector
 * arithmetic remains a typed refusal in the renderer.
 */

#include <stdint.h>

struct r2sleigh_bits_256 {
    uint64_t limb[4];
};

struct r2sleigh_bits_512 {
    uint64_t limb[8];
};

#if defined(__clang__) || defined(__GNUC__)
#define R2SLEIGH_UNUSED __attribute__((unused))
#else
#define R2SLEIGH_UNUSED
#endif

#define R2SLEIGH_DEFINE_WIDE_FIELD(CARRIER_BITS, LIMBS, FIELD_BITS, FIELD_TYPE)               \
    static inline R2SLEIGH_UNUSED FIELD_TYPE                                                  \
        r2sleigh_bits_extract_##CARRIER_BITS##_##FIELD_BITS(                                  \
            struct r2sleigh_bits_##CARRIER_BITS source, uint64_t bit_offset)                  \
    {                                                                                         \
        FIELD_TYPE result = (FIELD_TYPE)0;                                                    \
        uint32_t bit;                                                                          \
        for (bit = 0; bit < (uint32_t)(FIELD_BITS); ++bit) {                                  \
            const uint64_t source_bit = bit_offset + (uint64_t)bit;                           \
            const uint64_t limb = source_bit / UINT64_C(64);                                  \
            const uint64_t in_limb = source_bit % UINT64_C(64);                               \
            if (limb < (uint64_t)(LIMBS)                                                       \
                && ((source.limb[limb] >> in_limb) & UINT64_C(1)) != UINT64_C(0)) {           \
                result |= (FIELD_TYPE)((FIELD_TYPE)1 << bit);                                 \
            }                                                                                 \
        }                                                                                     \
        return result;                                                                        \
    }                                                                                         \
    static inline R2SLEIGH_UNUSED struct r2sleigh_bits_##CARRIER_BITS                          \
        r2sleigh_bits_insert_##CARRIER_BITS##_##FIELD_BITS(                                   \
            struct r2sleigh_bits_##CARRIER_BITS carrier, FIELD_TYPE field,                    \
            uint64_t bit_offset)                                                              \
    {                                                                                         \
        uint32_t bit;                                                                          \
        for (bit = 0; bit < (uint32_t)(FIELD_BITS); ++bit) {                                  \
            const uint64_t target_bit = bit_offset + (uint64_t)bit;                           \
            const uint64_t limb = target_bit / UINT64_C(64);                                  \
            const uint64_t in_limb = target_bit % UINT64_C(64);                               \
            if (limb < (uint64_t)(LIMBS)) {                                                    \
                const uint64_t mask = UINT64_C(1) << in_limb;                                 \
                if (((field >> bit) & (FIELD_TYPE)1) != (FIELD_TYPE)0) {                      \
                    carrier.limb[limb] |= mask;                                                \
                } else {                                                                      \
                    carrier.limb[limb] &= ~mask;                                               \
                }                                                                             \
            }                                                                                 \
        }                                                                                     \
        return carrier;                                                                       \
    }                                                                                         \
    static inline R2SLEIGH_UNUSED struct r2sleigh_bits_##CARRIER_BITS                          \
        r2sleigh_bits_zero_extend_##FIELD_BITS##_##CARRIER_BITS(FIELD_TYPE field)             \
    {                                                                                         \
        struct r2sleigh_bits_##CARRIER_BITS result = {{UINT64_C(0)}};                         \
        return r2sleigh_bits_insert_##CARRIER_BITS##_##FIELD_BITS(result, field, UINT64_C(0)); \
    }

R2SLEIGH_DEFINE_WIDE_FIELD(256, 4, 8, uint8_t)
R2SLEIGH_DEFINE_WIDE_FIELD(256, 4, 16, uint16_t)
R2SLEIGH_DEFINE_WIDE_FIELD(256, 4, 32, uint32_t)
R2SLEIGH_DEFINE_WIDE_FIELD(256, 4, 64, uint64_t)
R2SLEIGH_DEFINE_WIDE_FIELD(256, 4, 128, __uint128_t)
R2SLEIGH_DEFINE_WIDE_FIELD(512, 8, 8, uint8_t)
R2SLEIGH_DEFINE_WIDE_FIELD(512, 8, 16, uint16_t)
R2SLEIGH_DEFINE_WIDE_FIELD(512, 8, 32, uint32_t)
R2SLEIGH_DEFINE_WIDE_FIELD(512, 8, 64, uint64_t)
R2SLEIGH_DEFINE_WIDE_FIELD(512, 8, 128, __uint128_t)

/*
 * Exact arithmetic-flag helpers.  Keeping the intermediate arithmetic in the
 * unsigned carrier type avoids C signed-overflow undefined behavior.  A
 * rendered source operand appears once at the callsite; repeated bit tests are
 * performed only on these helper-local values.
 */
#define R2SLEIGH_DEFINE_ARITHMETIC_FLAGS(BITS, TYPE)                              \
    static inline R2SLEIGH_UNUSED uint8_t                                         \
        r2sleigh_int_carry_##BITS(TYPE left, TYPE right)                          \
    {                                                                             \
        const TYPE result = (TYPE)(left + right);                                 \
        return (uint8_t)(result < left);                                          \
    }                                                                             \
    static inline R2SLEIGH_UNUSED uint8_t                                         \
        r2sleigh_int_scarry_##BITS(TYPE left, TYPE right)                         \
    {                                                                             \
        const TYPE result = (TYPE)(left + right);                                 \
        const TYPE same_sign = (TYPE)~(TYPE)(left ^ right);                       \
        const TYPE changed_sign = (TYPE)(left ^ result);                          \
        const TYPE overflow = (TYPE)(same_sign & changed_sign);                   \
        return (uint8_t)((overflow >> ((BITS)-1)) & (TYPE)1);                     \
    }                                                                             \
    static inline R2SLEIGH_UNUSED uint8_t                                         \
        r2sleigh_int_sborrow_##BITS(TYPE left, TYPE right)                        \
    {                                                                             \
        const TYPE result = (TYPE)(left - right);                                 \
        const TYPE different_sign = (TYPE)(left ^ right);                         \
        const TYPE changed_sign = (TYPE)(left ^ result);                          \
        const TYPE overflow = (TYPE)(different_sign & changed_sign);              \
        return (uint8_t)((overflow >> ((BITS)-1)) & (TYPE)1);                     \
    }

R2SLEIGH_DEFINE_ARITHMETIC_FLAGS(8, uint8_t)
R2SLEIGH_DEFINE_ARITHMETIC_FLAGS(16, uint16_t)
R2SLEIGH_DEFINE_ARITHMETIC_FLAGS(32, uint32_t)
R2SLEIGH_DEFINE_ARITHMETIC_FLAGS(64, uint64_t)
R2SLEIGH_DEFINE_ARITHMETIC_FLAGS(128, __uint128_t)

#undef R2SLEIGH_DEFINE_ARITHMETIC_FLAGS
#undef R2SLEIGH_DEFINE_WIDE_FIELD
#undef R2SLEIGH_UNUSED

#endif
