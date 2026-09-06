/* Strict command-line oracle for the corpus functions gated by differential tests.
 * hashes.c remains the single semantic implementation; only its demo main is
 * renamed while it is included here.
 */
#define main hashes_corpus_main
#include "hashes.c"
#undef main

#include <inttypes.h>
#include <stdlib.h>

enum oracle_exit {
    ORACLE_OK = 0,
    ORACLE_USAGE = 64,
    ORACLE_FUNCTION = 65,
    ORACLE_HEX = 66,
    ORACLE_SEED = 67,
    ORACLE_ALLOC = 68,
};

enum oracle_function {
    ORACLE_FNV1A32,
    ORACLE_FNV1A64,
    ORACLE_DJB2,
    ORACLE_SDBM,
    ORACLE_ADLER32,
    ORACLE_CRC32_BITWISE,
    ORACLE_PEARSON,
    ORACLE_MURMUR3_32,
    ORACLE_XXHASH32,
};

static void usage(const char *program) {
    fprintf(stderr, "usage: %s FUNCTION HEX_BYTES [SEED]\n", program);
    fputs("functions: fnv1a32 fnv1a64 djb2 sdbm adler32 crc32_bitwise "
          "pearson murmur3_32 xxhash32\n",
          stderr);
    fputs("HEX_BYTES is an even-length hexadecimal string, or '-' for empty input.\n",
          stderr);
    fputs("SEED is required only for murmur3_32 and xxhash32; use decimal or "
          "0x-prefixed hexadecimal.\n",
          stderr);
}

static int parse_function(const char *name, enum oracle_function *function) {
    if (strcmp(name, "fnv1a32") == 0) {
        *function = ORACLE_FNV1A32;
    } else if (strcmp(name, "fnv1a64") == 0) {
        *function = ORACLE_FNV1A64;
    } else if (strcmp(name, "djb2") == 0) {
        *function = ORACLE_DJB2;
    } else if (strcmp(name, "sdbm") == 0) {
        *function = ORACLE_SDBM;
    } else if (strcmp(name, "adler32") == 0) {
        *function = ORACLE_ADLER32;
    } else if (strcmp(name, "crc32_bitwise") == 0) {
        *function = ORACLE_CRC32_BITWISE;
    } else if (strcmp(name, "pearson") == 0) {
        *function = ORACLE_PEARSON;
    } else if (strcmp(name, "murmur3_32") == 0) {
        *function = ORACLE_MURMUR3_32;
    } else if (strcmp(name, "xxhash32") == 0) {
        *function = ORACLE_XXHASH32;
    } else {
        return 0;
    }
    return 1;
}

static int function_needs_seed(enum oracle_function function) {
    return function == ORACLE_MURMUR3_32 || function == ORACLE_XXHASH32;
}

static int hex_nibble(char ch, uint8_t *nibble) {
    if (ch >= '0' && ch <= '9') {
        *nibble = (uint8_t)(ch - '0');
    } else if (ch >= 'a' && ch <= 'f') {
        *nibble = (uint8_t)(ch - 'a' + 10);
    } else if (ch >= 'A' && ch <= 'F') {
        *nibble = (uint8_t)(ch - 'A' + 10);
    } else {
        return 0;
    }
    return 1;
}

static int decode_hex(const char *hex, uint8_t **bytes, size_t *length) {
    size_t hex_length;
    uint8_t *decoded;

    if (strcmp(hex, "-") == 0) {
        *bytes = NULL;
        *length = 0;
        return ORACLE_OK;
    }

    hex_length = strlen(hex);
    if (hex_length == 0 || (hex_length & 1u) != 0) {
        return ORACLE_HEX;
    }

    *length = hex_length / 2;
    decoded = malloc(*length);
    if (decoded == NULL) {
        return ORACLE_ALLOC;
    }

    for (size_t index = 0; index < *length; ++index) {
        uint8_t high;
        uint8_t low;
        if (!hex_nibble(hex[index * 2], &high) ||
            !hex_nibble(hex[index * 2 + 1], &low)) {
            free(decoded);
            return ORACLE_HEX;
        }
        decoded[index] = (uint8_t)((high << 4) | low);
    }

    *bytes = decoded;
    return ORACLE_OK;
}

static int seed_digit(char ch, unsigned base, uint32_t *digit) {
    if (ch >= '0' && ch <= '9') {
        *digit = (uint32_t)(ch - '0');
    } else if (base == 16 && ch >= 'a' && ch <= 'f') {
        *digit = (uint32_t)(ch - 'a' + 10);
    } else if (base == 16 && ch >= 'A' && ch <= 'F') {
        *digit = (uint32_t)(ch - 'A' + 10);
    } else {
        return 0;
    }
    return *digit < base;
}

static int parse_seed(const char *text, uint32_t *seed) {
    unsigned base = 10;
    size_t index = 0;
    uint64_t value = 0;

    if (text[0] == '0' && (text[1] == 'x' || text[1] == 'X')) {
        base = 16;
        index = 2;
    }
    if (text[index] == '\0') {
        return 0;
    }

    for (; text[index] != '\0'; ++index) {
        uint32_t digit;
        if (!seed_digit(text[index], base, &digit)) {
            return 0;
        }
        value = value * base + digit;
        if (value > UINT32_MAX) {
            return 0;
        }
    }

    *seed = (uint32_t)value;
    return 1;
}

static void dispatch(enum oracle_function function, const uint8_t *bytes,
                     size_t length, uint32_t seed) {
    switch (function) {
    case ORACLE_FNV1A32:
        printf("%08" PRIx32 "\n", fnv1a32(bytes, length));
        break;
    case ORACLE_FNV1A64:
        printf("%016" PRIx64 "\n", fnv1a64(bytes, length));
        break;
    case ORACLE_DJB2:
        printf("%08" PRIx32 "\n", djb2(bytes, length));
        break;
    case ORACLE_SDBM:
        printf("%08" PRIx32 "\n", sdbm(bytes, length));
        break;
    case ORACLE_ADLER32:
        printf("%08" PRIx32 "\n", adler32(bytes, length));
        break;
    case ORACLE_CRC32_BITWISE:
        printf("%08" PRIx32 "\n", crc32_bitwise(bytes, length));
        break;
    case ORACLE_PEARSON:
        printf("%02" PRIx32 "\n", (uint32_t)pearson(bytes, length));
        break;
    case ORACLE_MURMUR3_32:
        printf("%08" PRIx32 "\n", murmur3_32(bytes, length, seed));
        break;
    case ORACLE_XXHASH32:
        printf("%08" PRIx32 "\n", xxhash32(bytes, length, seed));
        break;
    }
}

int main(int argc, char **argv) {
    enum oracle_function function;
    uint8_t empty_byte = 0;
    uint8_t *allocated_bytes = NULL;
    const uint8_t *bytes;
    size_t length;
    uint32_t seed = 0;
    int decode_status;
    int needs_seed;

    if (argc < 2) {
        usage(argv[0]);
        return ORACLE_USAGE;
    }
    if (!parse_function(argv[1], &function)) {
        fprintf(stderr, "error: unsupported function: %s\n", argv[1]);
        return ORACLE_FUNCTION;
    }

    needs_seed = function_needs_seed(function);
    if (needs_seed && argc == 3) {
        fprintf(stderr, "error: seed required for %s\n", argv[1]);
        return ORACLE_SEED;
    }
    if (argc != (needs_seed ? 4 : 3)) {
        usage(argv[0]);
        return ORACLE_USAGE;
    }

    decode_status = decode_hex(argv[2], &allocated_bytes, &length);
    if (decode_status == ORACLE_HEX) {
        fputs("error: HEX_BYTES must be nonempty, even-length hexadecimal or '-'\n",
              stderr);
        return ORACLE_HEX;
    }
    if (decode_status == ORACLE_ALLOC) {
        fputs("error: unable to allocate input buffer\n", stderr);
        return ORACLE_ALLOC;
    }
    bytes = length == 0 ? &empty_byte : allocated_bytes;

    if (needs_seed && !parse_seed(argv[3], &seed)) {
        free(allocated_bytes);
        fputs("error: SEED must be a uint32 in decimal or 0x-prefixed hexadecimal\n",
              stderr);
        return ORACLE_SEED;
    }

    dispatch(function, bytes, length, seed);
    free(allocated_bytes);
    return ORACLE_OK;
}
