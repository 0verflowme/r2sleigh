/* Command-line oracle for the shape corpus.
 *
 * shapes.c stays the single implementation; only its demo main is renamed
 * while it is included here, exactly as oracle.c does for hashes.c. The
 * expected value a differential case compares against is therefore produced by
 * the original source, compiled by the same compiler for the same target as
 * the binary the decompiler read.
 *
 * usage: shapes_oracle FUNCTION A B
 * A and B are unsigned 64-bit integers, decimal or 0x-prefixed hexadecimal.
 */
#define main shapes_corpus_main
#include "shapes.c"
#undef main

#include <errno.h>
#include <inttypes.h>
#include <stdlib.h>

enum oracle_exit {
    ORACLE_OK = 0,
    ORACLE_USAGE = 64,
    ORACLE_FUNCTION = 65,
    ORACLE_ARGUMENT = 66,
};

struct entry {
    const char *name;
    uint64_t (*call)(uint64_t, uint64_t);
};

static const struct entry entries[] = {
    {"shape_variadic", shape_variadic},
    {"shape_variadic_local", shape_variadic_local},
    {"shape_call_chain", shape_call_chain},
    {"shape_struct_pointer", shape_struct_pointer},
    {"shape_struct_value", shape_struct_value},
    {"shape_struct_array", shape_struct_array},
    {"shape_stack_buffer", shape_stack_buffer},
    {"shape_recurse_direct", shape_recurse_direct},
    {"shape_recurse_mutual", shape_recurse_mutual},
    {"shape_signed_divmod", shape_signed_divmod},
    {"shape_multiword_return", shape_multiword_return},
    {"shape_pointer_to_pointer", shape_pointer_to_pointer},
    {"shape_function_pointer", shape_function_pointer},
};

static void usage(const char *program) {
    fprintf(stderr, "usage: %s FUNCTION A B\n", program);
    fputs("functions:", stderr);
    for (size_t index = 0; index < sizeof entries / sizeof entries[0]; index++) {
        fprintf(stderr, " %s", entries[index].name);
    }
    fputs("\nA and B are unsigned 64-bit integers, decimal or 0x-hexadecimal.\n",
          stderr);
}

static int parse_word(const char *text, uint64_t *value) {
    char *end = NULL;
    errno = 0;
    unsigned long long parsed = strtoull(text, &end, 0);
    if (end == text || *end != '\0' || errno != 0) {
        return 0;
    }
    *value = (uint64_t)parsed;
    return 1;
}

int main(int argc, char **argv) {
    if (argc != 4) {
        usage(argv[0]);
        return ORACLE_USAGE;
    }
    const struct entry *chosen = NULL;
    for (size_t index = 0; index < sizeof entries / sizeof entries[0]; index++) {
        if (strcmp(argv[1], entries[index].name) == 0) {
            chosen = &entries[index];
            break;
        }
    }
    if (chosen == NULL) {
        usage(argv[0]);
        return ORACLE_FUNCTION;
    }
    uint64_t a = 0;
    uint64_t b = 0;
    if (!parse_word(argv[2], &a) || !parse_word(argv[3], &b)) {
        usage(argv[0]);
        return ORACLE_ARGUMENT;
    }
    printf("%016" PRIx64 "\n", chosen->call(a, b));
    return ORACLE_OK;
}
