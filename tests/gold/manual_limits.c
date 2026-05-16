#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

/*
 * Source-gold adversarial fixture for manual decompiler audits.
 *
 * Suggested local builds:
 *   gcc -g -O2 -fno-inline -fno-omit-frame-pointer -o /tmp/r2sleigh_manual_limits_O2 tests/gold/manual_limits.c
 *   gcc -g -O0 -fno-inline -fno-omit-frame-pointer -o /tmp/r2sleigh_manual_limits_O0 tests/gold/manual_limits.c
 */

#if defined(__GNUC__)
#define NOINLINE __attribute__((noinline, used))
#else
#define NOINLINE
#endif

typedef struct Item {
    int32_t id;
    uint16_t flags;
    uint16_t len;
    int32_t scores[4];
    char *name;
    struct Item *next;
} Item;

typedef struct Result {
    int32_t code;
    uint64_t hash;
    Item *hit;
    size_t count;
} Result;

volatile int32_t manual_sink;

NOINLINE int32_t struct_nested_array(Item *items, int32_t idx, int32_t add) {
    Item *it = &items[idx];
    it->scores[2] += add;
    if ((it->flags & 4) != 0) {
        return it->scores[2] + it->id;
    }
    return it->scores[0] - it->len;
}

NOINLINE int32_t out_param_parse(const char *s, Result *out) {
    int32_t sign = 1;
    uint64_t value = 0;
    size_t i = 0;
    uint64_t hash = 1469598103934665603ULL;
    if (s[0] == '-') {
        sign = -1;
        i = 1;
    }
    for (; s[i] >= '0' && s[i] <= '9'; i++) {
        value = value * 10 + (uint64_t)(s[i] - '0');
        hash ^= (unsigned char)s[i];
        hash *= 1099511628211ULL;
    }
    out->code = (int32_t)(value * (uint64_t)sign);
    out->hash = hash;
    out->count = i;
    out->hit = NULL;
    return i > 0 && s[i] == 0;
}

NOINLINE uint64_t fnv_fold(const unsigned char *buf, size_t n) {
    uint64_t hash = 1469598103934665603ULL;
    for (size_t i = 0; i < n; i++) {
        unsigned char c = buf[i];
        if (c >= 'A' && c <= 'Z') {
            c = (unsigned char)(c + 32);
        }
        hash ^= c;
        hash *= 1099511628211ULL;
    }
    return hash;
}

NOINLINE int32_t sparse_switch(int32_t op, int32_t a, int32_t b) {
    switch (op) {
    case -7:
        return a - b;
    case 0:
        return a + b;
    case 3:
        return a * 3 + b;
    case 42:
        return (a ^ b) + 42;
    case 1000:
        return b == 0 ? -1 : a / b;
    default:
        return op + a - b;
    }
}

NOINLINE int32_t table_walk(Item *head, const char *needle) {
    int32_t seen = 0;
    for (Item *it = head; it != NULL; it = it->next) {
        seen++;
        if (it->name == NULL || it->len == 0) {
            continue;
        }
        size_t i = 0;
        while (i < it->len && needle[i] != 0 && it->name[i] == needle[i]) {
            i++;
        }
        if (i == it->len && needle[i] == 0) {
            return it->id + seen;
        }
    }
    return -seen;
}

NOINLINE int32_t state_machine(const char *s) {
    int32_t state = 0;
    int32_t score = 0;
    for (size_t i = 0; s[i] != 0; i++) {
        unsigned char c = (unsigned char)s[i];
        switch (state) {
        case 0:
            if ((c >= 'a' && c <= 'z') || c == '_') {
                state = 1;
                score += 3;
            } else if (c >= '0' && c <= '9') {
                state = 2;
                score -= 5;
            } else {
                return -100 - (int32_t)i;
            }
            break;
        case 1:
            if (c >= '0' && c <= '9') {
                state = 2;
                score += c - '0';
            } else if (c == '-') {
                state = 3;
                score += 7;
            } else if (!(c >= 'a' && c <= 'z') && c != '_') {
                return -200 - (int32_t)i;
            }
            break;
        case 2:
            if (c == '_') {
                state = 1;
            } else if (c == '-') {
                state = 3;
            } else if (c < '0' || c > '9') {
                return -300 - (int32_t)i;
            }
            break;
        default:
            if (c != 'x') {
                return -400 - (int32_t)i;
            }
            state = 0;
            break;
        }
    }
    return score + state;
}

NOINLINE size_t mem_scan2(const unsigned char *buf, size_t n, unsigned char a, unsigned char b) {
    size_t count = 0;
    for (size_t i = 0; i < n; i++) {
        unsigned char c = buf[i];
        if (c == a || c == b) {
            count++;
        }
    }
    return count;
}

int main(int argc, char **argv) {
    Item items[2] = {
        {1, 4, 3, {1, 2, 3, 4}, "abc", NULL},
        {2, 0, 3, {5, 6, 7, 8}, "def", NULL},
    };
    Result out = {0};
    items[0].next = &items[1];
    manual_sink += struct_nested_array(items, argc & 1, argc);
    manual_sink += out_param_parse(argc > 1 ? argv[1] : "123", &out);
    manual_sink += (int32_t)fnv_fold((const unsigned char *)"AbC", 3);
    manual_sink += sparse_switch(argc, manual_sink, (int32_t)out.count);
    manual_sink += table_walk(items, argc > 2 ? argv[2] : "def");
    manual_sink += state_machine(argc > 3 ? argv[3] : "ab-xy9");
    manual_sink += (int32_t)mem_scan2((const unsigned char *)"banana", 6, 'a', 'z');
    return manual_sink == 0;
}
