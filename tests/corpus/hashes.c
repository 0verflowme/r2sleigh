/* Hash corpus for r2sleigh rendering evaluation.
   Every function is noinline so it survives -O2 as its own symbol.
   Every function keeps its accumulator in a register at -O1/-O2, which is
   the loop-carried recurrence the renderer has to bind. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define NOINL __attribute__((noinline))

/* ---- 1. FNV-1a 32 ---- */
NOINL uint32_t fnv1a32(const uint8_t *p, size_t n) {
    uint32_t h = 0x811c9dc5u;
    for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 0x01000193u; }
    return h;
}

/* ---- 2. FNV-1a 64 ---- */
NOINL uint64_t fnv1a64(const uint8_t *p, size_t n) {
    uint64_t h = 0xcbf29ce484222325ull;
    for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 0x100000001b3ull; }
    return h;
}

/* ---- 3. djb2 ---- */
NOINL uint32_t djb2(const uint8_t *p, size_t n) {
    uint32_t h = 5381u;
    for (size_t i = 0; i < n; i++) h = ((h << 5) + h) + p[i];
    return h;
}

/* ---- 4. sdbm ---- */
NOINL uint32_t sdbm(const uint8_t *p, size_t n) {
    uint32_t h = 0;
    for (size_t i = 0; i < n; i++) h = p[i] + (h << 6) + (h << 16) - h;
    return h;
}

/* ---- 5. Adler-32: two coupled accumulators ---- */
NOINL uint32_t adler32(const uint8_t *p, size_t n) {
    uint32_t a = 1, b = 0;
    for (size_t i = 0; i < n; i++) { a = (a + p[i]) % 65521u; b = (b + a) % 65521u; }
    return (b << 16) | a;
}

/* ---- 6. Fletcher-32 ---- */
NOINL uint32_t fletcher32(const uint16_t *p, size_t words) {
    uint32_t s1 = 0xffffu, s2 = 0xffffu;
    for (size_t i = 0; i < words; i++) { s1 = (s1 + p[i]) % 65535u; s2 = (s2 + s1) % 65535u; }
    return (s2 << 16) | s1;
}

/* ---- 7. CRC32 bitwise: nested loop, no table ---- */
NOINL uint32_t crc32_bitwise(const uint8_t *p, size_t n) {
    uint32_t c = 0xffffffffu;
    for (size_t i = 0; i < n; i++) {
        c ^= p[i];
        for (int k = 0; k < 8; k++) c = (c >> 1) ^ (0xedb88320u & (uint32_t)(-(int32_t)(c & 1)));
    }
    return ~c;
}

/* ---- 8/9. CRC32 table-driven: void init writing a global, then use ---- */
static uint32_t crc_tab[256];
NOINL void crc32_init(void) {
    for (uint32_t i = 0; i < 256; i++) {
        uint32_t c = i;
        for (int k = 0; k < 8; k++) c = (c >> 1) ^ (0xedb88320u & (uint32_t)(-(int32_t)(c & 1)));
        crc_tab[i] = c;
    }
}
NOINL uint32_t crc32_table(const uint8_t *p, size_t n) {
    uint32_t c = 0xffffffffu;
    for (size_t i = 0; i < n; i++) c = crc_tab[(c ^ p[i]) & 0xff] ^ (c >> 8);
    return ~c;
}

/* ---- 10. MurmurHash3 x86_32: rotates, tail switch, finaliser ---- */
static inline uint32_t rotl32(uint32_t x, int8_t r) { return (x << r) | (x >> (32 - r)); }
NOINL uint32_t murmur3_32(const uint8_t *p, size_t n, uint32_t seed) {
    uint32_t h = seed;
    const uint32_t c1 = 0xcc9e2d51u, c2 = 0x1b873593u;
    size_t nblocks = n / 4;
    for (size_t i = 0; i < nblocks; i++) {
        uint32_t k;
        memcpy(&k, p + i * 4, 4);
        k *= c1; k = rotl32(k, 15); k *= c2;
        h ^= k; h = rotl32(h, 13); h = h * 5u + 0xe6546b64u;
    }
    const uint8_t *tail = p + nblocks * 4;
    uint32_t k1 = 0;
    switch (n & 3) {
        case 3: k1 ^= (uint32_t)tail[2] << 16; /* fallthrough */
        case 2: k1 ^= (uint32_t)tail[1] << 8;  /* fallthrough */
        case 1: k1 ^= (uint32_t)tail[0];
                k1 *= c1; k1 = rotl32(k1, 15); k1 *= c2; h ^= k1;
    }
    h ^= (uint32_t)n;
    h ^= h >> 16; h *= 0x85ebca6bu;
    h ^= h >> 13; h *= 0xc2b2ae35u;
    h ^= h >> 16;
    return h;
}

/* ---- 11. xxHash32: four independent lanes, unrolled 16-byte stripe ---- */
#define XXP1 2654435761u
#define XXP2 2246822519u
#define XXP3 3266489917u
#define XXP4 668265263u
#define XXP5 374761393u
NOINL uint32_t xxhash32(const uint8_t *p, size_t n, uint32_t seed) {
    const uint8_t *end = p + n;
    uint32_t h;
    if (n >= 16) {
        const uint8_t *limit = end - 16;
        uint32_t v1 = seed + XXP1 + XXP2, v2 = seed + XXP2, v3 = seed, v4 = seed - XXP1;
        do {
            uint32_t w;
            memcpy(&w, p, 4); v1 = rotl32(v1 + w * XXP2, 13) * XXP1; p += 4;
            memcpy(&w, p, 4); v2 = rotl32(v2 + w * XXP2, 13) * XXP1; p += 4;
            memcpy(&w, p, 4); v3 = rotl32(v3 + w * XXP2, 13) * XXP1; p += 4;
            memcpy(&w, p, 4); v4 = rotl32(v4 + w * XXP2, 13) * XXP1; p += 4;
        } while (p <= limit);
        h = rotl32(v1, 1) + rotl32(v2, 7) + rotl32(v3, 12) + rotl32(v4, 18);
    } else {
        h = seed + XXP5;
    }
    h += (uint32_t)n;
    while (p + 4 <= end) { uint32_t w; memcpy(&w, p, 4); h = rotl32(h + w * XXP3, 17) * XXP4; p += 4; }
    while (p < end) { h = rotl32(h + (*p) * XXP5, 11) * XXP1; p++; }
    h ^= h >> 15; h *= XXP2;
    h ^= h >> 13; h *= XXP3;
    h ^= h >> 16;
    return h;
}

/* ---- 12. SipHash-2-4: 64-bit ARX, four state words carried across rounds ---- */
#define ROTL64(x, b) (uint64_t)(((x) << (b)) | ((x) >> (64 - (b))))
#define SIPROUND do { \
    v0 += v1; v1 = ROTL64(v1, 13); v1 ^= v0; v0 = ROTL64(v0, 32); \
    v2 += v3; v3 = ROTL64(v3, 16); v3 ^= v2; \
    v0 += v3; v3 = ROTL64(v3, 21); v3 ^= v0; \
    v2 += v1; v1 = ROTL64(v1, 17); v1 ^= v2; v2 = ROTL64(v2, 32); \
} while (0)
NOINL uint64_t siphash24(const uint8_t *in, size_t inlen, uint64_t k0, uint64_t k1) {
    uint64_t v0 = 0x736f6d6570736575ull ^ k0;
    uint64_t v1 = 0x646f72616e646f6dull ^ k1;
    uint64_t v2 = 0x6c7967656e657261ull ^ k0;
    uint64_t v3 = 0x7465646279746573ull ^ k1;
    const uint8_t *end = in + inlen - (inlen % 8);
    uint64_t b = ((uint64_t)inlen) << 56;
    for (; in != end; in += 8) {
        uint64_t m;
        memcpy(&m, in, 8);
        v3 ^= m;
        SIPROUND; SIPROUND;
        v0 ^= m;
    }
    switch (inlen & 7) {
        case 7: b |= ((uint64_t)in[6]) << 48; /* fallthrough */
        case 6: b |= ((uint64_t)in[5]) << 40; /* fallthrough */
        case 5: b |= ((uint64_t)in[4]) << 32; /* fallthrough */
        case 4: b |= ((uint64_t)in[3]) << 24; /* fallthrough */
        case 3: b |= ((uint64_t)in[2]) << 16; /* fallthrough */
        case 2: b |= ((uint64_t)in[1]) << 8;  /* fallthrough */
        case 1: b |= ((uint64_t)in[0]);       /* fallthrough */
        case 0: break;
    }
    v3 ^= b;
    SIPROUND; SIPROUND;
    v0 ^= b;
    v2 ^= 0xff;
    SIPROUND; SIPROUND; SIPROUND; SIPROUND;
    return v0 ^ v1 ^ v2 ^ v3;
}

/* ---- 13. Pearson: byte table lookup chain ---- */
static const uint8_t pearson_tab[256] = {
 98,  6, 85,150, 36, 23,112,164,135,207,169,  5, 26, 64,165,219,
 61, 20, 68, 89,130, 63, 52,102, 24, 229,132,245, 80,216,195,115,
 90,168,156,203,177,120,  2,190,188,  7,100,185,174,243,162, 10,
237, 18,253,225,  8,208,172,244,255,126,101, 79,145,235,228,121,
123,251, 67,250,161,  0,107, 97,241,111,181, 82,249, 33, 69, 55,
 59,153, 29,  9,213,167, 84, 93, 30, 46, 94, 75,151,114, 73,222,
197, 96,210, 45, 16,227,248,202, 51,152,252,125, 81,206,215,186,
 39,158,178,187,131,136,  1, 49, 50, 17,141, 91, 47,129, 60, 99,
154, 35, 86,171,105, 34, 38,200,147, 58, 77,118,173,246, 76,254,
133,232,196,144,198,124, 53,  4,108, 74,223,234,134,230,157,139,
189,205,199,128,176, 19,211,236,127,192,231, 70,233, 88,146, 44,
183,201, 22, 83, 13,214,116,109,159, 32, 95,226,140,220, 57, 12,
221, 31,209,182,143, 92,149,184,148, 62,113, 65, 37, 27,106,166,
  3, 14,204, 72, 21, 41, 56, 66, 28,193, 40,217, 25, 54,179,117,
238, 87,240,155,180,170,242,212,191,163, 78,218,137,194,175,110,
 43,119,224, 71,122,142, 42,160,104, 48,247,103, 15, 11,138,239
};
NOINL uint8_t pearson(const uint8_t *p, size_t n) {
    uint8_t h = 0;
    for (size_t i = 0; i < n; i++) h = pearson_tab[h ^ p[i]];
    return h;
}

/* ---- 14. combined: chains three hashes through a register ---- */
NOINL uint64_t combined(const uint8_t *p, size_t n) {
    uint64_t acc = fnv1a64(p, n);
    acc ^= (uint64_t)djb2(p, n) << 32;
    acc += (uint64_t)crc32_bitwise(p, n);
    acc = (acc << 7) | (acc >> 57);
    acc ^= (uint64_t)murmur3_32(p, n, (uint32_t)acc);
    return acc;
}

int main(void) {
    static const char msg[] = "The quick brown fox jumps over the lazy dog, 0123456789abcdef";
    const uint8_t *p = (const uint8_t *)msg;
    size_t n = sizeof(msg) - 1;
    crc32_init();
    printf("fnv1a32     %08x\n", fnv1a32(p, n));
    printf("fnv1a64     %016llx\n", (unsigned long long)fnv1a64(p, n));
    printf("djb2        %08x\n", djb2(p, n));
    printf("sdbm        %08x\n", sdbm(p, n));
    printf("adler32     %08x\n", adler32(p, n));
    printf("fletcher32  %08x\n", fletcher32((const uint16_t *)p, n / 2));
    printf("crc32_bit   %08x\n", crc32_bitwise(p, n));
    printf("crc32_tab   %08x\n", crc32_table(p, n));
    printf("murmur3_32  %08x\n", murmur3_32(p, n, 0x9747b28cu));
    printf("xxhash32    %08x\n", xxhash32(p, n, 0));
    printf("siphash24   %016llx\n", (unsigned long long)siphash24(p, n, 0x0706050403020100ull, 0x0f0e0d0c0b0a0908ull));
    printf("pearson     %02x\n", pearson(p, n));
    printf("combined    %016llx\n", (unsigned long long)combined(p, n));
    return 0;
}
