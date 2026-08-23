/* Independent branch/straight-line corpus. Shares no function name, constant,
   or shape with tests/e2e/vuln_test.c. Same *class* of code (guards, nested
   conditions, bitwise tests, struct access, short-circuit, dead branches) so
   the score is comparable. */
#include <stdint.h>
#include <stdio.h>

#define NOINL __attribute__((noinline))

typedef struct { int alpha; int beta; long gamma; } Rec;
typedef struct { char filler[0x180]; int tail; } Wide;

static int g_sink;
static long g_note;
static volatile int g_opaque;

NOINL int gate_one(int q)            { if (q == 0xBEEF) return 1; return 0; }
NOINL int gate_three(int m, int n, int o) {
    if (m == 7) { if (n == 14) { if (o == 21) return 1; } }
    return 0;
}
NOINL int affine_probe(int q)        { int r = q * 3 - 4; if (r == 41) return 1; return 0; }
NOINL int paired_sum_diff(int m, int n) {
    int s = m + n, d = m - n;
    if (s == 250) { if (d == 30) return 1; }
    return 0;
}
NOINL int mask_probe(unsigned int q) {
    if ((q & 0xC0u) == 0x40u) { if ((q & 0x07u) == 0x05u) return 1; }
    return 0;
}
NOINL int bounded_fetch(int *v, int i, int len) {
    if (i < 0 || i >= len) return -1;
    return v[i];
}
NOINL uint32_t narrow64(uint64_t q)  { return (uint32_t)q; }
NOINL uint64_t widen_pair(uint32_t hi, uint32_t lo) { return ((uint64_t)hi << 32) | lo; }
NOINL int sign_xor(int m, int n)     { return (m > 0) ^ (n > 0); }
NOINL int opaque_self_xor(int q)     { g_opaque = q; if ((g_opaque ^ g_opaque) != 0) return 1; return 0; }
static int zero_of(int q)            { return q ^ q; }
NOINL int pure_zero_guard(int q)     { if (zero_of(q) != 0) return 1; return 0; }
NOINL int global_eq_guard(int q)     { g_opaque = q; if (g_opaque == 11) return 1; return 0; }
NOINL int slot_eq_guard(int q)       { volatile int s = q; volatile int *p = &s; if (*p == 11) return 1; return 0; }
NOINL int elem_at(int *v, int i)     { return v[i]; }
NOINL int elem_before(int *v, int i) { return v[i - 1]; }
NOINL uint8_t narrow8(int q)         { return (uint8_t)q; }
NOINL int rec_write(Rec *o, int q)   { o->beta = q; return o->beta; }
NOINL int triple_temp(int q)         { int t = q + 2; return t + t + t; }
NOINL int rec_spread(Rec *o, int q)  { o->alpha = q; o->gamma = q + 9; return (int)o->gamma + o->alpha; }
NOINL uint16_t half_stride(uint16_t *v, int i) { return v[i]; }
NOINL int rec_index(Rec *v, int i, int q)      { v[i].beta = q; return v[i].beta + v[i].alpha; }
NOINL int wide_tail(Wide *o, int q)  { o->tail = q; return o->tail + 2; }
NOINL int constant_branch(int q)     { int f = 1; if (f) return q + 25; g_sink = q * 7; return g_sink; }
NOINL int and_chain(int m, int n)    { if (m) { if (n) return 1; } return 0; }
NOINL int inverted_guard(int q)      { if (q > 9) { g_note = q + 2; } else { return -1; } g_sink = q; return (int)g_note; }
NOINL void and_chain_effect(int m, int n) { if (m) { if (n) { g_sink = m + n; } } }
NOINL void inverted_void(int q)      { if (q > 9) { g_note = q; } else { return; } g_sink = q; }
NOINL int inverted_goto(int q)       { if (q > 9) { g_note = q; } else { goto out; } g_sink = q; out: return (int)g_note; }
NOINL int tail_guard(int q)          { if (q > 9) { g_note = q + 20; g_sink = q - 3; } return 0; }
NOINL int addr_chain(void)           { volatile uintptr_t b = 0x505e00ULL; volatile uintptr_t t = b + 0x210ULL; return (t == 0x506010ULL) ? 1 : 0; }
NOINL int typed_compete(int q)       { g_sink = q; g_note = q; return g_sink + (int)g_note; }
NOINL int bool_relay(int m, int n)   { int a = (m > 0); int b = (n > 0); if (a && b) return 2; if (a || b) return 1; return 0; }

int main(void) {
    Rec r = {0}; Wide w = {{0}, 0}; int v[8] = {1,2,3,4,5,6,7,8}; uint16_t hv[8] = {9,8,7,6,5,4,3,2};
    volatile int x = 5;
    printf("%d %d %d %d %d %d\n", gate_one(x), gate_three(x,x,x), affine_probe(15), paired_sum_diff(140,110), mask_probe(0x45), bounded_fetch(v,3,8));
    printf("%u %llu %d %d %d\n", narrow64(0x1122334455667788ull), (unsigned long long)widen_pair(1,2), sign_xor(1,-1), opaque_self_xor(x), pure_zero_guard(x));
    printf("%d %d %d %d %u\n", global_eq_guard(11), slot_eq_guard(11), elem_at(v,2), elem_before(v,2), narrow8(0x1234));
    printf("%d %d %d %u %d %d\n", rec_write(&r,4), triple_temp(x), rec_spread(&r,3), half_stride(hv,1), rec_index(&r,0,6), wide_tail(&w,8));
    printf("%d %d %d %d %d\n", constant_branch(x), and_chain(1,1), inverted_guard(20), inverted_goto(20), tail_guard(20));
    inverted_void(20); and_chain_effect(1,1);
    printf("%d %d %d\n", addr_chain(), typed_compete(x), bool_relay(1,1));
    return 0;
}
