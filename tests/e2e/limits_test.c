// Limits fixture: each function targets one thing the analysis is meant to prove.
//
// Compile four ways so the same source is seen at two optimisation levels on both
// supported architectures:
//   clang -arch x86_64 -O0 -g -o limits_test_x86     tests/e2e/limits_test.c
//   clang -arch x86_64 -O2 -g -o limits_test_opt_x86 tests/e2e/limits_test.c
//   clang -arch arm64  -O0 -g -o limits_test_arm     tests/e2e/limits_test.c
//   clang -arch arm64  -O2 -g -o limits_test_opt_arm tests/e2e/limits_test.c

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

// ---------------------------------------------------------------- VM dispatch

// Threaded interpreter: the dispatch is an indirect jump through a label table,
// which is the shape a jump-table recogniser cannot reach by reading branches.
int vm_threaded(const uint8_t *code, int len, int32_t seed) {
    static void *table[] = {&&op_halt, &&op_push, &&op_add, &&op_mul,
                            &&op_dup,  &&op_swap, &&op_jnz, &&op_neg};
    int32_t stack[64];
    int sp = 0, pc = 0;
    stack[sp++] = seed;
#define NEXT()                                                                 \
    do {                                                                       \
        if (pc >= len) goto op_halt;                                           \
        goto *table[code[pc++] & 7];                                           \
    } while (0)
    NEXT();
op_push:
    if (sp < 63 && pc < len) stack[sp++] = code[pc++];
    NEXT();
op_add:
    if (sp >= 2) { stack[sp - 2] += stack[sp - 1]; sp--; }
    NEXT();
op_mul:
    if (sp >= 2) { stack[sp - 2] *= stack[sp - 1]; sp--; }
    NEXT();
op_dup:
    if (sp >= 1 && sp < 63) { stack[sp] = stack[sp - 1]; sp++; }
    NEXT();
op_swap:
    if (sp >= 2) { int32_t t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t; }
    NEXT();
op_jnz:
    if (sp >= 1 && stack[sp - 1] != 0 && pc < len) pc = code[pc] % (len > 0 ? len : 1);
    NEXT();
op_neg:
    if (sp >= 1) stack[sp - 1] = -stack[sp - 1];
    NEXT();
op_halt:
    return sp > 0 ? stack[sp - 1] : 0;
#undef NEXT
}

// Register machine over a state struct: the selector is a memory field rather
// than a register, so the dispatch proof has to go through the load.
typedef struct { int32_t r[8]; int32_t pc; int32_t flag; } VmState;

int vm_register_machine(VmState *st, const uint8_t *prog, int len) {
    while (st->pc >= 0 && st->pc < len) {
        uint8_t op = prog[st->pc++];
        int a = (op >> 3) & 7, b = op & 7;
        switch (op >> 6) {
        case 0: st->r[a] = st->r[b]; break;
        case 1: st->r[a] += st->r[b]; break;
        case 2: st->r[a] ^= st->r[b]; st->flag = st->r[a] == 0; break;
        case 3:
            if (st->flag) st->pc = st->r[b] % (len > 0 ? len : 1);
            break;
        }
    }
    return st->r[0];
}

// Dispatch inside dispatch: the outer switch selects a handler that itself
// dispatches, which is where a single-level recogniser stops.
int vm_nested_dispatch(int outer, int inner, int v) {
    switch (outer & 3) {
    case 0:
        switch (inner & 3) {
        case 0: return v + 1;
        case 1: return v - 1;
        case 2: return v * 2;
        default: return v / 2;
        }
    case 1:
        switch (inner & 3) {
        case 0: return v ^ 0xff;
        case 1: return v & 0x0f;
        case 2: return v | 0xf0;
        default: return ~v;
        }
    case 2: return inner ? v << (inner & 7) : v;
    default: return v;
    }
}

// ---------------------------------------------------------------- SSA control

// Irreducible: two edges enter the loop body at different points, so no single
// header dominates it and the structurer cannot name one loop.
int ssa_irreducible(int n, int start) {
    int a = 0, b = 1;
    if (start) goto entry_b;
entry_a:
    a += n;
    if (a > 100) return a;
entry_b:
    b += a;
    if (b > 100) return b;
    a += b;
    if (a < 1000) goto entry_a;
    return a + b;
}

// A wide merge: eight predecessors reach one block, so the phi for `acc` has
// eight incoming values and every one has to be accounted for.
int ssa_wide_phi(int sel, int x) {
    int acc;
    switch (sel & 7) {
    case 0: acc = x + 1; break;
    case 1: acc = x - 1; break;
    case 2: acc = x * 3; break;
    case 3: acc = x / 3; break;
    case 4: acc = x % 7; break;
    case 5: acc = x << 2; break;
    case 6: acc = x >> 2; break;
    default: acc = -x; break;
    }
    return acc * acc + acc;
}

// Four loop-carried values updated together, so the phi web is a cycle rather
// than a chain and no single induction variable describes it.
int ssa_coupled_induction(int n) {
    int a = 1, b = 2, c = 3, d = 4;
    for (int i = 0; i < n; i++) {
        int na = b + d;
        int nb = a ^ c;
        int nc = d - a;
        int nd = c + b;
        a = na; b = nb; c = nc; d = nd;
    }
    return a + b + c + d;
}

// One loop with three exits, each producing a different value.
int ssa_multi_exit(const int *p, int n, int limit) {
    int sum = 0;
    for (int i = 0; i < n; i++) {
        if (!p) return -1;
        sum += p[i];
        if (sum > limit) return sum;
        if (p[i] == 0) break;
    }
    return sum == 0 ? -2 : sum;
}

// Aliasing through a union: the same bytes are read as two types, so a memory
// model that keys on type alone answers wrongly.
typedef union { uint64_t q; uint32_t d[2]; uint8_t b[8]; } Bits;

uint32_t ssa_union_alias(uint64_t v, int which) {
    Bits u;
    u.q = v;
    u.b[which & 7] ^= 0xa5;
    return u.d[(which >> 3) & 1] + u.b[0];
}

// ---------------------------------------------------------------- symex depth

// Twenty independent conditions: 2^20 paths, so any explorer without pruning
// has to refuse rather than enumerate.
int symex_path_explosion(const uint8_t *k) {
    int score = 0;
    for (int i = 0; i < 20; i++) {
        if (k[i] & 1) score += (1 << (i & 15));
        else score -= (i * 3);
    }
    return score;
}

// One reachable answer behind arithmetic: proving the return needs a solver
// rather than a range.
int symex_constraint(int32_t a, int32_t b, int32_t c) {
    if (a * 3 + b != 77) return 0;
    if (b - c * 2 != 11) return 0;
    if ((a ^ c) != 0x5a) return 0;
    return a + b + c;
}

// The branch depends on a value loaded from a table, so feasibility needs the
// memory contents and not just the index.
int symex_memory_branch(const uint8_t *t, int i) {
    uint8_t v = t[i & 15];
    if (v > 200) return v * 2;
    if (v > 100) return v + 50;
    if (v > 50) return v - 25;
    return 0;
}

// Provably unreachable: nothing satisfies both guards, so the body is dead and
// the proof has to say so rather than render it.
int symex_unreachable(int x) {
    if (x > 100 && x < 50) {
        return x * 999;
    }
    return x;
}

// The loop bound is symbolic and the body is affine, so the exit value is
// closed-form rather than something to unroll.
int symex_symbolic_bound(int n, int step) {
    int total = 0;
    for (int i = 0; i < n; i += (step > 0 ? step : 1)) total += i;
    return total;
}

// ---------------------------------------------------------------- types, ABI

typedef struct { int32_t id; float w; struct { int16_t x, y; } pos; char tag[8]; } Node;

float abi_struct_walk(const Node *ns, int n) {
    float acc = 0.0f;
    for (int i = 0; i < n; i++) acc += ns[i].w * (float)(ns[i].pos.x + ns[i].pos.y);
    return acc;
}

// Mixed integer and SSE parameters interleaved: the two ABI sequences advance
// independently and a single positional list cannot describe it.
double abi_mixed_params(int a, double b, int c, double d, int e, double f) {
    return b * a + d * c + f * e;
}

// Out-params of three widths written through pointers.
void abi_out_params(int v, int8_t *lo, int32_t *mid, int64_t *hi) {
    *lo = (int8_t)(v & 0xff);
    *mid = v * 3;
    *hi = (int64_t)v * 0x100000000LL;
}

// Variadic: the count is a parameter and the register save area is implicit.
long abi_variadic_sum(int count, ...) {
    __builtin_va_list ap;
    __builtin_va_start(ap, count);
    long total = 0;
    for (int i = 0; i < count; i++) total += __builtin_va_arg(ap, int);
    __builtin_va_end(ap);
    return total;
}

// Returned by value in two registers.
typedef struct { int64_t lo, hi; } Pair;

Pair abi_pair_return(int64_t a, int64_t b) {
    Pair p;
    p.lo = a * b;
    p.hi = a ^ b;
    return p;
}

// Array whose extent is proven by the loop bound rather than declared.
int types_array_extent(const int32_t *a) {
    int m = a[0];
    for (int i = 1; i < 16; i++) if (a[i] > m) m = a[i];
    return m;
}

// ---------------------------------------------------------------- call graph

static int helper_even(int n);
static int helper_odd(int n);

static int helper_even(int n) { return n == 0 ? 1 : helper_odd(n - 1); }
static int helper_odd(int n) { return n == 0 ? 0 : helper_even(n - 1); }

int calls_mutual_recursion(int n) { return helper_even(n) + helper_odd(n); }

typedef int (*BinOp)(int, int);
static int op_add_fn(int a, int b) { return a + b; }
static int op_sub_fn(int a, int b) { return a - b; }
static int op_mul_fn(int a, int b) { return a * b; }

// Indirect call through a table: the callee is only known once the index is.
int calls_indirect_table(int which, int a, int b) {
    static BinOp ops[] = {op_add_fn, op_sub_fn, op_mul_fn};
    return ops[which % 3](a, b);
}

// A call in the tail position that the optimiser turns into a jump.
int calls_tail(int n, int acc) {
    if (n <= 0) return acc;
    return calls_tail(n - 1, acc + n);
}

int main(int argc, char **argv) {
    uint8_t code[16];
    for (int i = 0; i < 16; i++) code[i] = (uint8_t)(argc * i);
    VmState st;
    memset(&st, 0, sizeof st);
    Node ns[4];
    memset(ns, 0, sizeof ns);
    int8_t lo; int32_t mid; int64_t hi;
    abi_out_params(argc, &lo, &mid, &hi);
    Pair pr = abi_pair_return(argc, argc + 1);
    int32_t arr[16];
    for (int i = 0; i < 16; i++) arr[i] = argc * i;
    long total = vm_threaded(code, 16, argc) + vm_register_machine(&st, code, 16)
        + vm_nested_dispatch(argc, argc + 1, argc + 2) + ssa_irreducible(argc, argc & 1)
        + ssa_wide_phi(argc, argc) + ssa_coupled_induction(argc)
        + ssa_multi_exit(arr, 16, 100) + (int)ssa_union_alias((uint64_t)argc, argc)
        + symex_path_explosion(code) + symex_constraint(argc, argc, argc)
        + symex_memory_branch(code, argc) + symex_unreachable(argc)
        + symex_symbolic_bound(argc, 2) + (int)abi_struct_walk(ns, 4)
        + (int)abi_mixed_params(argc, 1.5, argc, 2.5, argc, 3.5)
        + lo + mid + (int)hi + (int)pr.lo + (int)pr.hi
        + (int)abi_variadic_sum(3, argc, argc, argc) + types_array_extent(arr)
        + calls_mutual_recursion(argc) + calls_indirect_table(argc, argc, argc + 1)
        + calls_tail(argc, 0);
    printf("%ld\n", total);
    return 0;
}
