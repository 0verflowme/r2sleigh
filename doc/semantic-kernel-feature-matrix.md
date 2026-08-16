# Semantic-Kernel Feature Matrix

This matrix describes production authorization, not benchmark coverage. A
fixture name, algorithm identity, source resemblance, instruction count, or
renderer template can never grant executable C authority.

Production follows one generic spine:

```text
immutable source snapshot
    -> Sleigh/r2il
    -> canonical SSA and source obligations
    -> generic r2cert ledger closure
    -> typed semantic-C regions
    -> rendering
```

The only statuses are:

- **Certified**: a generic, artifact-bound contract closes every source
  obligation exactly once.
- **Residual**: useful facts exist, but no complete generic typed region owns
  the function.
- **Unsupported**: the semantic model cannot represent the operation safely.

## Generic production capabilities

| Capability | Status | Exact production boundary |
| --- | --- | --- |
| Typed integer expressions | Certified | Machine width, signedness, casts, shifts, wrapping policy, producers, and source obligations are explicit. Unsupported expressions stay open or refuse. |
| ABI parameters and returns | Certified | The source interface is revision-bound and carries exact physical ABI storage plus the logical carrier projection. A low-bits parameter retains both identities, for example physical `RSI` and logical `ESI`; names are never authority. Typed return-address and stack-pointer carriers are mandatory for an exact interface. |
| Source obligation inventory | Certified | Every canonical instruction/effect begins as live, structural, proven dead, or unsupported. Stable semantic IDs do not depend on names or rendered positions. |
| Single-block terminal return | Certified | One exact typed block, no successors, one return, complete generic ledger closure, and no unsupported inputs/effects. |
| Plain RAM statements in a terminal block | Certified | Ordered, exactly-once reads/writes with explicit address space, width, endianness, object/access identity, and helper execution policy. Stack/custom/word-addressed/unknown memory refuses. |
| Direct void call followed by return | Certified | One exact source callsite identity, complete argument mapping, no unresolved result/clobber semantics, and closed return ownership. Other calls remain residual. |
| Two-arm terminal conditional | Certified | One generic condition plus two terminal arms with exact polarized edges and complete obligation mappings. Joins and nested control remain residual. |
| Conditional shared-return funnel | Residual | Generic multi-block accounting does not yet bind the join carrier and shared return to one exact typed-output owner manifest. The former specialized path is quarantined. |
| Narrow switch-return function | Certified | Exact selector, cases/default, terminal arms, and complete source mappings. General fallthrough/join switches remain residual. |
| Narrow carrier-free/counting loops | Certified | Generic loop/control contracts own initializer, condition, latch transition, exits, and loop-carried obligations. General bodies, memory reductions, and multi-exit loops remain residual. |
| Aggregate layout and member evidence | Residual | Source type graphs and affine access facts are retained. The remaining specialized aggregate renderer must be folded into the generic memory/lvalue region before this becomes a general production capability. |
| Traps, atomics, volatile and unknown effects | Unsupported | Obligations expose them; no executable C is emitted without an exact semantic policy. |

## Benchmark and algorithm fixtures

The following are regression inputs only. They have no production engine
region, no algorithm-specific typed-output seal, and no fixed renderer:

| Fixture family | Production status | Required route to regain executable C |
| --- | --- | --- |
| FNV O0/O2 | Residual | Generic memory loop, byte normalization, unsigned reduction, and return composition. |
| `sum_array` O0/O2 | Residual | Generic affine indexed load, induction variable, reduction, vector/scalar control, and return. |
| struct-array cases | Residual | Generic affine address, stride, authoritative layout/member lvalue, memory order, and arithmetic. |
| branchless `check_secret` / `complex_check` | Residual | Generic typed expression and return composition, independent of the source function name or constants. |
| nested wrap32 O0 | Residual | Generic private-frame elimination, conditional control, wrapping arithmetic, join, and return. |
| private-frame predicate fixtures | Residual | Generic stack-object lifetime/alias proof plus generic conditional/return composition. |

Tests for these families must enter through the public engine with immutable
real binaries. They may provide independent semantic oracles, but they may not
construct algorithm-specific facts, certificates, render permits, or expected
output using the renderer under test.

## Cross-cutting gates

| Gate | Requirement |
| --- | --- |
| Provenance | Positive tests use a versioned binary and manifest, exact source/binary/function hashes, exact symbol file offset and virtual address, complete lift consumption, and validated memory spaces. |
| Obligation closure | Every executable typed-C function has exactly one final disposition for every source obligation. Deletion or duplication fails before rendering. |
| Differential execution | Prepared SSA and the generic typed semantic-C AST run from identical state and compare returns, observable memory, calls, traps, and bounded termination. |
| Compiled C | Generated strict C is compiled and executed against an independent oracle; syntax-only compilation and renderer-derived expected output are insufficient. |
| Generalization | Renaming symbols, relocating addresses, changing cosmetic names, and using equivalent compiler variants cannot change authority. Held-out functions using the same generic constructs are required. |
| FFI | One generated ABI-138/V2 table transports the exact snapshot-schema-11/accessor-schema-4/source-interface-schema-10 contract. No legacy compatibility branch or direct manual ABI may authorize analysis. |
| Failure | Missing or ambiguous evidence residualizes/refuses. It never falls through to heuristic executable C. |

Production code may name generic semantic constructs such as memory, return,
conditional, loop, call, and aggregate. Algorithm and benchmark names belong
only in fixtures, manifests, independent test oracles, and optional
non-authoritative annotations.
