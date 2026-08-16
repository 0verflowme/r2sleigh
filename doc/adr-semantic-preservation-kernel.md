# ADR: Semantic Preservation Kernel Ownership

- Status: Accepted target architecture; implementation incomplete
- Date: 2026-08-06
- Rewrite branch: `codex/semantic-preservation-kernel`

## Problem

A decompiler cannot justify executable C by recognizing a benchmark, matching a
symbol name, counting output statements, or reproducing source-shaped text.
Those techniques can make examples look better while silently dropping machine
effects. The required property is stronger: every live effect in the canonical
machine representation must survive exactly once into an explicitly typed
output node, or the function must residualize/refuse.

## Ownership spine

```text
immutable radare2 function snapshot
        -> generated opaque FFI table
        -> r2il / Sleigh lift
        -> r2ssa graph + source obligation inventory
        -> r2sym evidence + r2types annotations
        -> r2cert closed semantic ledger
        -> r2dec certified regions + typed semantic-C nodes
        -> cosmetic rendering
```

Each fact has one owner:

| Owner | Authority |
| --- | --- |
| radare2 | Immutable signature, calling convention, typed ABI carriers, stack resources, callsites, layouts, assumptions, and revision identity |
| generated FFI | Bounds/ownership validation, opaque lifetimes, panic containment, and exact current wire contract |
| r2il / lift | Canonical machine effects and architecture storage coordinates |
| r2ssa | SSA graph, object and MemorySSA facts, source boundaries, deterministic IDs, liveness, and exhaustive obligations |
| r2sym | Symbolic evidence and bounded semantic policy |
| r2types | Width, signedness, logical projections, layouts, and type evidence |
| r2cert | Artifact-local semantic authority, machine evidence, exact-once ledger closure, and refusal diagnostics |
| r2dec | Typed output-node ownership, proof-preserving structuring, semantic-C interpretation, and rendering |
| r2engine | Request orchestration, budgets, routing, and measured session reuse |

No downstream layer reconstructs a missing upstream fact. Names are cosmetic or
weak hints only and cannot grant executable output.

## Fixture policy

Names such as `fnv_fold`, `sum_array`, and `struct_array` may appear in test
sources and offline lift captures because they describe ordinary programs used
to exercise hashing, loops, and aggregate addressing. They are never production
route keys or certification inputs. Byte offsets and hashes in an offline
capture prove which immutable binary slice was lifted; they do not authorize a
semantic result.

A positive certified test must enter through the same bounded radare2 snapshot
provider as a user request. Hand-authored R2IL/SSA may test local analysis or an
expected refusal, but it cannot produce `TrustedSsaArtifact`, a certification
ledger, or executable C. Stripped benchmark fixtures without exact
address-linked type provenance are expected to refuse certification rather than
receive a test-only interface.

## Source obligations

Every canonical instruction has one initial state:

- live obligation;
- proven dead;
- structural/control-only; or
- unsupported/unknown.

The inventory covers observable reads/writes, calls and arguments/results,
returns, predicates/transfers, traps/ordering, loop-carried state, state
transitions, and every value producer required by a live root. Stable IDs are
independent of names, traversal order, and rendered AST position.

Every obligation receives exactly one final semantic disposition. Missing or
duplicate dispositions fail before structuring. Unsupported semantics remain
residual/refused; they never become guessed C.

## Artifact authority

Durable graph/context/topology snapshots are replay diagnostics, not bearer
tokens. Runtime proofs derived from one immutable `SsaArtifact` share an opaque
run-local authority seal. Only cloning the retaining `Arc<SsaArtifact>`
preserves the exact allocation and authority; independently rebuilt,
assumption-conditioned, or foreign artifacts receive a different seal even if
their diagnostic bytes are equal. Ledgers, effects, controls, and region
permits must share that seal.

`r2source` owns the only coherent source capture. Its
`OwnedFunctionSnapshot` has no public constructor from blocks, layouts,
interfaces, hashes, or revision values. A synchronous radare ABI adapter must
deep-copy the opaque callback payload, validate the closed machine tuple and
bounded image, then create one run-local `Arc` lineage. Function names are
presentation fields and are excluded from semantic fingerprints and identities.
Source CFG and call metadata remain advisory until the trusted Sleigh decoder
independently derives and exactly matches them.

Analysis-only SSA and trusted prepared SSA are different authority domains.
The final r2cert API accepts only the opaque trusted prepared type retained from
the source capture; it does not accept a generic `SsaArtifact` and perform a
runtime provenance guess. Manual blocks and caller-created interfaces may be
analyzed or used in refusal tests, but they cannot inhabit the certifying type.

Return certification retains the exact source-declared return-address carrier
and exit stack-pointer state. A generic source-boundary pass—not a recognizer—
roots every reaching producer. Missing, partial, ambiguous, cyclic, or foreign
machine state fails closed.

## Typed output ownership

`r2cert` proves semantic closure but does not authorize C by mapping count.
Final authority belongs to opaque r2dec region/function values after they prove
that every obligation is owned by the actual artifact-local typed node:

- a `SemanticCExprId` for expressions;
- the exact memory statement producer and component;
- the exact call producer and argument/result component;
- the exact control producer and predicate/transfer component; or
- the exact return producer and return-value component.

Rendered text, names, output counts, and AST positions are never owners.

## Structuring contract

A structuring transformation consumes certified regions and returns:

- a structured region;
- exact source-obligation to typed-node ownership;
- control-domain evidence;
- residual obligations; and
- a deterministic refusal reason.

The intended order is straight-line, if/else, simple loops, explicitly proven
loop rewrites, break/continue, multi-exit loops, switches, then irreducible CFGs.
A while-to-for rewrite must map the exact initializer, phi, comparison, update,
and latch transition. General counted-loop rendering is currently disabled
until those machine operations are independently proven; topology and widths
alone are insufficient.

## Benchmark and fixture policy

Algorithm names such as FNV, sum-array, struct-array, or check-secret may occur
in black-box tests and immutable fixture manifests only. Production code has no
algorithm-specific recognizer, certificate, route, renderer, formula, binary
offset, or source-shaped template.

Positive tests must start from a tracked immutable binary and genuine radare2
snapshot, then drive the public lift -> SSA -> certify -> typed-AST pipeline.
They must not hand-author positive R2IL, source interfaces, retained facts, or
permits. Binary offsets and hashes are provenance fields in a generic manifest,
not semantic inputs.

Generated C is checked against an independent oracle and prepared-SSA execution
over boundary, aliasing, overflow, and deterministic random probes. Comparing a
renderer with itself is circular and forbidden. Unsupported cases are positive
refusal tests, not fake success cases.

## FFI and radare2 seam

The final boundary is one generated API table with opaque session/response
handles. All pointer/length pairs, schemas, capabilities, ownership, and output
views are validated before use; every callback contains unwind. Direct legacy
Rust exports and duplicate handwritten declarations are deleted as consumers
migrate. There is one current architecture, not parallel compatibility paths.

radare2 supplies one coherent immutable function snapshot. Analysis is
read-only. Any mutation is an explicit validated transaction whose complete
application changes revision identity; partial application rolls back.

## Performance

Per-phase measurements cover snapshot, lift, SSA, obligations, evidence, types,
certification, structuring, rendering, and FFI conversion. A cache remains only
when a realistic session trace demonstrates reuse and lower total latency/RSS.
The design keeps algorithm-local memoization and shared immutable artifacts,
uses worklists for deep traversals, and enforces cancellation/complexity
budgets. Benchmark scores never substitute for manual semantic inspection.

## Admission rule

Executable semantic C is admitted only when all of the following are true:

1. the immutable source snapshot and machine context are coherent;
2. the source obligation inventory is complete;
3. all proof objects share one artifact authority seal;
4. every obligation has exactly one preserving disposition;
5. every disposition has one exact typed output owner;
6. machine widths, signedness, wrapping, shifts, casts, memory policy, ABI
   projections, return address, and exit stack pointer are explicit;
7. no residual, refused, unsupported, or open control obligation remains; and
8. semantic differential and compiled-C checks cover the admitted contract.

Anything else residualizes or refuses.

## Definition of done

- Any deliberate effect deletion or duplication fails before rendering.
- Real O0/O2 fixtures pass independent SSA/typed-AST/compiled-C differential
  checks across supported architectures.
- No benchmark-specific production authority remains.
- radare2 provides one coherent snapshot and transactional mutation boundary.
- The generated FFI table is the only Rust ABI and passes malformed-input,
  unwind, ownership, ASan, and UBSan tests.
- Manual lift -> SSA -> obligation -> evidence -> typed-node -> output
  backtracking is recorded for representative calls, switches, loops, memory,
  aggregates, and unsupported control.
- Unsupported inputs visibly residualize/refuse.
