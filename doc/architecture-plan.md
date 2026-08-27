# Architecture plan: dispositions, bindings, and projections

Execution status as of 2026-08-26 on `codex/binding-spine-rewrite`:

- stage 0, the honest 54-cell harness, is committed at `e787934`;
- stage 1, the non-consuming binding-plan contract, is committed at `5078419`;
- stage 2, canonical spans and sealed register/use/write projections, is
  committed at `8c56573`, `697cc9a`, `00eccbb`, and `d7b378d`;
- stage 3, the topology-only lowering split, is committed at `32f7adc`;
- the exact loop-edge `UseSite` prerequisite for stage 5 is committed at
  `ce53a33`;
- the source-coherence fix that retains outputless literal leaves is committed
  at `798a742`;
- stage 4, the independent non-consuming binding audit, is committed at
  `6f6cc33`.

Every completed stage preserved all 54 raw-output snapshots byte-for-byte. The
strict raw baseline reports 0 passing, 26 compile failures, 27 signature
mismatches, and 1 blocked renderer error. The old “38 of 54” number was produced
only after the harness erased declared types and is not a quality measurement.

Revision 2. Revision 1 proposed one `Binding` per `ValueId`. That model was
wrong at the cardinality, rebuilt an upstream fact downstream, and was gated on
measurements the harness cannot make. This revision replaces it.

---

## 1. The end goal

The decompiler should produce, for any function it accepts, a single C rendering
whose correctness is *structural* rather than observed. "Done" is four
properties, each with a stated way of being proved — and none of them is proved
by a corpus pass count.

1. **Every emitted identifier is declared once, in a scope that dominates every
   surviving read, and is assigned before that read on every path.** Proved by
   construction: the phase that decides a value is named is the phase that emits
   its declaration, and placement is derived from a sealed structured-region
   artifact rather than stored. The current structurer consumes and discards
   `Region`, so stage 7 must first retain that artifact.
2. **Every use renders the exact slice it consumes.** Proved by an internal
   invariant — every `UseSite` carries a projection backed by an upstream
   canonical fact — and tripwired externally by compiling the untouched emitted
   declarations under a strict dialect with warnings as errors.
3. **The rendering is deterministic.** Proved by a property test that shuffles
   input orderings and requires the same partition, the same bindings, and
   byte-identical output.
4. **Every obligation is accounted for.** `rendered + justified_elision +
   refused = total obligations`, and `unaccounted = 0`. Separately, `refused` is
   an explicit failure and `defects = 0` for output the decompiler accepts.

The corpus is a canary against regression. It is not the specification, and no
gate below is satisfied by passing it. Section 6 says why.

---

## 2. Where we actually are

Measured at `ed7dfdc`.

| Crate            | Lines  | Largest file                      | Lines  |
|------------------|--------|-----------------------------------|--------|
| r2dec            | 91,675 | `fold/op_lower/mod.rs`            | 14,401 |
| r2sym            | 71,187 | `semantics/native_worker.rs`      | 12,667 |
| r2ssa            | 55,778 | `function.rs`                     |  9,903 |
| r2types          | 54,095 | `writeback.rs`                    | 22,006 |
| r2engine         | 12,057 | `lib.rs`                          | 10,737 |
| r2source         |  9,812 | —                                 |        |
| r2sleigh-lift    |  8,166 | —                                 |        |
| r2il             |  4,621 | —                                 |        |
| **total Rust**   | **325,539** |                              |        |

Other signals: 46 `allow(dead_code)`, 14 TODO/FIXME/HACK, 684 call sites of
`display_name()`, 225 sites touching the alias tables, 950 `cargo fmt` hunks,
184 clippy diagnostics, 57 build warnings.

Corpus 4 → 38 of 54 on this branch. Per configuration: x64 -O0 7, x64 -O1 7,
x64 -O2 4, arm64 -O0 7, arm64 -O1 7, arm64 -O2 6.

---

## 3. The one defect

> **A value has many tables that can answer for it, and they are allowed to
> disagree.**

The exhibit is `UseInfo` in `crates/r2dec/src/analysis/mod.rs`, at **36 fields**.
Several are one fact keyed differently: `value_ids_by_var`, `value_ids_by_name`
and `vars_by_value_id` are one relation in three directions, each writable
independently; `ambiguous_value_vars` / `ambiguous_value_ids` /
`ambiguous_value_names` are one set under three key types; `definitions_by_value`
is value-keyed where `formatted_defs` is string-keyed.

The tree already admits it. The struct's last field is a shipped counter of the
drift, whose comment says the drift is structural rather than a discipline
failure at the call sites:

```rust
/// Writes that reached the string-keyed half and not the value-keyed one.
/// ...
/// Those entries are exactly what the location model has to account for
/// before the string-keyed half can be derived rather than stored ...
pub(crate) unkeyed_writes: BTreeMap<&'static str, usize>,
```

### What the shape cost, observed

- **Six inert fixes in a row.** Each edited a rule governing the *name* when the
  rule on the path governed the *value*, or the reverse. Located only by planting
  `CExpr::External { name: "ZZMARKERZZ" }` and grepping `pdd`.
- **Three measured regressions from single-table edits.** Span-gate widening
  37 → 19; a guard on the `Block` arm of `structure_region` 37 → 17; excluding
  self-zeroing writes in parameter recovery 37 → 36. Each was correct alone;
  another table still answered, and the answers differed.
- **A rendering non-determinism** from `close_carrier_aliases_over_edge_copies`
  making one unordered, non-fixpoint pass over edges.
- **A naming ladder** — `carrier_alias` → `var_alias` → `param_alias` → base —
  over 225 sites, where which rung answers depends on insertion order in tables
  written by different passes.

The project's standing rule — trace a defect to its source, fix it there, never
at the symptom site — is *unimplementable* under this shape, because "the source"
is not a place. That is the thing to fix.

---

## 4. The model

Five identities. **Four already exist in the tree.** Only `BindingId` is new.

```
CanonicalLocation   the machine place       r2source/src/contracts.rs:30
SpanId              one uninterrupted run   r2ssa/src/span.rs:24
ValueId             one SSA version         r2ssa/src/graph.rs:17
UseSite             one consumption         r2ssa/src/graph.rs:20
BindingId           one rendered C object   (new)
```

### This is not a hierarchy

Revision 1 arranged these as a strict containment chain with
`Binding -> Option<CanonicalLocation>`. That is wrong, and the tree says why in
two places. `r2ssa/src/span.rs` opens:

> A register is not a variable. A compiler will keep an accumulator in `RAX` for
> one loop and an index in it for the next, and every layer that reasons about
> "the value in `RAX`" then has to decide which of those it means.

and `normalize.rs:1057`:

> an entry value, a phi, a latch update and a post-loop merge are four SSA values
> and one C local.

So the relation runs both ways. One `CanonicalLocation` holds several unrelated
program variables over time; one recovered variable moves register → stack →
register. `Binding -> Option<CanonicalLocation>` is only valid in the restricted
single-location case, which is not the general one.

The correct shape:

```
CanonicalLocation ──has temporal contents──▶ SpanId
SpanId              ──contains──────────────▶ ValueId
ValueId              ──is consumed at────────▶ UseSite

BindingId ──coalesces a certified set of──▶ ValueId / SpanId
```

`BindingId` is a **renderer projection across the SSA graph**, not a child of a
machine location. It references an upstream coalescing or carrier certificate; it
never stores a second origin claim of its own. That distinction is the whole
correction: revision 1's `Origin { Carrier { id, width }, StackSlot(off), ... }`
rebuilt `CanonicalLocation` inside the renderer, which is the same defect this
plan exists to remove, committed by the plan itself.

The certificate inside a sealed `Binding` is opaque outside the binding-plan
module. A `SpanId` or `SemanticId` is only the identity of a candidate upstream
fact, not proof by itself. Sealing must resolve that identity against the exact
`SourceOwnedFunctionFacts` authority and prove that the values whose dispositions
name the binding are exactly the certified member set. `Singleton` likewise means
exactly one bound value after that check; it is not a freely constructible claim.

### Disposition, not a nullable name

Revision 1 held `name: Option<SymbolId>` beside an independent `Site`, which
permits invalid combinations and detects them with a debug assertion. Encode the
legal states instead, so the invalid ones cannot be written:

```rust
enum ValueDisposition {
    Bound   { binding: BindingId },
    Inline  { expr: MachineExprId, proof: InlineProof },
    Elided  { reason: ElisionReason, proof: DeadValueProof },
    Refused { reason: RefusalReason },
}
```

Validation returns a typed refusal in release builds. A malformed artifact must
not silently render, and must not panic during `pdd`.

### Width belongs to the use

One value is read at several widths. A single declaration type cannot describe
that, and cannot express `AH`, SIMD lanes, extraction offsets, partial writes, or
target-specific zero-extension. `CanonicalLocation` exists precisely because
`CanonicalStorageId` conflates the place with the slice:

> A `CanonicalStorageId` records a slice: `EAX` and `RAX` differ in it because
> they differ in size, which makes two writes to one register look like writes to
> two places. A location is the register, and the slice is what a particular
> access took of it.

So the canonical upstream contract is:

```rust
struct Binding { declaration_type: CType, /* ... */ }

/// What one reader takes of the binding. Keyed by `UseSite`.
enum MachineUseDisposition {
    Exact(MachineUseSlice),
    Refused(MachineUseRefusal),
}

/// What one definition puts back. Keyed by definition site.
enum MachineWriteDisposition {
    Exact(MachineWriteProjection),
    Refused(MachineWriteRefusal),
}
```

`ZeroExtend` is where `narrow_write_clears_register` moves: it stops being a
predicate consulted at render time and becomes a fact recorded at the definition.
`BindingPlan` owns one validated `MachineProjection` and delegates both lookups
to it. Copying slice or write geometry into renderer-owned tables, even with an
opaque proof beside each copy, would create the second answerer this rewrite is
removing.

### Placement is derived, never stored

Declaration placement is a pure lowering phase immediately before AST emission:

```
sealed structured-region artifact
  + binding definitions
  + surviving planned uses
  → declaration location | PlacementRefusal
```

No parallel authoritative placement table. The emitted AST contains the resulting
declaration, and that is the only record. Storing a placement plus a proof of the
placement would recreate exactly the two-answerers defect: the stored placement
and the region tree it came from can drift.

Three things the calculation must keep separate:

1. **Declaration scope** — where the C object is introduced.
2. **Initialization and assignment sites** — where values are written into it.
3. **Reaching-definition validity** — whether every surviving read is preceded by
   an assignment on every path.

These are not the same question, and conflating them is a way to be wrong
quietly: **hoisting a declaration can make C compile without fixing a read that is
semantically uninitialized.** A value assigned in both arms of an `if` and read
after the merge needs one declaration before the `if`, an assignment in each arm,
and the read after — hoisting alone produces the same text whether or not the
second arm actually assigns. Reaching-definition validity is what separates them,
and a failure of it is a `PlacementRefusal`, not a hoist.

The calculation uses **surviving planned uses**, not every original SSA use.
Inlined, elided and refused values have no uses to dominate.

### The obligation ledger

Value disposition and effect disposition are separate ledgers. "Zero readers"
justifies removing a *pure* computation only; a call, a store, a volatile load or
a `callother` must survive with no readers at all. This is not a refinement — it
is on the critical path, because `callother` is one of the open corpus failures.

Accounting is two equations, kept apart from quality:

```
rendered + justified_elision + refused = total obligations
unaccounted = 0
```

and then, separately:

```
refused  = explicit failure, never success
defects  = 0 for output the decompiler accepts as native
```

The split is what stops both games. "Declare everything" cannot satisfy the first
equation without also raising `defects`. "Refuse everything" satisfies the first
equation and fails outright on the second. The tree already prints this shape:
`632 rendered, 38 elided, 0 refused, 11 unaccounted, 96 defects`.

### Determinism

The rule is not a container choice:

> Every closure computes a unique least fixpoint using a monotone transfer over a
> stable domain; scheduling uses a sorted worklist.

`ValueId` allocation is already dense and stable for one exact prepared
artifact: `graph.rs` interns `ValueId(values.len())` while walking canonical
reverse-postorder blocks, then phi and op operands in their stored order. The
`BTreeMap` is only the reverse interning index; it does not choose allocation
order. Indexed vectors therefore give deterministic O(1) lookup and iteration
without claiming that IDs survive a changed traversal.
But the actual determinism bug on this branch was not map order; it was a single
non-fixpoint pass. Dense storage does not address that class.

Where the relation is genuinely an equivalence, union-find with a **canonical
minimum representative** is simpler and nearly linear. `StorageSpans` is already
union-find (`span.rs:33`) — but its representative is *not* canonical. `union`
merges by rank (`span.rs:99`) and `span_of` returns whichever node became root,
so the **partition** is stable while the **`SpanId` value** depends on union
order. Anything keying naming or ordering off a `SpanId` inherits that. Taking
the class minimum as the representative closes it.

Every closure gets a property test that shuffles input edge order and requires
the same partition, the same bindings, and byte-identical rendered output.

---

## 5. Honest scope

**Addressed:** `UseInfo` (36 fields); `PreparedSemanticView` (24), partially; the
naming ladder and its 225 sites; undeclared identifiers (property 1); wrong-width
rendering (property 2); rendering determinism (property 3); the elision-versus-
effect confusion (property 4).

**Not addressed, needing separate work:** `CompiledSemanticInfo` (38 fields,
r2sym), `RadareAbi138Accessors` (34, r2source), `ExploreStats` (31),
`EngineTypeWritebackJsonCore` (28), `VmStepSummary` (27). The 13-parameter
functions — `make_ctx`, `insert_structured_memory_access`,
`insert_raw_memory_subeffect`, `from_captured_parts` — which need parameter
objects and splitting. Deep nesting: 440 of 9,844 functions at ≥6 levels, max 12.
`writeback.rs` at 22,006 lines and `native_worker.rs` at 12,667: neither is on the
naming, projection or placement path, and both are deferred.

Thirteen structs sit at ≥20 fields; this plan addresses 2, which are the 2 that
produce rendering defects. No Rust or C function in the repo reaches 20
parameters — the maximum is 13 in Rust and 8 in C.

**Not addressed and not fixed by this rewrite:** `callother` lowering,
sibling-function linking (`sym__rotl32`), and struct typing. They appear in the
open-defect table and must not be counted on any binding-rewrite gate.

---

## 6. Why the corpus is not the specification

`tests/corpus/verify_rendering.py` rewrites the C it verifies:

- one fixed input (`msg`, a single 61-byte string);
- every parameter and every local declaration rewritten to `long`
  (lines 65, 66, 68);
- a width invented for every dereference the rendering left untyped
  (lines 76, 87), counted as `assumed` but not fatal;
- subscripts rewritten to `(((unsigned char *)(long)(X))[Y])`;
- compiled with `clang -w` (line 168), suppressing all warnings.

The consequence is sharper than leniency. **The harness deletes declared types
before compiling**, so it is structurally incapable of observing a value rendered
at the wrong width — which is property 2, the thing most of this work exists to
establish. A transformed success is not proof of emitted-C correctness. Logging
the rewrites is useful; it does not convert a transformed pass into a proof.

Three separate scores replace the single number:

| Score | What it is | What it proves |
|---|---|---|
| **Raw** | Emitted C compiles with only an external prelude and data mapping — declarations untouched, explicit strict dialect, warnings as errors | Syntax and declared typing |
| **Diagnostic** | The transformed C compiles and runs | The rendering computes something, on one input |
| **Differential** | Behaviour matches the original across empty, boundary-length and randomised inputs and seeds | Semantics, on a distribution |

Warnings-as-errors is necessary and still not sufficient: an explicitly wrong
cast compiles silently. So property 2 has two gates, not one — the compiler is
the **external tripwire**, and the internal invariant that every `UseSite` carries
an exact, upstream-backed projection is the **proof**.

---

## 7. The plan

Eight stages. Each exits on a stated measurement. Corpus numbers are reported at
every gate, up, down or flat — as a signal, never as the gate.

### Stage 0 — Make the raw and differential harness trustworthy

Emit each rendering verbatim to `raw/<config>_<fn>.c` beside the transformed
copy. Add the strict-dialect raw compile and the differential runner. Print, per
file, which rewrites the transformer applied and how many widths it assumed.

**Gate:** all three scores reported per entry. Raw and differential scores exist
for all 54 whether or not they pass. Every transformer rewrite is listed.

### Stage 1 — Define the model, consume nothing

Land `ValueDisposition`, `BindingId`, `Binding`, the initial projection views,
the effect-disposition enum, and the refusal types. No construction, no
consumption. Define the module APIs of `op_lower` and `use_info` in the same
stage, because stage 3 splits behind them. Stage 4 deletes the initial
renderer-owned projection copies after the upstream `MachineProjection` proves
it already owns the exact/refused dense tables; keeping both would violate the
model rather than complete it.

`analysis::use_info::UseAnalysisInput` owns the exact source-analysis seam.
`fold::op_lower::PlannedLoweringInput::try_new` owns the source/plan seam and
rejects an authority mismatch or a `MachineProjection` that does not validate
against that exact source. Neither API is called by the render path in this
stage, and there is still no production `BindingPlan` constructor.

**Gate:** types compile and are unreferenced by the render path. Corpus
byte-identical on all 54 raw outputs.

### Stage 2 — Extend the canonical upstream facts

In `r2il`, `r2sleigh-lift`, and `r2ssa`: give `StorageSpans` a canonical minimum
representative; fold `span::same_run` into `CanonicalStorageId::location()`,
which it duplicates; seal architecture register geometry at the lift boundary;
expose per-`UseSite` slice facts so `UseProjection` is read from upstream rather
than inferred downstream; and record `ZeroExtend` at definitions instead of
consulting `narrow_write_clears_register` at render time. Existing downstream
answers remain temporarily untouched because this is still a non-consuming
stage; they are deleted atomically at the relevant cutover.

**Gate:** every fact `UseProjection` needs is answerable from `r2ssa`/`r2types`
without a renderer table. Shuffle property test passes on the span partition.
Corpus byte-identical on all 54.

### Stage 3 — Split the lowering topology behind the defined APIs

Split `op_lower/mod.rs` (14,401) and `use_info.rs` (12,311) behind the stage-1
facades — moving code, not editing it. This is deliberately a topology-only
split. `UseAnalysisInput` and `PlannedLoweringInput` have the correct authority
shape, but they are not yet mandatory runtime seams: production use analysis
operates on normalized/materialized blocks with additional environment, control,
and prepared-fact inputs, while production lowering enters through `FoldInputs`
and `FoldingContext`. Pretending a mechanical move had sealed those paths would
create a paper invariant. Stage 4 must carry the exact source and plan authority
through those real inputs when it constructs the shadow plan.

`writeback.rs` and `native_worker.rs` are deferred: neither is on an ownership
seam this rewrite touches.

**Gate:** **all 54 raw outputs byte-identical**, not "38 still pass". Tests
retain the exact pre-split behavior. The focused `r2dec` result remains 623
passing with the same three pre-existing failures; the split neither fixes nor
hides them. A single differing raw-output byte means the split was not
mechanical.

### Stage 4 — Shadow construction and divergence classification

Build the value-disposition and binding tables from the existing analysis
without consuming them. Retain one validated upstream `MachineProjection` and
delegate its dense use/write lookups rather than copying their facts. The checked
seal proves exact source authority, machine-projection validity, dense domain
completeness, certificate membership, and one disposition per SSA value before
producing a `BindingPlan`. At the analysis/render boundary, classify each
divergence from the old tables **against canonical upstream evidence** — which of the two is
right, and which upstream fact says so.

The divergence list is *evidence*, not the specification. A divergence where both
sides disagree with upstream is a third finding, not a tie.

Observable-effect outcomes are deliberately not stored in this pre-render plan.
Whether an effect rendered is knowable only after folding and final AST/ledger
reconciliation; copying that answer backward into a future lowering input would
be temporal circularity. Stage 4 records only the honest legacy observations
available today: graph literals are inline, while nonconstant values, uses, and
writes are `LegacyAbsent`. The old renderer has neither an authority-sealed
value-decision journal nor stable original use/write identities after
normalization. Inventing those answers from names would make the shadow result
look complete by repeating the defect it is meant to expose. The decision
journal lands after normalized origins in stage 5; the canonical effect ledger
cuts over in stage 7.

The shadow oracle is constructed independently from the candidate plan: it
reseals the exact source artifact, builds a fresh machine projection, and derives
certificate components with its own traversal. The report then re-derives and
validates every stored observation and count. Its public audit ledger exposes
the three domain equations and refusal total rather than caching a pass bit.
Construction occurs only after code generation and the historical final work
poll, so it cannot change rendered C or cancellation/deadline decisions.

**Gate:** independently enumerate every canonical `ValueId`, every graph-input
`UseSite`, and every output-producing `InstId`; the observed and classified
counts must equal those three domain counts. Every non-agreement is classified
as old-wrong, shadow-wrong, or both-wrong with a typed upstream evidence key,
including equal-but-both-wrong cases. The gate requires
`shadow_wrong = both_wrong = unclassified = 0` and `refused = 0`. A typed
canonical refusal remains visible in the ledger, but it is a non-quality result,
never a pass. The seal must be valid, and a non-empty source must produce a
non-empty domain. Corpus raw output remains byte-identical on all 54 — nothing
consumes the plan yet, so any change means something does; find it.

### Stage 5 — Cut over naming, delete the naming tables

`ValueDisposition::Bound` becomes the only source of an identifier. Delete
`carrier_alias`, `var_alias`, `param_alias` and the ladder ordering them, in the
same change as the cutover — not a stage later.

The cutover first replaces `MaterializedEdgeCopies` with a sealed normalization
artifact whose block-aligned origin rows move with every inserted or removed op.
An inserted phi-edge copy names its original phi definition and incoming
`UseSite`; a guarded edge also records the original guard use and identifies its
synthetic preserve operand as synthetic; a relocated certified initializer
records the complete sorted set of phi uses it replaces. These are transformation
origins, not new semantic identities. The current tuple `HashSet<(block, dst,
src)>` loses those facts and can collapse distinct occurrences, so it cannot
authorize the cutover. Where the upstream loop-carrier edge contract does not
retain the exact phi-input `UseSite`, extend that contract in `r2ssa`; `r2dec`
must not recover it from a predecessor/value pair.

Once those origins are sealed, add an authority-bound legacy observation journal
at the points where the old renderer actually binds, inlines, elides, or refuses
each value/use/write obligation. Initialize the full dense V/U/W domain, accept
only idempotent duplicate decisions, reject conflicts, and seal after final AST
materialization. Binding equivalence comes from complete sorted `ValueId` member
sets, never from emitted names or symbol-allocation order. This journal is the
last comparison oracle for the naming cutover; it is not a second renderer
contract.

Expect a regression. A measured regression here is how far the rewrite still has
to go, not grounds for reverting it.

**Gate:** ledger balances — `rendered + justified_elision + refused = total`,
`unaccounted = 0` — on all 54. `refused` reported as failure. Corpus reported
honestly, whatever it is.

### Stage 6 — Cut over per-use projection, delete the width aliases

Every `UseSite` renders through its canonical `MachineUseDisposition`. Delete
the width and member-view aliases in the same change.

**Gate:** raw score compiles under strict dialect with warnings as errors, on
every entry that renders. Every `UseSite` has an upstream-backed projection —
zero inferred. Both gates, not either.

### Stage 7 — Cut over placement, inlining, elision, and the effect ledger

Placement becomes the pure lowering phase over a sealed structured-region
artifact. Because the current structurer discards `Region`, retaining and
sealing that artifact is the first part of this stage, not a renderer-side
placement cache.
`InlineProof` and `DeadValueProof` become required. The effect ledger lands
separately from the value ledger.

**Gate:** every surviving read is dominated by its declaration and preceded by an
assignment on every path, or the binding is a `PlacementRefusal`. No effectful
obligation elided for want of readers. Differential score reported across all
input classes.

---

## 8. Fastest path

- **Stage 0 first.** Every later stage is measured through the harness, and the
  current one cannot see property 2 at all. Two turns were lost once to a cast the
  harness itself inserted; one regex slip (`__?u?int` for `(?:__)?u?int`) moved
  the corpus 37 → 18 with no decompiler change.
- **Stage 1 before stage 3.** Splitting along an API that does not exist yet is
  how you split along the wrong seam. Define, then split.
- **Stage 2 before stage 4.** Divergences are classified against upstream
  evidence, so the evidence has to be answerable first, or the classification
  degrades into preferring whichever table is newer.
- **Delete at cutover, never later.** A stage that leaves the old table in place
  leaves two answerers, which is the defect.
- **Do not chase the open corpus failures before stage 5.** The name and width
  families dissolve in stages 5 and 6. Fixing them individually first means
  fixing them twice — and three of the six inert fixes were exactly that.
- **Deferred and unblocking:** `writeback.rs`, `native_worker.rs`, the
  13-parameter functions, deep nesting, clippy, fmt. Any time. Not instead of a
  stage.

---

## 9. Rules of engagement

1. **Trace before the guard.** A value has several tables that can answer for it.
   Suppressing one is indistinguishable from a wrong fix while another answers.
2. **A change that alters no rendered output does not stay in the tree.** It
   proves nothing. This does *not* apply to a change that restructures a blocking
   seam and costs corpus results on the way; that is progress with a price.
3. **Never trust a corpus number without confirming the install.** `make -C
   r2plugin install` must print `Installed to ...`. A failed install silently
   leaves the old plugin and reads exactly like a regression.
4. **Check `df` at the first `codesign` failure.** Roughly 40 codesign errors and
   two false readings had one cause: a full disk from a 69 GB `target/debug` in a
   release-only workflow.
5. **When a number moves and it should not have, stop.** The regex slip was caught
   only because 37 → 18 was impossible for the change made.
6. **The 2340 tests caught none of this branch's defects.** They are a regression
   net. The invariants in section 4 and the ledger in section 4 are what tests can
   actually assert.
7. **A refusal is a failure, not a pass.** Satisfying a checker by declining to
   answer is the same shape as the reverted pass that satisfied the undefined-name
   detector by declaring the undefined names.

---

## 10. Open defects at the stage-0 baseline

The harness now accounts for every cell. Failure status and causal diagnosis
remain separate: a cell is never omitted merely because its root cause has not
yet been classified.

| Configuration | Generation | Raw | Diagnostic | Differential |
|---|---:|---:|---:|---:|
| x64 O0 | 9 present | 9 signature mismatch | 9 signature mismatch | 9 blocked |
| x64 O1 | 9 present | 9 signature mismatch | 9 signature mismatch | 9 blocked |
| x64 O2 | 8 present, 1 renderer error | 8 signature mismatch, 1 blocked | 8 signature mismatch, 1 blocked | 9 blocked |
| arm64 O0 | 9 present | 9 compile failure | 7 pass, 2 failure | 7 diagnostic-backed pass, 2 blocked |
| arm64 O1 | 9 present | 8 compile failure, 1 signature mismatch | 7 pass, 1 failure, 1 signature mismatch | 7 diagnostic-backed pass, 2 blocked |
| arm64 O2 | 9 present | 9 compile failure | 6 pass, 3 failure | 6 diagnostic-backed pass, 3 blocked |

Known causal examples remain useful for routing, not accounting:

| Cause | Cleared by |
|---|---|
| x64 parameter/signature over-recovery | Stage 5 and upstream type projection |
| murmur3 merge values read before declaration | Stages 5 and 7 |
| crc32_bitwise undeclared register piece/alias values | Stage 5 |
| fnv1a64 narrow/wide piece composition | Stage 6 |
| xxhash32 unresolved rotate, `callother`, and struct typing | Separate upstream semantic/type work where the binding rewrite supplies no proof |

---

## 10b. Measured state at 21d961e

Seven fixes landed since the stage-0 baseline, each traced to its source before
any code was written. Three further changes were measured inert and reverted;
five hypotheses were disproven by trace before code.

| | baseline | now |
|---|---:|---:|
| workspace tests | 2236 pass / 2 fail | 2238 pass / 0 fail |
| generation present | 7 of 54 | 8 of 54 |
| raw / diagnostic / differential | 0 of 54 | 0 of 54 |
| placement audit refused | 33 | 5 |
| placement audit passed | 7 | 27 |
| binding audit failed | 41 | 27 |
| binding audit passed | 7 | 21 |
| raw errors that are not the signature check | 30 | 20 |

Refusal classes cleared outright: `region_does_not_dominate_occurrence` (18),
`read_before_assignment` (18), `ambiguous_observation_execution_order` (6),
`label followed by a declaration` (12 compiler errors), and the 41 cells whose
refusal named an authority that had not failed.

### What each fix was

- `33db0ba` The install guard used `rg`, which is absent from a plain shell, so
  every measurement aborted after a successful install. Separately, three sites
  collapsed typed journal failures into a machine-projection refusal, so 41 of 47
  cells were filed against the wrong authority.
- `9cc6cc5` Live-out matched the full `CanonicalStorageId` of a return slot, so a
  value composed by `xor eax, eax` and `sete al` was seen only as the zero, and
  `recover_interface` recovered no parameters at all.
- `0ebb565` A placement refusal was computed, held aside, and reported only after
  the seal it had caused, so the seal's symptom hid it.
- `11e3530` Normalization materializes a phi as one copy per incoming edge, and
  placement took each copy's block from the original phi rather than from the
  predecessor the copy lives in.
- `d19a77a` `BindingRole` had no name for a caller-supplied value outside the
  convention's argument slots, so placement demanded an assignment for a value
  the caller had already supplied.
- `d8eafa5` A stack assignment's target is an lvalue whose address reads are
  ordered against its own store; treating them as unsequenced operands marked
  six functions ambiguous.
- `21d961e` A label must be followed by a statement, so an inline declaration
  cannot be placed there.

### What the raw score asserts, and what it does not

The raw runner used to assert that the emitted function had exactly the source's
parameter and return types, which `mint_recovered_interface` documents it never
claims: a parameter is an unsigned integer of the register's own width, and
signedness, pointer-ness and names are erased by compilation. No decompiler
change could satisfy that, and all eight generating cells failed on it before
reaching a real defect.

Raw now calls the function through the signature the rendering itself declares,
converting the data pointer as an integer of the declared width. What it proves
is unchanged and still strict: the emitted C compiles under warnings-as-errors
with its declarations untouched, and runs.

The comparison was not discarded. Each entry carries a `typed_recovery` record
with the declared and expected types and whether they agree, reported and never
gating, so it remains a visible target of its own. All eight cells record
`parameters_match: false` today: every one renders
`uint64_t (int64_t, int64_t)` where the source is
`uint32_t (const uint8_t *, size_t)`.

### The remaining twenty errors, by owning file

| Error | Cells | Owner |
|---|---:|---|
| `implicit conversion changes signedness` | 6 | `type_from_size` call sites in `r2dec/fold/op_lower/implementation.rs` |
| unused variable / set-but-not-used | 13 | a value whose readers the fold deleted stays `Bound`; needs transitive dead-value analysis, `r2ssa/semantic.rs` and the fold |
| `unused label` | 1 | a label minted with no `goto` reaching it, `r2dec/structure.rs` |

Two further classes sit behind the same files. Eight `rendered_value_required`
cells are the AArch64 link register bound as a program object: no stack-frame
round trip is certified for it because `collect_callee_stack_allocation_certificates`
yields no allocations on AArch64, so the collector's body never runs. Nineteen
`non_quality` cells are effect-obligation refusals where a removed phi's
`LoopCarriedState` and `LiveValueProducer` obligations are refused
`BlockNotRendered`: the state is carried by the materialized edge copies, but no
`ElisionReason` names that, and letting each of N copies claim the obligation
would report a duplicate occurrence instead. That ownership question is the
stage-7 effect-ledger cutover.

### Attribution of the first five fixes

`33db0ba`, `9cc6cc5`, `0ebb565`, `11e3530` and `d19a77a` were staged with
`git add <file>` on files that already carried uncommitted work from a
concurrent session in this worktree, so each of those commits also contains
several hundred lines that session wrote. The work is intact on the branch and
the tree builds and tests green, but those commit messages describe only the
part authored under them. `0ebb565` and `11e3530` are the largest cases, at
roughly 500 and 430 lines respectively.

The history is deliberately left as it is rather than rewritten, because the
other session is still building on this branch and rewriting five commits
underneath it would be the worse outcome. Every commit from `d8eafa5` onward was
staged file by file with the staged diff checked before committing.

### A note on the machine-role coordinate system

`SourceMachineRoles` storages arrive from radare2's register profile
(`libr/anal/function.c`, `*offset = item->offset / 8`) while graph storages are
Sleigh varnode offsets: on AArch64 the captured return-address role reports
offset 0 where `x0` is 16384 and `x30` is 16624. Both are tagged
`CanonicalStorageSpace::Register`, so the type asserts they are comparable when
they are not. Nothing has broken because every existing comparison is
capture-against-capture. Any question of the form "is this graph value the
machine's return address" needs a translation that does not exist: the wire
carries `name_length` but no name, and radare2's public view struct has no name
field either.

---

## 11. The durable statement

> One canonical location per machine place, one certified span per uninterrupted
> content, one disposition per SSA value, one binding per rendered C object, and
> one projection per use.

Four of those five already exist upstream. The rewrite is mostly a matter of
letting the renderer read them instead of re-deriving them — and of deleting what
it used to re-derive them with, in the same change that stops using it.
