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

### The unused-variable class, and three attempts that failed

Thirteen of the raw errors are declarations no statement reads --
`uint32_t tmp_11f00_3 = stack_m28;` in djb2 is the shape. The values have
exactly one graph use, and the machine disposition of that use is `Exact`, so
the plan says it renders. What actually happens is that the load feeds a
condition code nothing reads: `ValueId(223)` is consumed only by an `IntCarry`
whose output is already `Elided { UnobservedValue }`.

Three attempts were measured and all three reverted.

**Marking the value elided in the plan.** A fixpoint over dispositions -- a
value every use of which feeds an elided value is elided -- fires correctly and
marks both loads. The emitted C is byte-identical. The reason is an ordering
bug in the attempt itself: `binding_components` recomputes eligibility from a
vector captured before the fixpoint and then assigns `Bound` over the result.
Anything that sets a disposition before components are built is overwritten.

**Making the fold consult the plan.** `lower_op` does see these operations in
statement mode with the right `ValueId`s, so a guard there is well placed. It
was inert only because the disposition it read had been overwritten as above.
Worth knowing regardless: the fold consults `ValueDisposition` at no call site
anywhere under `crates/r2dec/src/fold/`, so the plan can mark a value elided and
the renderer will still emit it, and the journal does not object.

**Closing eligibility over dead uses.** Widening the ineligibility set instead,
so components never form, regresses badly: generation falls from eight functions
to three seeded from raw ineligibility, and to four when seeded only from the
unobserved and structural-unused reasons. The premise is unsound. An unobserved
*output* does not mean its operands are unrendered -- a loop carrier's merge can
be unobserved while the update feeding it is genuinely rendered -- so "every use
feeds something unobserved" does not imply dead.

**Excluding the value from the binding domain at all.** Restricting the closure
to flag consumers -- a register-spaced output of a single byte, which a carrier
merge can never be -- is sound where the broader rules were not, and it does
remove the unused variables. It still regresses: generation falls from eight
functions to five, and djb2, sdbm and adler32 refuse with
`missing_program_variable_authorization`.

That refusal is the answer the four attempts were circling. The fold does not
skip a value it has no binding for; it *demands* one.
`analysis::lower::LowerCtx::bound_program_symbol` maps
`PlannedValueSymbol::Elided` onto `MissingProgramVariableAuthorization`, while
the `require_value` it calls documents the opposite in its own comment: "Inline
and elided values are successful answers: neither authorizes a C program
variable, but both are complete plan dispositions." One of the two is wrong, and
it is the caller.

So the order is fixed, and it is the reverse of what all four attempts assumed.
The fold has to gain a no-emit path first -- `bound_program_symbol` returning
"this value has no rendered occurrence" rather than a refusal, threaded out
through `var_name` and `assignment_lhs_expr` to the `LoweredOp::None` that
`lower_op` already has -- and only then can the plan stop binding the value.
Removing the binding first is what every one of these attempts did, and it is
why every one of them failed. `analysis/lower.rs` is not held by the concurrent
session.

**The fifth attempt narrows it once more.** Marking the flag-only values
`Elided { DeadFlagOnly }` -- a successful plan answer rather than the
placeholder refusal -- and adding the `lower_op` guard so their definitions are
never lowered still leaves djb2, sdbm and adler32 refusing
`missing_program_variable_authorization`. The demand does not come from lowering
the dead value's own definition at all. It comes from lowering the *flag
operation*, which is still emitted and resolves its operands, and operand
resolution runs in `LowerMode::Expr` where the statement-mode guard never fires.

So the no-emit path has to cover the consumer as well as the definition: an
operation whose output the plan elided must not be lowered in either mode, and
its operands must never be demanded. Five attempts have each removed one more
reason the value is still reached; this is the sixth and it is the one that
decides whether the approach works at all.

### Attempts six and seven, and what to do instead

Guarding both lowering modes leaves the plan build itself failing, and
`R2SLEIGH_DEBUG_UNOWNED` names it exactly:
`Seal(InvalidElisionProof { value: ValueId(223) })`. The sealing oracle
re-derives every elision reason independently and `DeadFlagOnly` had no arm.
Adding one lets the plan build and moves the refusal on to
`exact_use_requires_rendered_occurrence`. Eliding the uses and writes of
unrendered values in turn takes generation from eight functions to zero.

Three pieces are worth keeping when someone returns to this. Narrowing
eligibility to flag consumers -- a register-spaced output of a single byte,
which a loop carrier's merge can never be -- is sound and does remove the unused
variables. The `DeadFlagOnly` arm in the seal's proof validator is correct and
required. The `lower_op` guard is in the right place.

What is not understood is how many consumers still demand these values. Seven
attempts each found exactly one more, serially, at a build and corpus cycle
apiece, and the last showed the failure is not monotonic: three functions
regressing became nothing rendering in a single step. The next attempt should
enumerate rather than iterate -- instrument every producer of
`MissingProgramVariableAuthorization` and
`exact_use_requires_rendered_occurrence` at once and take the whole list in one
run before changing anything.

That enumeration has now been taken, and it settles the question.
`MissingProgramVariableAuthorization` has sixty-two producers across nine files
-- twenty-four in `analysis/lower.rs`, fourteen in `op_lower/implementation.rs`,
nine in `lib.rs`, four in `op_lower/lowering.rs`, three each in
`op_lower/calls.rs` and `analysis/prepared_semantic.rs`, two each in
`op_lower/memory_renderer.rs` and `structure.rs`, and one in `fold/stack.rs` --
and `ExactUseRequiresRenderedOccurrence` adds nine more.

Every one of them is a site that demands a program variable for a value. Making
a value non-bound turns each into a potential refusal, which is exactly why
seven serial attempts each discovered precisely one more consumer. There is no
short chain to walk to its end. Giving the renderer a no-emit path is a contract
change over roughly seventy demand sites, four of the nine files belong to a
concurrent session, and it is the stage-5 naming cutover in full rather than a
defect that can be fixed.

### The four smaller refusal classes, traced

Nineteen refusals sat in four classes that had never been looked at. They
resolve into two families and one unknown.

**Eight are the dead-value class again.** Six
`exact_write_requires_rendered_occurrence` and two
`exact_use_requires_rendered_occurrence` are a write or a use whose machine
disposition is `Exact` and for which no occurrence was rendered -- the same
disagreement between the plan and the renderer described above, seen from the
use and write ledgers instead of the value ledger. They are gated by the same
seventy-site cutover.

**Five are the narrow-write projection.**
`preserved_carrier_read_before_assignment` is
`PlacementRefusal::ReadBeforeAssignment` where the read is a
`PlacementRead::PreservedCarrierWrite`: the implied read of the bytes a partial
write preserves, occurring before the binding is ever assigned. On x86-64 a
32-bit register write clears the upper half, so there is no preserved read at
all and the projection should be `ZeroExtend` rather than `Insert`. That
decision lives in `r2ssa::machine::exact_zero_extend_write`, which the
concurrent session is extending -- `machine.rs` carries 176 uncommitted lines
including a second zero-extend path inserted directly after it.

**Two are unknown.** `missing_machine_projection_authorization` on
`crc32_bitwise` and `xxhash32` at AArch64 -O2 report a null cause and need a
probe.

So of the fifty-four cells, everything except those two is now traced to a named
cause, and every remaining fix lands either in the seventy-site cutover or in a
file the concurrent session holds.

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

## What is left, and exactly where it lives

Raw errors are down to two. Everything else was traced to a cause and fixed
there. What follows is the state after that, with the measurement behind each
claim.

### The scores

Generation 15, raw 14, diagnostic 12, differential 12, of 54.

Generation is deliberately below raw. It counts cells that produced a
rendering, and eleven of them were producing C that does not compile while
reporting it as rendered. The undeclared-name check now resolves a name
against the scope that has to declare it rather than against the function as a
whole, so those cells refuse instead. Raw, diagnostic and differential did not
move when that landed, because none of those functions was compiling anyway.

A cell that renders and a cell that compiles are now much closer to the same
thing, which is the direction that matters. Generation rises again when the
loop shape below is fixed.

### A do-while condition reads a name declared inside its own body

`structure.rs`'s `Region::DoWhileLoop` takes its condition expression from
`get_branch_condition_with_predicate(cond_block)` and separately flattens that
block's *statements* into the loop body. When the condition is a temporary the
block computes, the declaration lands inside the braces and the read lands in
the `while (...)`, which in C is not in that scope.

The fix belongs there: either the condition block's statements stay with the
condition, or the loop is emitted as `while (1) { body; if (!cond) break; }` so
the computation and its use share a scope. Repairing the scope downstream --
hoisting the declaration out after the fact -- would be compensating at the
symptom, and the AST node would still be one C cannot express.

This is not edited here because the concurrent session is rewriting that exact
call: its diff changes `observe_control_ownership(*cond_block, CStmt::DoWhile
{ ... })` into `observe_loop_control_ownership(loop_id, *cond_block,
CStmt::DoWhile { ... })`, which is the expression that would have to change.

Eleven generation cells.

### `xor r, r` reads the register it does not depend on

`crc32_bitwise` on x64 emits `EAX_0 = EAX_0 ^ EAX_0`. `EAX_0` is correctly an
`EntryValue` -- version zero with no defining instruction -- so it is declared
without an initializer, and reading it is what the machine does. A strict
compile rejects it.

The identity that removes it already exists: `simplify_op` folds `IntXor` with
`a == b` to zero. It does not run, because `DecompilePrepConfig` disables
`enable_inst_combine` on the decompile path.

Enabling it was measured: raw 14 to 16, and `adler32/arm64_O0` stops rendering,
taking differential 12 to 11. The refusal is `missing machine projection
authorization` from `certified_memory_access_expr` in
`fold/op_lower/memory_renderer.rs`, which requires `fact.address == address`.
The certified memory-access facts are keyed on the `ValueId`s the address
computation had *before* prep ran, so any prep pass that rewrites that
computation invalidates the certificate that authorizes it. The flag is not the
defect; the ordering is.

Fixing it means deriving those certificates after prep, or carrying them across
it -- which is `semantic.rs`, also the concurrent session's. Until then the
flag stays off, because trading a differential cell for two raw cells is the
wrong direction.

The two remaining raw errors.

## Architecture work: what was done and what it cost

All four architecture items are settled. Three needed a change, one turned
out not to exist, and two of the four were diagnosed wrongly first -- both
times by reasoning from the symptom instead of tracing the value.

### A1. A declaration the read cannot see

Diagnosed first as a structurer defect: `Region::DoWhileLoop` flattens its
condition block's statements into the body while the condition expression
stays outside, so a temporary the body declares is read out of scope. The
proposed fix was to reshape the loop into `while (1) { body; if (!cond) break; }`.

That was wrong. Tracing the binding rather than the symptom showed the
condition temporary is a plan binding carrying an `Inline` decision, and
inlining is what moves its declaration into the body. The loop shape never
had to change.

Whether an inline is expressible is a fact about the emitted tree, not about
the occurrence set the decisions were derived from, so the tree is asked:
apply, check that every name is declared in a scope that dominates its reads,
and demote any inline the check reports to the lexical declaration it now
carries as a fallback. A demotion only ever turns an inline into a
declaration, so it terminates.

Generation 15 to 26, raw 14 to 22, diagnostic and differential 12 to 20.

### A2. A constant is a boolean

Diagnosed first as certificates keyed on pre-prep value ids, invalidated by
any pass that renumbers. Also wrong: certificates are already collected after
prep, and every memory-access fact matched its site exactly when traced.

The real blocker was `value_has_boolean_producer`, which decides whether a
value may be interned as a boolean by walking back to a producing comparison.
Folding `0xfff1 == 0` replaces that comparison with a `Copy` of a constant,
and a constant has no defining instruction, so the walk concluded the value
had never been boolean and refused every use of the select reading it -- the
divide-by-zero guard Sleigh emits around a division. A constant zero or one
is a boolean; constant folding a comparison is exactly how a boolean becomes
one.

With that fixed, `enable_inst_combine` could be turned on for the decompile
path, which is what removes `EAX_0 = EAX_0 ^ EAX_0` -- an uninitialised read
of an entry value that no internal check refuses, and the deliberate hole in
property 1's second half.

Raw 22 to 27, raw errors 4 to 0. Every function that renders now compiles
under a strict dialect with warnings fatal.

### A3. Not needed

Structural control ownership was to be made visible at the seal so that a
`BranchInd` rendered as a switch could state the elision of its target
operand. Enabling `inst_combine` removed the two cells that motivated it.

The architectural gap is real -- nothing the journal holds records that the
structure took ownership of a transfer -- but there is no failing case, and
writing the mechanism ahead of a trace is the exact move this project's
history warns against. It is recorded here and left unbuilt.

### A4. Determinism, proved rather than asserted

Property 3 had one `shuffle` reference in the tree. It now has a property
test that renders one function from two orderings of its input blocks and
requires byte-identical output, with the entry block held first because the
first block is what defines the entry.

Nothing was found to fix. The corpus repeat comparison is the stronger
probe and it agrees: all fifty-four cells are byte-identical across two
separate runs. That is decisive rather than merely encouraging, because
Rust seeds each process's hash maps differently, so any hash iteration
order reaching the output would have diverged between the two processes.

### Where the properties stand

Property 1 is enforced, both halves: the dominating-scope check drives
placement's own inline decision, and the uninitialised entry read it could
not refuse is now never generated. Property 2 is tripwired by the raw gate,
which is at zero errors. Property 3 has a test and passes it. Property 4 was
already enforced, and is the check that caught every regression made against
this branch.

## Redesign: one stack coordinate system, and identity we prove ourselves

Nine cells refuse with `missing program-variable authorization`. The refusal is
retained in `fold/stack.rs` when `require_stack` fails, the reason is
`MissingSourceIdentity`, and the object it names is an ordinary local. What
follows is why that happens, and what to build instead.

### What is there now

Stack addresses are tracked as roots in two parallel maps.
`stack_address_roots` allows either base; `entry_stack_address_roots` allows
only the stack pointer. Every arm of the propagation fixpoint is written twice,
once per map, differing in a size gate and in one call -- about two hundred and
forty lines in which each operation is handled two ways.

The one call is `rebase_declared_frame_pointer`, which resets a declared frame
pointer's root to `(FramePointer, 0)`. After `push rbp; mov rbp, rsp` the frame
pointer genuinely *is* the entry stack pointer less eight, and this discards
that. From then on there are two coordinate systems for the same addresses with
no way to compare them, and `record_entry_stack_root` treats two spellings of
one slot as a contradiction: it deletes the root and marks the object
permanently ambiguous.

Separately, an object's size and identity are taken from radare2's declared
slot table, with a callee-allocation certificate as the only fallback. When
neither answers, `size` is `None`, the object has no identity, and every use of
it refuses the whole function.

### What the measurements say

Removing the rebase was tried and is measured neutral: generation, raw,
diagnostic and differential all stay at 29. It is not sufficient on its own, so
the coordinate split is the smaller half of the problem.

The larger half is that identity is outsourced. `murmur3_32` at -O0 has fourteen
stack objects and radare2 reports no stack variables at all for it -- `afvj`
returns only two register arguments. `fnv1a32`, which renders, gets its objects
from callee-allocation certificates instead, and those succeed there only
because it is a leaf function with no explicit frame allocation.

This is the same failure as the parameter that was dropped earlier today, where
radare2 counted a register the function writes without reading. An external
opinion is being used for something the analysis can prove.

### What to build

One coordinate system. Every stack address root is expressed relative to the
entry stack pointer. The frame pointer stops being a base and becomes an
ordinary value whose root is `(entry stack pointer, -k)`, learned from the copy
that establishes it. `StackAddressBase::FramePointer` survives only as the form
radare2's declared slots arrive in, converted into our coordinates at ingest.

One root map, and the duplicated arms collapse into it.

Identity derived from the object's own accesses. An object accessed at a
consistent width through a proven entry-relative address is a stack object of
that size, and that is a positive fact about the program. Radare2's slot table
becomes a naming and typing hint, never the source of identity, and
`MissingSourceIdentity` comes to mean that the analysis could not prove a
location rather than that radare2 was silent.

### Stages, each with a gate

The order below is not the obvious one, and the reason is worth stating because
the obvious order was tried first and is wrong.

Convert declared frame-pointer slots into entry-relative coordinates at ingest,
so that every internal root is stack-pointer-relative and a base is no longer
part of an object's identity. The gate is generation at or above twenty-nine.

Then derive the size from the accesses when no declared slot answers. The gate
is that no differential cell is lost.

Then collapse the two root maps and delete `rebase_declared_frame_pointer`. The
gate is that the rendering of the passing cells is byte-identical, which the
determinism property test is already able to check.

### Why the width cannot be derived first

Deriving the width first was implemented and reverted. It works -- the objects
of `murmur3_32` acquire widths of eight and four, the refusal moves from
`missing program-variable authorization` to a later machine-projection one, and
the object at entry offset zero correctly keeps no width because it is the
return address and no access agrees on a width for it.

It also breaks `memory_ssa_separates_saved_sp_slot_from_frame_relative_local`,
which exists to keep two objects apart: a saved stack-pointer slot at
`(StackPointer, -8)` and a frame-relative local at `(FramePointer, -8)`. Same
offset, different base, genuinely different places. Its assertion says that an
uncaptured stack resource must not borrow another coordinate's width, and
deriving from accesses does exactly that while two bases are still in play.

Requiring the object's coordinate to be captured is not enough to satisfy it,
because both of those objects have captured coordinates. The bases are what
distinguish them, so the width may only be derived once a base is no longer how
two objects are told apart -- which is the first stage, not this one.

The test is the design speaking. In a unified coordinate system those two
objects are distinguished by their true entry-relative offsets, the saved slot
at entry minus eight and the local at entry minus eight minus the frame size,
and no base is needed to separate them.

Everything stack-related depends on this, so the corpus will move before it
settles. That is expected, and it is why each stage has a gate rather than one
measurement at the end.

---

# Revision 3: finishing the rewrite

Revision 2 described the model and eight stages. Stages 0, 1, 3 and most of 7
landed, and the corpus became honest -- generation, raw, diagnostic and
differential all agree, with no raw errors and nothing rendered wrong. The
central defect of section 3 was reduced and not removed, and property 2's
internal half was never established.

This revision says what remains and when it is finished. It is written because
a partial rewrite is worse than no rewrite: the tree then carries both the old
shape and the new one, and every later change has to satisfy both.

## What done means

All four properties of section 1 proved by their stated method, the section 3
defect removed, and the corpus at parity across optimization levels: every one
of the fifty-four cells rendering, with generation, raw, diagnostic and
differential equal.

Parity at -O2 needs work revision 2 explicitly excluded -- `callother`
lowering, sibling-function linking, struct typing. Those are carried here as
their own track rather than folded into the rewrite, because they are separate
defects that happen to stand between us and the same number.

## Track A -- remove the many answerers

`UseInfo` is thirty-one fields. Several are one fact keyed several ways, each
independently writable: `value_ids_by_var` against `value_ids_by_name` against
`vars_by_value_id`; the ambiguity set under three key types;
`definitions_by_value` against `formatted_defs`; `stable_memory_values` against
`stable_memory_values_by_value`. `unkeyed_writes` counts the drift between two
of them and still ships.

**A1.** Classify every field: answerable upstream, derivable from another
field, or a genuinely stored fact with one writer. *Gate:* every field
classified, each naming the upstream fact or the field it derives from.

**A2.** Delete the string-keyed half and the drift counter it measures.
*Gate:* ledger balances on all fifty-four; corpus reported, never gating.

**A3.** Collapse each multi-directional relation to one stored direction with
derived accessors. *Gate:* no field is written by more than one pass.

**A4.** Delete the alias ladder -- `carrier_alias`, `var_alias`,
`param_alias` -- in the same change that stops reading it. *Gate:* one source
of an identifier, which is `ValueDisposition::Bound`.

## Track B -- make inference unrepresentable

Property 2 has two gates and only the external one holds. `cast_expr_if_needed`
infers an operand type from a hint and drops it when the hint is absent, which
is how the sign flag came to be compared as unsigned and `crc32_bitwise`
returned a CRC of nothing while compiling cleanly.

**B1.** A cast on the render path cannot be constructed without a projection
that only the upstream fact layer can make. The compiler then enumerates every
inferred site, exactly as it enumerated every unrecorded refusal. *Gate:* it
compiles, and the enumeration is the work list.

**B2.** Convert each site to carry its projection, or refuse where upstream
has no fact to carry. *Gate:* zero inferred casts on the render path; raw stays
at zero errors.

## Track C -- finish what was started

**C1.** Definitions classified `Insert` that are narrow writes clearing their
carrier should be `ZeroExtend`. This is revision 2's stage 2, left unfinished.
*Gate:* the five `preserved_carrier_read_before_assignment` cells resolve or
name a different cause.

**C2.** Collapse `stack_address_roots` and `entry_stack_address_roots` into one
map and delete `rebase_declared_frame_pointer`. *Gate:* rendering of passing
cells byte-identical, which the determinism test can check.

**C3.** Binding components stay derived twice, because the independence is a
cross-check rather than a copy. Each *rule* moves to one place both derivations
call, so they cannot drift on a rule while still checking each other's result.
*Gate:* no rule stated twice; the seal still rejects a plan whose components
disagree.

## Track D -- the corpus to parity

**D1.** Clear the remaining refusal classes, largest first, each traced to a
cause before any change.

**D2.** The named analysis gaps: call-result facts for an unresolved external
callee, `callother` lowering, sibling-function linking, struct typing.

*Gate:* fifty-four of fifty-four, with generation, raw, diagnostic and
differential equal, and O0, O1 and O2 at parity.

## Order, and why

A and B first. Revision 2's section 8 says not to chase corpus failures before
the naming and width families dissolve, because fixing them individually means
fixing them twice, and three of six inert fixes were exactly that. That
reasoning has not changed. C runs alongside, since each item is independent. D
last.

Expect the corpus to fall during A and B. It is a canary, and the ledger is the
instrument: `rendered + justified_elision + refused = total`, `unaccounted = 0`,
`defects = 0` on accepted output. A fall with the ledger balanced is the rewrite
working; a rise with it unbalanced is the rewrite being cheated.

## Revision 4 -- what the tracks found when they were run

Tracks A through D were written from a reading of the code. Running them
changed what several of them are about, and the corrections are worth more than
the original statements, so they are recorded here rather than edited in above.

### Track A: most of it was unread, and one part of it was refusing

A1's classification found six `UseInfo` fields with no reader at all, and the
whole name-keyed identity -- `value_ids_by_name`, `ambiguous_value_names`, and
a `value_id_for_name_or_bind` that minted `ValueId(9500 + len)` for any
spelling that had none -- reachable only from the lowering tests. That last
part was not merely unused but inert: a minted identity is written to the
name-keyed map while every lookup that matters goes through `value_ids_by_var`,
which the fixtures never seeded. Deleting the seeding entirely left every test
passing, which says the fixtures had been running against an empty `UseInfo`.

Two findings from A were not anticipated by it.

The first is that a deleted table can keep refusing. `merge_prepared_stack_slot`
lost its destination field and still reported a dropped fact whenever a slot had
no value identity, and that report is read at the lowering catch-all to refuse
the function. A refusal on behalf of a table that no longer exists is not
conservative, it is false, and nothing about the deletion made it visible. Any
further field deletion has to check for this shape: the writer that survives its
table and reports the loss.

The second is that `definitions_by_value` was not a field to be collapsed but
the output of a second renderer. `analysis/lower.rs` held a complete duplicate
lowering of every SSA operation into a C expression, with its own operand
resolution, its own cast rules and its own type-from-width helpers, and its
results went into that map. Nothing read them. Making the accessor return
`None` unconditionally left all fifty-four cells byte-identical, so the only
consumer of a definition the ladder produced was the ladder itself, resolving
its own operands. It is gone, 2042 lines, and with it `PassEnv`, five
`FoldArchConfig` fields, `FoldInputs::display_names` and `FoldInputs::strings`.

### Track B is smaller than five clusters, and points somewhere else

One of B's five clusters of inferred casts, the `TypeOracle` channel, was
reachable only from that ladder. `SourceEvidenceTypeOracle` was constructed on
every native render and handed to the fold, and the fold's only reader was the
duplicate lowering. Deleting the ladder retired the cluster.

B1's actual proposal -- make `cast_needed` refuse when it has no source type --
was traced and is not yet the right first move. Its blast radius is every
arithmetic and comparison operation whose destination has a certified type, and
a refusal there aborts the whole function, so it would convert a large number of
renders into refusals before any of them could be given a source to carry.

The trace turned up something more direct. Every binding is declared with
`Binding::declaration_type`, which is always `CType::machine_bits(width)` --
unsigned. The cast policy compares against `type_hint_for_var`, which reports
what upstream proved the value *means*: signed, a pointer, a typedef. These are
two answerers for one value's type, and only one of them is about the program
the compiler reads. A value declared `uint32_t` and believed `int32_t` gets no
cast at all, because target and source compare equal, and the emitted expression
is then unsigned. That is the shape of the sign-flag defect that made
`crc32_bitwise` return a CRC of nothing, and it is still representable.

Switching the cast source to the declared type is correct and measured
byte-identical on this corpus, which means the disagreement does not currently
bite here. Per the rule that a partial fix changing no rendered behaviour does
not stay in the tree, it is not committed on its own; it belongs in the same
change as the refusal that completes it.

### Track C1 was three defects, and none of them was the one named

C1 said definitions classified `Insert` that are narrow writes clearing their
carrier should be `ZeroExtend`. Tracing the five cells found instead:

**The lift already states the clear.** `mov eax, edx` lifts to `Copy` followed
by `IntZExt { dst: RAX, src: EAX }`; Ghidra's x86 specification carries a family
of sub-constructors for exactly this. `materialize_cleared_register_write`
synthesized a second `IntZExt` for the same carrier one op earlier -- twenty-
seven of them in one block of `crc32_bitwise`, none ever read -- and the machine
layer's certificate, which looked at ordinal+1, was reading that invention
rather than the lift. Removing the synthesizer required rewriting the
certificate from an adjacency test into the dataflow question it means: before
anything reads the carrier, does the block define it as a zero-extension of what
this write left in its slice.

**A phi is not a machine write.** `machine_write_disposition` runs on every
graph instruction with an output, phis included, and derives a carrier-relative
projection from geometry alone. For a merge of a sub-register that comes out as
`Insert`, which asserts the merge preserves the carrier's other bits. It neither
does nor could; where the carrier is live across the merge it has a phi of its
own, and that phi is what answers for it. Two of the five cells are phis.

**The phi fold order is a display-name sort.** Each phi kills the slots it
overlaps before seeding its own, so the last phi to mention a register owns
every width of it, and `block.phis` is ordered by display name. That order puts
`EDX` before `RDX` but `R8` before `R8D`, because the wide name is a prefix of
the narrow one only for the extended registers. A 32-bit loop carrier in `r8`
therefore erased its own 64-bit carrier root while identical code in `rdx` did
not, and only across a back edge, where no later program order re-establishes
the carrier. An answer that depends on a name sort cannot be right whichever way
it comes out.

### What the refusals were hiding

Fixing the phi defects takes the corpus from thirty-five to thirty-seven, and
makes `adler32` at O1 render *wrongly*: the machine saves a sum into `r8d`
before clobbering `r9`, and the rendering places both in one C object, so the
saved value is destroyed and the subtraction reads the quotient.

This is the sharpest thing the tracks have produced. The five
`preserved_carrier_read_before_assignment` refusals were not only false, they
were also load-bearing -- they were suppressing a binding-collapse defect
underneath, and removing them exposes it. It follows that clearing a refusal
class is not a safe operation to measure by cell count. Every cell a refusal
fix newly admits has to be checked against the differential oracle before the
fix lands, and a fix that admits a wrong render is not finished, however correct
its own reasoning is.

### Track D: where the seventeen remaining refusals actually come from

With the phi and span defects fixed the corpus is at thirty-seven of
fifty-four and the refusals sort into five classes. Traced:

**Seven cells: no call-site interface at all.** These refuse at the
`CallDefine` arm for want of a call-result source, and the chain runs back
through `process_call_result_flow_block`, which needs a complete call boundary,
to `collect_source_boundary_facts`, which only completes a boundary inside
`if let Some(interface) = machine_context.call_site_interface(call_site.id)`.
For the failing calls that returns `None`, so the boundary is never completed
and every use of a call's result in the function is refused.

The failing calls in `murmur3_32` are three `call sym._rotl32`, and `_rotl32`
is a local function in the same binary. radare2's own signature for it is
`void sym._rotl32 ()` -- no arguments, void return -- for a function that takes
two and returns one. So the answer is not to trust radare2 harder. It is that a
callee we have the code for should have its interface derived from our own
analysis, which is the "sibling-function linking" D2 already names.

**Two facts about this class are worth separating.** The first is that a call
emits one `CallDefine` per register it may have destroyed, and the renderer
treated every one as the call's result: at -O0 `murmur3_32` has nine clobbers
to one result at a single call. The second is that the result register and the
lane the callee's prototype is declared at are different values -- an `int`
returned in `rax` gives a `CallDefine` for `RAX` and one for `EAX` -- and the
boundary certifies the carrier while the program reads the lane. Both are
fixed and measured, and both are currently inert on rendering because the
interface is missing underneath them, so neither is in the tree. They belong in
the same change as whatever supplies the interface.

**Three cells: `preserved_carrier_read_before_assignment`, and these are the
real ones.** Two of the five were phis and are fixed. What is left is genuine
`Insert`: `xor cl, byte [rdi + rax]` in `pearson` at both O1 and O2, and
`movdqa xmm0, xmmword [...]` in `crc32_bitwise` at O2. A byte write into `rcx`
really does preserve the other seven bytes, so `Insert` is the honest
projection and the refusal is asking a fair question: the renderer emits the
preserved bits by reading the object it is assigning, and nothing has assigned
it yet.

**The rest:** two `observation journal`, three `effect obligations refused`,
two `read_before_assignment`. Not yet traced.

### Track C2 rests on a premise that does not hold

C2 said to collapse `stack_address_roots` and `entry_stack_address_roots` into
one map, on the reading that a value with two stack coordinates is the plan's
one defect in the stack model. Tried, and it is not.

The two maps do not answer the same question. `entry_stack_address_roots` says
where a value is relative to the stack pointer the function was entered with,
which is a machine-provable displacement. `stack_address_roots` says where a
value is relative to the base its own frame is addressed from, which for a
function that establishes its own frame is the same fact and for a function
that *receives* a frame pointer is not: a received frame pointer has no
provable relation to the entry stack pointer, and no derivation can supply one.

The measurement is unambiguous. Merging the two by adopting the stronger gates
is byte-identical on all fifty-four corpus cells -- every corpus function
addresses its frame from the stack pointer -- and it breaks
`exact_parameter_home_reuses_one_parameter_binding_identity`, whose fixture
addresses a parameter home from a *received* frame pointer and which then loses
its stack-slot certificate entirely. That is the corpus behaving exactly as the
canary it is: silent about a capability it does not exercise.

So `StackAddressBase` is not a second coordinate system smuggled into one
model. It is the honest statement that two different things can be known about
a stack position, and which one is available depends on the function. The
`base == StackPointer` filters scattered through `semantic.rs` are not leaks;
they are consumers saying they need the stronger fact.

What C2 correctly identified is now done: `rebase_declared_frame_pointer` was
reduced to an identity function by an earlier commit and left standing as a
comment carrier, along with the `declared_stack_bases` argument four call sites
threaded to it. That is deleted.
