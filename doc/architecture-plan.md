# Architecture plan: one binding per value

Status as of 2026-08-25, branch `arch/location-ssa`, HEAD `aa1c01f`.
Corpus 38 of 54. 2340 tests pass. Tree clean.

This document states what we are building, why the current shape blocks us, how
we get there, and in what order. It is written to be read without the session
that produced it.

---

## 1. The end goal

The decompiler should produce, for any function it accepts, a single C rendering
that is **correct by construction** rather than correct by inspection. Concretely,
"done" is four testable properties:

1. **Every emitted identifier is declared exactly once, before its first read.**
   Not checked by a detector after the fact — impossible to violate, because the
   thing that decides a value has a name is the same thing that emits its
   declaration.
2. **Every value is rendered at the width it is read at.** A 32-bit read of a
   64-bit register renders as a cast or a member view, never as the wrong value
   and never as an undeclared narrow twin.
3. **The rendering is deterministic.** Same input bytes, same output text, on
   every run and every platform. No iteration-order dependence anywhere on the
   path from SSA to text.
4. **The corpus is 54 of 54** — nine functions across six configurations
   (x86-64 and AArch64 at -O0, -O1, -O2), each compiled from the decompiler's own
   output and run to the value the original produces.

Property 4 is the measurement. Properties 1–3 are the reason it can be reached
and held rather than approached asymptotically.

Beyond that: the plugin should be fast enough that `pdd` on a large function is
not something the user waits on, and the codebase should be small enough that a
person can find the code that decides a given piece of output in one search.

---

## 2. Where we actually are

Measured, not estimated.

| Crate            | Lines  |
|------------------|--------|
| r2dec            | 91,675 |
| r2sym            | 71,187 |
| r2ssa            | 55,778 |
| r2types          | 54,095 |
| r2engine         | 12,057 |
| r2source         |  9,812 |
| r2sleigh-lift    |  8,166 |
| r2il             |  4,621 |
| **total Rust**   | **325,539** |

Largest files: `r2types/src/writeback.rs` (22,006 lines),
`r2dec/src/fold/op_lower/mod.rs` (14,401), `r2dec/src/fold/tests/pipeline.rs`
(13,167), `r2sym/src/semantics/native_worker.rs` (12,667),
`r2dec/src/analysis/use_info.rs` (12,311).

Other signals: 46 `allow(dead_code)`, 14 TODO/FIXME/HACK, 684 call sites of
`display_name()`, 225 sites touching the alias tables, 950 `cargo fmt` hunks,
184 clippy diagnostics, 57 build warnings.

The corpus went 4 → 38 of 54 on this branch. Per configuration at HEAD:
x64 -O0 7, x64 -O1 7, x64 -O2 4, arm64 -O0 7, arm64 -O1 7, arm64 -O2 6.

---

## 3. The one defect

Everything expensive on this branch traces to a single shape:

> **A value has many tables that can answer for it, and they are allowed to
> disagree.**

The exhibit is `UseInfo` in `crates/r2dec/src/analysis/mod.rs`. It has **36
fields**. Several of them are the same fact keyed differently:

- `value_ids_by_var`, `value_ids_by_name`, `vars_by_value_id` — one relation,
  three directions, each writable independently.
- `ambiguous_value_vars`, `ambiguous_value_ids`, `ambiguous_value_names` — one
  set, three key types.
- `definitions_by_value` (value-keyed) and `formatted_defs` (string-keyed).
- `semantic_values_by_value`, `stable_memory_values`,
  `stable_memory_values_by_value`.

The tree already admits this. The last field of the struct is:

```rust
/// Writes that reached the string-keyed half and not the value-keyed one.
///
/// Every paired store is written through one helper, so the two halves
/// cannot drift by a missed call site. They still drift when the value has
/// no canonical identity to key on: the helper writes the name and skips the
/// `ValueId`. Those entries are exactly what the location model has to
/// account for before the string-keyed half can be derived rather than
/// stored ...
pub(crate) unkeyed_writes: BTreeMap<&'static str, usize>,
```

That is a **counter of the drift**, shipped in production, with a comment saying
the drift is structural and cannot be fixed by discipline at the call sites.

### What this shape costs, in observed failures

**Six inert fixes in a row.** Each edited a rule that governed the name, when the
rule on the path governed the value — or the reverse. The defect was only located
by planting `CExpr::External { name: "ZZMARKERZZ" }` and grepping `pdd` output to
find which table actually answered.

**Three measured regressions from single-table edits.** Widening the span gate:
37 → 19. Guarding the Block arm of `structure_region`: 37 → 17. Excluding
self-zeroing writes in parameter recovery: 37 → 36. In each case the edit was
correct in isolation; another table still answered for the same value and the two
answers now differed.

**A rendering non-determinism** that survived because `close_carrier_aliases_over_edge_copies`
made a single unordered pass over edges. Same binary, different output. Fixed by
sorting and iterating to fixpoint — but the bug was only possible because the
alias closure is a table separate from the thing it aliases.

**A naming ladder** — `carrier_alias` → `var_alias` → `param_alias` → base name —
spread across 225 sites. Each rung is a table. Which rung answers depends on
insertion order in tables written by different passes.

The pinned rule for this project ("trace to the source, fix it there, no
compensating workaround at the symptom site") is *unimplementable* under this
shape, because "the source" is not a place. A value has four sources. That is the
thing to fix.

---

## 4. What we build

**One record per value. One place that decides.**

```rust
/// The single answer for one SSA value: whether it is named, what width it is
/// read at, where it is emitted, and what it came from.
struct Binding {
    value: ValueId,
    /// `None` means this value has no name and must be inlined at its use.
    name:  Option<SymbolId>,
    /// The width the value is *read* at, not the width its storage has.
    ty:    CType,
    site:  Site,
    origin: Origin,
}

enum Site {
    /// Emitted as a declaration at this position; the only place a name is bound.
    Emit { block: BlockId, index: usize },
    /// Substituted into each reader; has no declaration.
    Inline,
    /// Bound by the function signature.
    Parameter(usize),
    /// Deliberately not emitted; carries the reason so it can be explained.
    Elided(ElisionReason),
}

enum Origin {
    Carrier { id: CarrierId, width: u32 },
    StackSlot(i64),
    Param(usize),
    Temp,
    Global(u64),
}
```

Held in one table, `BindingTable: BTreeMap<ValueId, Binding>` — ordered, so
iteration is deterministic by construction rather than by remembering to sort.

### Invariants

These are checked, in debug builds, at the boundary between analysis and
rendering. A violation is a panic with the offending `ValueId`, not a silently
wrong rendering.

1. `binding.name.is_some()` **iff** `site` is `Emit` or `Parameter`.
   *(A name exists exactly when something declares it. This is property 1 of the
   end goal, as a data-structure invariant.)*
2. `site == Inline` **implies** an expression is reconstructible for the value.
3. `site == Elided(_)` **implies** the value has zero readers.
4. Two bindings never share a `SymbolId`.
5. A reader of a value at width *w* sees `binding.ty` of width *w*, or an
   explicit cast node — never a second binding for the same storage.

Invariant 5 is what dissolves the narrow-carrier-member family (`eax_5`,
`rcx_6`, `ecx_9`) that consumed most of this branch: a 32-bit read of a 64-bit
carrier stops being a second value that needs its own name and becomes a width
recorded on the one binding.

### Why this is the right cut

The renderer stops asking questions. Today `get_expr_inner` and its neighbours
ask, for each value: is it a carrier? does it have an alias? is it a member view?
is it single-use? is it a return register? — and each question is a table lookup
that can disagree with the last. Under the binding table there is one lookup and
the answer is total. The 684 `display_name()` sites collapse toward one accessor
on `Binding`.

---

## 5. Honest scope

**Fixed directly:**
- `UseInfo` (36 fields) — the multi-table state the binding table replaces.
- `PreparedSemanticView` (24 fields) — same reason, partially.
- The naming ladder and its 225 sites.
- The undeclared-identifier family (invariant 1).
- The width family (invariant 5).
- Rendering determinism (ordered table).

**Not fixed by this, and needing separate work:**
- `CompiledSemanticInfo` (38 fields, r2sym), `RadareAbi138Accessors` (34,
  r2source), `ExploreStats` (31), `VmStepSummary` (27),
  `EngineTypeWritebackJsonCore` (28). These are report, accessor and statistics
  structs in crates the binding table does not reach. 13 structs sit at ≥20
  fields; this plan addresses 2 of them, but they are the 2 that produce
  rendering defects.
- The 13-parameter functions (`make_ctx` in `r2dec/src/analysis/lower.rs`,
  `insert_structured_memory_access` and `insert_raw_memory_subeffect` in
  `r2ssa/src/semantic.rs`, `from_captured_parts` in `r2source`). These need
  parameter objects and function splitting, which is mechanical and independent.
  No Rust or C function in the repo reaches 20 parameters; the maximum is 13 in
  Rust and 8 in C.
- Deep nesting: 440 of 9,844 functions nest ≥6 levels, maximum 12. Mostly in the
  same god files; splitting them addresses most of it.
- `writeback.rs` at 22,006 lines. Splitting is required but is not architecture.

---

## 6. The plan

Six stages. Each has an exit gate that is a measurement, not a judgement. The
corpus number is reported at every gate whether it moved up, down, or not at all.

### Stage 0 — Make the harness honest *(prerequisite, small)*

`tests/corpus/verify_rendering.py` rewrites the C it verifies — it patches
subscripts to `(((unsigned char *)(long)(X))[Y])` and stashes casts behind a
regex. Two full turns were lost this session hunting a cast that the *harness*
had inserted, and one regex slip (`__?u?int` for `(?:__)?u?int`) moved the corpus
37 → 18 with no decompiler change at all.

Do: emit the decompiler's output verbatim to `raw/<config>_<fn>.c` alongside the
patched copy, and have the verifier print which rewrites it applied to each file.

**Gate:** every failing function's raw output is readable without running `pdd`
by hand, and the rewrite list is printed.

### Stage 1 — Mechanical splitting *(no behaviour change)*

Split the four god files along seams that already exist, moving code without
editing it. `writeback.rs` (22,006), `op_lower/mod.rs` (14,401),
`use_info.rs` (12,311), `native_worker.rs` (12,667).

This is deliberately **before** the rewrite, not after. Stage 3 has to touch
hundreds of call sites; doing that inside 22,000-line files is where the six
inert fixes came from. This stage is safe, parallelisable, and makes every later
stage cheaper.

**Gate:** no file over 3,000 lines in `r2dec` and `r2types`; corpus unchanged at
38; tests unchanged at 2340. A corpus move here means the split was not
mechanical — revert and redo it.

### Stage 2 — Build the table alongside, believe nothing

Construct the `BindingTable` from the existing analysis. Do not consume it. At
the analysis/render boundary, compare each binding against what the existing
tables say and log divergences under `R2SLEIGH_DEBUG_BINDINGS`.

**Gate:** divergence count printed per function across all 54 corpus entries.
Corpus unchanged at 38 (nothing consumes the table yet — a move means something
does, find it). The divergence list *is* the specification for stage 3: every
divergence is a place the old tables disagree with each other.

### Stage 3 — Consume for names, delete the ladder

Make `Binding::name` the only source of an identifier. Delete `carrier_alias`,
`var_alias`, `param_alias` and the ladder that orders them. Turn invariant 1 on.

This is the stage that regresses. That is expected and acceptable: a measured
regression here is information about how far the rewrite still has to go, not
grounds for reverting it. Report the number plainly and keep going.

**Gate:** invariant 1 holds on all 54 entries — zero undeclared identifiers, by
construction rather than by detector. Corpus is reported honestly whatever it is.

### Stage 4 — Consume for width, then for elision

Turn on invariant 5 (`ty` is the read width). Then invariant 3 (elided implies
no readers), which subsumes the single-use propagation pass and its whole-body
read count.

**Gate:** all five invariants on. Corpus back above 38 and climbing.

### Stage 5 — Delete the dead tables

Remove every field of `UseInfo` the binding table now answers for, including
`unkeyed_writes` — the drift counter has nothing left to count. Remove the
`allow(dead_code)` markers that were hiding the removed paths.

**Gate:** `UseInfo` under 12 fields. Zero clippy diagnostics, zero build
warnings, `cargo fmt` clean. Corpus 54 of 54.

---

## 7. Fastest path

The ordering above is chosen for speed, not tidiness.

- **Stage 0 first** because every later stage is measured through the harness,
  and a dishonest harness makes every measurement suspect. It cost two turns
  once; over five stages it would cost far more. It is a few hours.
- **Stage 1 before stage 2**, not after, because stage 3's edits land in the
  files stage 1 splits. Splitting after the rewrite means doing the rewrite in
  the hardest possible place first.
- **Stage 2's divergence log replaces guessing.** The single most expensive
  pattern on this branch was writing a fix before taking a trace. The divergence
  list is the trace, taken once, for every value at once.
- **Stages 1 and 0 are parallelisable** — different files, no shared state. So
  are the four file splits inside stage 1.
- **Do not chase the remaining 16 corpus failures before stage 3.** Five of them
  (murmur3 ordering, murmur3's lost zero, crc32_bitwise's undeclared temporaries)
  are name and width defects that stages 3 and 4 dissolve. Fixing them
  individually first means fixing them twice.

The genuinely independent work — the 13-parameter functions, deep nesting,
`r2sym`'s wide structs, clippy and fmt — can be done at any point and does not
block anything. It should not be done *instead of* the stages.

---

## 8. Rules of engagement

Learned on this branch, at cost.

1. **Trace before the guard.** A value typically has several tables that can
   answer for it. Suppressing one is indistinguishable from a wrong fix while
   another still answers. Count the tables, change them together.
2. **A change that alters no rendered output does not stay in the tree.** It
   proves nothing. This does *not* apply to a change that genuinely restructures
   a blocking seam and costs corpus results on the way — that is progress with a
   price, and it stays.
3. **Never trust a corpus number without confirming the install.** `make -C
   r2plugin install` must print `Installed to ...`. A failed install silently
   leaves the old plugin and reads as a regression identical to a real one.
4. **Check `df` at the first `codesign` failure.** About 40 codesign errors and
   two false corpus readings this session had one cause: a full disk, from a
   69 GB `target/debug` in a release-only workflow.
5. **When the number moves and it should not have, stop.** The `__?u?int` regex
   slip was caught only because 37 → 18 was impossible for the change made.
6. **The 2340 tests caught none of this branch's defects.** They are a
   regression net, not a specification. The corpus is the specification. Add
   invariant checks (section 4) as the thing tests can actually assert.

---

## 9. Open defects at HEAD

Sixteen corpus failures, five causes. Each is recorded with its trace in
`doc/handoff-location-ssa.md`.

| Cause | Entries | Disposition |
|---|---|---|
| murmur3 region/ordering — `t20380_5`, `t11f00_10` read before the merge declares them | 2 | Stage 3 |
| murmur3 lost zero — `k1` renders as `arg3`, from parameter over-recovery | 2 | Stage 3 |
| crc32_bitwise — undeclared `tregalias_`, `tregpiece_` temporaries | 2 | Stage 3 |
| fnv1a64 — `r8d` piece composition | 1 | Stage 4 |
| xxhash32 — 2 harness-blocked on `sym__rotl32`, 2 wrong values, 1 `callother`, 1 struct type error | 6 | Stage 0 and 4 |

---

## 10. What "done" looks like

The corpus at 54 of 54, held across a rebuild. `UseInfo` under 12 fields.
No file over 3,000 lines. Five invariants asserted at the analysis/render
boundary, so that the properties in section 1 are structural rather than
observed. Zero warnings, zero clippy diagnostics, `cargo fmt` clean.

And the pinned rule finally implementable: when a value renders wrong, there is
exactly one record that decided it, and that record is where the fix goes.
