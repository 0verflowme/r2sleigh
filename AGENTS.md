# Agent Guidelines for r2sleigh

> LLM-focused working rules for contributors and coding agents.

## North Star

`r2sleigh`, `r2ssa`, `r2sym`, `r2types`, `r2dec`, `r2plugin`, and
`../radare2` are one subsystem.

The goal is not "more commands" or "more crates doing similar work." The goal
is a gold-standard radare2 analysis engine where:

- one canonical fact has one canonical owner
- facts flow through typed contracts, not JSON reparsing
- decompiler, types, symbolic execution, and radare2 core views agree
- expensive work is summarized, cached, and reused
- output is deterministic
- architecture and API seams may be rewritten whenever the rewrite is cleaner

The plugin should feel like radare2 itself got smarter, not like radare2 grew a
second shell.

## Non-Negotiables

1. One fact, one owner.
2. Treat this repo and `../radare2` as one component boundary.
3. `r2plugin` is orchestration/FFI glue only.
4. Do not reconstruct missing semantics downstream.
5. Prefer typed contracts over JSON blobs and stringly maps.
6. `r2types::FunctionFacts` is the canonical combined type+semantic contract.
7. `r2types::FunctionTypeFacts` is the canonical type/layout/signature payload.
8. `r2sym::SemanticArtifact` is the canonical semantic artifact.
9. `r2sym` owns semantic policy and evidence; consumers interpret it.
10. Deterministic ordering beats cleverness.
11. Rewrite bad seams instead of patching around them.
12. Validation is part of the change, not optional cleanup.

## Optimization Doctrine

Low-quality implementations tend to optimize the wrong thing. Do not do that.

The target is not fantasy "`O(1)` symex." The target is:

- `O(1)` or `O(log n)` lookup for metadata, indexes, summaries, and caches
- `O(n)` passes over blocks, SSA ops, or facts whenever possible
- bounded search when search is unavoidable
- incremental recomputation instead of whole-function replay
- summary reuse across query, typing, and decompilation
- explicit budgets for solver work, symbolic exploration, and structuring

Use this mental model:

- repeated whole-function scans are a smell
- repeated solver queries for the same fact are a smell
- recomputing downstream what already exists upstream is a smell
- parallel representations of the same fact are a bug
- hash-order-dependent output is a bug

If you cannot explain the asymptotic and practical cost of a new analysis path,
you do not understand it well enough to land it.

### Efficiency Rules

1. Prefer canonical summaries over re-analysis.
2. Prefer incremental updates over full rebuilds.
3. Prefer typed caches over ad hoc memoization.
4. Prefer `BTreeMap` / `BTreeSet` when ordering affects output or tests.
5. Prefer one richer pass over many weak overlapping passes.
6. Prefer explicit budgets and refusal modes over silent blowups.
7. Prefer stronger upstream facts over downstream heuristics.

## Architectural Stance

This system should move toward a gold-standard analysis architecture even when
that requires invasive refactors.

- It is acceptable to redesign contracts, move logic across crates, or change
  FFI and `../radare2` seams when the result is cleaner.
- Do not preserve a bad abstraction because it already exists.
- Do not add end-stage hacks in `r2plugin` or `r2dec` to hide missing upstream
  semantics.
- If a crate is carrying policy it should not own, move that policy.

The right question is not "what is the smallest diff?" It is "what is the
cleanest owner and the cheapest long-term design?"

## Task-Start Protocol

For any non-trivial change, follow this order:

1. Identify the user-visible behavior or broken invariant.
2. Identify the canonical owner: `../radare2`, lift, SSA, symex, types,
   decompiler, export, CLI, or plugin.
3. Identify the existing typed contract to extend before creating a new one.
4. State the complexity target: lookup, traversal, search, cache, summary.
5. Push facts upstream to the owner instead of reconstructing them downstream.
6. Add the smallest deterministic test at the layer users actually exercise.
7. If the seam crosses into `../radare2`, validate both repos before claiming
   the work is complete.

## Ownership Boundaries

Use this map by default:

- `../radare2`
  - core analysis facts
  - typed collectors
  - native analysis metadata and persistence
  - library seams that should exist for radare2 consumers generally
- `crates/r2il`
  - canonical IL data model and serialization
- `crates/r2sleigh-lift`
  - Sleigh/P-code lifting
  - register naming
  - disassembly formatting
  - ESIL formatting
- `crates/r2ssa`
  - SSA construction
  - phi handling
  - dominators / def-use
  - prepared function facts
  - determinism and SSA-local transforms
- `crates/r2sym`
  - symbolic state
  - semantic artifacts
  - evidence algebra
  - query planning
  - summaries and replay
  - solver-facing semantic policy
- `crates/r2types`
  - signature parsing and normalization
  - type inference
  - layout inference
  - external type context normalization
  - canonical `FunctionTypeFacts`
  - canonical combined `FunctionFacts`
- `crates/r2dec`
  - lowering
  - semantic interpretation of canonical facts
  - structuring
  - rendering
- `crates/r2sleigh-export` / `crates/r2sleigh-cli`
  - shared export/CLI plumbing
- `r2plugin`
  - command dispatch
  - JSON shaping
  - FFI
  - radare2 integration glue

Do not let the same policy exist in two crates "for now."

## Canonical Contracts

These are the preferred subsystem seams:

- `r2ssa::SsaArtifact` and `PreparedFunctionFacts`
  - canonical SSA/dataflow preparation
- `r2sym::SemanticArtifact`
  - canonical semantic artifact
- `r2sym::SemanticEvidence`
  - canonical evidence carrier
- `r2sym::{ArtifactBuildPlan, QueryPlan, TargetQueryRoutePlan, TypePlan, DecompilePlan}`
  - canonical plan surfaces
- `r2types::FunctionTypeFacts`
  - canonical type/layout/signature payload
- `r2types::FunctionFacts`
  - canonical combined type+semantic payload
- `r2dec::SemanticRoutePlan`
  - renderer route selected from canonical upstream capabilities

If a caller needs more information, extend these contracts instead of creating
parallel wrappers.

## Typed `radare2` Seam

The plugin must not parse `afcfj`, `afvj`, `tsj`, or similar command output as
an internal data source.

Rules:

- use the typed function/base-type collector APIs in `../radare2`
- keep user-visible commands, but do not use them as plugin internals
- if a typed field is missing, add it in `../radare2`
- prefer one consolidated typed context payload over multiple overlapping JSON
  blobs

If the right fix belongs in `../radare2`, implement it there.

## Plugin Philosophy

The public product should be workflow-oriented, not command-oriented.

The plugin should:

- improve `aa`, `af`, `pdfj`, `pdd`, type views, and existing radare2 analysis
  surfaces
- keep a small public command surface
- treat engine-inspection commands as debug/maintainer tools
- move knobs to config (`e anal.sleigh.*`) where that is cleaner than inventing
  verbs

If you are about to add a new command, stop and ask:

1. should this be automatic?
2. should this enrich an existing radare2 view instead?
3. should this be config rather than a verb?
4. is this just a debug surface?

## Rewrite Bias

When current architecture blocks correctness, composability, or efficiency:

- rewrite the seam
- move the owner
- shrink duplicated policy
- reshape FFI if needed
- change module layout if needed

Avoid:

- plugin-side reparsing
- decompiler-side type policy
- consumer-local semantic policy that should live in `r2sym`
- compatibility shims that silently become permanent

## Optimization Checklist

Before landing any non-trivial change, check these explicitly:

1. Did I add a second owner for an existing fact?
2. Did I add a repeated full-function walk?
3. Did I add repeated solver work that should be cached or summarized?
4. Did I add a new JSON-shaped internal type where a Rust type should exist?
5. Did I add ordering nondeterminism?
6. Did I move policy downstream instead of upstream?
7. Did I preserve a bad seam instead of rewriting it?

If any answer is "yes", the design is probably wrong.

## Build And Run

Use these commands from the workspace root unless noted otherwise.

```bash
# Build the workspace with x86 support
cargo build --workspace --features x86

# Run the Rust test suite
cargo test --workspace --features x86

# Run the CLI explicitly
cargo run -p r2sleigh-cli --bin r2sleigh --features x86 -- \
  disasm --arch x86-64 --bytes "31c00000000000000000000000000000" --format json

# Install the plugin via the workspace alias
cargo install-plugin -- --features x86

# Or install all plugin architectures through the Makefile helper
make -C r2plugin RUST_FEATURES=all-archs install

# Run the preferred plugin regression suite
make -C tests/r2r run

# Run the Rust e2e suite when needed
cargo e2e-test
```

Notes:

- `cargo run --features x86 -- ...` at the workspace root is stale; use
  `-p r2sleigh-cli --bin r2sleigh`
- `cargo install-plugin` is defined in `.cargo/config.toml`
- x86/x86-64 lifting still expects 16 bytes minimum
- if you touch the typed `../radare2` seam, build and test `../radare2` too

## Testing Policy

### Default: `tests/r2r`

Use `tests/r2r` for new regressions involving:

- plugin commands such as `a:sla.*`, `a:sym.*`, `pdd`, `pdD`
- stable JSON/text/ESIL output
- CFG / SSA / def-use / type payload shape
- command UX and error text
- radare2 integration behavior

Why:

- faster feedback
- better diffs
- already normalized around real radare2 command execution

### Use `tests/e2e` only when `r2r` is the wrong tool

Keep Rust E2E tests for:

- FFI / ABI checks
- CLI export semantics
- benchmark-style assertions
- direct Rust orchestration cases that `r2r` cannot express cleanly

## Required Validation Bar

If you touch `r2ssa`, `r2sym`, `r2types`, `r2dec`, `r2plugin`, or the typed
`../radare2` seam, the minimum validation bar is:

```bash
cargo test -p r2ssa
cargo test -p r2sym
cargo test -p r2types
cargo test -p r2dec
cargo test -p r2sleigh-plugin
cargo clippy -p r2ssa --all-targets -- -D warnings
cargo clippy -p r2sym --all-targets -- -D warnings
cargo clippy -p r2types --all-targets -- -D warnings
cargo clippy -p r2dec --all-targets -- -D warnings
cargo clippy -p r2sleigh-plugin --features all-archs -- -D warnings
make -C r2plugin RUST_FEATURES=all-archs install
make -C tests/r2r run
```

If you also changed `../radare2`, add:

```bash
make -C ../radare2 -j4
cd ../radare2/test && r2r -L -o results.json db/cmd/cmd_af db/json/json1
```

Do not claim the seam is fixed without both sides being green.

## `r2r` Placement Guide

`tests/r2r/db/extras/r2sleigh_core`
- small deterministic instruction-level checks

`tests/r2r/db/extras/r2sleigh_integration_fast`
- function-level behavior that should stay quick

`tests/r2r/db/extras/r2sleigh_integration_extended`
- heavier symbolic, taint, decompilation, and larger-CFG coverage

## Common Change Workflows

### Change the type / decompiler seam

1. Choose the owner. If the answer is "more than one", the design is wrong.
2. Extend `r2types` first for signatures, layouts, and type facts.
3. Keep `r2dec` on semantic interpretation and rendering only.
4. If the plugin needs more context, extend `../radare2` instead of parsing
   more command JSON.
5. If the seam is wrong, redesign it across repos instead of layering adapters.
6. Add or update `r2r` before broad snapshot churn.

### Change symbolic / query behavior

1. Put semantic policy in `r2sym`.
2. Put evidence and ambiguity in canonical artifact/evidence types.
3. Put routing in canonical plans.
4. Let `r2types` / `r2dec` consume those plans; do not reinvent them.
5. Add solver-budget and determinism coverage where applicable.

### Add or change a plugin command

1. Decide whether the feature should really be automatic or radare2-native.
2. Rust-side data shaping usually lives in `r2plugin/src/lib.rs`.
3. C dispatch/help lives in `r2plugin/r_anal_sleigh.c`.
4. Add `r2r` coverage for help, happy path, and failure path.

## Plugin Command Surface

Treat this as two tiers:

- public / user-facing
  - `a:sla`
  - `a:sla.dec`
  - `pdd`, `pdD`
  - `a:sym.explore`
  - `a:sym.solve`
  - `a:sym.state`
- debug / engine inspection
  - low-level IL / SSA / facts / plan / replay / path listing commands

Do not expand the public surface casually. Prefer deeper integration over more
verbs.

## Two SSA Block Types

There are two different block types in `r2ssa`:

| Type | Location | Purpose |
|------|----------|---------|
| `SSABlock` | `crates/r2ssa/src/block.rs` | single-instruction SSA block |
| `FunctionSSABlock` | `crates/r2ssa/src/function.rs` | function block with phi nodes |

`r2dec` works with `FunctionSSABlock`.

## File Quick Reference

| File | Edit this when... |
|------|--------------------|
| `crates/r2il/src/opcode.rs` | adding or changing IL ops |
| `crates/r2sleigh-lift/src/disasm.rs` | changing P-code lifting or register naming |
| `crates/r2sleigh-lift/src/esil.rs` | changing text or ESIL rendering |
| `crates/r2ssa/src/` | changing SSA construction, def-use, prepared facts |
| `crates/r2sym/src/` | changing semantic artifacts, query, summaries, replay, solver policy |
| `crates/r2types/src/` | changing type inference, layouts, canonical function facts |
| `crates/r2dec/src/` | changing lowering, structuring, rendering |
| `r2plugin/src/lib.rs` | changing plugin-side Rust logic and JSON payloads |
| `r2plugin/r_anal_sleigh.c` | changing command dispatch/help or C-side integration |
| `../radare2/libr/include/r_anal.h` | changing typed collector APIs used by the plugin |
| `tests/r2r/db/extras/` | adding or updating regression snapshots |

## Gotchas

1. x86/x86-64 lifting still expects 16 bytes minimum.
2. ESIL subtraction must use ASCII `-`, not Unicode minus.
3. `Const` means literal; `Unique` means temporary SSA-like storage, not memory.
4. Width mismatches usually need explicit sign/zero extension.
5. Register aliasing must stay deterministic.
6. `#[no_mangle]` is now `#[unsafe(no_mangle)]` under Rust 2024.
7. Plugin, CLI, and export feature matrices are not identical.
8. If output stability matters, hash-order nondeterminism is a bug.
9. Use `r2dec/address.rs::parse_address_from_var_name()` for consistent
   `const:` / `ram:` parsing.
10. On the decompiler/type path, do not reintroduce `r2dec` type ownership just
    to make an old test compile.

## Useful References

- `README.md` for current build and testing quick-start
- `ROADMAP.md` for current system direction and priority order
- `tests/e2e/README.md` for the split between Rust E2E and `r2r`
- `doc/` for IL, SSA, ESIL, decompiler, taint, symex, and type-system notes
- radare2 ESIL docs: <https://book.rada.re/disassembling/esil.html>
- Ghidra P-code reference: <https://ghidra.re/courses/languages/html/pcoderef.html>
