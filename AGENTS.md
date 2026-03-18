# Agent Guidelines for r2sleigh

> LLM-focused working notes for contributors and coding agents.

## Project Summary

`r2sleigh` is the Sleigh-backed analysis and decompiler pipeline for radare2.

```text
.sla (Ghidra) --> libsla --> P-code --> r2il --> ESIL
                                          |
                                          +--> SSA (r2ssa)
                                          +--> Type inference (r2types)
                                          +--> Symbolic / taint (r2sym)
                                          +--> Decompiler (r2dec)
                                          +--> Plugin / CLI export surfaces
```

The repository is no longer just "P-code to ESIL". A lot of current work lands in SSA, symbolic execution, type inference, decompilation, and radare2 integration layers.

Treat this workspace and `../radare2` as one analysis system. `r2sleigh` is part of the radare2 analysis/decompiler stack, not a separate sidecar that should paper over missing library seams at the end of the pipeline.

The opening sections are the operational rules. Later sections are reference material.

## Fast Path Rules

1. Find the canonical owner of a fact before editing code. Cross-crate cooperation is expected; duplicated policy is not.
2. Treat this workspace and `../radare2` as one component boundary. If the right fix belongs in radare2, implement it there instead of patching around it in Rust.
3. `r2plugin` is orchestration/FFI glue only. Do not fix missing semantics by reparsing command output or merging policy there.
4. For decompiler/type context, do not add new plugin-side parsing of `afcfj`, `afvj`, or `tsj`. If the seam is wrong, fix it in `../radare2` and keep the plugin on the typed collector path.
5. `r2types::FunctionTypeFacts` is the only canonical type/layout/signature contract on the decompiler path.
6. Default to `tests/r2r` for new plugin regressions and command-output checks. Do not add new snapshot-style plugin tests to `tests/e2e/integration_tests.rs` unless `r2r` genuinely cannot express the case.
7. Build and run commands in this repo have drifted over time. Prefer the commands in this file over older examples.
8. File paths below use the current `src/` layout. Older references like `r2plugin/lib.rs` are stale.
9. Architecture feature support differs by crate. Check the relevant `Cargo.toml` before documenting or wiring a new arch.
10. When the current architecture blocks a clean design, rewrite the seam or crate API instead of adding end-stage hacks. Large refactors, FFI changes, and cross-repo redesigns are acceptable when they reduce long-term complexity.

## Task-Start Protocol

For any non-trivial change, follow this order:

1. Identify the user-visible behavior or broken invariant.
2. Decide which layer should own the fix: `../radare2`, lifting, SSA, symex, types, decompiler, export, CLI, or plugin glue.
3. Look for an existing typed contract to extend before adding new JSON blobs, stringly maps, or parallel wrapper types.
4. Push facts upstream to the canonical owner instead of reconstructing them downstream.
5. Add the smallest deterministic test at the layer users actually exercise.
6. If the seam crosses into `../radare2`, validate both repos before claiming the fix is complete.

## Change Placement Guide

Use this as the default "where should this logic live?" map:

- `../radare2`: core analysis facts, typed collectors, and library seams that should exist for radare2 consumers generally.
- `crates/r2sleigh-lift`: Sleigh/P-code lifting, disassembly, register naming, text formatting, and ESIL formatting.
- `crates/r2ssa`: SSA construction, phi handling, dominators, def-use, determinism, and SSA-local transforms.
- `crates/r2sym`: symbolic execution, taint propagation, summaries, path exploration, and solver-facing symbolic policy.
- `crates/r2types`: signature parsing, type inference, layout inference, external context normalization, and canonical merged type facts.
- `crates/r2dec`: lowering, semantic interpretation, structuring, folding, and rendering.
- `crates/r2sleigh-export` and `crates/r2sleigh-cli`: shared export plumbing and CLI surface behavior.
- `r2plugin`: command dispatch, FFI, serialization, and radare2 integration glue only.

## Workspace Layout

```text
crates/
├── r2il/             # Core IL types and serialization
├── r2sleigh-lift/    # Sleigh/P-code lifting, disassembly, ESIL formatting
├── r2sleigh-export/  # Unified export pipeline for lift/ssa/defuse/dec
├── r2sleigh-cli/     # Standalone CLI
├── r2ssa/            # SSA form, dominators, def-use, optimization
├── r2sym/            # Symbolic execution, taint, summaries, solving
├── r2types/          # Type inference and signatures
└── r2dec/            # Decompiler AST, folding, lowering, codegen
r2plugin/             # Rust cdylib + C radare2 wrapper
tests/
├── r2r/              # Preferred snapshot and command regression suite
└── e2e/              # Rust semantic/FFI/benchmark suite and fixture binaries
```

## Whole-System Architecture Stance

`r2il`, `r2sleigh-lift`, `r2ssa`, `r2sym`, `r2types`, `r2dec`, `r2sleigh-export`, `r2plugin`, and `../radare2` should be treated as one radare2 analysis/decompiler subsystem with explicit internal ownership.

- Optimize for clean typed seams and correct ownership, not for preserving historical plugin boundaries.
- `r2plugin` is an integration surface, not the place to recover missing semantics from downstream command output.
- If a clean solution requires moving logic across crates or across the `../radare2` boundary, do it at the owning layer.
- Prefer principled rewrites over incremental "fix it later in the plugin/decompiler/export path" patches.
- Cross-component cooperation is required; cross-component policy duplication is not.

## Ownership Boundaries

These boundaries are the main architectural guardrail. The crates should work together as one pipeline, but each fact still needs one canonical owner. Most recent churn happened when multiple crates tried to "help" each other by owning the same policy.

- `r2ssa` owns SSA construction, decompile-safe SSA preparation, determinism, and SSA-local transforms.
- `r2sym` owns symbolic state modeling, taint propagation, summaries, path exploration, and solver-facing symbolic policy.
- `r2types` owns signature parsing/normalization, type inference, layout inference, external context parsing, field lookup policy, and canonical merged type facts.
- `r2dec` owns decompiler semantic facts, lowering, structuring, and rendering only.
- `r2plugin` owns orchestration, JSON/FFI, command dispatch, and radare2 integration glue only.
- `../radare2` owns core analysis facts, typed collectors, and library seams that should exist for radare2 consumers generally, not just this workspace.

Do not put the same policy in two crates "temporarily". That temporary state lasted a long time and created most of the recent regressions.

When multiple layers need the same fact, push that fact toward its canonical owner and expose it through a typed contract instead of rebuilding it independently in each crate.

## Typed `radare2` Context Seam

The plugin used to pull decompiler/type context by shelling out to radare2 commands and re-parsing JSON from `afcfj`, `afvj`, and `tsj`. That was convenient, but it created duplicate ownership and brittle parsing policy in the plugin.

Current rule:

- For decompiler/type analysis, use the typed function/base-type collector API in `../radare2`.
- Keep user-visible commands like `afcfj`, `afvj`, and `tsj`, but do not use them as an internal plugin data source.
- If the plugin lacks a typed field from radare2, add it to the `r_anal` API instead of layering more command parsing into `r2plugin`.
- Prefer one consolidated external-context payload across the C/Rust FFI boundary rather than multiple partially overlapping JSON blobs.
- Treat `../radare2` as available for coordinated changes. If the right fix needs new FFI, collector APIs, or analysis metadata, add them there and wire them through cleanly.

This seam exists to keep `r2plugin` orchestration-only and to keep type/signature/layout policy out of the plugin.

## Canonical Type Contract

`r2types::FunctionTypeFacts` is the only canonical type/layout/signature artifact for the decompiler path.

- `r2types` may consume local inference artifacts, radare2 external context, and decompiler-emitted semantic field-access facts.
- `r2dec` should consume `FunctionTypeFacts` only. Do not add back public `TypeInference`, duplicate `FunctionType`, or decompiler-side external-signature / stack-var setters.
- `r2plugin` may gather inputs and serialize outputs, but it must not own signature merge policy, external/local struct reconciliation, or layout query policy.

If a caller needs more type information, extend `FunctionTypeFacts` or the `r2types` query contract instead of creating a second type wrapper layer elsewhere.

## Rewrite Bias

When the current architecture blocks correctness, composability, or maintainability:

- Prefer rewriting the seam, contract, or owning crate over adding compensating logic at the end of the pipeline.
- It is acceptable to redesign APIs, move logic across crates, reshape FFI, or perform cross-repo refactors involving `../radare2`.
- Do not preserve a bad abstraction just because it already exists.
- The goal is a better end-to-end radare2 component, not the smallest possible diff.
- Avoid plugin-side or decompiler-side "final fixups" that only exist to hide missing upstream semantics.

## Rust Typing Rules For Rewrites

Recent work went better once ownership seams stopped relying on stringly maps and implicit conventions.

- Prefer enums, newtypes, named structs, and small typed input structs over raw `HashMap<String, ...>` plus comments.
- Use traits at crate seams where the contract matters, for example layout queries or semantic fact access.
- Use `BTreeMap` / `BTreeSet` whenever iteration order can affect decompiler output, local naming, snapshots, or SSA determinism.
- Use `From` / `TryFrom` for typed boundary conversions instead of ad hoc parsing spread across crates.
- Keep JSON-only types at the JSON boundary. Internal analysis code should use typed Rust models first and serialize late.
- Avoid boolean mode flags when there are more than two semantic states; use enums instead.

## Core Types and Entry Points

| Type / Function | Location | Purpose |
|-----------------|----------|---------|
| `Varnode` | `crates/r2il/src/varnode.rs` | Sized data location: reg/mem/const/unique |
| `SpaceId` | `crates/r2il/src/space.rs` | Address-space enum |
| `R2ILOp` | `crates/r2il/src/opcode.rs` | Semantic IL op enum |
| `R2ILBlock` | `crates/r2il/src/opcode.rs` | One-instruction IL block |
| `ArchSpec` | `crates/r2il/src/serialize.rs` | Architecture metadata |
| `Disassembler` | `crates/r2sleigh-lift/src/disasm.rs` | libsla wrapper and P-code lifting |
| `format_op()` / `op_to_esil()` | `crates/r2sleigh-lift/src/esil.rs` | Text and ESIL formatting |
| `run_action_output()` | `crates/r2sleigh-cli/src/main.rs` | CLI action/format dispatcher |
| export helpers | `crates/r2sleigh-export/src/lib.rs` | Shared export pipeline used by CLI/plugin |
| `SSAVar` | `crates/r2ssa/src/var.rs` | Versioned SSA variable |
| `SSAOp` | `crates/r2ssa/src/op.rs` | SSA operation enum |
| `to_ssa()` | `crates/r2ssa/src/block.rs` | R2IL block -> SSA block |
| `DefUseInfo` | `crates/r2ssa/src/defuse.rs` | Def-use analysis result |
| `FunctionSSABlock` / `SSAFunction` | `crates/r2ssa/src/function.rs` | Function-level SSA with phi nodes |
| `AnalysisResult` and type passes | `crates/r2types/src/` | Type inference payloads |
| `CExpr` / `CStmt` | `crates/r2dec/src/ast.rs` | Decompiler AST |
| `FoldingContext` | `crates/r2dec/src/fold/` | Expression folding and simplification |
| `LowerCtx` | `crates/r2dec/src/analysis/lower.rs` | SSA-to-expression lowering |
| plugin Rust surface | `r2plugin/src/lib.rs` | JSON commands, analysis helpers, FFI |
| plugin C wrapper | `r2plugin/r_anal_sleigh.c` | radare2 callbacks and command dispatch |

## Build and Run

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

- `cargo run --features x86 -- ...` is stale at the workspace root; use `-p r2sleigh-cli --bin r2sleigh`.
- `cargo install-plugin` is defined in `.cargo/config.toml` and wraps `r2plugin/src/bin/r2sleigh-plugin-install.rs`.
- x86/x86-64 disassembly still needs at least 16 bytes of input; pad with zeros.
- If you touch the typed radare2 seam in `r2plugin/r_anal_sleigh.c`, plan to build and test `../radare2` too. Fix the library seam there instead of adding more plugin-side command parsing.

## Architecture Support

Feature matrices are not identical across crates.

- `r2plugin` currently exposes `x86`, `arm`, `riscv`, and `all-archs`.
- `r2sleigh-cli` currently exposes `x86`, `arm`, `mips`, `riscv`, and `all-archs`.
- There is still some compatibility code for `mips` in shared/plugin code, but the plugin crate itself is currently feature-gated around `x86`, `arm`, and `riscv`.
- If you change architecture wiring, inspect both `r2plugin/Cargo.toml` and `crates/r2sleigh-cli/Cargo.toml`.

For radare2 auto-selection, the plugin currently maps common values like:

- `anal.arch=x86`, `anal.bits=64` -> `x86-64`
- `anal.arch=x86`, `anal.bits=32` -> `x86`
- `anal.arch=arm`, `anal.bits=32` -> `arm`
- `anal.arch=arm`, `anal.bits=64` or `anal.arch=arm64` / `aarch64` -> `aarch64`
- `anal.arch=riscv`, `anal.bits=32` -> `riscv32`
- `anal.arch=riscv`, `anal.bits=64` -> `riscv64`

Manual override stays:

```bash
r2 -qc 'a:sla.arch x86-64; a:sla.arch' /bin/ls
```

## Testing Policy

### Default: `tests/r2r`

Use `tests/r2r` for new regressions involving:

- plugin commands such as `a:sla.*`, `a:sym.*`, `pdd`, `pdD`
- stable JSON/text/ESIL outputs that are worth exact normalized snapshots
- CFG/SSA/def-use/type payload shape when structural assertions are the better fit
- command UX, help text, error text, and normalized decompiler output
- radare2 integration behavior that is best expressed as command snapshots

Why:

- faster feedback
- better snapshot-style diffs
- already normalized around radare2 command execution
- consistent with how users exercise the plugin

### Use `tests/e2e` only when `r2r` is the wrong tool

Keep Rust E2E tests for:

- FFI / ABI checks
- CLI `run` export semantics
- analysis-quality thresholds or benchmark-style assertions
- cases that need direct Rust-side orchestration rather than command snapshots

`tests/e2e/integration_tests.rs` still exists, but it is not the default place for new plugin regression coverage.

## Adding New Tests

### Preferred workflow for new features

1. Implement the feature.
2. If the user-facing behavior is visible through radare2 commands, add or update an `r2r` case.
3. If the feature needs a specific binary pattern, add or update a fixture source under `tests/e2e/`.
4. Run `make -C tests/r2r run`.
5. If the change also affects CLI semantics, FFI, or benchmark-style behavior, run `cargo e2e-test` or a focused `tests/e2e` module.

### Required validation for ownership / seam changes

If you touch `r2ssa`, `r2sym`, `r2types`, `r2dec`, `r2plugin`, or the typed `../radare2` context seam, the minimum validation bar is:

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

During local iteration, a focused subset is fine. Do not mark an ownership or seam change complete until the full relevant validation bar is green.

If you also changed `../radare2`, add:

```bash
make -C ../radare2 -j4
cd ../radare2/test && r2r -L -o results.json db/cmd/cmd_af db/json/json1
```

Do not claim the seam is fixed without both sides being green.

### Where to put new `r2r` cases

`tests/r2r/db/extras/r2sleigh_core`
- very small, deterministic instruction-level checks
- good for `a:sla.json`, `a:sla.regs`, `a:sla.mem`, `a:sla.vars`

`tests/r2r/db/extras/r2sleigh_integration_fast`
- function-level plugin behavior that should stay quick
- good for `a:sla.ssa.func`, `a:sla.cfg.json`, `a:sla.dom`, `a:sla.types`, `a:sla.opvals`

`tests/r2r/db/extras/r2sleigh_integration_extended`
- slower or heavier coverage
- symbolic execution, taint, complex decompilation, larger binaries

### `r2r` test authoring tips

- Prefer exact full-output snapshots for stable user-facing surfaces after normalization.
- Use `tests/r2r/normalize_snapshot.py` or `jq -S -c` to canonicalize stable output before snapshotting.
- Prefer structural assertions only when ordering, naming, or formatting is expected to evolve, especially for SSA, symex, taint, and large CFG/DOM payloads.
- Keep these args unless you have a reason not to:

```text
-e scr.color=false -e log.level=0 -e bin.relocs.apply=true
```

- `tests/r2r/Makefile` builds the fixture binaries from `tests/e2e/` and symlinks them into `tests/r2r/bins/`.
- If you add a brand-new fixture binary, update `tests/r2r/Makefile` so the harness links it.

Minimal `r2r` example:

```text
NAME=instruction_regs_snapshot
FILE=bins/vuln_test_x86
ARGS=-e scr.color=false -e bin.relocs.apply=true
EXPECT=<<EOF_EXPECT
{"read":["EDI","RBP"],"write":[]}
EOF_EXPECT
CMDS=<<EOF_CMDS
s `is~check_secret[2]`+0x4 >/dev/null
a:sla.regs | python3 normalize_snapshot.py regs
EOF_CMDS
RUN
```

### Fixture guidance

Use the smallest fixture that exercises the behavior:

- `tests/e2e/vuln_test.c` for focused plugin features and common analysis cases
- `tests/e2e/stress_test.c` for larger decompiler/symbolic/type cases
- `tests/e2e/test_func.c` for small structured helper functions
- `tests/e2e/sym_test.c` for symbolic-execution-specific patterns

When you add a fixture function:

1. Add the function with a short comment explaining what it exercises.
2. Wire it into the fixture's `main()` or other entry path if the tests need runtime access.
3. Add or update the corresponding `r2r` snapshot.

## Common Change Workflows

### Add a new R2IL opcode

1. Add the variant to `crates/r2il/src/opcode.rs`.
2. Teach the lifter to emit it in `crates/r2sleigh-lift/src/disasm.rs`.
3. Add text and ESIL formatting in `crates/r2sleigh-lift/src/esil.rs`.
4. Check any export path that formats or serializes the new op through `crates/r2sleigh-export/src/lib.rs` or CLI output.
5. Add tests. Prefer an `r2r` snapshot when the opcode is visible through plugin output.

### Add SSA support for a new op

1. Add the SSA variant to `crates/r2ssa/src/op.rs`.
2. Convert it in `crates/r2ssa/src/block.rs`.
3. Update `dst()` and `sources()` in `crates/r2ssa/src/op.rs`.
4. Add function-level or instruction-level coverage, usually via `a:sla.ssa`, `a:sla.ssa.func`, or `a:sla.defuse`.

### Add decompiler support for a new SSA op

1. Add lowering in `crates/r2dec/src/analysis/lower.rs` if needed.
2. Add fold/codegen support under `crates/r2dec/src/fold/`.
3. Test through `a:sla.dec` snapshots and add direct Rust tests when local folding behavior is easier to assert there.

### Change the type / decompiler seam

1. Start by deciding which crate should own the policy. If the answer is "more than one", the design is wrong.
2. Extend `r2types` contracts first when the change affects signatures, layouts, or external context.
3. Keep `r2dec` on semantic facts and rendering. If decompiler code needs to rediscover type/layout policy from rendered expressions, stop and move that logic upstream.
4. If the plugin needs more context from radare2, extend the typed `r_anal` seam in `../radare2` instead of parsing more command JSON.
5. If the existing seam is fundamentally wrong, redesign it across both repos instead of layering more adapters on top.
6. Add or update `r2r` coverage before broad snapshot churn. The right fix is usually a stronger semantic assertion, not a bigger snapshot.

### Add or change a plugin command

1. Rust-side command data shaping usually lives in `r2plugin/src/lib.rs`.
2. radare2 command dispatch and help text live in `r2plugin/r_anal_sleigh.c`.
3. Add or update `r2r` coverage for help text, happy path, and error path.

### Add a new architecture

1. Update the relevant crate feature flags.
2. Wire spec/disassembler creation in the CLI, plugin, and export surfaces that need it.
3. Add at least one focused test path for the new arch.
4. Prefer documenting only architectures that are actually wired and tested in the crate you changed.

## Plugin Command Surface

Common instruction-level commands:

| Command | Purpose |
|---------|---------|
| `a:sla` | status / help |
| `a:sla.info` | current architecture info |
| `a:sla.arch [name]` | get or set Sleigh arch override |
| `a:sla.json` | raw r2il for current instruction |
| `a:sla.regs` | read/write registers |
| `a:sla.opvals` | analysis src/dst register view |
| `a:sla.mem` | memory accesses |
| `a:sla.vars` | varnodes |
| `a:sla.ssa` | instruction SSA |
| `a:sla.defuse` | instruction def-use |

Function-level commands:

| Command | Purpose |
|---------|---------|
| `a:sla.ssa.func` | function SSA with phi nodes |
| `a:sla.ssa.func.opt` | optimized function SSA |
| `a:sla.defuse.func` | function-wide def-use |
| `a:sla.dom` | dominator tree |
| `a:sla.slice <var>` | backward slice |
| `a:sla.types` | type-inference payload |
| `a:sla.taint` | taint analysis |
| `a:sla.sym` | symbolic summary |
| `a:sla.sym.paths` | explored symbolic paths |
| `a:sla.sym.merge [on|off]` | symbolic merge toggle |
| `a:sla.dec [name|addr]` | decompile |
| `pdd`, `pdD` | aliases for `a:sla.dec` |
| `a:sla.cfg` | ASCII CFG |
| `a:sla.cfg.json` | CFG JSON |

Targeted symbolic commands:

| Command | Purpose |
|---------|---------|
| `a:sym.explore <target>` | explore paths reaching target |
| `a:sym.solve <target>` | solve concrete input for target |
| `a:sym.state` | show cached symbolic state |

Important:

- Use `a:sym.solve`, not the old `a:sla.sym.solve` spelling.
- Use `a:sla.cfg.json` when you want stable structured assertions.

## Two SSA Block Types

There are two different block types in `r2ssa`:

| Type | Location | Purpose |
|------|----------|---------|
| `SSABlock` | `crates/r2ssa/src/block.rs` | single-instruction SSA block |
| `FunctionSSABlock` | `crates/r2ssa/src/function.rs` | function block with phi nodes |

`r2dec` works with `FunctionSSABlock`.

When writing direct decompiler tests, build `FunctionSSABlock` values directly rather than assuming a convenience constructor exists.

## File Quick Reference

| File | Edit this when... |
|------|--------------------|
| `crates/r2il/src/opcode.rs` | adding or changing IL ops |
| `crates/r2sleigh-lift/src/disasm.rs` | changing P-code lifting or register naming |
| `crates/r2sleigh-lift/src/esil.rs` | changing text or ESIL rendering |
| `crates/r2sleigh-export/src/lib.rs` | changing shared export formatting or action plumbing |
| `crates/r2sleigh-cli/src/main.rs` | changing CLI commands or action/format routing |
| `crates/r2ssa/src/op.rs` | changing SSA operations |
| `crates/r2ssa/src/block.rs` | changing SSA conversion |
| `crates/r2ssa/src/function.rs` | function SSA / phi handling |
| `crates/r2ssa/src/defuse.rs` | changing def-use analysis |
| `crates/r2sym/src/` | changing symbolic execution or taint internals |
| `crates/r2types/src/` | changing type inference |
| `crates/r2types/src/context.rs` | changing typed external context imported from radare2 |
| `crates/r2dec/src/fold/` | changing decompiler folding and lowering |
| `crates/r2dec/src/codegen.rs` | changing C output formatting |
| `r2plugin/src/lib.rs` | changing plugin-side Rust logic and JSON payloads |
| `r2plugin/r_anal_sleigh.c` | changing radare2 callbacks, command help, dispatch |
| `../radare2/libr/include/r_anal.h` | changing the typed function/base-type collector API used by the plugin |
| `../radare2/libr/anal/fcn.c` | implementing typed function-context collection |
| `../radare2/libr/anal/type.c` | implementing typed base-type collection / parity with `tsj` |
| `tests/r2r/Makefile` | changing r2r harness setup or fixture linking |
| `tests/r2r/db/extras/` | adding or updating snapshot regressions |
| `tests/e2e/README.md` | checking when to use Rust E2E vs `r2r` |
| `tests/e2e/integration_tests.rs` | legacy semantic/FFI coverage, not the default for new snapshots |

## Gotchas

1. x86/x86-64 lifting still expects 16 bytes minimum.
2. ESIL subtraction must use ASCII `-`, not Unicode minus.
3. `Const` means literal; `Unique` means temporary SSA-like storage, not memory.
4. Width mismatches usually need explicit sign/zero extension.
5. Register aliasing needs deterministic policy in output and recovery.
6. `#[no_mangle]` is now `#[unsafe(no_mangle)]` under Rust 2024.
7. Plugin, CLI, and export crate feature matrices are not identical.
8. Prefer `a:sla.cfg.json`, `a:sla.types`, and `jq`-normalized checks over raw pretty-printed output in snapshots.
9. Use `r2dec/address.rs::parse_address_from_var_name()` for consistent `const:` / `ram:` parsing.
10. Taint summaries intentionally filter noisy stack/frame-pointer labels.
11. If you add a new fixture binary, remember both the build step and the `tests/r2r/bins/` symlink step.
12. If output stability matters, assume hash-order nondeterminism is a bug. Use deterministic ordering in SSA facts, decompiler facts, and local naming.
13. On the decompiler/type path, tests may now see `r2types::CTypeLike` rather than a local `r2dec` type wrapper. Do not reintroduce `r2dec` type ownership just to make an old test compile.

## Useful References

- `README.md` for current build and testing quick-start
- `tests/e2e/README.md` for the split between `r2r` and Rust E2E
- `doc/` for IL, SSA, ESIL, decompiler, taint, symex, and type-system notes
- radare2 ESIL docs: <https://book.rada.re/disassembling/esil.html>
- Ghidra P-code reference: <https://ghidra.re/courses/languages/html/pcoderef.html>
