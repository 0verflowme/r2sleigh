# Executable verification of rendered output

This corpus is a regression canary, not the semantic specification. It measures
nine functions at `-O0`, `-O1`, and `-O2` on x86-64 and AArch64: 54 explicit
cells. A missing, duplicate, or unparsable rendering remains a failed cell; it
cannot disappear from the totals.

## Run the complete matrix

From the workspace root:

```bash
# Optional: keep build artifacts outside this worktree.
export CARGO_TARGET_DIR=/absolute/path/to/a/task-specific-target

tests/corpus/run_matrix.sh --gate measurement
```

The script always installs the plugin first and requires the install to print
`Installed to ...`. It then builds all six binaries and source-backed oracle
executables, captures marked `pdd` dumps, verifies all 54 cells, and writes:

```text
tests/corpus/artifacts/
  bin/                 corpus and oracle executables
  dumps/               full marked pdd sessions
  raw/                 exact extracted renderer output
  compile/<config>/    raw and diagnostic compile envelopes
  results/<config>.json
  results/matrix.json
  plugin-install.log
  provenance.txt
```

Artifacts are ignored by Git. Results retain full compiler diagnostics and every
differential input, seed, exit code, and output.

## The three scores

Each of the 54 records always contains three independent measurements.

- **Raw:** Exact emitted declarations and body compiled with `-std=c11`, the
  documented warning set, and `-Werror`. Only the invalid radare2 linkage name
  and mapped image addresses are adapted by the compile envelope; both are
  recorded. Local, parameter, and return declarations remain untouched.
- **Diagnostic:** The historical compatibility transformation compiles and runs
  the legacy input. Every retype, dereference-width assumption, subscript
  rewrite, and mapped address is listed. A pass here is diagnostic evidence, not
  proof that the emitted C is valid.
- **Differential:** The raw executable when it compiles, otherwise the explicitly
  labelled diagnostic executable, is compared with `oracle.c` over empty,
  boundary-length, legacy, deterministic-random inputs, and multiple seeds for
  MurmurHash3 and xxHash.

`oracle.c` includes `hashes.c` after renaming only its demonstration `main`, so
`hashes.c` remains the single semantic implementation of the reference
functions. `reference.txt` is retained as the old one-input record; it is no
longer the differential oracle.

## Raw byte baseline

Stages that should not affect rendering compare the exact raw SHA-256 for every
cell with `raw-baseline-sha256.json`. A missing or mismatched hash is printed in
the `snapshot` score.

Creating or intentionally updating the reviewed baseline is explicit:

```bash
tests/corpus/run_matrix.sh --accept-baseline --gate measurement
```

The gate is always explicit. Use `--gate snapshot` for byte-preserving stages,
`--gate raw` once all emitted C must compile under the strict type tripwire, and
`--gate differential` only when every raw executable must also match the oracle.
The final rewrite gate is deliberately conjunctive:

```bash
tests/corpus/run_matrix.sh --gate cutover
```

It refuses a dirty tracked tree, repeats generation, and requires byte-identical
raw output together with completed binding, effect, placement, and render audits,
strict raw compilation, and the complete raw-backed differential vector set in
all 54 cells.

Before accepting, inspect the raw files and the matrix report. Never update the
manifest merely to make a mechanical stage pass; a changed byte during such a
stage means the change was not mechanical.

## The shape corpus, a second gate

`hashes.c` is nine variations on one program shape: a loop over bytes
accumulating an integer. No struct, no array of structs, no recursion, no
variadic call, no signed division, no multi-word return, no pointer to a
pointer. Three defects found by an external benchmark were invisible to the 54
cells for exactly that reason.

`shapes.c` is a second source with thirteen functions whose shapes the hash
corpus cannot express, and `shapes_oracle.c` includes it the way `oracle.c`
includes `hashes.c`. Every scored function is
`uint64_t shape_*(uint64_t, uint64_t)`, so the harness hands it two integers and
compares one back; the shape under test lives in the body and in the noinline
helpers it calls, which the verifier pulls in transitively from their own
renderings.

```bash
tests/corpus/locked_shapes.sh --gate shapes-measurement
```

It is a separate script with its own gate names, so the 54 hash cells keep
gating merges unchanged. Its results are `results/shapes_<config>.json` and
`results/shapes-matrix.json`, and it prints a per-cell map naming, for every
red cell, the rule that refused. Many cells are red today and that is the point:
the map is the deliverable, and `doc/handoff-location-ssa.md` carries the
current reading of it.

Gates, weakest first:

- `shapes-measurement` -- every cell produced a record. Fails only if the
  harness stopped measuring.
- `shapes-snapshot` -- every rendering matches `raw-baseline-shapes-sha256.json`.
  Opt-in only, and deliberately not implied by the correctness gates: most of
  these cells are refusal comments, and pinning their text would make an
  improvement read as a regression.
- `shapes-raw` -- the emitted C compiles strictly for every cell.
- `shapes-differential` -- every cell agrees with the source-built oracle from a
  raw-backed executable.

Promote a shape by adding its name to `REQUIRED_DIFFERENTIAL` in
`run_shapes.sh` once its six cells pass; when all thirteen are listed,
`shapes-differential` becomes the gate and the list can go. Promote only on
evidence from `locked_shapes.sh`, never a bare invocation.

Adding a function means adding it to `SHAPE_SPECS` in `verify_rendering.py` and
nowhere else: `corpus_names.py` reads the scored functions and helper callees
out of that one table for both the sweep and the run script.

## Accounting and interpretation

Compiling and running output does not prove that its CFG, types, or control flow
are justified. The renderer's internal invariants and obligation ledger remain
the proof surface:

```text
rendered + justified_elision + refused = total obligations
unaccounted = 0
```

`refused` is an explicit failure, not a successful result. Raw compilation is an
external type tripwire; the internal requirement that every surviving `UseSite`
has an upstream-backed exact projection is the width proof.
