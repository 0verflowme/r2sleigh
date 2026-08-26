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
