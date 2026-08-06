# Rewrite Quality Gates

`scripts/quality-gate.sh` is the local quality gate for rewrite work. It is
deliberately conservative: a missing tool is a failed gate with an install
hint, not a skipped check.

Run it from the repository root:

```bash
scripts/quality-gate.sh
```

To inspect the command sequence without running the expensive phases:

```bash
scripts/quality-gate.sh --dry-run
```

To make existing Dylint findings fatal for a cleaned slice:

```bash
scripts/quality-gate.sh --strict-dylint
```

## Scope

The gate owns tooling only. It does not change Cargo manifests, Rust sources, or
the radare2 seam. It is meant to catch rewrite regressions before broader
workspace and plugin validation.

The current phases are:

1. Tool availability checks.
2. Dependency checks with `cargo machete --with-metadata --skip-target-dir` and
   `cargo +nightly udeps --workspace --all-targets --features x86`.
3. Formatting and linting with `cargo fmt --all -- --check` and
   `cargo clippy --workspace --all-targets --features x86 -- -D warnings`.
4. Local Dylint linting through `tools/dylints/r2sleigh_lints`.
5. Focused Kani proofs already present in `r2il`, `r2ssa`, and `r2types`.
6. Targeted mutation testing for `crates/r2ssa/src/var.rs`.

## Required Tools

Install the optional gate tools explicitly:

```bash
cargo install cargo-machete
cargo install cargo-udeps --locked
cargo install cargo-dylint dylint-link
cargo install --locked kani-verifier
cargo install --locked cargo-mutants
rustup toolchain install nightly
rustup component add rustfmt clippy
rustup toolchain install nightly-2026-04-16 \
  --component rustc-dev \
  --component llvm-tools-preview
```

The pinned Dylint toolchain comes from
`tools/dylints/r2sleigh_lints/rust-toolchain`; update that file only as part of
an intentional Dylint maintenance change.

## Mutation Settings

Mutation testing is intentionally narrow and deterministic:

```bash
cargo mutants --no-config \
  --manifest-path crates/r2ssa/Cargo.toml \
  --file crates/r2ssa/src/var.rs \
  --baseline run \
  --jobs 2 \
  --timeout 300 \
  --no-times \
  --output target/quality-gate/mutants-r2ssa-var
```

Use environment variables to tune only local resource usage:

```bash
R2SLEIGH_MUTANTS_JOBS=4 R2SLEIGH_MUTANTS_TIMEOUT=600 scripts/quality-gate.sh
```

## Interpreting Failures

Missing tools fail before the gate starts expensive phases. Install the reported
tool and rerun the script.

`cargo machete` and `cargo udeps` failures require checking whether the
dependency is genuinely unused or used through a pattern that the tool cannot
see.

Dylint warnings are reported by default because the current tree still has
known architectural debt. Use `--strict-dylint` or
`R2SLEIGH_STRICT_DYLINT=1` when a touched slice is clean enough to deny
warnings. A strict failure usually means code is classifying semantic storage
or address facts with string prefixes instead of typed contracts.

Kani failures are proof failures for existing harnesses. Fix the invariant or
tighten the proof; do not delete a harness to make the gate pass.

Surviving mutants in `r2ssa` variable handling mean tests do not pin the
expected behavior tightly enough. Add focused tests before accepting the rewrite.

This gate does not replace the full validation bar in `AGENTS.md`; run the
crate and plugin checks there when the touched subsystem requires it.
