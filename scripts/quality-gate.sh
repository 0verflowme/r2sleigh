#!/usr/bin/env bash
set -Eeuo pipefail

usage() {
    cat <<'EOF'
Usage: scripts/quality-gate.sh [--dry-run] [--strict-dylint]

Runs the rewrite quality gate from the r2sleigh repository root.

Phases:
  1. Tool availability checks
  2. Dependency checks: cargo machete, cargo +nightly udeps
  3. Formatting and Clippy
  4. Local Dylint lint: tools/dylints/r2sleigh_lints
  5. Focused Kani harnesses already present in the repo
  6. Targeted cargo mutants for crates/r2ssa/src/var.rs

Environment:
  R2SLEIGH_MUTANTS_JOBS     Jobs for cargo mutants, default: 2
  R2SLEIGH_MUTANTS_TIMEOUT  Global cargo mutants timeout seconds, default: 300
  R2SLEIGH_STRICT_DYLINT    Set to 1 to deny Dylint warnings
EOF
}

dry_run=0
strict_dylint="${R2SLEIGH_STRICT_DYLINT:-0}"
while [ "$#" -gt 0 ]; do
    case "$1" in
        --dry-run)
            dry_run=1
            ;;
        --strict-dylint)
            strict_dylint=1
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "error: unknown argument: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
    shift
done

script_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
repo_root="$(CDPATH= cd -- "$script_dir/.." && pwd -P)"
cd "$repo_root"

phase_index=0

phase() {
    phase_index=$((phase_index + 1))
    printf '\n==> [%d] %s\n' "$phase_index" "$1"
}

quote_command() {
    local arg
    printf '+'
    for arg in "$@"; do
        printf ' %q' "$arg"
    done
    printf '\n'
}

run() {
    quote_command "$@"
    if [ "$dry_run" -eq 0 ]; then
        "$@"
    fi
}

missing_count=0

missing_tool() {
    missing_count=$((missing_count + 1))
    printf 'missing: %s\n' "$1" >&2
    printf 'install: %s\n' "$2" >&2
}

require_file() {
    if [ ! -f "$1" ]; then
        echo "error: required file not found: $1" >&2
        exit 1
    fi
}

require_pattern() {
    local pattern="$1"
    local file="$2"
    if ! grep -Fq "$pattern" "$file"; then
        echo "error: expected pattern not found in $file: $pattern" >&2
        exit 1
    fi
}

require_command() {
    local name="$1"
    local install="$2"
    if ! command -v "$name" >/dev/null 2>&1; then
        missing_tool "$name" "$install"
    fi
}

require_cargo_command() {
    local label="$1"
    local install="$2"
    shift 2
    if ! "$@" >/dev/null 2>&1; then
        missing_tool "$label" "$install"
    fi
}

require_rustup_toolchain() {
    local toolchain="$1"
    local install="$2"
    if ! rustup run "$toolchain" rustc --version >/dev/null 2>&1; then
        missing_tool "rustup toolchain $toolchain" "$install"
    fi
}

require_rustup_component() {
    local toolchain="$1"
    local component="$2"
    local install_component="${3:-$component}"
    if ! rustup component list --toolchain "$toolchain" --installed 2>/dev/null \
        | grep -Eq "^${component}(-|$)"; then
        missing_tool "$component component for $toolchain" \
            "rustup component add $install_component --toolchain $toolchain"
    fi
}

phase "Tool availability checks"
require_file Cargo.toml
require_file tools/dylints/r2sleigh_lints/Cargo.toml
require_file tools/dylints/r2sleigh_lints/rust-toolchain
require_file crates/r2il/src/memory.rs
require_file crates/r2ssa/src/var.rs
require_file crates/r2types/src/lattice.rs

require_pattern "contains_interval_matches_half_open_math" crates/r2il/src/memory.rs
require_pattern "next_version_is_checked_and_monotonic" crates/r2ssa/src/var.rs
require_pattern "integer_meet_shape_is_sound" crates/r2types/src/lattice.rs

require_command cargo "install Rust from https://rustup.rs/"
require_command rustup "install Rust from https://rustup.rs/"
require_command cargo-machete "cargo install cargo-machete"
require_command cargo-udeps "cargo install cargo-udeps --locked"
require_command cargo-fmt "rustup component add rustfmt"
require_command cargo-clippy "rustup component add clippy"
require_command cargo-dylint "cargo install cargo-dylint dylint-link"
require_command dylint-link "cargo install cargo-dylint dylint-link"
require_command cargo-kani "cargo install --locked kani-verifier"
require_command cargo-mutants "cargo install --locked cargo-mutants"

require_cargo_command "cargo machete" "cargo install cargo-machete" cargo machete --version
require_rustup_toolchain nightly "rustup toolchain install nightly"
require_cargo_command "cargo +nightly udeps" \
    "rustup toolchain install nightly && cargo install cargo-udeps --locked" \
    cargo +nightly udeps --version
require_cargo_command "cargo fmt" "rustup component add rustfmt" cargo fmt --version
require_cargo_command "cargo clippy" "rustup component add clippy" cargo clippy --version
require_cargo_command "cargo dylint" "cargo install cargo-dylint dylint-link" cargo dylint --version
require_cargo_command "cargo kani" "cargo install --locked kani-verifier" cargo kani --version
require_cargo_command "cargo mutants" "cargo install --locked cargo-mutants" cargo mutants --version

dylint_toolchain="$(
    sed -n 's/^[[:space:]]*channel[[:space:]]*=[[:space:]]*"\([^"]*\)".*/\1/p' \
        tools/dylints/r2sleigh_lints/rust-toolchain
)"
if [ -z "$dylint_toolchain" ]; then
    echo "error: could not read Dylint toolchain channel" >&2
    exit 1
fi
require_rustup_toolchain "$dylint_toolchain" \
    "rustup toolchain install $dylint_toolchain --component rustc-dev --component llvm-tools-preview"
require_rustup_component "$dylint_toolchain" rustc-dev
require_rustup_component "$dylint_toolchain" llvm-tools llvm-tools-preview

if [ "$missing_count" -ne 0 ]; then
    echo "error: missing quality-gate tools; install them before rerunning" >&2
    exit 127
fi

phase "Dependency checks"
run cargo machete --with-metadata --skip-target-dir
run cargo +nightly udeps --workspace --all-targets --features x86

phase "Formatting and Clippy"
run cargo fmt --all -- --check
run cargo clippy --workspace --all-targets --features x86 -- -D warnings

phase "Local Dylint lint"
if [ "$strict_dylint" -eq 1 ]; then
    dylint_rustflags="-D warnings"
    if [ -n "${DYLINT_RUSTFLAGS:-}" ]; then
        dylint_rustflags="${DYLINT_RUSTFLAGS} ${dylint_rustflags}"
    fi
    run env DYLINT_RUSTFLAGS="$dylint_rustflags" \
        cargo dylint --path tools/dylints/r2sleigh_lints --workspace -- \
        --all-targets --features x86
else
    run cargo dylint --path tools/dylints/r2sleigh_lints --workspace -- \
        --all-targets --features x86
fi

phase "Focused Kani harnesses"
run cargo kani --manifest-path crates/r2il/Cargo.toml \
    --harness contains_interval_matches_half_open_math \
    --output-format terse
run cargo kani --manifest-path crates/r2ssa/Cargo.toml \
    --harness next_version_is_checked_and_monotonic \
    --output-format terse
run cargo kani --manifest-path crates/r2ssa/Cargo.toml \
    --harness data_ref_mask_to_bits_is_total_and_bounded \
    --output-format terse
run cargo kani --manifest-path crates/r2types/Cargo.toml \
    --harness integer_meet_shape_is_sound \
    --output-format terse
run cargo kani --manifest-path crates/r2types/Cargo.toml \
    --harness rendered_expression_policy_authority_is_fail_closed_for_unresolved_callsites \
    --output-format terse

phase "Targeted cargo mutants for r2ssa var"
mutants_jobs="${R2SLEIGH_MUTANTS_JOBS:-2}"
mutants_timeout="${R2SLEIGH_MUTANTS_TIMEOUT:-300}"
run cargo mutants --no-config \
    --manifest-path crates/r2ssa/Cargo.toml \
    --file crates/r2ssa/src/var.rs \
    --baseline run \
    --jobs "$mutants_jobs" \
    --timeout "$mutants_timeout" \
    --no-times \
    --output target/quality-gate/mutants-r2ssa-var

if [ "$dry_run" -eq 1 ]; then
    printf '\nquality gate dry run complete\n'
else
    printf '\nquality gate passed\n'
fi
