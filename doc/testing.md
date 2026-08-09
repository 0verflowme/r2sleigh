Testing Strategy
================

Overview
--------

r2sleigh has approximately 200 tests across 7 crates plus an end-to-end
integration test suite. All new features require tests.

Test Levels
-----------

### Unit Tests

Each crate has inline test modules:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_my_feature() {
        // ...
    }
}
```

Run with:

```bash
cargo test --all-features
```

### Integration Tests (tests/e2e/)

End-to-end tests run radare2 with the plugin installed and validate output.
Located in tests/e2e/integration_tests.rs.

Run with:

```bash
cd tests/e2e
cargo test
```

### Snapshot Tests (tests/r2r/)

Fast deterministic regression checks using `r2r` with diffable expectations.

Run with:

```bash
make -C tests/r2r run
```

The `tests/r2r` harness installs the plugin with `all-archs` by default so
running snapshots does not clobber a local ARM/RISC-V capable plugin install.
Override with `R2R_RUST_FEATURES=...` only when you intentionally want a
reduced backend set.

`tests/r2r` is preferred for stable command output checks (`a:sla.info/json/regs/mem/vars`)
and migrated deterministic integration checks from:
- `plugin_status`
- `instruction_analysis` (deterministic slice)
- `function_ssa` / `ssa_opt` (deterministic slice)
- `cfg`
- `slicing` (basic deterministic slice)
- stress regression smoke checks
- taint/symbolic/path/interactive-symbolic stable slices
- decompilation guardrail snapshots
- deep radare2 integration smoke checks

Prefer exact normalized snapshots there for stable user-facing output. Use
`tests/r2r/normalize_snapshot.py` and `jq -S -c` to canonicalize cross-platform
noise before snapshotting. Keep structural assertions for high-churn payloads
such as SSA, symbolic execution, taint, and large CFG/DOM JSON.

`tests/e2e` keeps non-snapshot checks (CLI run behavior, direct FFI, and
analysis-quality benchmark thresholds).

### Advisory Semantic Metadata Benchmark

Use the benchmark script to compare semantic output and `aaaa` timing with
semantic metadata enabled vs disabled:

```bash
python3 scripts/bench_semantic_metadata.py \
  --runs 7 \
  --max-overhead-pct 5 \
  --json-out /tmp/semantic-bench.json
```

Default behavior is advisory (always exits `0`) and reports PASS/FAIL in the
output JSON. Use `--strict` to return non-zero on threshold failures.

Test Harness
------------

The e2e harness (tests/e2e/lib.rs) provides:

### r2_cmd(binary, cmd)

Run a radare2 command on a binary. Returns R2Result.

### r2_at_func(binary, func, cmd)

Seek to a function then run a command:

```rust
let result = r2_at_func(vuln_test_binary(), "main", "pdd");
result.assert_ok();
assert!(result.contains("int"));
```

### r2_at_addr(binary, addr, cmd)

Seek to an address then run a command.

### R2Result

```rust
pub struct R2Result {
    pub stdout: String,
    pub stderr: String,
    pub exit_code: Option<i32>,
    pub crashed: bool,
    pub panicked: bool,
}
```

Methods:
- assert_ok() -- panics if crashed or panicked
- contains(pattern) -- check stdout/stderr for string
- contains_all(patterns) -- all patterns present
- contains_any(patterns) -- any pattern present
- parse_json::<T>() -- deserialize stdout as JSON

Test Binaries
-------------

### vuln_test.c

Located at tests/e2e/vuln_test.c. Contains test functions exercising
specific patterns. Each function is a numbered test case selected via
main()'s switch statement.

Compile:

```bash
gcc -O0 -g -fno-stack-protector -no-pie -o vuln_test vuln_test.c
```

### Adding a Test Pattern

1. Add a function to vuln_test.c:

```c
int test_my_pattern(int x) {
    // Pattern that exercises the feature
    return x * 2;
}
```

2. Add to main() switch:

```c
case N:
    result = test_my_pattern(atoi(argv[2]));
    break;
```

3. Recompile the binary.

4. Add integration test:

```rust
#[test]
fn test_my_pattern() {
    let result = r2_at_func(vuln_test_binary(), "test_my_pattern", "pdd");
    result.assert_ok();
    assert!(result.contains("expected_output"));
}
```

What to Test for Each Feature
-----------------------------

New opcode:
  - Unit test in crate
  - r2r test via a:sla.json when output is deterministic
  - e2e semantic assertion if structure/churn requires richer parsing

New plugin command:
  - r2r exact normalized snapshot for deterministic user-facing output
  - e2e test for semantic/edge-case behavior where snapshots are brittle

New optimization pass:
  - Unit test in r2ssa with before/after SSA
  - e2e test via a:sla.ssa.func.opt

Bug fix:
  - Regression test reproducing the original bug

Decompiler change:
  - r2r exact normalized full snapshot via `pdd` only for an exact source-backed fixture
  - e2e only when decompiler behavior needs semantic parsing instead of snapshot diffs

Test Coverage Checklist
-----------------------

Before committing:

1. cargo build --features x86 succeeds
2. cargo test --features x86 passes
3. make -C tests/r2r run passes (for deterministic plugin-output changes)
4. cd tests/e2e && cargo test passes (for semantic/ffi/high-churn plugin changes)
5. New feature has at least one test
6. Edge cases are covered (empty input, large input, error paths)
