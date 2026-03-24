# E2E Tests for r2sleigh (Rust Semantic/FFI Suite)

Rust-based integration tests for non-snapshot coverage:
- CLI `run` export behavior
- direct plugin FFI ABI checks
- analysis-quality benchmark thresholds

For deterministic command-output diffs, use `tests/r2r`.

## Prerequisites

1. Build the test binaries:
   ```bash
   cd tests/e2e
   gcc -O0 -g -o vuln_test vuln_test.c
   gcc -O0 -g -o test_func test_func.c
   # optional stress corpus binaries used by regression tests
   gcc -O0 -g -o stress_test stress_test.c
   gcc -O2 -g -o stress_test_opt stress_test.c
   ```

2. Build the plugin:
   ```bash
   cargo build --release -p r2plugin
   ```

3. Ensure `r2` is in your PATH with the plugin loaded.

## Running Tests

Snapshot suite:

```bash
make -C tests/r2r run
```

Rust semantic/FFI suite:

From the `tests/e2e` directory:

```bash
cargo test
```

Note: this directory sets `RUST_TEST_THREADS=1` via `tests/e2e/.cargo/config.toml`.
The test harness already serializes `r2` execution with a global mutex, so a
single test thread avoids noisy "running for over 60 seconds" messages from
queued tests.

From the workspace root, use:

```bash
cargo e2e-test
```

Run specific test module:

```bash
cargo test cli_run
cargo test ffi
cargo test analysis_quality_benchmark
```

Run with output:

```bash
cargo test -- --nocapture
```

From workspace root:

```bash
cargo test -p r2sleigh-e2e-tests
```

## Test Structure

| Module | Description |
|--------|-------------|
| `cli_run` | CLI `run` action export regression checks |
| `ffi` | Direct FFI tests against plugin library |
| `analysis_quality_benchmark` | Analysis-quality threshold and coverage metrics |

## When to use Rust E2E vs r2r

- Use `tests/r2r` for deterministic command-output snapshots (`a:sla.*` text/JSON views).
- Prefer exact normalized snapshots there for stable user-facing surfaces such as `a:sla.info`, small `a:sla.*` JSON/text views, signatures, and `a:sla.dec`.
- Keep structural assertions there only for high-churn internals such as SSA, symex, taint, and large CFG/DOM payloads.
- Use `tests/e2e` for:
  - FFI behavior and ABI checks
  - CLI run/export behavior checks
  - analysis quality and performance thresholds
