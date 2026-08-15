Contributing to r2sleigh
========================

Thank you for your interest in contributing. This document covers the workflow,
code style, and testing requirements for all contributions.

Reporting Issues
----------------

When reporting a bug, include:

1. **Architecture and binary**: what you were analyzing (e.g., x86-64 ELF)
2. **Command**: the exact radare2 or CLI command that failed
3. **Expected vs actual output**: what you expected and what you got
4. **Version info**: output of `r2 -v` and `cargo --version`

For crashes, include a backtrace if possible:

```bash
RUST_BACKTRACE=1 r2 -qc 'aaa; s main; pdd' /path/to/binary
```

Getting Started
---------------

1. Fork the repository
2. Create a feature branch: `git checkout -b feature/my-change`
3. Make your changes
4. Add tests (see Testing Requirements below)
5. Run the full test suite:
   ```bash
   cargo test --all-features
   cd tests/e2e && cargo test
   ```
6. Open a pull request

Commit Messages
---------------

Use short, descriptive commit messages. Prefix with the affected component:

```
r2il: add FloatCompare opcode
r2ssa: fix phi placement for switch blocks
r2dec: improve for-loop detection heuristic
plugin: add a:sla.newcmd command
tests: add e2e test for taint analysis
docs: update ESIL translation table
```

- First line: imperative mood, max 72 characters
- Body (optional): explain *why*, not *what*

Rust Code Style
---------------

The project uses Rust edition 2024.

### Error handling

- Use `thiserror` for error types
- Return `Result<T, E>` from fallible functions, not `panic!`
- Use `anyhow` only in tests and CLI, not in library crates

### Naming

- Types: `PascalCase`
- Functions/methods: `snake_case`
- Constants: `SCREAMING_SNAKE_CASE`
- Feature flags: lowercase with hyphens (`all-archs`)

### Formatting and lints

```bash
cargo fmt --all
cargo clippy --all-features -- -D warnings
```

### Edition 2024 notes

- Use `#[unsafe(no_mangle)]` instead of `#[no_mangle]`
- Use `unsafe { ... }` blocks inside `unsafe fn` bodies

### Prefer

- `format!()` over string concatenation
- `matches!()` over verbose `match` with `true`/`false` arms
- Exhaustive `match` over `_ =>` catch-all when feasible
- Small, focused functions over large monoliths

Testing Requirements
--------------------

**All new features must have tests.** This is enforced during review.

### What to test

| Change type | Required test |
|-------------|---------------|
| New opcode | Unit test in crate + e2e test via `a:sla.json` |
| New plugin command | e2e test in `tests/e2e/integration_tests.rs` |
| New optimization pass | Unit test in `r2ssa` + e2e test via `a:sla.ssa.func.opt` |
| Bug fix | Regression test reproducing the bug |
| Decompiler change | e2e test via the `pdd` borrowed-snapshot decompiler path |

### Adding a test binary pattern

If your change needs a specific binary pattern to exercise:

1. Add a function to `tests/e2e/vuln_test.c`
2. Add it to the `main()` switch
3. Recompile: `gcc -O0 -g -fno-stack-protector -no-pie -o vuln_test vuln_test.c`

See [doc/testing.md](doc/testing.md) for the full guide.

### Running tests

```bash
# Unit tests
cargo test --all-features

# Integration tests
cd tests/e2e
cargo test

# Specific test
cd tests/e2e
cargo test test_taint_analysis
```

Pull Request Checklist
----------------------

Before submitting a PR, confirm:

- [ ] `cargo build --all-features` succeeds
- [ ] `cargo test --all-features` passes
- [ ] `cargo clippy --all-features -- -D warnings` is clean
- [ ] `cd tests/e2e && cargo test` passes (if plugin-related)
- [ ] New features have tests
- [ ] Commit messages follow the style above
- [ ] Documentation updated if needed (doc/, AGENTS.md)

Code Review
-----------

All PRs are reviewed before merging. Reviewers will check:

- Correctness (does it do what it claims?)
- Test coverage (are edge cases handled?)
- Style consistency (does it match the codebase?)
- Performance (does it avoid unnecessary allocations or O(n^2) patterns?)

License
-------

By contributing, you agree that your contributions are licensed under the
LGPL-3.0-only license, matching the project.
