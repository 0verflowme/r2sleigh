r2sleigh
========

Sleigh-to-r2il compiler and radare2 analysis plugin. Converts Ghidra P-code
processor specifications into a typed intermediate language suitable for binary
analysis, SSA transformation, decompilation, symbolic execution, and taint
analysis.

```
.sla (Ghidra) --> libsla --> P-code --> r2il --> ESIL (radare2)
                                          |
                                          +--> SSA (r2ssa) --> Taint / Symbolic (r2sym)
                                          |
                                          +--> Decompiler (r2dec) --> C code
                                          |
                                          +--> Type Inference (r2types)
```

Features
--------

- Pure Rust (edition 2024) using `libsla` (Ghidra native bindings)
- Strongly-typed intermediate language (r2il) with 60+ opcodes
- SSA transformation with dominator tree, phi nodes, and optimization pipeline
- Constraint-based type inference with struct/signature support
- Decompiler producing C code with expression folding, control flow structuring,
  for-loop/switch detection, string literals, and symbol resolution
- Z3-backed symbolic execution with path exploration
- SSA-based taint analysis with automatic radare2 integration
- radare2 plugin with 20+ commands, automatic analysis hooks, and ESIL output
- CLI tool for standalone Sleigh compilation and disassembly

Quick Start
-----------

### Build the CLI

```bash
cargo build --release -p r2sleigh-cli --features x86
```

### Build and install the radare2 plugin

```bash
cd r2plugin
make RUST_FEATURES=all-archs install
```

For a smaller build, you can still choose one architecture (for example, `RUST_FEATURES=x86`).

### First commands

```bash
# CLI: disassemble bytes
r2sleigh disasm --arch x86-64 --bytes "4889e500000000000000000000000000"

# CLI: one-liner instruction export (action + format)
r2sleigh run --arch x86-64 --bytes "31c00000000000000000000000000000" --action lift --format r2cmd

# Plugin: decompile a function
r2 -qc 'aaa; s main; a:sla.dec' /bin/ls

# Plugin: SSA form
r2 -qc 'aaa; s main; a:sla.ssa' /bin/ls

# Plugin: taint analysis
r2 -qc 'aaa; s main; a:sla.taint' /bin/ls
```

Supported Architectures
-----------------------

| Architecture | Feature Flag | Status |
|--------------|-------------|--------|
| x86-64       | `x86`       | Working |
| x86 (32-bit) | `x86`      | Working |
| ARM          | `arm`       | Available |
| RISC-V 64    | `riscv`     | Available |
| RISC-V 32    | `riscv`     | Available |
| MIPS         | `mips`      | Available |

Project Structure
-----------------

| Crate | Purpose |
|-------|---------|
| `r2il` | Core IL types: `Varnode`, `SpaceId`, `R2ILOp`, `R2ILBlock` |
| `r2sleigh-lift` | Sleigh/P-code to r2il translation, ESIL formatting |
| `r2sleigh-export` | Unified instruction exporter (lift/ssa/defuse/dec) |
| `r2sleigh-cli` | CLI: compile, disasm, info commands |
| `r2ssa` | SSA: CFG, dominator tree, phi nodes, optimization, taint |
| `r2sym` | Symbolic execution: Z3 solver, path exploration |
| `r2types` | Type inference: constraint solver, signatures, struct shapes |
| `r2dec` | Decompiler: expression folding, structuring, codegen |
| `r2plugin` | radare2 plugin: Rust cdylib + C wrapper |

Documentation
-------------

| Document | Description |
|----------|-------------|
| [BUILDING.md](BUILDING.md) | Build instructions, installation, troubleshooting |
| [CONTRIBUTING.md](CONTRIBUTING.md) | How to contribute, code style, PR guidelines |
| [DEVELOPERS.md](DEVELOPERS.md) | Architecture overview, module map, how to extend |
| [ROADMAP.md](ROADMAP.md) | Planned features and priorities |
| [doc/r2il.md](doc/r2il.md) | Intermediate language design |
| [doc/ssa.md](doc/ssa.md) | SSA construction and optimization |
| [doc/decompiler.md](doc/decompiler.md) | Decompiler pipeline |
| [doc/esil.md](doc/esil.md) | ESIL generation |
| [doc/taint.md](doc/taint.md) | Taint analysis |
| [doc/symex.md](doc/symex.md) | Symbolic execution |
| [doc/plugin.md](doc/plugin.md) | radare2 plugin and commands |
| [doc/plugin-rfe-2026.md](doc/plugin-rfe-2026.md) | plugin feature and integration RFE |
| [doc/types.md](doc/types.md) | Type inference |
| [doc/testing.md](doc/testing.md) | Testing strategy |

Testing Quick Commands
----------------------

```bash
# Plugin regression suite
make -C tests/r2r run

# Rust non-snapshot integration suite
cd tests/e2e && cargo test
```

CLI `run` Action/Format Matrix
------------------------------

- `lift`: `json`, `text`, `esil`, `r2cmd`
- `ssa`: `json`, `text`
- `defuse`: `json`, `text`
- `dec`: `c_like`, `json`, `text`

`r2cmd` emits replay lines with sidecar JSON comments:

```text
# {"op_index":0,"op":"Copy","op_json":{"Copy":{...}}}
ae <esil_expression>
```

R2IL Format / Endianness / Memory Semantics
-------------------------------------------

- `FORMAT_VERSION` is now `4`.
- Saving emits v4 (`postcard` encoding).
- Optional legacy loader support for v1/v2/v3 (`bincode` encoding) is available via the `r2il/legacy-bincode` feature.
- Legacy v1/v2 files are auto-upgraded in memory on load when legacy support is enabled.
- Legacy bool endianness remains as compatibility shim (`big_endian` / `r2il_is_big_endian`), while canonical fields are:
  - `instruction_endianness`
  - `memory_endianness`
- Memory semantics baseline includes explicit ops and ordering:
  - `Fence`
  - `LoadLinked` / `StoreConditional`
  - `AtomicCAS`
  - `LoadGuarded` / `StoreGuarded`

Compatibility Guarantees
------------------------

- `.r2il` writer emits format version `v4`.
- `.r2il` reader supports `v4` by default.
- Reading legacy `v1`/`v2`/`v3` artifacts requires enabling `r2il/legacy-bincode`.
- With legacy support enabled, loading v1/v2 artifacts upgrades fields in memory while preserving behavior.
- Instruction export action/format compatibility is strict and validated:
  - `lift`: `json`, `text`, `esil`, `r2cmd`
  - `ssa`: `json`, `text`
  - `defuse`: `json`, `text`
  - `dec`: `c_like`, `json`, `text`
- Unsupported action/format pairs fail explicitly (no silent fallback).

Requirements
------------

- Rust 1.85+ (edition 2024)
- radare2 (for plugin)
- pkg-config (for plugin build)
- Z3 (for symbolic execution, optional)

License
-------

LGPL-3.0-only
