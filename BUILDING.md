Building r2sleigh
=================

Prerequisites
-------------

| Dependency | Version | Notes |
|------------|---------|-------|
| Rust | 1.85+ | Edition 2024; install via [rustup](https://rustup.rs/) |
| radare2 | 5.9+ | Required for plugin build and integration tests |
| pkg-config | any | Used to locate radare2 headers and libraries |
| GCC / Clang | any | C compiler for the plugin wrapper |
| Z3 | 4.8+ | Optional; required for symbolic execution (`r2sym`) |

### Verifying radare2 installation

```bash
# Confirm radare2 is installed and pkg-config can find it
pkg-config --cflags r_anal
r2 -H R2_USER_PLUGINS
```

Building the CLI Tool
---------------------

The CLI tool (`r2sleigh-cli`) operates standalone, without radare2.

```bash
# Build with x86 support (default)
cargo build --release -p r2sleigh-cli --features x86

# Build with all supported architectures
cargo build --release -p r2sleigh-cli --features all-archs

# Verify
cargo run --release -p r2sleigh-cli --features x86 -- \
  disasm --arch x86-64 --bytes "31c0000000000000000000000000000000"
```

### Feature Flags

| Flag | Architectures | Notes |
|------|--------------|-------|
| `x86` | x86, x86-64 | Most common; includes 16/32/64-bit modes |
| `arm` | ARM (32-bit) | ARM v7 and earlier |
| `mips` | MIPS | Big and little endian |
| `riscv` | RISC-V (RV32GC, RV64GC) | Little-endian baseline |
| `all-archs` | All of the above | Larger binary, longer compile |

Building the radare2 Plugin
----------------------------

The plugin consists of a Rust cdylib (`libr2sleigh_plugin.so`) and a C wrapper
that implements radare2's `RAnalPlugin` / `RArchPlugin` interfaces.

```bash
cd r2plugin

# Build release with x86 (default)
make

# Build a fast debug version for local iteration
make RUST_TARGET=debug

# Build with all architectures
make RUST_FEATURES=all-archs

# Build maximum-optimized distributable artifacts
make RUST_TARGET=dist
```

### Make Targets

| Target | Description |
|--------|-------------|
| `make` | Build both analysis and architecture plugins (release) |
| `make rust` | Build only the Rust library |
| `make install` | Copy plugins to `R2_USER_PLUGINS` directory |
| `make uninstall` | Remove plugins from `R2_USER_PLUGINS` directory |
| `make clean` | Remove build artifacts |
| `make distclean` | Remove all artifacts including Rust `target/` |

### Make Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `RUST_TARGET` | `release` | `debug`, `release`, or `dist` |
| `RUST_FEATURES` | `x86` | Sleigh feature flags |

Installation
------------

```bash
cd r2plugin
make install
```

This copies three files to `~/.local/share/radare2/plugins/`:

- `anal_sleigh.so` -- analysis plugin
- `arch_sleigh.so` -- architecture plugin
- `libr2sleigh_plugin.so` -- Rust shared library

### Verifying installation

```bash
# Check plugin loads
r2 -qc 'L' /bin/ls | grep sleigh

# Check architecture detection
r2 -qc 'a:sla.info' /bin/ls
```

Uninstallation
--------------

```bash
cd r2plugin
make uninstall
```

Running Tests
-------------

```bash
# Unit tests (all crates)
cargo test --all-features

# Integration tests (requires radare2 + plugin installed)
cd tests/e2e
cargo test
```

For advisory semantic metadata/performance checks (non-blocking by default):

```bash
python3 scripts/bench_semantic_metadata.py --runs 7 --max-overhead-pct 5
```

See [doc/testing.md](doc/testing.md) for the full testing guide.

Conformance / Compatibility Gate Commands
-----------------------------------------

Run the PR8 hardening gate with:

```bash
cargo test -p r2il
cargo test -p r2sleigh-export --features x86
cargo test -p r2sleigh-cli --features x86,arm,riscv
cargo test -p r2sleigh-plugin --features x86,arm,riscv
cd tests/e2e && cargo test --test integration ffi::
cargo clippy --all-targets --all-features -- -D warnings
```

R2IL Format Compatibility
-------------------------

- The sole format identity is `R2PSTC05`; there is no separate format-version authority.
- The loader accepts exactly `R2PSTC05 || payload_length_u64_le || postcard(ArchSpec)` and rejects truncation or trailing bytes.
- Older versions and encodings are rejected instead of being migrated through a second semantic path.

Troubleshooting
---------------

### `pkg-config` cannot find radare2

Set `PKG_CONFIG_PATH` to the directory containing `r_anal.pc`:

```bash
export PKG_CONFIG_PATH=/usr/local/lib/pkgconfig:$PKG_CONFIG_PATH
```

### Plugin loads but commands fail

Ensure the Rust shared library is in the same directory as the C plugin:

```bash
ls $(r2 -H R2_USER_PLUGINS)
# Should show: anal_sleigh.so  arch_sleigh.so  libr2sleigh_plugin.so
```

### "16 bytes minimum" error

libsla requires at least 16 bytes of input for x86-64 (variable-length
instructions). Pad shorter inputs with zeros:

```bash
r2sleigh disasm --arch x86-64 --bytes "31c0000000000000000000000000000000"
```

### Architecture not detected

The plugin reads `anal.arch` and `anal.bits` from radare2. If auto-detection
fails, set them explicitly:

```bash
r2 -qc 'e anal.arch=x86; e anal.bits=64; aaa; s main; a:sla.dec' /bin/ls
```

Or override with the plugin command:

```bash
r2 -qc 'a:sla.arch x86-64; aaa; s main; a:sla.dec' /bin/ls
```

### Build fails with linker errors

Ensure both radare2 development headers and the C++ standard library are
available:

```bash
# Debian/Ubuntu
sudo apt install radare2-dev libstdc++-dev

# Fedora
sudo dnf install radare2-devel libstdc++-devel
```

Release And Dist Builds
-----------------------

The workspace `release` profile is tuned for normal local and CI iteration:
optimized code, parallel codegen, abort-on-panic, and stripped artifacts.
Use `dist` only when a maximum-optimized distributable artifact is worth the
extra link time.

```toml
[profile.release]
lto = false
codegen-units = 16
panic = "abort"
strip = true

[profile.dist]
inherits = "release"
lto = true
codegen-units = 1
```

Examples:

```bash
cargo build --release -p r2sleigh-plugin --features x86
cargo build --profile dist -p r2sleigh-plugin --features all-archs
make -C r2plugin RUST_TARGET=dist RUST_FEATURES=all-archs
```
