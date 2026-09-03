# Pinned binaries

Two programs the repository ships as bytes rather than as sources to rebuild.
They are compiled from `tests/corpus/branchy.c` and `tests/corpus/hashes.c` with
GCC 13.3.0 on Linux x86-64, at `-O0` and `-O2` respectively, with
`-g0 -fno-pie -no-pie`.

They exist for two reasons the compiled corpus cannot serve.

The corpus is built by clang on the machine running the gate, so its cells move
when the compiler moves, and the coverage report invalidates them when the
compiler string differs from the baseline's. These do not move: the bytes are
in the repository, so the same cell means the same program on every machine and
in continuous integration. That is what makes them the gating population.

They are also the only GCC-built code the gate measures. Every other compiled
cell comes from clang, and the benchmark this project is measured against uses
GCC, so a defect that only appears in GCC's output would otherwise reach the
benchmark before it reached a gate.

The system-binary sweep is the complement to these: real foreign code, but
whatever the machine happens to have, so it is measured and reported and never
gates. Rebuild these only deliberately, and re-bless the coverage baseline in
the same commit when you do.
