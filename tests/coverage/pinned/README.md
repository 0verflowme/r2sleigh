# Pinned binaries

Two programs the repository ships as bytes rather than as sources to rebuild.
They are compiled from `tests/corpus/branchy.c`, `tests/corpus/hashes.c` and
`tests/corpus/shapes.c` with GCC 13.3.0 on Linux x86-64, at `-O0`, `-O2` and
`-O0` respectively, with `-g0 -fno-pie -no-pie`.

`shapes_gcc_x64_O0` was added after a change passed the fifty-four-cell corpus
at 54 of 54, with the differential agreeing against a source-built oracle, and
rendered **nothing at all** on Linux ELF: zero of fifteen functions on the
benchmark binary. The two other pinned programs did not catch it, because they
are compiled from sources whose functions barely call anything, and the defect
was at the call boundary. Fifty-two of their sixty-eight functions kept
rendering while the platform was completely broken.

So the third program is deliberately the call-heavy one. `shapes.c` exists to
exercise what the hash corpus cannot -- variadic calls at differing argument
counts, calls in sequence with address-taken locals read after each, direct and
mutual recursion, a struct returned across two registers, a call through a
function pointer -- and compiled for ELF it is the only local gate that would
have failed on that change.

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
