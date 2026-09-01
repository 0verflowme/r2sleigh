Whole-binary render coverage
============================

The 54-cell matrix in `tests/corpus` scores nine hand-picked functions and
checks that what they render is *correct*. It is a canary, and it deliberately
says nothing about the other question: how much of a binary renders at all.

That question was answered by hand, and the answer was wrong twice. Once by a
factor of six, because ninety of the hundred and thirty-six entries radare2
lists in `/bin/ls` are sixteen-byte import thunks and were counted as functions.
Once by fourteen refusals, because a number measured in an earlier session was
carried forward instead of remeasured, and a change was credited with an
improvement that was partly not there.

So this gate measures it, over the corpus's own sources built at the same six
configurations. Every function radare2 finds is decompiled -- three hundred and
thirteen of them, against the matrix's fifty-four -- and one bit per function is
recorded, with the typed cause when it did not render.

```
tests/coverage/run_coverage.sh                    # measure and gate
tests/coverage/run_coverage.sh --accept-baseline  # record what it measured
```

What the gate fails on
----------------------

A function that rendered in the baseline and now refuses. That is the only hard
failure, and it is the one the matrix cannot catch: a change can leave all
fifty-four cells matching and still stop a hundred other functions rendering.

A function in the baseline that was not swept also fails, so a sweep that
silently stopped covering something cannot pass.

Everything else is reported and does not fail. A function that now renders, a
function that is new, and a refusal whose cause changed are all printed; the
first two ask to be re-blessed. A cause is normalised before comparison --
counts of refused obligations, and the line numbers inside a refusal's site --
because a baseline that churns on those is a baseline nobody re-blesses
honestly.

Why the compiler is recorded
----------------------------

The binaries are built here, from checked-in sources, by whatever `clang` is on
the path. A different compiler is a different program, and comparing this
baseline against it would be comparing two different function sets. The baseline
carries the compiler's version string and the gate refuses rather than reports a
difference that is not about the decompiler.
