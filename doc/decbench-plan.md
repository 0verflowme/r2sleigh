Where r2sleigh stands against DecBench, and what it would take
==============================================================

DecBench (decbench.com, Noelo Lab / University of Georgia) ranks decompilers by
how often they recover source *exactly*. Three metrics, each scored as the
percentage of functions on which a decompiler is perfect, plus a Union score for
being perfect on at least one:

1. **Structural correctness** -- graph edit distance between the source CFG and
   the decompiled CFG, via `cfgutils`.
2. **Type correctness** -- decompiled variable and signature types against the
   binary's DWARF.
3. **Recompilation bytematch** -- recompile the decompiled function with the
   original toolchain and flags, compare assembly by Jaccard similarity over
   normalised operands.

Published standings: Codex 53.9, Claude Code 46.9, angr 28.4 (best conventional
decompiler). The default dataset is unoptimised, roughly 34k functions, with a
250-function `sample-set` and an evaluation kit for submissions.

What we have actually measured
------------------------------

Nothing on their dataset. Every number below is from binaries built here, and
the gap between "our corpus" and "their corpus" is exactly the kind of gap this
project's history says to distrust. Getting a real score is the first task, not
the last.

**Coverage, on the population DecBench uses.** Their default set is
unoptimised, and it is x86-64 ELF. Building `tests/corpus/branchy.c` as an
x86-64 ELF object at `-O0` and sweeping every function: **30 of 33 render, 90
per cent**, against 78 per cent across our own six-configuration corpus and 27
per cent of the real functions in `/bin/ls`. The format is not a blocker and the
unoptimised case is our best one. Our headline numbers come from arm64e Mach-O,
which DecBench does not use.

**Metric 1, structure.** Plausibly our strongest. We build structured regions
and refuse rather than emit a goto, so where we render, the CFG is a real
`if`/`else`/loop tree rather than a linearisation. Unmeasured against
`cfgutils`.

**Metric 2, types.** Near zero, by design and by construction.
`recover_interface` says it outright: every parameter is an unsigned integer of
the register's own width, and "signedness, pointer-ness and names are never
asserted". `int gate_one(int q)` renders as
`uint64_t sym_gate_one(uint64_t EDI_0)`, with locals named `tmp_6a80_1`,
`stack_m16` and `ZF_1`. None of that matches DWARF. The plugin also refuses to
ingest DWARF during analysis on purpose, which is right -- the ground truth must
not be an input -- but it means the types have to be *inferred*, and today they
are declined instead.

**Metric 3, bytematch.** The output compiles: a rendered function needs only
`#include <stdint.h>` added. It does not match. `gate_one` is 37 bytes and about
ten instructions in the original; recompiling our C at the same flags gives 131
bytes. The excess is machine detail we render faithfully -- condition-flag
variables, one temporary per p-code value, stack slots as pseudo-locals, and
`r2sleigh_int_sborrow_*` helper calls.

So the Union score today would come almost entirely from structure, on the
functions we render.

What it would take
------------------

**Stage 0 -- get measured.** Build a harness under `decbench/decompilers/raw`,
or take the 250-function evaluation kit. Until that runs, every line above is
inference. This project has had a stated fact overturned by a measurement three
times; do not plan past this step.

**Stage 1 -- stop rendering the machine.** One change fixes most of both weak
metrics, and it is ordinary output-quality work rather than a change of
principle. Fold flag computations into the comparison that consumes them, so
`ZF_1 = (a - b) == 0; if (!ZF_1)` becomes `if (a != b)`; that removes the flag
variables, most temporaries, and the arithmetic-helper calls on common paths.
Collapse the unoptimised stack round trip, where a parameter is spilled and
immediately reloaded, using the carrier machinery that already exists. Both are
protected by the corpus differential oracle.

**Stage 2 -- infer types rather than declining to.** This one needs a decision,
because it is in tension with the project's refusal-first stance: a metric that
scores type *correctness* gives declining to answer and answering wrong the same
score. The principle survives if inference is evidence-based -- a value used as a
load address is a pointer, a signed comparison proves signedness, the width of an
access proves the width -- and everything unproven keeps today's honest default.
Signatures first: the return type and the parameter types are what the metric
weights, and `r2types` exists for this.

**Stage 3 -- coverage on real unoptimised code.** Ninety per cent on a
thirty-three function object is not 34k functions of coreutils. Measure, then
take the causes in the order the measurement gives.

**Stage 4 -- the two mapped features.** The composed return value (the largest
cause in our own gate) and rendering a direct tail call. Both are written up in
`doc/handoff-location-ssa.md` with their blockers named.

An honest target
----------------

Beating angr's 28.4 looks reachable on structure alone if coverage on their set
holds near what we see at `-O0`. Beating the LLMs at 47-54 needs Stage 2, and
Stage 2 is a change in what this decompiler is willing to claim. That is a
decision to take deliberately rather than to drift into.
