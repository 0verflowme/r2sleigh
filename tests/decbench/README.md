Getting measured on DecBench
============================

[DecBench](https://decbench.com) ranks decompilers by how often they recover
source *exactly*: control-flow structure by graph edit distance, variable and
signature types against DWARF, and assembly similarity after recompiling with
the original toolchain. Its Union score is the share of functions perfect on at
least one of the three.

We have never been measured on it. `doc/decbench-plan.md` records what was
measured here instead and why that is not the same thing. This directory holds
the harness that closes that gap.

`r2sleigh_raw.py` is a DecBench decompiler backend for this plugin. It belongs
in *their* tree, at `decbench/decompilers/raw/r2sleigh_raw.py`, and is kept here
so the work is not stranded in a scratch directory and so the next person can
see what it assumes about us.

Running it
----------

```
git clone https://github.com/noelo-lab/decbench
python3.12 -m venv venv && venv/bin/pip install -e decbench
cp tests/decbench/r2sleigh_raw.py decbench/decbench/decompilers/raw/
# register it for the decorator side effect
#   decbench/decompilers/raw/__init__.py: add `r2sleigh_raw,` to the import list
venv/bin/decbench list-decompilers     # r2sleigh should read Available: Y
venv/bin/decbench download sample-set --dest data
venv/bin/decbench evaluate-tree data -d r2sleigh -d angr -m ged -m type_match -m byte_match
```

`angr` is worth running alongside: it is the strongest conventional decompiler
on the board at 28.4, and it installs as a plain Python dependency, so it is the
reference point that costs nothing to keep.

What the harness assumes
------------------------

**The plugin must already be installed.** `make -C r2plugin RUST_FEATURES=all-archs
install` first. Availability is probed by checking that `a:sla` actually swaps
radare2's architecture, not merely that `r2` exists — otherwise the harness would
happily benchmark stock r2dec and report it as us.

**One `r2` process per binary.** `aaa` dominates the wall time, so every
requested function is decompiled in a single invocation, split apart by
sentinels printed into the command stream.

**A declined function is omitted, not emitted.** We refuse rather than guess,
and a refusal comment is not decompiled C. Reporting one as if it were would
score a parse failure where the tool actually declined; both are zero on every
metric, and the decline count and its typed causes are kept in the result
metadata so the rate stays visible rather than disappearing into the denominator.


First measured result
---------------------

`bzip2recover`, `-O0`, from DecBench's own dataset — r2sleigh beside angr, the
strongest conventional decompiler on the board:

| metric | r2sleigh | angr |
|---|---|---|
| ged (mean, lower is better) | **5.43** | 5.54 |
| type_match (mean, higher is better) | **0.00** | 0.59 |

Read it with the denominator in view. GED is averaged over the functions each
decompiler actually produced, and we produced seven of the twelve source
functions in that file while declining five; a mean over the subset we were
willing to render is not the same population angr's mean covers. What the number
does establish is that where we render, our control-flow structure is already
competitive with the best conventional decompiler — and that the type metric is
not a small gap but the whole of one.

Three things were needed to get a score at all, and each would have silently
read as zero rather than as a bug:

* `greadlink` on `PATH` (`brew install coreutils`) — without it Joern cannot
  parse the source and GED is skipped, not failed.
* radare2's flag prefixes stripped from function names, so `dbg.readError`
  matches the source's `readError`.
* the same name written into the emitted C, because the decompiled CFG is keyed
  by the function name inside the code, not by the name in the result record.

`byte_match` is still unmeasured here: it recompiles with the original toolchain,
which means a Linux toolchain this harness was not run under.

Running it from this repository
-------------------------------

`run_decbench.sh` does the whole of the above against a Linux host and compares
the result with `baseline.json`, per function and per metric. Its default is the
acceptance population, not a smoke test: every TOML under `projects/sailr` (26
at the time this contract was written), every binary each project produces,
and `O0`, `O1`, and `O2`:

```
tests/decbench/run_decbench.sh                    # full 26 x 3 sweep
tests/decbench/run_decbench.sh --accept-baseline  # merge the sweep into the record

# bounded verification or investigation (selection is printed in the report)
tests/decbench/run_decbench.sh \
  --project bzip2 --project zlib --opt-level O0 --opt-level O1

# deterministic zero-based shards; merge their generated JSON afterward
tests/decbench/run_decbench.sh --shard 0/2
tests/decbench/run_decbench.sh --shard 1/2
python3 tests/decbench/merge_decbench.py \
  --input tests/decbench/artifacts/<first>/function_results.json \
  --input tests/decbench/artifacts/<second>/function_results.json \
  --output tests/decbench/artifacts/function_results.json

# continue checkpoints left by an interrupted invocation
tests/decbench/run_decbench.sh --resume decbench-<timestamp>-<pid>
```

It needs an ssh alias for a Linux x86-64 host with the radare2 fork built and
DecBench installed; `contabo` by default, `--host` or
`R2SLEIGH_DECBENCH_HOST` to change it. The metric recompiles the decompiled
output, so the host's toolchain has to be the one that built the benchmark's
binaries, which is why this cannot run on a developer's Mac.

Two hazards it handles, because both have already cost measurements here.

It installs into a private `HOME` for the run. radare2 reads user plugins from
`$HOME`, so two trees measuring at once otherwise overwrite each other's
library and each scores the other's work.

It appends a unique string to the tree it copies over and refuses to measure
unless that string is in the installed library. `make install` once aborted on
stale object files, left the previous library in place, and DecBench scored it
happily. The numbers came back identical to the baseline, which is exactly what
a change with no effect looks like.

The witness is checked once for every project/optimization cell immediately
before that project's DecBench invocation. The per-cell records are copied into
the local run artifact and their count is asserted before reporting. A resumed
run also checks the tree fingerprint, selection, and DecBench commit before it
is allowed to reuse its private plugin.

One DecBench invocation handles all selected optimization levels for a project.
It therefore builds that project once per required optimization and reuses the
compiled tree for both decompilers instead of rebuilding for separate r2sleigh
and reference passes. The next project starts only after the finished project's
result has been checkpointed; its bulky compiled/decompiled tree is then
removed. This bounds remote disk use by the largest project rather than the
whole sailr set and makes project-level resume possible.

The plugin still has a private `HOME`, but Cargo's target, registry, and rustup
toolchains are shared explicitly. Without that separation each old one-cell run
copied about 2.2 GB into its private home even though the complete bzip2 result
tree was only about 1.6 MB. Successful sweep directories are deleted
automatically. `--gc` audits finished/stale directories and `--gc-force`
removes only those; a current marker and recent interrupted runs remain intact.

Angr is run only when the selected reference cells are absent from
`baseline.json`, when `--refresh-reference` is requested, or when the installed
angr version differs from the version recorded in the baseline. A version
change invalidates the old reference rather than mixing versions. The baseline
keeps angr's per-function values and rendered flags, so ordinary tree sweeps
pay only for r2sleigh. Missing reference cells refresh angr at project
granularity: one incomplete project does not cause completed projects in the
same sweep to rerun angr, while all requested optimization levels still share
that project's single DecBench invocation. Completeness is recorded per metric
and per cell, so adding a metric such as `vj_ged` invalidates only cells that
have never measured it rather than treating an older three-metric row as a
complete reference.

The final cost line measures end-to-end wall time, the peak size of the
garbage-collected run directory, the peak host disk consumption observed while
a project is live, and the retained host disk change. The 26-by-3 projection
uses the observed project/optimization-cell rate and is deliberately labeled an
extrapolation rather than a promise about differently sized projects.

The required metrics are `byte_match`, `ged`, `vj_ged`, and `type_match`.
Current DecBench upstream contains the VJ implementation but does not register
it as a standalone metric. `decbench_cli.py` registers that existing algorithm
only when native `vj_ged` is absent; a native registration wins automatically,
and the selected source is printed and recorded. This is an unapproximated VJ
distance, not an alias of DecBench's separately budgeted `ged` metric.

Reading the summary
-------------------

Every metric is printed twice for each decompiler:

* **rendered mean** is the metric's native mean over functions for which that
  metric produced a value;
* **all-function quality mean** uses the entire angr/reference function
  universe and contributes zero for a refusal or missing value.

`byte_match` and `type_match` already use zero as their worst value. Raw `ged`
and `vj_ged` are distances where zero is perfect, so filling a refusal with raw
zero would reward it. Their all-function number therefore maps each rendered
distance `d` to `1 / (1 + d)` and then fills refusals with zero. The report and
baseline name that scale explicitly. Function coverage is printed as its own
rendered/total fraction as well.

Function keys are `project/binary/opt::function`; projects that produce the
same binary and function names cannot collide. The merger refuses duplicate or
missing project/optimization cells. On cached-reference sweeps, functions not
present in r2sleigh's raw result are restored from the reference universe as
explicit zero-scored refusals. Missing projects, optimization cells, binary
groups, and function counts are printed rather than silently shrinking the
population.

What the record is for
----------------------

`byte_match` and `type_match` are the only measurements here that score the
*content* of a rendered function rather than its shape. Every defect they would
have caught went unnoticed until they were first run: an argument dropped from
a variadic call, the stack pointer drifting eight bytes at each call site, a
register-named local staged before every argument. The corpus cannot see any of
them, because it is nine hash functions of one shape with fixed inputs.
