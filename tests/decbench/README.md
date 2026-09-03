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
the result with `baseline.json`, per function and per metric:

```
tests/decbench/run_decbench.sh                    # compare with the record
tests/decbench/run_decbench.sh --accept-baseline  # record this run instead
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

What the record is for
----------------------

`byte_match` and `type_match` are the only measurements here that score the
*content* of a rendered function rather than its shape. Every defect they would
have caught went unnoticed until they were first run: an argument dropped from
a variadic call, the stack pointer drifting eight bytes at each call site, a
register-named local staged before every argument. The corpus cannot see any of
them, because it is nine hash functions of one shape with fixed inputs.
