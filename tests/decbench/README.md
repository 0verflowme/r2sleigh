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
