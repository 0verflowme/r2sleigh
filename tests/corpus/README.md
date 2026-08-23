# Executable verification of rendered output

`pdd` output that reads plausibly is not output that is right. Every earlier
measurement in this branch scored a rendering by inspecting it -- does it declare
what it mentions, does a loop have a body, does a non-void function return -- and
each of those scores was wrong in the same direction, because a body can satisfy
all of them and still compute something else.

This harness settles it the only way it can be settled. It takes each rendering,
compiles it, runs it on the input the reference binary was run on, and compares
the value. Nothing else counts as correct.

## Running it

    clang -O2 -o h_arm64_O2 hashes.c              # or any target and level
    ./h_arm64_O2 > reference.txt                  # what the program computes
    ./sweep.sh h_arm64_O2 > out_arm64_O2.txt      # what r2sleigh renders
    python3 verify_rendering.py arm64_O2

`sweep.sh` drives `pdd`, which is r2sleigh's renderer. `pdc` is radare2's own
pseudo-decompiler and answers happily with raw register arithmetic; comparing
`pdc` across two builds of this plugin proves nothing, and that mistake was made
here once already.

## What the verdicts mean

  * **CORRECT** -- compiled, ran, produced the reference value.
  * **wrong** -- compiled and ran, produced something else. The rendering says
    what the program does not do.
  * **nocompile** -- the rendering is not C. Almost always `use of undeclared
    identifier`, which is a name that reached the page with nothing defining it.
  * **hang** -- the loop the rendering describes does not terminate.

A `[N width(s) assumed]` note means the rendering dereferenced an address
without saying how wide the load was, and the harness had to pick one. C that
does not state a load width has not said what the program does, so the note is
a defect report and not a caveat about the harness.

The harness retypes parameters and locals as `long` and inserts casts at each
dereference, because a rendering types an address-carrying value as an integer
and then dereferences it. It does not change any operator or constant, so a
rendering that computes the right value still computes it afterwards.

## Data the rendering reads

A rendering that reads a table reads it at the address the binary puts it at,
and the harness process has nothing mapped there. `pearson` scored `wrong` on an
empty result for that reason while its rendering was exactly right.

So the bytes are lifted out of the binary with `r2` and the literal is pointed at
a copy. Only literals inside a mapped section are substituted: FNV's prime is
`0x100000001b3`, which looks precisely like a Mach-O address and is not one, and
substituting it broke a rendering that had been correct.

## Baseline

Nine hash functions, x86-64 and arm64, `-O0`/`-O1`/`-O2`, 54 renderings.

    at the start of the work    4 correct
    now                        26 correct

    x86-64 -O0   6      arm64 -O0   6
    x86-64 -O1   4      arm64 -O1   5
    x86-64 -O2   0      arm64 -O2   5

Structural inspection scored 21 of the original 54 sound when four of them ran
correctly. That difference is why this exists.
