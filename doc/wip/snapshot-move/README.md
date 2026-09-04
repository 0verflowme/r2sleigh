# Moving the function-snapshot capture out of the radare2 fork

Paused mid-way. The radare2 half is finished, committed and verified; the
plugin half compiles but has never run. This directory holds everything needed
to resume on another machine.

## Why

The fork carried 20,136 added lines. An audit found that of the 68 public APIs
it added, r2sleigh called six, and the ~4,000 lines of capture in
`libr/anal/function.c` read only public struct fields and called public
functions. It was r2sleigh's own policy — which facts to collect, at what
granularity, with what proof marking — compiled into radare2.

Two arguments carried more weight than the line count. Code the fork owns is
code an upstream merge can silently delete, which happened once: a routine
merge resolved conflicts to upstream's side and removed 5,366 lines and 23
files without a conflict marker. And capture logic inside radare2 means every
change to what r2sleigh collects forces a fork rebuild across every worktree.

## State

**radare2 side — done.** Branch `fork/drop-unconsumed-snapshot-api` in
`~/code/fork/radare2`, commit *"Move the function-snapshot capture out of
radare2"*, 18 files, +342 / −9,089.

| | before | after |
| --- | --- | --- |
| fork source | 14,571 | 9,317 |
| fork tests | 5,565 | 2,252 |
| total | 20,136 | 11,569 |
| `libr/anal/function.c` | +5,547 | +803 |
| `libr/include/r_anal.h` | +617 | +215 |
| `libr/anal/function_snapshot.h` | 78 | 35 |

Verified: full build clean, unit tests build clean, 89 pass and 9 fail — the
same 9 that fail on unmodified radare2, compared by assertion message rather
than line number because the test files were edited.

**Plugin side — compiles, never run.** `snapshot_capture.c` (~6,000 lines) and
`snapshot_capture.h` here are the generated capture. `r_anal_sleigh.patch` and
`snapshot_walk.patch` rewire the plugin onto it. With those applied, every
plugin translation unit compiles against the new fork with zero errors.

## What radare2 kept, and why

- **The locking discipline.** `anal->lock` exists upstream but upstream takes
  it in zero places; all 59 acquisitions across ten files are fork-added. A
  plugin cannot make radare2's own mutators take a lock, so this cannot move.
- **`r_anal_function_context_hash`**, rewritten to hash radare2's own state
  rather than build a snapshot to read one field out of it. It deliberately
  excludes the dirty epochs — see the comment at its definition.
- **Six exported functions.** Five read `RAnal->priv` proof tables, so they are
  radare2's to answer and were only ever missing an export. The sixth is
  `r_anal_cc_location_uses`. Fifteen smaller helpers were duplicated into the
  plugin instead, because growing radare2's API to serve one plugin is what
  this change undoes.

## Remaining work

1. Apply `r_anal_sleigh.patch` and `snapshot_walk.patch`, copy
   `snapshot_capture.{c,h}` into `r2plugin/`, and add `snapshot_capture.c` to
   the two link lines in `r2plugin/Makefile` (`ANAL_PLUGIN_SO` and
   `ARCH_PLUGIN_OBJS`).
2. Port `staged_plugin_tests.c` (3,428 lines, extracted from four fork test
   files) into the plugin's suite. These were moved rather than deleted so no
   fact stops being checked; they are not yet wired to a runner.
3. Install the fork and run r2sleigh's gates. This was deliberately not done:
   installing system-wide would disturb the other fourteen worktrees while four
   sessions were in flight.
4. Re-run `pipeline.sh` after the in-flight branches land — the move is
   scripted precisely so it can be replayed against a moved base.

## The radare2 merge is a replay, not a resolve

Merging `fork/drop-unconsumed-snapshot-api` into `anal/subregister-argument-spills`
conflicts in four files, and resolving it by hand loses work. Two commits landed
on the base after the move branched:

    39be056200  Carry loader-owned initialization return arity in snapshots
    4e9e163f83  Expose logical return arity in function snapshots

They add `RAnalSnapshotReturnArity`, a `return_arity` field on both the
signature view and the snapshot, a derivation helper, a hash contribution and a
bin-symbol fallback -- all inside the code the move relocated. Taking the move's
side of the conflict silently drops every one of them; that was confirmed by
resolving it and then finding the arity gone from radare2 and absent from the
plugin's carried header.

The correct path is to re-run `pipeline.sh` with the base at
`anal/subregister-argument-spills`, so the move is regenerated from a tree that
already contains the arity work and it flows into the capture automatically.
That needs a build to converge, which is why it was left for a machine with
headroom rather than hand-ported here.

## Reproducing

`pipeline.sh` replays the whole radare2-side transformation from a pristine
checkout. It hardcodes `/private/tmp/claude-501` and a worktree at
`r2-forkcut`; both need repointing on another machine. Stages, in order:

    move.py         relocate the capture, emit snapshot_capture.c
    surgeries.py    rewire radare2's own consumers; new context hash; ABI change
    finish_move.py  strip prototypes, carry types, export the private-state queries
    dup_shared.py   copy helpers both sides need (transitive)
    prune_dead.py   remove declarations the move left dangling
    strip_types.py  retire the snapshot types from r_anal.h

Order matters twice: `dup_shared` must copy helpers before `prune_dead` deletes
them, and `strip_types` must run after `prune_dead` removes the last
references. The manifests (`movable.txt`, `keep.txt`, `export.txt`,
`clash.txt`, `dupforce.txt`, `carried_types.json`) are convergence state, built
by iterating against the compiler.

## Two cautions for whoever resumes

**Do not trust a hand-written C parser here.** A brace counter used to pick
function extents was wrong four separate ways — `'{'` inside a character
literal, `{` inside a block comment, two prototypes sharing a line, and
multi-line forward declarations read as definitions — and each caused one
function's span to swallow its neighbour. The compiler caught every one. The
move set was converged against compiler output rather than against the parse.

**The dead-code pass deletes other people's code if it infers.** An earlier
version removed live upstream code three times — `ReadAhead`/`read_ahead` in
`fcn.c`, `get_functions_block_cb` in `function.c`, `fcn_call_convention` —
because it inferred deadness from that same parser. It now uses two exact
rules: remove a declaration only if it names a function this move relocated,
or remove a definition only if its identifier occurs exactly once in all of
`libr`, which can only be itself. Keep it that way.

## Unrelated defect found on the way

`test_anal_artifacts` fails 8 assertions at HEAD, before any of this work.
`priv->anal_artifacts` is never initially allocated — the only caller of
`r_core_anal_artifact_store_new` is `artifact_store_clone`, which needs an
existing store — so `r_core_anal_artifacts_replace` returns `INVALID_ARGUMENT`
on first use. Not caused by the move, and not fixed inside it.
