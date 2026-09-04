# Beating angr on DecBench, end to end

Written to be picked up cold. Three contexts, one per axis, landing sequentially
so the corpus gate and the plugin install lock are never contested.

## The arithmetic that orders everything

Under the honest denominator a refusal scores zero, so every similarity score is
`S = c · m̄` — coverage times the mean over rendered functions. Measured on the
current baseline over 1,768 functions:

| | ours | angr | factor needed |
| --- | --- | --- | --- |
| coverage | **0.738** | 0.989 | ×1.34 |
| `byte_match` all-function | 0.058 | 0.435 | ×7.5 |
| `type_match` all-function | 0.066 | 0.360 | ×5.5 |

**The coverage figure was wrong until now and the correction is large.** The
baseline averaged over O0 *and* O1, but every sailr project declares
`optimization_levels = ["O0", "O2", "O2-noinline"]` — **no project configures
O1**. decbench builds the level when asked and then has no source data to match
against, so all 842 O1 functions came back unmatched and scored as refusals. On
O0 alone, which is a level that exists, coverage is 683/926 = 0.738 rather than
714/1768 = 0.404. The harness now refuses an unconfigured level instead of
producing a cell of zeros.

The two metric rows still need re-measuring on configured levels only; they are
carried here unchanged from the mixed baseline and are therefore pessimistic by
an unknown amount.

**Coverage alone is not sufficient**, and this is the correction that reorders
the old plan. Even at `c = 1.0` our rendered mean of 0.144 still loses to angr's
all-function 0.435. Beating angr needs ≈2.5× on coverage *and* ≈3× on rendered
quality. Coverage still goes first, because `∂S/∂m̄ = c` means every rendering
improvement made today pays at forty cents on the dollar — but the rendering
work is not optional and must not be deferred indefinitely.

Two measurement rules, both learned by getting them wrong:

- **Take the census on the population being optimised.** A local-corpus census
  ranked one cause at 62% that is 5% of the benchmark, because the local corpus
  is mostly import thunks. Acting on it would have been a sampling error.
- **Refusal causes compose multiplicatively.** `P(render) = ∏(1 − pᵢ)`, and a
  census shows only the first cause per function. Removing one cause unmasks the
  next, so coverage work is iterated against a *fresh* census, never planned once.

## Decision taken: marked partial rendering

A function with an unprovable cell now renders what is proven and **marks the
gap in-band**, rather than the whole function being refused. Previously one
unanswered cell cost the entire function, which is why coverage sits at 0.404.

This does not weaken the no-false-assertions rule and the distinction is the
point: nothing unproven is ever asserted, and the marking is what keeps the
output honest — a reader and a compiler can both see exactly where the proof
stopped. What changes is the *granularity* of refusal, not its meaning.

## Context A — coverage, 0.404 → ~0.99

Land this first; it re-prices everything after it.

1. ~~Finish the zlib/O1 root cause.~~ **Dissolved, not solved.** O1 is not a
   configured level for any project, so that entire cell was measuring something
   decbench cannot score. There was no decompiler defect in it. Four instruments
   were built while chasing it and all are worth keeping: the harness names how a
   process ended, refuses a run whose plugin will not load, refuses an
   unconfigured optimization level, and no longer scores radare2's "install
   r2dec" notice as a rendered function.
   **Re-baseline on O0 and O2 before planning anything else** — every priority
   derived tonight came from the O1 census and is therefore untrustworthy.
2. **Implement the marked partial tier.** This is the structural work of this
   context. The refusal must become per-cell rather than per-function, and the
   marking must be visible in the emitted C.
3. **Re-census on the benchmark population and iterate** by frequency, taking a
   fresh census after each cause is closed.

Expect the second cause to be `UnrepresentableControlFlow`
(`crates/r2dec/src/lib.rs:3215`) or the loop-graph guard at
`crates/r2engine/src/route.rs:618`, both aggravated by -O1 inlining merging
callee loops into callers.

## Context B — rendered quality, `byte_match` 0.144 → 0.45+

The main lever is `r2rewrite`: 93 proven rules, a proof harness, a live call
site, and it changes **no rendered expression except subscripts**. Three causally
chained reasons, and fixing any one alone changes zero bytes:

1. The canonical term has no rendering consumer. Every consumer of
   `plan.canonical()` is `.access(...)`; the disposition carries a machine id,
   `Inline { expr: MachineExprId }`, and rendering re-lowers the original SSA op.
2. The rewriter's input is gated on the decision its output was meant to change:
   the plan binds a value → the rewriter may not expand it → the rule that would
   prove it redundant cannot match → it stays bound.
3. Even a fired rule leaves the local, because the declaration is minted from
   the binding.

**Superseded by measurement — do not build the fixed point.** The decision to
break the circularity with a fixed point rested on premise 1, which was already
stale: `ValueDisposition::Inline` carries a `TermId`, not a machine id, and 18 of
the 93 rules already fire and reach output. Measured over all 54 cells,
`inline_today == inline_perm` in every one and `newly_inline` is zero
everywhere, because `inlinable_core` consults the canonical roots only to ask
whether the root is `Opaque`, and expansion never changes opacity. The proposed
fixed point therefore converges in one step to today's answer: **the measured
upper bound on its effect is zero changed renderings.** Building the plugin with
`term_absorbs_producer -> true` confirmed it end to end — 53 of 54 cells stop
rendering, and the survivor is byte-identical.

**Do this instead, and it is far cheaper.** A value the plan *binds* has its
assignment right-hand side rendered from the machine arena; its canonical term is
computed and discarded. **421 distinct values have a rule firing today whose
result never reaches output** for that reason alone — 234 `literal.compare`, 64
`subscript.constant_stride`, 58 `literal.or`, 19 `identity.and_self`, and more.
The proof is in the emitted C: `identity.and_self` fires on 19 bound values and
the corpus contains exactly 19 occurrences of `X & X`. No policy change, no
partition change, no fixed point — render a bound value's RHS from its canonical
term.

Also in this context, ordered by measured evidence rather than column size:

- **Bound intermediates rendered as named locals.** The only change so far
  measured to move `byte_match`: fixing the call-argument class alone moved the
  mean 0.111 → 0.196.
- **Integer widths declared from the carrier, not the value**, so an `eax` value
  read through `rax` is declared 64-bit and re-narrowed at every operand.

Explicitly not drivers: `same_type_casts` (removing 3,210 casts moved
`byte_match` by 0.000) and `literal_only_declarations`.

## Context C — `type_match` 0.173 → 0.40+

Largely already connected: 45 of 54 corpus cells now declare a pointer
parameter, and the arm64/x64 divergence is closed. Remaining known defect: where
two uses disagree about a pointee the pointer is correctly refused, but the
refusal lands on `int64_t` — a *signed assertion* — where the rule requires the
honest `uint64_t`. Signedness is a claim; refusing to know a pointee must not
produce a claim about signedness the evidence does not support.

## Cross-cutting, do in any context

- ~~Delete the inert CFG guard fields.~~ **Done** (`51f5aab`). The cascade ran
  deeper than the three fields: the probe, the preprobe risk summary and its two
  helpers, and `cfg_guard_reason` with its controlled variant were all
  unreachable — 291 lines. The size gate now refuses after one pass over the
  block vector. `cfg_guard_reason_from_summary` stays; type routing uses it.
  Note for whoever is next: `CFG::risk_summary()` is now reached only by tests,
  and `SSAFunction::from_blocks_raw_with_control`'s control parameter has no
  caller passing anything but `UncheckedSsaWorkControl`.
- **Bless the snapshot baseline.** `--gate differential` also enforces a snapshot
  ratchet that is red because `tests/corpus/raw-baseline-sha256.json` predates
  the type work. The correctness half passes 54/54; this is an unblessed
  baseline, and blessing is a deliberate acceptance.

## Verification, every context

- `cargo test --workspace` green.
- `./tests/corpus/locked_matrix.sh --gate differential` green. `--gate
  measurement` is never a correctness gate; it cannot fail on a wrong answer.
- Never run two gates or a gate and a benchmark at once — they contend for the
  install lock and both fail. Check `pgrep -f 'locked_matrix|run_decbench'`.
- Report both denominators. The mean over rendered functions is biased upward by
  selection and will *fall* as coverage rises; the all-function mean is the
  honest number and cannot be improved by refusing.

## Hazards that have already cost time

- **Never `git add -A` a directory here.** Build artifacts sit beside sources. A
  committed macOS `.o` was rsynced to the Linux benchmark host, where make saw it
  as current and handed a Mach-O file to the linker.
- **Check the installed library, not the build tree.** `make install` silently
  skipped installing libraries for a long period because `install-pkgconfig` is a
  *prerequisite* of `install` and was failing on a self-copy. Headers moved
  forward, libraries did not, and plugins failed to `dlopen` with a bare
  undefined symbol. Fixed, but verify by symbol rather than by timestamp.
- **zsh does not word-split unquoted variables.** This produced two false
  findings in one session — a broken include-flag list, and a loop that ran once
  with four addresses as operands to a single command.
- **Do not trust a hand-written C parser.** A brace counter used to find function
  extents was wrong four separate ways and each caused a span to swallow its
  neighbour. Converge against compiler output instead.
