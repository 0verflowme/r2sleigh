# Beating angr on DecBench, end to end

Written to be picked up cold. Three contexts, one per axis, landing sequentially
so the corpus gate and the plugin install lock are never contested.

## The arithmetic that orders everything

Under the honest denominator a refusal scores zero, so every similarity score is
`S = c · m̄` — coverage times the mean over rendered functions. Measured on the
current baseline over 1,768 functions:

| | ours | angr | factor needed |
| --- | --- | --- | --- |
| coverage | 0.404 | 0.992 | ×2.5 |
| `byte_match` all-function | 0.058 | 0.435 | ×7.5 |
| `type_match` all-function | 0.066 | 0.360 | ×5.5 |

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

1. **Finish the zlib/O1 root cause.** That single cell is 715 of 1,054 refusals
   — 68% of every refusal in the benchmark. Five binaries report *zero*
   functions observed and two report exactly one; that is whole-binary loss, not
   715 individual refusals. Already eliminated with evidence: harness timeout
   (the 7-binary run takes ~1,176 s against a 3,600 s per-binary budget), refusal
   aborting the command sequence, r2 command truncation, and the harness failing
   to install the plugin. Two instruments now exist that did not before — the
   harness records a `harness:`-prefixed cause naming how the process ended, and
   a run refuses outright if the plugin does not load. Re-run and read them.
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

- **Delete the inert CFG guard fields.** `cfg_guard_reason`,
  `summary_probe_needed` and `summary_probe_skipped_large_cfg` have no non-test
  readers; only `op_count` is consulted. Deleting them removes the last SSA build
  from the probe path and lets the size gate move ahead of the probe. Keep their
  facts as tests.
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
