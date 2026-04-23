r2sleigh Roadmap
================

> Vision: `r2sleigh` is not a sidecar plugin with many commands.
> It is the analysis brain of radare2: one typed subsystem that lifts,
> structures, solves, types, summarizes, and renders functions coherently.

North Star
----------

The system we are aiming for has these properties:

- one canonical IL substrate
- one canonical SSA/dataflow layer
- one canonical semantic artifact with explicit evidence
- one canonical combined `FunctionFacts` contract
- one planner surface for query, types, and decompilation
- one replay/trace validation loop
- one small public plugin surface that feels native to radare2

The metric is not command count. The metric is whether radare2 feels like it
gained one coherent, mathematically disciplined analysis engine.

Current State (Apr 2026)
------------------------

The core architecture reset is done.

Completed high-value work:

- canonical `r2sym::SemanticArtifact` ownership
- canonical evidence and plan surfaces in `r2sym`
- `FunctionFacts` as the combined type+semantic contract
- removal of legacy mirrored symbolic/type ownership
- planner-gated symbolic query routing
- target-local narrowing with explicit ambiguity handling
- decompiler planner/consumer split
- canonical VM summary routing in decompiler/plugin
- explicit semantic schema/cache versioning
- end-to-end plugin transport on canonical facts/plans
- strong `r2r` coverage and full validation bar

The system is no longer missing foundations. The next work is about using those
foundations better across the whole stack.

Strategic Principles
--------------------

1. One subsystem, not many tools.
   - `r2il`, `r2ssa`, `r2sym`, `r2types`, `r2dec`, `r2plugin`, and
     `../radare2` should behave like one analysis engine.

2. Optimize for typed ownership, not command growth.
   - The best improvements are deeper integration and stronger facts, not
     additional verbs.

3. Optimize for practical asymptotics.
   - aim for `O(1)` / `O(log n)` lookups
   - `O(n)` passes where possible
   - bounded search where unavoidable
   - summaries and incremental reuse everywhere else

4. Prefer principled rewrites over downstream patchwork.

5. Determinism beats cleverness.

What Is Done
------------

### 1. Canonical Semantic Rewrite

Done:

- `r2sym` is the semantic owner
- evidence and ambiguity are first-class
- query routing is planner-gated
- target-local narrowing is authoritative and source-consistent
- symbolic artifact transport is canonical across plugin/export surfaces

### 2. Consumer Hardening

Done:

- `r2types` consumes canonical semantics through `FunctionFacts`
- `r2dec` routes through planner + consumer modules
- VM decompile path is honest summary mode instead of pretending to be native
- plugin JSON/reporting is on canonical facts and plan fields

### 3. Decompiler/Plugin Integration

Done:

- canonical semantic route planning
- VM summary rendering route
- combined facts/plan reporting
- strong `r2r` coverage for the new paths

What Is Not Done
----------------

The biggest remaining gains are not foundational rewrites. They are whole-stack
intelligence improvements:

- shared assumption model
- deeper reuse of interprocedural summaries across all consumers
- trace/replay as a first-class validation loop
- richer semantic type algebra
- stronger VM semantic rendering
- narrower and more native plugin surface

Priority Order
--------------

The real implementation order from here is:

`P0 assumptions -> P1 summary reuse -> P2 replay loop -> P3 semantic typing ->
P4 VM semantics -> P5 command-surface rationalization -> P6 incremental/perf`

### P0 — Shared Assumption Model

Goal:

Turn the subsystem into an interactive reasoning engine instead of a static
batch analyzer.

Deliverables:

- canonical typed assumption model across `r2ssa`, `r2sym`, and `r2types`
- explicit persistence or transport seam through plugin and, if needed,
  `../radare2`
- incremental recomputation of affected analyses
- assumptions influence:
  - query narrowing
  - branch feasibility
  - type/layout recovery
  - decompiler simplification

Why this is highest ROI:

- users often know one critical fact the engine does not
- this amplifies every existing subsystem instead of adding a silo

Success criteria:

- one assumption set changes query, types, and decompiler coherently
- assumptions are explicit, typed, serializable, and test-covered

### P1 — Promote Interprocedural Summaries To Whole-Stack Inputs

Goal:

The summaries already present in `r2sym` should stop being mostly query power
and start being a shared strength across the subsystem.

Deliverables:

- summary-driven return/value-shape hints for `r2types`
- summary-driven helper-call simplification for `r2dec`
- summary-backed applicability/evidence surfaced in function facts
- stricter reuse of library and derived summaries instead of rediscovery

Why:

- interproc summary work already exists in `r2sym`
- downstream consumers currently leave too much value on the table

Success criteria:

- better out-param inference
- better return-shape inference
- better helper-call rendering
- fewer downstream local heuristics

### P2 — Replay And Trace As First-Class Validation

Goal:

Make debugger state and replay checkpoints part of the normal semantic loop.

Deliverables:

- replay seeds as canonical engine input, not just expert-only path control
- typed import of debugger/trace state
- witness validation against replayed state
- static-vs-observed semantic mismatch reporting

Why:

- this is the cleanest bridge between static and dynamic reasoning
- replay infrastructure already exists and needs promotion, not reinvention

Success criteria:

- replay and witness validation share canonical semantic state
- observed state can refine confidence without becoming semantic owner

### P3 — Semantic Type Algebra V2

Goal:

Make `r2types` consume more of the semantic artifact than memory terms alone.

Deliverables:

- use `pre`, `post`, `control`, and `targets` alongside memory facts
- use diagnostics and residual reasons to refuse unsafe projections
- infer:
  - out-params
  - return shape
  - field applicability
  - layout confidence

Why:

- current type recovery is useful but still too memory-led
- this is the biggest non-query value gap

Success criteria:

- fewer unsafe struct candidates
- stronger return/out-param recovery
- cleaner agreement between types and decompiler output

### P4 — VM Semantic Rendering V2

Goal:

Move VM analysis from summary comments toward structured semantic rendering.

Deliverables:

- selector recovery
- handler graph summaries
- guarded transfer summaries
- switch-like pseudo-C from canonical VM semantics

Non-goal:

- do not start with a fake "full VM decompiler"

Why:

- current VM path is honest but leaves value on the table

Success criteria:

- VM functions render as structured semantic summaries, not just comments
- VM routes remain explicitly marked as summary-driven where appropriate

### P5 — Public Surface Rationalization

Goal:

Make the plugin feel native to radare2 instead of exposing every internal stage
as a first-class user command.

Deliverables:

- define public vs debug command tiers
- move config-like behaviors to `e anal.sleigh.*`
- enrich existing radare2 views instead of growing more plugin verbs
- keep expert inspection surfaces available, but demoted

Why:

- command count is not a quality metric
- intelligent integration should reduce, not expand, user-visible surface area

Success criteria:

- fewer public commands
- stronger existing radare2 workflows
- less need for users to think in crate boundaries

### P6 — Incremental And Performance Discipline

Goal:

Turn the subsystem into a cheaper engine to run repeatedly.

Deliverables:

- stronger summary caches
- fewer repeated full-function passes
- explicit invalidation and reuse boundaries
- budget-aware scheduling
- deterministic cache keys and cost-aware planners

Why:

- the architecture is now clean enough that the next gains come from reuse

Success criteria:

- repeated analysis gets cheaper
- large-CFG behavior stays bounded
- downstream consumers reuse upstream work instead of re-deriving it

Per-Crate Direction
-------------------

### `r2il` / `r2sleigh-lift`

Keep the IL small, typed, and architecture-faithful. Extend only when new
semantics are truly canonical across the stack.

### `r2ssa`

Focus on:

- prepared facts
- deterministic SSA
- incremental recomputation hooks
- assumption-aware control/dataflow preparation

### `r2sym`

Focus on:

- semantic artifact authority
- evidence algebra
- query planning
- summaries
- replay
- witness generation
- summary composition across consumers

### `r2types`

Focus on:

- semantic type algebra
- stronger `FunctionFacts`
- candidate ranking and refusal logic
- struct/signature/layout confidence

### `r2dec`

Focus on:

- rendering from canonical plans/facts
- less local planning
- stronger helper/summary interpretation
- VM structured summary rendering

### `r2plugin`

Focus on:

- orchestration
- JSON shaping
- radare2-native integration
- shrinking the public surface over time

### `../radare2`

Focus on:

- typed collectors
- persistence of shared analysis metadata
- debugger/trace seams that should exist for all consumers

Anti-Goals
----------

Do not spend roadmap energy on:

- command count inflation
- plugin-side reparsing of existing commands
- parallel type or semantic owners
- decompiler-local policy that should live upstream
- pretending hard analyses are "`O(1)`"

If a change improves the subsystem by deleting a command, moving an owner, or
rewriting a seam, that is progress.

Acceptance Standard
-------------------

The target plugin system should eventually have these properties:

- a user can rely on normal radare2 workflows and quietly get better analysis
- symex, types, decompiler, and replay agree on the same facts
- assumptions update the whole subsystem coherently
- summaries are reused across crates instead of being rediscovered
- evidence and fallback reasons are visible and honest
- the public command surface is smaller and smarter, not larger

That is the gold standard we should optimize toward.
