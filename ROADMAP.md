r2sleigh Roadmap
================

> Vision: `r2sleigh` is not a sidecar plugin with many commands.
> It is the analysis brain of radare2: one typed subsystem that lifts,
> structures, solves, types, summarizes, validates, and renders functions
> coherently.

North Star
----------

The system we are aiming for has these properties:

- one canonical IL substrate
- one canonical SSA/dataflow layer
- one canonical semantic artifact with explicit evidence
- one canonical combined `FunctionFacts` contract
- one canonical engine session and route planner
- one typed radare2 context seam
- one planner surface for query, types, and decompilation
- one replay/trace validation loop
- one small public plugin surface that feels native to radare2

The metric is not command count. The metric is whether radare2 feels like it
gained one coherent, mathematically disciplined analysis engine.

Current State (May 2026)
------------------------

The foundation reset is mostly complete. The project is now typed-session-first:
`r2plugin` is mostly orchestration glue, and semantic ownership sits in the Rust
crates that own the facts.

Current ownership shape:

- `r2ssa`: SSA, def-use, prepared facts, deterministic dataflow inputs.
- `r2sym`: semantic artifacts, evidence, summaries, replay/query behavior.
- `r2types`: canonical `FunctionFacts`, type projection, writeback facts.
- `r2engine`: session orchestration, route planning, artifact cache keys, cost model.
- `r2dec`: lowering, structuring, and rendering from canonical facts.
- `r2plugin`: radare2 command dispatch, typed context collection, FFI, apply/render glue.
- `../radare2`: typed seam provider and validation target.

Recent high-value progress:

- removed major JSON-shaped internal seams from analysis/session paths
- moved plugin analysis toward typed radare2 context collection
- consolidated `anal.sla.*` knobs away from the normal user workflow
- tied analysis depth to normal radare2 depth (`aa`, `aaa`, `aaaa`)
- added kernel smoke harness and strict checks
- added corpus benchmark harnesses and documentation
- added bounded native-linear semantic summaries for large Coreutils workers
- strengthened native-worker summaries for file, FTS, parser, sort, format,
  metadata, record-stream, and memory families
- improved `r2types` semantic role projection and aggregate identity handling
- cleaned focused Coreutils quality: no generic args, no residual decompile
  markers, no generated `sla_struct_*` signature leaks, and only small tracked
  generic type residue remains
- kept benchmark outputs and local corpus artifacts out of source control
- expanded r2r/plugin validation around typed sessions and decompiler behavior
- added the initial `r2engine` crate so plugin decompile routing can move out of
  command glue and into an explicit session/planner boundary

Current benchmark signal:

- focused Tier 1 Coreutils, `max_functions=12`: green
- average score: `100.0`
- hard failures: `0`
- residual decompile count: `0`
- radare2 candidate count: `0`
- generic arg total: `0`
- generic type total: `15`
- generated aggregate signature leaks: `0`
- summary-only native worker routes: `77`
- setup time still dominates command time in this gate
- `tests/r2r`: green on 85 plugin tests

This is a strong focused signal, not a declaration of "gold standard" yet.
Focused Coreutils is hard-failure clean with tracked generic type residue; broad
Coreutils, CGC, Juliet, and real kernel acceptance still need to become
recurring gates.

Architecture Rewrite Direction
------------------------------

The next large step is a spine rewrite, not a blank-slate rewrite of every
crate. The current ownership map is right, but route selection, summary
classification, callsite/type provenance, and plugin orchestration still have
too much heuristic glue.

The intended fact flow is:

`radare2 typed context + lifted IL -> r2ssa canonical facts -> r2sym semantic
evidence -> r2types constraints -> r2engine route/cache/session -> r2dec render`

Rewrite targets:

- `r2engine` becomes the single orchestration brain for decompile, type, query,
  profile, cache, refusal, and route decisions.
- `r2sym` summary classification becomes evidence-first. Symbol names are weak
  hints, not semantic ownership.
- `r2ssa` owns canonical stack slots, ABI callsite provenance, return
  provenance, memory regions, and switch/jump-table facts.
- `r2types` becomes a constraint/projection engine over radare2 types, ABI
  facts, callsite evidence, semantic summaries, imports, structs, and user
  assumptions.
- `r2dec` renders canonical facts and explicit residuals. It must not invent
  missing control flow, repair type policy, or hide placeholder facts.
- `r2plugin` calls typed session APIs and applies results. It should not own
  route policy, summary policy, cache strategy, or semantic repair.

Known Heuristic Debt
--------------------

The following items are intentional short-term debt and should be retired, not
expanded:

- name-first native worker family matching in `r2sym`
- hardcoded role/signature tables used as authoritative facts
- duplicated route policy in `r2dec` and `r2engine`
- summary pseudo-calls standing in for real loop/control reconstruction
- decompiler-side call argument repair
- decompiler-side stack placeholder cleanup
- switch fallback that invents placeholder case values
- fixed semantic worker island caps instead of evidence-ranked scheduling
- plugin-side detached summary/decompile orchestration
- large decompiler thread stack as a workaround for recursive structuring
- split cache layers with weak artifact/render hit rates

Budgets and residuals are not debt when they are explicit and honest. They
become debt only when they hide missing upstream facts or fabricate semantics.

Strategic Principles
--------------------

1. One subsystem, not many tools.
   - `r2il`, `r2ssa`, `r2sym`, `r2types`, `r2dec`, `r2plugin`, and
     `../radare2` should behave like one analysis engine.

2. Optimize for typed ownership, not command growth.
   - The best improvements are deeper integration and stronger facts, not
     additional verbs.

3. Optimize for practical asymptotics.
   - use `O(1)` or `O(log n)` lookup for metadata, indexes, summaries, and caches
   - use `O(n)` passes over blocks, SSA ops, and fact sets where possible
   - use bounded search where search is unavoidable
   - reuse summaries and incrementally recompute instead of rediscovering facts

4. Prefer principled rewrites over downstream patchwork.
   - if a seam is bad, rewrite the seam
   - if policy is in the wrong crate, move it
   - if output only works because of a downstream patch, fix the upstream fact

5. Determinism beats cleverness.
   - stable ordering and stable cache keys are correctness requirements

6. Refusal is better than silent nonsense.
   - budgets, residual reasons, confidence, and evidence must stay explicit

What Is Done
------------

### 1. Canonical Semantic Ownership

Done:

- `r2sym` owns semantic policy and evidence
- `r2sym::SemanticArtifact` is the canonical semantic artifact
- query routing is planner-gated
- target-local narrowing has explicit ambiguity handling
- native worker summaries are first-class artifacts, not decompiler hacks
- semantic schema/cache versioning is explicit

Remaining:

- promote summaries into a richer shared registry
- make replay/witness validation part of the normal semantic loop
- improve broad-corpus summary classification beyond focused Coreutils

### 2. SSA/Dataflow Preparation

Done:

- deterministic prepared facts exist
- `r2dec` consumes function-level SSA blocks
- dataflow facts feed decompiler/type/symex paths
- large-function paths can use prepared summary routes instead of unbounded replay

Remaining:

- incremental recomputation hooks
- assumption-aware preparation
- stronger stable indexes for repeated metadata lookup
- broader validation on irreducible CFGs, kernel helpers, and obfuscated flows

### 3. Type System And Function Facts

Done:

- `r2types::FunctionFacts` is the canonical combined type+semantic contract
- `r2types::FunctionTypeFacts` is the canonical type/layout/signature payload
- semantic role hints strengthen signatures and aggregate identity
- generated local aggregates no longer override authoritative semantic roles
- focused Coreutils generic args/types are clean

Remaining:

- semantic type algebra V2
- better out-param, return-shape, and layout confidence inference
- typed assumption model integration
- replacement of large per-function role tables with a canonical role/signature registry
- stronger refusal logic for unsafe local struct candidates

### 4. Decompiler Routing And Rendering

Done:

- `r2dec` routes through canonical plans/facts
- native-linear bounded summary path prevents large worker timeouts
- summary-backed worker rendering exists
- VM path is honest about summary-driven routes
- decompiler/plugin integration is covered by r2r

Remaining:

- structured semantic rendering for more loop/control islands
- helper-call simplification from interprocedural summaries
- VM semantic rendering V2
- less local planning where canonical upstream plans can decide

### 5. Plugin And radare2 Integration

Done:

- plugin is much closer to glue: collect typed context, call Rust session APIs,
  apply/render facts
- typed mutation/writeback paths exist
- plugin output reports canonical facts/plans
- user workflow follows normal radare2 analysis depth
- public command surface is stable enough for current testing

Remaining:

- shrink and tier command surface: public workflow commands vs debug/maintainer commands
- move config-like behavior to `e anal.sleigh.*`
- enrich normal radare2 views more directly
- add radare2 typed seams where current plugin glue still compensates
- persistence for shared assumptions and possibly replay/trace state

### 6. Benchmark And Acceptance Infrastructure

Done:

- Python benchmark harness
- corpus setup helper
- benchmark documentation
- focused Coreutils benchmark
- kernel smoke harness
- strict checks for generated output/corpus isolation

Remaining:

- broad Coreutils gate, not only focused targets
- CGC gate after broad Coreutils quality holds
- Juliet/CWE gate after CGC signal is stable
- recurring real kernel smoke gate, local-only
- trend reports that highlight slowest commands, residual families, generic type
  regressions, and candidate radare2 issues

What Is Not Done
----------------

The biggest remaining gains are whole-stack intelligence and scale:

- shared typed assumptions
- `r2engine` adoption across type/query/decompile command paths
- canonical role/signature registry instead of growing local match tables
- deeper summary reuse across `r2sym`, `r2types`, and `r2dec`
- trace/replay as a first-class validation loop
- semantic type algebra beyond memory-led projection
- structured VM semantic rendering
- broader benchmark gates
- cheaper repeated analysis through incremental caching
- more native radare2 integration with fewer public plugin verbs

Priority Order
--------------

The real implementation order from here is:

`P0 spine rewrite -> P1 whole-stack summary reuse -> P2 semantic type algebra
-> P3 replay/trace validation -> P4 VM rendering -> P5 native radare2 surface
-> P6 incremental/perf -> P7 broad corpus gates`

### P0 - Analysis Spine Rewrite

Goal:

Remove the remaining heuristic glue that makes the system look better than its
canonical facts, while preserving the existing crate ownership model.

Deliverables:

- single route/session/cache owner in `r2engine`
- evidence-first summary classifier in `r2sym`
- canonical callsite, stack-slot, return, memory-region, and switch facts in
  `r2ssa`
- one signature/type constraint path in `r2types`
- `r2dec` rendering from selected routes and canonical facts only
- `r2plugin` reduced to typed context collection, command dispatch, FFI, and
  applying/rendering engine results

Success criteria:

- route policy exists in one crate
- summary names are hints, not authoritative semantic ownership
- no decompiler-side stack/call-arg repairs are needed for benchmark-clean output
- fake switch cases, fake control flow, and placeholder type facts are rejected
  or rendered as explicit residuals
- focused Coreutils remains green while setup/command time improves

### P0a - Engine Session Boundary

Goal:

Make `r2engine` the only subsystem that decides which artifacts are needed for a
function request.

Deliverables:

- route planning for decompile/type/query requests
- typed artifact cache keys and invalidation boundaries
- engine metrics for planning, SSA, semantic, type, and render costs
- migration of plugin decompile/type/query orchestration into `r2engine`
- removal of duplicated planner logic from plugin glue

Success criteria:

- plugin commands call `r2engine` for orchestration
- `r2dec` renders selected routes instead of owning global scheduling decisions
- repeated requests reuse engine artifacts deterministically
- small-function fast paths do not pay semantic-worker setup costs unnecessarily

### P0b - Shared Assumptions And Role Registry

Goal:

Create the typed control plane that lets a user, replay seed, or upstream
radare2 fact refine the whole subsystem coherently.

Deliverables:

- canonical typed assumption model across `r2ssa`, `r2sym`, `r2types`, and `r2dec`
- typed assumption transport through `FunctionFacts`
- plugin import/export and, if needed, radare2 persistence seams
- assumption-aware:
  - SSA preparation
  - query narrowing
  - branch feasibility
  - type/layout recovery
  - decompiler simplification
- canonical semantic role/signature registry for known helper families
- deterministic registry lookup by normalized symbol, summary kind, and evidence
- migration of large ad hoc role match tables into the registry

Why this is first:

- assumptions amplify every subsystem
- role/signature knowledge is currently useful but too table-shaped
- this avoids another round of per-function patches as we move beyond Coreutils

Success criteria:

- one assumption changes query, types, and decompiler output coherently
- assumptions are typed, serializable, deterministic, and test-covered
- Coreutils role/signature behavior comes from a registry, not scattered policy

### P1 - Promote Summaries To Whole-Stack Inputs

Goal:

Make summaries a shared source of truth for query, type, and decompiler behavior.

Deliverables:

- summary-backed return/value-shape hints for `r2types`
- summary-backed out-param inference
- summary-backed helper-call simplification for `r2dec`
- summary applicability/evidence surfaced in `FunctionFacts`
- reusable domain summaries for:
  - string scans
  - hash/fold loops
  - getopt-style parsers
  - table walkers
  - file/record streams
  - libc-ish helpers
  - kernel helper families

Why:

- `r2sym` already knows more than consumers currently exploit
- downstream rediscovery is slower and less reliable than summary reuse

Success criteria:

- fewer downstream local heuristics
- better helper-call rendering
- stronger return and out-param facts
- summaries are cached once and consumed many times

### P2 - Semantic Type Algebra V2

Goal:

Make `r2types` reason over the full semantic artifact, not just memory hints and
signature roles.

Deliverables:

- consume semantic `pre`, `post`, `control`, `targets`, diagnostics, and residual reasons
- infer out-params, return shapes, field applicability, and layout confidence
- use residual reasons to refuse unsafe projections
- rank local struct candidates by evidence strength and semantic compatibility
- expose confidence and refusal reasons through `FunctionFacts`

Why:

- focused type quality is strong, but broad type quality needs semantic algebra
- unsafe layouts are worse than honest unknowns

Success criteria:

- fewer unsafe struct candidates
- stronger out-param/return recovery
- cleaner agreement between type facts and decompiler output
- no downstream reconstruction of missing type semantics

### P3 - Replay And Trace Validation

Goal:

Make debugger state and replay checkpoints part of the normal semantic loop.

Deliverables:

- replay seeds as canonical engine input
- typed import of debugger/trace state
- witness validation against replayed state
- static-vs-observed semantic mismatch reporting
- confidence refinement from observed state without making replay the semantic owner
- likely `../radare2` typed seam for debugger/trace snapshots

Why:

- this is the cleanest bridge between static and dynamic analysis
- replay infrastructure exists but is not yet a standard validation path

Success criteria:

- observed state can validate or challenge static facts
- witnesses and replay share canonical semantic state
- mismatches are surfaced as evidence, not hidden as local overrides

### P4 - VM Semantic Rendering V2

Goal:

Move VM analysis from honest comments toward structured semantic rendering.

Deliverables:

- selector recovery
- handler graph summaries
- guarded transfer summaries
- switch-like pseudo-C from canonical VM semantics
- explicit route labels for summary-driven VM rendering

Non-goal:

- do not start with a fake "full VM decompiler"

Why:

- the current VM path is honest, but still leaves structure on the table

Success criteria:

- VM functions render as structured semantic summaries, not only comments
- VM routes remain explicitly marked as summary-driven where appropriate

### P5 - Native radare2 Surface And Command Rationalization

Goal:

Make the plugin feel like radare2 got smarter, not like radare2 grew a second
shell.

Deliverables:

- define public vs debug command tiers
- move config-like behavior to `e anal.sleigh.*`
- enrich existing radare2 workflows:
  - `aa`
  - `aaa`
  - `aaaa`
  - `af`
  - `pdfj`
  - `pdd`
  - type views
- keep expert inspection commands available but demoted
- add typed `../radare2` seams when the right fact belongs upstream

Why:

- command count is not quality
- users should not need to think in crate boundaries

Success criteria:

- fewer public commands
- better normal radare2 output
- plugin internals are inspectable without being the main UX

### P6 - Incremental And Performance Discipline

Goal:

Make repeated analysis cheaper and more predictable.

Deliverables:

- stronger typed caches
- deterministic cache keys
- explicit invalidation boundaries
- budget-aware scheduling
- fewer repeated full-function passes
- reuse prepared summaries across query, types, and decompiler
- benchmark support for identifying repeated setup and command costs

Why:

- benchmark progress is still slower than desired
- the clean architecture now makes reuse possible

Success criteria:

- repeated analysis gets cheaper
- large-CFG behavior stays bounded
- command latency improves without hiding residuals or lowering quality

### P7 - Broad Corpus Acceptance

Goal:

Move from focused wins to recurring broad confidence.

Deliverables:

- broad Coreutils acceptance gate
- CGC vulnerability-oriented gate
- Juliet/CWE gate
- local-only real kernel smoke gate
- compare reports for every major tranche

Why:

- focused Coreutils being clean is necessary but not sufficient
- gold standard requires broad and adversarial coverage

Success criteria:

- broad Coreutils stays green without generic/regression drift
- CGC/Julet results classify failures into owner buckets
- kernel smoke remains local-only and reproducible

Component Status
----------------

### `r2il` / `r2sleigh-lift`

State:

- stable enough for current x86/arm/riscv/mips coverage
- still the canonical place for IL/lift/register semantics

Next:

- extend only for real architecture semantics
- preserve deterministic register aliasing and width behavior

### `r2ssa`

State:

- prepared facts and deterministic SSA are solid enough for current consumers

Next:

- assumption-aware dataflow
- incremental recomputation hooks
- stronger indexed metadata for repeated lookups

### `r2sym`

State:

- semantic artifact authority is established
- native worker summaries and evidence algebra are much stronger

Next:

- summary registry
- replay/witness validation
- more canonical summaries for broad corpus families
- summary composition across consumers

### `r2types`

State:

- canonical `FunctionFacts` path is established
- focused Coreutils hard failures and generic args are clean
- remaining focused-gate generic type residue is tracked
- generated aggregate leakage is fixed for current hot targets

Next:

- semantic type algebra V2
- assumption-aware type recovery
- role/signature registry extraction
- stronger layout confidence and refusal logic

### `r2engine`

State:

- initial crate exists for session orchestration, route planning, cache keys,
  and shared engine helpers
- plugin decompile paths already use parts of the engine boundary

Next:

- own all decompile/type/query route decisions
- absorb duplicated route policy from `r2dec` and plugin glue
- own session-level artifact/render reuse and metrics
- expose typed request/response APIs for plugin commands

### `r2dec`

State:

- planner/facts route is in place, but route policy still needs to move upward
- large-worker native-linear summary path prevents major timeouts
- summary-backed rendering exists

Next:

- summary-backed helper-call simplification
- structured loop/control-island rendering
- VM semantic rendering V2
- delete local route policy and downstream repair once upstream facts exist

### `r2plugin`

State:

- much closer to typed orchestration glue
- command/radare2 integration is covered by r2r

Next:

- shrink public surface
- improve normal radare2 workflow integration
- keep debug commands available but clearly tiered
- add upstream radare2 seams when plugin glue is compensating for missing core APIs

### `../radare2`

State:

- clean tree is used for typed seam validation
- typed collectors are now central to plugin correctness

Next:

- typed assumption persistence if needed
- debugger/trace typed snapshot seam
- richer typed collectors where plugin currently lacks native facts

Engineering Rules For Future Tranches
-------------------------------------

Before landing any non-trivial change:

1. Identify the user-visible behavior or invariant.
2. Identify the canonical owner.
3. Extend an existing typed contract before creating a new one.
4. State the complexity target.
5. Push facts upstream instead of reconstructing downstream.
6. Add deterministic tests at the exercised layer.
7. Run benchmark comparison when behavior affects quality or performance.
8. Validate both repos if the seam crosses into `../radare2`.

Default validation bar for core changes:

```bash
python3 -m unittest tests.test_kernel_smoke tests.test_reversing_benchmark tests.test_setup_corpus
cargo test -p r2ssa
cargo test -p r2sym
cargo test -p r2types
cargo test -p r2engine
cargo test -p r2dec
cargo test -p r2sleigh-plugin --features all-archs
cargo clippy -p r2ssa --all-targets -- -D warnings
cargo clippy -p r2sym --all-targets -- -D warnings
cargo clippy -p r2types --all-targets -- -D warnings
cargo clippy -p r2engine --all-targets -- -D warnings
cargo clippy -p r2dec --all-targets -- -D warnings
cargo clippy -p r2sleigh-plugin --features all-archs -- -D warnings
make -C r2plugin LOCAL_R2_DIR=/private/tmp/radare2-r2sleigh-clean RUST_FEATURES=all-archs
PATH="/usr/local/bin:/opt/homebrew/bin:$PATH" make -C tests/r2r run LOCAL_R2_DIR=/private/tmp/radare2-r2sleigh-clean R2R_TIMEOUT=120 R2R_JOBS=1
git diff --check
```

Benchmark gate for Coreutils-focused tranches:

```bash
python3 scripts/reversing_benchmark.py \
  --preset tier1 \
  --coreutils-dir /tmp/r2sleigh-corpora/src/coreutils/coreutils-9.11/src \
  --focused-coreutils \
  --no-repo-fixtures \
  --analysis aaa \
  --max-functions 12 \
  --timeout 120 \
  --jobs 1 \
  --plugin-dir r2plugin \
  --r2 ../radare2/binr/radare2/radare2 \
  --tmpdir /tmp/r2sleigh-coreutils-tmp \
  --out /tmp/r2sleigh-coreutils-current.json
```

Anti-Goals
----------

Do not spend roadmap energy on:

- command count inflation
- plugin-side reparsing of existing command output
- parallel type or semantic owners
- decompiler-local policy that should live upstream
- pretending hard analyses are `O(1)`
- hiding residual/budget behavior to make reports look green
- adding per-function patches when a registry, summary, or typed seam is the
  correct owner

If a change improves the subsystem by deleting a command, moving an owner, or
rewriting a seam, that is progress.

Acceptance Standard
-------------------

The target plugin system should eventually have these properties:

- a user can rely on normal radare2 workflows and quietly get better analysis
- symex, types, decompiler, and replay agree on the same facts
- assumptions update the whole subsystem coherently
- summaries are reused across crates instead of rediscovered
- evidence and fallback reasons are visible and honest
- benchmark gates cover focused and broad corpora
- large functions stay bounded without losing useful semantic summaries
- the public command surface is smaller and smarter, not larger

That is the gold standard we should optimize toward.
