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
- one canonical request orchestrator and route planner
- one typed radare2 context seam
- one planner surface for query, types, and decompilation
- one replay/trace validation loop
- one certifying render contract: high-level C only when checked canonical
  facts justify it, otherwise residual/refusal
- one small public plugin surface that feels native to radare2

The metric is not command count. The metric is whether radare2 feels like it
gained one coherent, mathematically disciplined analysis engine.

Current State (May 2026)
------------------------

The foundation reset is mostly complete. The project is now typed-request-first:
`r2plugin` is command/FFI glue, while source-owned runtime facts and semantic
authority stay with the Rust crates that own them.

Current ownership shape:

- `r2ssa`: SSA, def-use, prepared facts, deterministic dataflow inputs.
- `r2sym`: semantic artifacts, evidence, summaries, replay/query behavior.
- `r2types`: advisory `FunctionFacts`, source-owned runtime facts, type
  projection, and writeback facts.
- `r2engine`: request orchestration, route planning, execution metrics, cost model.
- `r2dec`: lowering, structuring, and rendering from canonical facts.
- `r2plugin`: radare2 command dispatch, typed context collection, FFI, apply/render glue.
- `../radare2`: typed seam provider and validation target.

Recent high-value progress:

- removed major JSON-shaped internal seams from analysis/request paths
- moved plugin analysis toward typed radare2 context collection
- consolidated `anal.sla.*` knobs away from the normal user workflow
- tied analysis depth to normal radare2 depth (`aa`, `aaa`, `aaaa`)
- added kernel smoke harness and strict checks
- added corpus benchmark harnesses and documentation
- added bounded native-linear semantic summaries for large Coreutils workers
- strengthened native-worker summaries for file, FTS, parser, sort, format,
  metadata, record-stream, and memory families
- added broad Coreutils hot-worker coverage for BLAKE2, regex reconstruction,
  yacc/date parsing, install/chown/who/read-utmp/shred/factor/seq/tsort, base
  codecs, tab stops, and signal parsing
- improved `r2types` semantic role projection and aggregate identity handling
- moved direct native-worker summary route policy into `r2sym`, with `r2engine`
  consuming a typed semantic route policy instead of maintaining a parallel
  allowlist
- tightened semantic type algebra so role out-param projection requires
  write/escape evidence; role signatures may still contribute concrete
  types/names, but not fake out-param behavior
- added explicit benchmark strict-threshold gates for hard failures, residual
  decompiles, and average score
- cleaned focused Coreutils quality: no generic args, no residual decompile
  markers, no generated `sla_struct_*` signature leaks, and no remaining
  generic type residue in the focused/fair `max_functions=100` gate
- kept benchmark outputs and local corpus artifacts out of source control
- expanded r2r/plugin validation around typed requests and decompiler behavior
- added the initial `r2engine` crate so plugin decompile routing can move out of
  command glue and into an explicit request/planner boundary
- added the first certifying decompiler proof spine, since replaced by exact
  source owners, closed typed ledgers, typed routes, and opaque output seals
- added prepared SSA certificate surfaces for control, expression, memory,
  stack-slot, callsite, and return-value facts
- bridged return-register writes into `ReturnValueCertificate` evidence for
  branch-return functions
- preserved field/layout certificates through `r2types::FunctionTypeFacts` and
  `r2types::FunctionFacts`
- moved certified render gating into the engine/decompiler path, including
  proof-aware member rendering and explicit residuals for unproven array indexes
- tightened summary rendering so summary-only routes no longer emit executable
  source-shaped C at all; exact summaries stay comments/facts until native
  CFG/control/dataflow proof owns the rendered statements
- converted the `table_walk`, parser/count/hash source-gold checks away from
  synthetic `summary_*` loop bodies and added benchmark/oracle hygiene tests that
  reject future source-gold expectations blessing synthetic summary locals
- hardened decompiler audit checks for raw SSA/register leaks such as lowercase
  `r10_1` artifacts
- updated plugin/r2r coverage for certified C, proof residuals, and raw artifact
  rejection; `tests/r2r` is green on 95 plugin tests
- made exact prepared ownership allocation-bound: downstream runtime owners
  retain `Arc<r2ssa::SsaArtifact>`, and only cloning that `Arc` preserves the
  exact allocation and its run-local authority

Archived pre-removal benchmark signal (not current authority):

The generic argument/type totals below came from the deleted detached
type-report command. Fresh benchmark reports no longer emit or gate on those
metrics; genuine type evidence is checked through `afcfj`/`afvj` and compiled
or differential fixtures.

- focused Tier 1 Coreutils, `max_functions=12`: green
- focused/fair Tier 1 Coreutils, `max_functions=100`: green on `603` targets
- average score: `100.0`
- hard failures: `0`
- residual decompile count: `0`
- radare2 candidate count: `0`
- generic arg total: `0`
- generic type total: `0`
- generated aggregate signature leaks: `0`
- summary-only native worker routes: `586`
- setup time still dominates a meaningful part of this gate
- `tests/r2r`: green on 95 plugin tests after route evidence and synthetic
  summary-output gating
- source-gold closure gate: oracle-clean but intentionally closure-red on the
  remaining proof gaps: 4 cases / 12 targets / 13 expectations, average score
  `97.0`, source-oracle failures `0`, residual decompiles `2`, proof gaps `1`
  (`dbg.table_walk` O2), fake-output counters `0`
- broad Coreutils hot-worker manifest: green on `32` targets, hard failures
  `0`, generic args `0`, generic types `0`, residuals `0`
- broad Coreutils `max_binaries=108`, `max_functions=12`: closure-clean on
  `111` cases / `1,270` targets, average score `100.0`, min score `100`,
  hard failures `0`, failure kinds `{}`, residual decompile count `0`,
  generic args `0`, generic types `0`, radare2 candidates `0`
- broad Coreutils timeouts are eliminated in the current gate; the old
  timeout-heavy broad run had `case_setup_s=309.7`, `command_s=2271.6`, and 14
  command timeouts concentrated in `blake2b_compress`,
  `re_string_reconstruct`, `yyparse`, `install_file_in_file`, `chown_files`,
  and `who`
- current broad Coreutils timing is `case_setup_s=339.1`, `target_setup_s=12.3`,
  `setup_s=351.4`, `command_s=243.8`, and `setup_to_command_ratio=1.44`; setup
  reuse remains the visible performance bottleneck

This is now a strong Coreutils gate signal, not a declaration of "gold
standard" yet.

The broader May 2026 mixed limit run exposed the current production gap outside
that gate:

- corpus shape: Coreutils, generated kernel-like programs, manual source-gold
  cases, and local Linux kernel modules
- status: incomplete
- target count: `47`
- average score: `76.08`, which is misleading because closure failed
- timeouts: `6`
- source-oracle failures: `90`
- temp/stack leaks: `6`
- undefined identifiers: `2`
- fake structured loop class: observed once, then fixed to an explicit residual

This means the benchmark average is not a sufficient closure metric. The next
roadmap phase is certifying correctness: every rendered high-level construct
must be backed by checked canonical facts, and unknown structure must stay as a
residual or refusal. Summary reuse, budget caps, and bounded workers remain
necessary engineering controls, but they are not the correctness solution.

Latest certifying proof-loop status:

Completed:

- proof contract documentation and initial proof-kernel types
- retired detached proof counters and render-permission compatibility fields;
  typed route facts plus opaque typed-output seals now carry runtime policy
- prepared SSA certificates for loops, switches, if regions, expressions,
  memory accesses, stack slots, callsites, and return values
- return-value proof bridge from return-exit predecessor register writes
- field/layout proof retention in `FunctionTypeFacts` and `FunctionFacts`
- certified member rendering when a type/layout proof exists
- explicit residual rendering for unproven array/subscript output
- upstream `ArrayIndexCertificate` inference from typed aggregate layout and
  local field profiles, including external typedef aliases
- typed `SignatureCertificate` and `OutParamCertificate` projection surfaces
  in `r2types::FunctionTypeFacts`
- summary projection and decompile type overrides now use certified render
  signatures for authority decisions instead of raw `merged_signature`
- `OutParamCertificate` now carries projection evidence, and escape-only
  interproc summaries certify pointer flow but not writeback/out-param
  semantics
- `OutParamCertificate` now also carries exact source identity for semantic
  claims, native worker/region summaries, and interproc write/transfer effects
- out-param authority now requires source identity at the canonical type-fact
  boundary; decompiler comments and engine proof coverage ignore unsourced
  out-param certificates
- summary-kind signature projection now filters out name-hint worker summaries
  even when another non-name summary makes the artifact type-projectable
- certified repeated struct-array member rendering when field/layout proof
  covers the accessed members
- stable render-node IDs for structured-control validation, replacing the first
  count-only loop/switch gate with node-keyed certificate matching
- switch render-node shape and exact case-value checks against
  `SwitchCertificate` case/default evidence
- exact anchor matching between rendered loop/switch nodes and
  `LoopCertificate` / `SwitchCertificate` identities
- removed decompiler-side stack-home call-argument repair and the final
  reserved stack-home AST rewrite; stack-home/callsite correctness now has to
  come from upstream analysis facts or remain visible instead of being repaired
  after rendering
- explicit `SummaryRoleCertificate` materialization in `r2sym` for non-name
  evidence-backed summary roles
- exact summary-role identity enforcement in `r2dec` rendering and `r2types`
  summary-driven type projection; consumers now match summary certificates by
  stable summary identity, anchor, and kind instead of accepting any same-kind
  certificate
- strict closure-gate counters for fake stack slots, missing summary-role
  certificates, proof coverage gaps, temp/stack leaks, undefined identifiers,
  and fake-output classes
- raw lowercase SSA/register artifact detection in decompiler output
- r2r expectations for certified C and proof residuals
- removed the imported-call printf sibling repair path; call rendering now
  preserves explicit current callsite argument bindings and residualizes
  uncertified prepared call arguments instead of syncing them from a helper
  result
- strengthened call-argument source provenance with exact `ValueId` ownership,
  including preserved stack-home inputs and ABI register copies
- removed the iterative region fallback that invented numbered switch cases for
  unknown multi-successor control; no canonical case values now means an
  explicit irreducible/residual region with an analysis reason
- tightened structured-control validation so rendered loop/switch nodes match
  certificates by exact render-proof anchor identity instead of certificate
  order; partial certificate coverage now residualizes
- strengthened switch render validation so rendered case values must match
  canonical `SwitchCertificate` case values exactly; non-literal or mismatched
  rendered cases now force residual output
- strengthened switch selector validation so placeholder selectors such as
  `switch (test)` cannot satisfy a `SwitchCertificate` that carries canonical
  selector evidence
- strengthened loop render validation so rendered condition presence must agree
  with canonical `LoopCertificate` predicate evidence; unconditional `while (1)`
  no longer satisfies a certificate that proves a real loop condition
- wired loop condition `PredicateId` provenance through the folding/structuring
  seam and validated it against `LoopCertificate.condition`; a rendered loop
  with the wrong predicate now residualizes instead of masquerading as certified
  control flow
- wired loop condition `ValueId` provenance through the same render proof and
  validated it against the `PredicateFact.condition` referenced by
  `LoopCertificate.condition`; a same-anchor/same-predicate loop with the wrong
  rendered condition value now residualizes
- rewrote `ControlRenderProof` from kind+anchor markers into deterministic CFG
  proof tokens carrying loop body/latch/exit blocks and switch case/default
  targets, then validated those tokens against `LoopCertificate` and
  `SwitchCertificate`
- wired switch selector `ValueId` provenance through the folding/structuring
  seam and validated it against `SwitchCertificate.selector`
- promoted the fake loop/switch control class into recurring r2r coverage by
  building the manual source-gold limit fixture in the r2r harness and adding
  checks that accept explicit residuals or future source-grade control while
  rejecting known fake loop/switch renderings
- started expression/effect render-node closure by carrying exact return
  `ValueId` provenance in `EffectRenderProof` and validating it against
  `ReturnValueCertificate.value`
- extended expression/effect render-node closure to call and memory effects:
  call proofs now carry rendered argument `ValueId`s and memory proofs carry
  exact address/value `ValueId`s, with mismatches residualized
- closed call-target render proof closure: rendered call proofs now carry the
  callee target `ValueId` and must match `CallsiteCertificate.target`
- closed the first non-effect expression render proof gate: pure assignment
  RHS roots now require an exact renderable `ExpressionCertificate` for the SSA
  value defined at the rendered op site, and missing/mismatched expression proof
  residualizes instead of letting an unproven expression stand as certified C
- proved the first phi-backed expression class in `r2ssa`: identity phis over a
  single renderable `ValueId` can be certified as renderable expressions, while
  mixed/path-dependent phis remain unrenderable until stronger phi proof exists
- closed the prepared-call argument proof gap: `PreparedCallView`
  authoritative arguments now carry exact `ValueId` provenance, and strict
  rendering rejects right-looking call argument expressions whose values do not
  match `CallsiteCertificate.argument_values`; internal prepared call-result
  expressions also require a one-to-one argument/expression `ValueId` bijection
- started stack-home/out-param proof closure at the owner: `r2ssa`
  `CallsiteCertificate` now carries stack-pointer-relative call-home argument
  certificates with stack offset, stored `ValueId`, and memory-access proof, and
  `r2dec` strict call rendering consumes those certified stack values alongside
  register argument values
- removed name-only hash/crypto semantic authority from the summary/type path:
  `_hash` / `_hasher` / digest-family names no longer manufacture `HashFold`
  summaries or authoritative crypto signatures without structural evidence
- blocked all name-only native-worker summary materialization from
  `FunctionSemanticSummary::unknown(..., Some(name))`; worker summaries now need
  non-name semantic evidence, and libc-like summary seeds require import/PLT
  evidence instead of raw local names such as `malloc` or `memcpy`
- moved exported role signature/type projection off raw name-candidate helpers
  and onto `NativeWorkerRoleIdentity` evidence; `NameHint` role identities now
  refuse signature and type projection, while non-name evidence-backed roles can
  still project through the registry
- removed internal `r2types` interproc summary-name role projection: summaries
  now export observed effects and return relations only, exact role
  signatures/types require a non-name `NativeWorkerRoleIdentity`, and
  `HeapAlloc` return evidence maps directly to the semantic `allocation_ptr`
  typedef without consulting function names
- evidence-gated summary route policy: `PreferFull`, direct summary routing,
  summary applicability, and program-orchestrator preprobe decisions no longer
  fire from a bare name; engine preprobe policy now consumes route decisions
  from actual summary evidence when a summary exists
- explicit route certificates now own native-worker route authority:
  direct-summary and `PreferFull` routes require a `SummaryRouteCertificate`,
  name-family routes require compatible non-name worker evidence, arbitrary
  structural evidence no longer blesses unrelated names, and residual
  `summary_only` artifacts no longer drive type semantic fallback
- aligned the remaining `r2ssa` test-only summary seed helper with production
  import/PLT/reloc evidence rules; bare/local names such as `malloc`, `memcpy`,
  `sym.malloc`, and `sym._copyin` no longer seed semantic summaries even in
  interprocedural tests
- closed a structural-worker role identity leak: `r2sym` no longer lets a
  structural-only native-worker classifier inherit an arbitrary summary/function
  name as non-name `SummarySeed` evidence; structural-only workers keep
  canonical structural role names unless an interprocedural summary produced a
  primary non-name summary
- closed detached parameter-home return provenance: `r2dec` scalar
  return/predicate selection now consumes canonical `HiddenHome` /
  `ParamHome` stack-slot facts before accepting autogenerated `local_*` return
  names, so parameter-home returns render from typed facts instead of a final
  AST cleanup pass
- proof-gated synthesized source-call expressions: in certified mode `r2dec`
  now rebuilds an owned call-result expression from a source call only when the
  `CallsiteCertificate` target is renderable and the rendered arguments match
  certified argument `ValueId`s; mismatched prepared-call arguments refuse
  synthesis instead of manufacturing plausible helper-call C
- closed a false exact branch-proof bug in the symbolic engine: `BoolNot` now
  has logical semantics (`x == 0 ? 1 : 0`) for symbolic byte-sized flag
  carriers in both executor and backward precondition compilation, so an
  unconstrained argument flowing through stack memory no longer becomes an
  exact always-true branch proof
- tightened semantic branch pruning in `r2dec` so actionable/likely control
  islands no longer erase native branches unless the semantic artifact carries
  exact reachable-target evidence
- updated installed-plugin `r2r` closure after the fix: `alloc_and_copy` now
  renders the owned `malloc`/`memcpy` flow without residual/fallback output
- closed the `sum_array` residual checkpoint without weakening proof rules:
  the residual `ValueId(27)` / `ValueId(36)` pair was traced to version-0
  return-register phi-carrier copies (`EAX_1 = EAX_0`, `RAX_1 = RAX_0`), so
  `r2dec` now suppresses only that low-level carrier class at the
  SSA-to-statement boundary instead of certifying it as source semantics; the
  installed plugin renders a source-like `for` loop with no residuals or raw
  return-register artifacts
- tightened out-param proof ownership: summary rollups no longer classify
  escape-only pointer flow as an out-param, interproc memory writes to argument
  regions now produce explicit `InterprocMemoryWrite` out-param certificate
  evidence, and summary/fallback comments report certified out-param labels from
  `FunctionTypeFacts` instead of raw summary indices
- added explicit `SignatureCertificateSource` provenance so exact signature
  certificates record whether their proof came from external typed context,
  local inference, type assumptions, recovered variables, slot overrides,
  summary roles/kinds, semantic projection, or interproc summaries; `r2types`,
  `r2engine`, `r2dec`, `r2sleigh-plugin`, clippy, plugin install, and
  `tests/r2r` are green after the change
- enforced signature writeback authority at the certificate boundary: local
  inference remains visible as certificate provenance, but plugin mutation/FFI
  writeback now requires an exact `SignatureCertificate` with an authoritative
  source, and engine summary projection preserves the signature certificate
  when it changes the merged signature
- removed executable return synthesis from raw summary rollups: interprocedural
  `SummaryReturnRelation` data now stays visible as summary metadata and
  residualizes until an exact return-value render certificate owns the value
- tightened summary-render signatures: external parsed signatures now seed
  `ExternalContext` signature certificates, summary-only headers use
  `merged_signature` only when the current signature certificate authorizes it,
  and uncertified merged signatures fall back to explicit unknown/register-param
  rendering instead of silently shaping summary C
- closed the remaining decompiler-side signature render authority leak:
  `FunctionTypeFacts::render_authorized_signature()` is now the single
  type-owner gate for signature rendering, variable recovery, VM/summary
  headers, standard function params/return types, and `TypeInference` external
  signature hints; name/arity-only external certificates may render names but
  still refuse radare2 signature writeback when parameter types are incomplete
- closed the engine-side signature writeback leak: `r2engine` now derives
  bounded/semantic type writeback signatures only from
  `FunctionTypeFacts::writeback_authorized_signature()`, decompile type
  overrides copy signatures only when the override has render authority, and
  weak-summary argument contract checks use the same certified render gate
- closed the O0 `sparse_switch` residual checkpoint without weakening the proof
  gate: `r2dec` now recognizes transparent SSA branch-forwarder blocks made of
  non-return temp/status-flag copies plus a typed branch target, suppresses
  unreachable shared merge blocks after terminating if/else arms, uses
  predecessor return-value certificates for already-rendered branch-arm
  returns, and derives edge-specific phi return candidates from predecessor
  definitions. The live O0/O2 renders no longer residualize
- promoted O0 `sparse_switch` into recurring source-gold by adding typed,
  integer-only linear expression canonicalization. The decompiler now collects
  pure integer scalar additive terms into deterministic affine forms such as
  `a * 3 + b`, while pointer, stack/IP, float, untyped, call, memory, and other
  side-effecting terms remain uncollapsed

Still blocking gold closure:

- loop render closure now covers exact anchors, condition presence, predicate
  identity, predicate condition `ValueId`, body/latch/exit CFG membership; the
  remaining loop work is broader source-gold/adversarial coverage, not known
  certificate content
- switch render closure now covers exact anchors, case/default counts, case
  values, placeholder-selector rejection, selector `ValueId` equivalence, and
  case/default targets; remaining switch work is broader source-gold coverage,
  not known certificate content
- expression/phi certificates at the exact render-node granularity
- expression/phi closure now covers value returns, call targets, call
  arguments, memory address/value effects, and pure assignment RHS roots;
  remaining expression work is exact proof for nested/general expression nodes
  and non-identity/path-sensitive phi-backed rendered values
- call argument, out-param, and signature certificates strong enough to delete
  the remaining downstream stack-home/call/type rescue paths across all call
  and summary routes; prepared call arguments now require exact
  `CallsiteCertificate.argument_values` equality and stack-home arguments have
  first-class callsite certificates; escape-only out-param leakage is blocked
  and argument-region memory writes certify out-param evidence with exact source
  identity; unsourced out-param certificates are rejected before they can affect
  decompiler comments or proof coverage, while signature rendering now consumes
  only `SignatureCertificate`; summary projection and decompile type overrides
  use render-authorized signatures for authority decisions. Deeper call-output
  rendering and upstream exact signature projection proof are still open
- `SummaryRoleCertificate` rendering and summary-driven type projection now
  require exact summary identity, anchor, and kind; summary materialization from
  names alone and internal interproc summary-name role projection are blocked,
  and route decisions carry explicit certificates. Remaining summary-role work
  is auditing any other consumers and expanding compatibility coverage only
  when new non-name summary families justify it
- recurring source-gold closure gates still need expansion, but the manual
  fake loop/switch control cases now run in normal r2r
- full route ownership in `r2engine` across decompile, type, query, execution
  metrics, and refusal decisions
- the next concrete proof checkpoint is call-output/signature projection
  closure: prove call-output/writeback effects and exact signature projections
  from canonical certificates, then delete the remaining downstream rescue
  paths

Architecture Rewrite Direction
------------------------------

The next large step is a spine rewrite, not a blank-slate rewrite of every
crate. The current ownership map is right, but route selection, summary
classification, and callsite/type provenance still have too much heuristic
glue.

The intended fact flow is:

`radare2 typed context + lifted IL -> r2ssa canonical facts -> r2sym semantic
evidence -> r2types constraints -> r2engine request/route execution -> r2dec render`

The intended certifying render flow is:

`canonical facts + evidence -> checked claim -> render permission`

Where:

- `r2ssa` proves structural/dataflow facts: loops, switches, dominators,
  def-use, callsite provenance, memory regions, and stack slots.
- `r2sym` owns the evidence algebra, semantic claims, summary applicability, and
  ambiguity/refusal policy.
- `r2types` proves type/layout/signature projections from semantic and typed
  context evidence.
- `r2engine` routes by proof coverage, cost, budgets, and refusal policy.
- `r2dec` renders only from render permissions and explicit residuals.
- `r2plugin` exposes and applies results; it does not make semantic claims.

The required permission levels are:

- `CertifiedC`: emitted C construct is backed by checked canonical facts.
- `SummaryComment`: output is intentionally summary-driven and visibly marked.
- `Residual`: facts are insufficient for structured C, but partial information
  can be rendered honestly.
- `Refuse`: analysis exceeded a proof, cost, or evidence boundary.

Current certificate inventory:

Implemented or surfaced, with some render paths still partial:

- `LoopCertificate`
- `SwitchCertificate`
- `IfRegionCertificate`
- `ExpressionCertificate`
- `MemoryAccessCertificate`
- `FieldAccessCertificate`
- `StackSlotCertificate`
- `CallsiteCertificate`
- `ReturnValueCertificate`
- `ArrayIndexCertificate`
- `OutParamCertificate`
- `SignatureCertificate`
- `SummaryRoleCertificate`

Still needed for closure-quality output:

- exact render-node enforcement for every implemented certificate surface

Rewrite targets:

- `r2engine` becomes the single orchestration brain for decompile, type, query,
  execution metrics, refusal, and route decisions.
- `r2sym` summary classification becomes evidence-first. Symbol names are weak
  hints, not semantic ownership.
- `r2ssa` owns canonical stack slots, ABI callsite provenance, return
  provenance, memory regions, and switch/jump-table facts.
- `r2types` becomes a constraint/projection engine over radare2 types, ABI
  facts, callsite evidence, semantic summaries, imports, structs, and user
  assumptions.
- `r2dec` renders canonical facts and explicit residuals. It must not invent
  missing control flow, repair type policy, or hide placeholder facts.
- `r2plugin` calls typed request APIs and applies results. It should not own
  route policy, summary policy, budget policy, or semantic repair.

Known Heuristic Debt
--------------------

The following items are intentional short-term debt and should be retired, not
expanded:

- name-first native worker family matching in `r2sym`
- hardcoded role/signature tables used as authoritative facts
- duplicated route policy in `r2dec` and `r2engine`
- shape-only loop/switch rendering without checked certificates
- summary pseudo-calls standing in for real loop/control reconstruction
- remaining decompiler-side stack-home/call-argument rescue paths
- decompiler-side stack placeholder cleanup
- remaining switch rendering that lacks exact render-node/certificate identity
- fixed semantic worker island caps instead of evidence-ranked scheduling
- large decompiler thread stack as a workaround for recursive structuring
- benchmark averages that can mask incomplete status, timeouts, executable
  semantic-oracle failures, or fake-output classes
- source-shape checks that are not yet exercised in recurring advisory reports

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
   - use `O(1)` or `O(log n)` lookup for metadata, indexes, summaries, and local
     memoization
   - use `O(n)` passes over blocks, SSA ops, and fact sets where possible
   - use bounded search where search is unavoidable
   - reuse summaries and incrementally recompute instead of rediscovering facts

4. Prefer principled rewrites over downstream patchwork.
   - if a seam is bad, rewrite the seam
   - if policy is in the wrong crate, move it
   - if output only works because of a downstream patch, fix the upstream fact

5. Determinism beats cleverness.
   - stable ordering and stable semantic fingerprints are correctness requirements

6. Refusal is better than silent nonsense.
   - budgets, residual reasons, confidence, and evidence must stay explicit

7. Proof beats appearance.
   - high-level C is allowed only after the checker seals exact typed output
   - failed proof obligations become residuals or refusals, not prettier guesses
   - summary reuse and caps can make analysis cheaper, but cannot justify semantics

Certifying Decompiler Execution Plan
------------------------------------

This is the next correctness spine. The goal is not a full formal proof system
on day one; the goal is a local proof kernel that prevents fabricated C and
makes every rendered construct traceable to its canonical owner.

### Phase 0 - Proof Contract And Fake-Semantics Gate

Deliverables:

- design document for source-owned obligations, closed ledgers, typed routes,
  and opaque output seals
- opaque typed-output seal retaining exact source identity
- canonical proof failure reasons that can be surfaced in engine reports,
  decompiler residuals, and benchmarks
- recurring negative tests for fake loops, fake switches, fake stack slots,
  fake call arguments, fake signatures, and name-only summaries

Success criteria:

- incomplete proof means residual/refusal
- benchmark closure fails if fake-output counters are non-zero
- average score cannot override incomplete status, timeouts, or executable
  semantic-oracle failure; source-shape comparisons remain advisory

### Phase 1 - Control Certificates

Owners:

- `r2ssa`: loop/switch/region certificates from CFG, dominators, dominance
  frontiers, backedges, exits, and jump-table evidence
- `r2sym`: feasibility and path evidence when structure depends on semantic
  reachability
- `r2dec`: render only certified loops/switches/regions

Deliverables:

- `LoopCertificate`
- `SwitchCertificate`
- `IfRegionCertificate`
- residual rendering for unproven or irreducible regions
- r2r/source-gold coverage for the kernel-style fake-loop class

Success criteria:

- no `while`, `for`, `do`, or `switch` appears unless the matching certificate
  exists
- unstructured control remains explicit and stable
- large functions fail boundedly instead of consuming unbounded wall time

### Phase 2 - Expression Certificates

Owners:

- `r2ssa`: def-use, value ranges where local, phi provenance, and expression
  DAG ownership
- `r2sym`: path-sensitive equalities, constraints, and ambiguity evidence
- `r2dec`: expression rendering from certified value provenance only

Deliverables:

- `ExpressionCertificate`
- phi/use certificates for merged values
- residual expression nodes for unproven temps/registers
- deterministic expression simplification order

Success criteria:

- no undefined identifiers in rendered C
- temp/register leaks are counted as proof failures unless explicitly residual
- simplification never changes the proven value domain

### Phase 3 - Memory, Stack, And Layout Certificates

Owners:

- `r2ssa`: memory regions, stack slots, load/store provenance, alias buckets
- `r2types`: field, array, aggregate, pointer, and out-param layout projection
- `r2sym`: semantic memory effects and summary-backed memory claims

Deliverables:

- `MemoryAccessCertificate`
- `StackSlotCertificate`
- `FieldAccessCertificate`
- `ArrayIndexCertificate`
- `OutParamCertificate`

Success criteria:

- no fake locals, fake fields, or fake array indexes
- struct field recovery is source-grade on source-gold cases before it is
  called closure
- unsafe layout candidates carry refusal reasons instead of being rendered as
  confident C

### Phase 4 - Callsite And Signature Certificates

Owners:

- `r2ssa`: ABI argument locations, callsite def-use, return provenance
- `r2types`: signature normalization and type projection
- `r2sym`: semantic role evidence and summary applicability

Deliverables:

- `CallsiteCertificate`
- `ReturnValueCertificate`
- `SignatureCertificate`
- `SummaryRoleCertificate`
- name hints represented as weak evidence, never as authority

Success criteria:

- no decompiler-side call argument repair
- no hardcoded role signature overrides without typed or structural evidence
- helper summaries remain visibly summary-driven unless true native control/data
  facts are certified

### Phase 5 - Engine Routes By Proof Coverage

Owner:

- `r2engine`

Deliverables:

- proof coverage metrics in request reports
- render route selected from available certificates, summaries, and budgets
- typed refusal policy for timeout, solver budget, missing certificate, and
  ambiguous evidence
- request-local preparation bound to proof-relevant inputs and schema versions

Success criteria:

- route policy exists in one crate
- repeated requests deterministically rebuild the same checked artifacts
- caps prevent blowups but do not convert unknowns into semantics

### Phase 6 - Proof-Aware Benchmarks And Semantic Closure

Owners:

- benchmark harness, source oracle, and recurring local acceptance

Deliverables:

- proof/fake-output counters in benchmark reports
- source-shape checks retained as advisory diagnostics for generated
  kernel-like programs and manual tricky cases
- closure-gate mode that fails on incomplete status, timeouts, oracle failures,
  fake-output counters, fake stack slots, missing summary-role certificates,
  proof coverage gaps, undefined identifiers, and temp/stack leaks
- owner buckets for proof failures

Success criteria:

- closure is impossible when status is incomplete
- executable semantic-oracle failures block closure even if average score is
  high; source-shape mismatches block only source-likeness claims
- every failure family is assigned to a canonical owner before feature work

Completed proof-closure work:

1. Added `doc/certifying_decompiler.md`.
2. Added the initial checked-claim/proof-failure/render-permission spine.
3. Added prepared SSA certificate surfaces for loop, switch, if-region,
   expression, memory, stack-slot, callsite, and return-value facts.
4. Added a return-register predecessor bridge for `ReturnValueCertificate`.
5. Preserved field/layout certificates through `FunctionTypeFacts` and
   `FunctionFacts`.
6. Made member rendering depend on type/layout proof instead of cleanup.
7. Residualized array/subscript rendering when `ArrayIndexCertificate` is
   missing.
8. Added raw lowercase SSA/register artifact rejection in standard C output.
9. Updated plugin/r2r expectations for certified C and proof residuals.
10. Added strict closure-gate benchmark counters for fake stack slots,
    summary-role certificate gaps, and proof coverage gaps.
11. Revalidated the full local bar, including `make -C tests/r2r run`.
12. Deleted the imported printf sibling repair path and replaced it with exact
    callsite source provenance plus certified/residual call-argument rendering.
13. Removed the fake switch-case fallback in iterative region composition:
    unknown multiway control now residualizes instead of emitting synthetic
    `case 0`, `case 1`, ... C.
14. Tightened structured-control proof checks from ordered certificate slots to
    exact render-proof anchors for loops and switches, including partial
    certificate coverage residuals.
15. Closed the next switch fake-output gap: rendered switch case values must
    exactly match `SwitchCertificate` values, and non-literal/mismatched cases
    residualize.
16. Closed the next loop fake-output gap: rendered loop condition presence must
    agree with `LoopCertificate` predicate evidence, so unconditional loops do
    not masquerade as certified conditional loops.
17. Closed the next switch selector fake-output gap: placeholder selectors are
    rejected whenever `SwitchCertificate` has canonical selector evidence.
18. Rewrote control render proofs to carry exact rendered loop CFG membership
    and switch targets; loop body/latch/exit mismatches and switch case/default
    target mismatches now residualize.
19. Closed switch selector provenance: rendered switch proofs now carry the
    selector `ValueId` used by the folding path and must match
    `SwitchCertificate.selector`.
20. Closed loop condition predicate provenance: rendered loop proofs now carry
    the `PredicateId` used by the folding path and must match
    `LoopCertificate.condition`.
21. Closed loop condition value provenance: rendered loop proofs now carry the
    predicate condition `ValueId` and must match the `PredicateFact.condition`
    referenced by `LoopCertificate.condition`.
22. Promoted manual source-gold fake-control coverage into r2r: the
    `manual_limits` fixture now builds as O0/O2 r2r binaries and checks
    table-walk/sparse-switch output for either honest residuals or future
    source-grade control, never fake loop/switch C.
23. Started exact expression/effect proof closure by extending return render
    proofs with the returned `ValueId` and rejecting mismatches against
    `ReturnValueCertificate.value`.
24. Extended exact effect proof closure to calls and memory: rendered call
    proofs validate callee target and argument `ValueId`s against
    `CallsiteCertificate`, and rendered memory proofs validate address/value
    `ValueId`s against `MemoryAccessCertificate`.
25. Removed the name-only hash/crypto semantic path: `r2sym` no longer creates
    `HashFold` summaries from `_hash` / `_hasher` / digest-family names, and
    `r2types` no longer projects authoritative crypto signatures from those
    names alone.
26. Blocked broad name-only native-worker summary materialization: unknown
    summaries carrying only a symbol name now produce no native-worker
    summaries, direct summary routes reject name-only applicability, and known
    libc summary seeds require import/PLT-shaped evidence.
27. Moved the public role signature/type projection seam to
    `NativeWorkerRoleIdentity`: exported callers can no longer ask `r2types` for
    authoritative signatures from arbitrary names, and `NameHint` identities are
    rejected by the projection API.
28. Removed the internal interproc summary-name role projection path in
    `r2types`: role signatures/types no longer come from summary root/function
    names, exact role projection is gated on non-name role identity evidence,
    callee facts retain only observed summary effects, and heap allocation
    return typing is derived from `SummaryReturnRelation::HeapAlloc`.
29. Evidence-gated native-worker route policy: `r2sym` no longer allows
    name-only `PreferFull` or direct-summary route decisions, `r2engine`
    preprobe/large-CFG decisions consume summary-backed route policy when a
    semantic summary exists, and `tests/r2r` remains green on 94 plugin tests.
30. Added explicit `SummaryRouteCertificate` route certificates:
    direct-summary, `PreferFull`, summary applicability, and named route-family
    decisions now require compatible non-name worker evidence; unrelated
    structural evidence no longer certifies arbitrary symbol families; residual
    `summary_only` artifacts are barred from type semantic fallback; and
    `tests/r2r` remains green on 94 plugin tests.
31. Added exact non-effect expression-root render proofs: certified pure
    assignment RHS roots now require a renderable `ExpressionCertificate` whose
    defining op site matches the rendered statement; missing, unknown, or
    wrong-site expression proof residualizes, and stack/local stores prove the
    consumed RHS `ValueId` rather than inventing a destination value; `cargo
    test -p r2dec`, `cargo clippy -p r2dec --all-targets -- -D warnings`, and
    `tests/r2r` are green on 94 plugin tests.
32. Added identity-phi expression certificate closure in `r2ssa`: a phi output
    is renderable only when every incoming edge carries the same renderable
    `ValueId`; mixed phis remain explicit unrenderable expression facts rather
    than becoming guessed C.
33. Added exact prepared-call argument value proof: `PreparedCallView` now
    stores `authoritative_arg_values` beside rendered argument expressions,
    strict rendering requires those values to equal
    `CallsiteCertificate.argument_values`, and mismatched prepared arguments
    residualize instead of rendering plausible but unproved call C; prepared
    call-result expressions also refuse argument lists without the same
    value/expression bijection.
34. Added first-class stack-home call argument certificates: `r2ssa`
    callsite certificates now record stack-pointer-relative stored argument
    values with their stack offsets and memory-access proof, and `r2dec` strict
    rendering accepts stack-passed prepared arguments only through that
    certified value stream.
35. Fixed symbolic `BoolNot` as a logical operation in `r2sym::SymValue` and
    routed both executor and backward branch-precondition compilation through
    it. This removes the false exact proof where byte-sized `!ZF` simplified to
    always-true after bitwise `~ZF`, preserving both branches for unconstrained
    arguments.
36. Made semantic branch erasure require exact reachable-target evidence in
    `r2dec`; likely/actionable control facts may still inform residual/summary
    rendering, but they no longer delete native branches.
37. Revalidated the full local bar again: package tests, full `r2ssa` /
    `r2sym`, all required clippy checks, all-arch plugin install, and
    `make -C tests/r2r run` are green on 94 plugin tests.
38. Closed the current `sum_array` expression-residual checkpoint by proving the
    residuals were not source expressions: they were version-0 return-register
    phi carriers inserted by phi materialization, so `r2dec` suppresses only
    that low-level carrier class before certified expression residualization.
    The regression now requires a source-like `for` loop, no residual comments,
    and no raw `eax_` / `rax_` artifacts.
39. Tightened out-param certificate closure: `InterprocSummaryView` rollups and
    helper views no longer treat escape-only pointer flow as writeback,
    argument-region memory writes create explicit `InterprocMemoryWrite`
    certificate evidence, and summary/fallback output reports certified
    out-param labels from canonical type facts.
40. Added signature-certificate source tracking: exact
    `SignatureCertificate`s now carry deterministic provenance for external
    typed context, local inference, assumptions, recovered variables, slot
    overrides, summary roles/kinds, semantic projection, and interproc
    summaries, keeping signature proof from collapsing into an unqualified
    "exact" bit.
41. Consumed signature certificate provenance in the plugin writeback boundary:
    signature and callconv mutations plus FFI signature facts are emitted only
    when the current `SignatureCertificate` has an authoritative source
    (`ExternalContext`, explicit assumption, recovered variable, slot override,
    evidence-backed summary role, semantic projection, or interproc summary).
    Local-only inferred signatures are reported but refused for radare2
    mutation, and engine decompile type overrides now preserve the matching
    signature certificate instead of copying only the signature text.
42. Removed the raw summary-return executable path: `SummaryReturnRelation`
    rollups no longer render `return argN`, `return allocated_memory`, constants,
    or globals without a first-class return-value render certificate. The
    relation remains visible in summary comments and unresolved returns now
    residualize with an explicit comment.
43. Enforced signature certificate authority for summary-rendered function
    headers: parsed external context now seeds `ExternalContext`
    `SignatureCertificate`s, external `void *` and exact empty-arity signatures
    can be certified as explicit source types, and summary-only rendering ignores
    uncertified `merged_signature` values.
44. Enforced exact `SummaryRoleCertificate` identity for summary rendering:
    worker summary certificate IDs are derived from summary content, native
    region certificates use region identity, and `r2dec` accepts summary-backed
    rendering only when `(stable_id, anchor, kind)` matches the rendered
    summary.
45. Extended exact `SummaryRoleCertificate` authority into summary-driven type
    projection: `r2types` no longer projects role type hints from any same-kind
    worker or region summary, while uncertified generic memory summaries still
    emit explicit out-pointer refusal diagnostics instead of silently inventing
    pointer writeback facts.
46. Revalidated the current summary-role proof checkpoint with focused
    `r2sym` / `r2dec` / `r2types` tests, package tests for `r2types`,
    `r2engine`, `r2dec`, and `r2sleigh-plugin`, clippy for the touched crates
    including all-arch plugin clippy, and `make -C tests/r2r run` green on 94
    plugin tests.
47. Added exact source identity to `OutParamCertificate`: out-param certificates
    now retain semantic-claim IDs, native worker/region summary IDs, and
    interproc write/transfer effect origins instead of exposing only broad
    evidence categories. Focused out-param tests, full `r2types` tests,
    downstream `r2engine` / `r2dec` / `r2sleigh-plugin` tests, and clippy for
    the touched/downstream crates are green; `make -C tests/r2r run` is green
    on 94 plugin tests after the contract change.
48. Made exact out-param source identity mandatory for consumer authority:
    `FunctionTypeFacts` drops unsourced out-param certificates, `r2dec` reports
    only source-authorized out-param labels, and `r2engine` proof coverage
    counts only source-authorized out-param certificates. Focused tests,
    package tests for `r2types`, `r2engine`, `r2dec`, and `r2sleigh-plugin`,
    clippy for the touched/downstream crates, and `make -C tests/r2r run` are
    green on 94 plugin tests.
49. Tightened the first remaining signature-authority leak in `r2engine`:
    summary projection now derives parameter counts and preserve-context
    decisions from `render_authorized_signature()`, decompile type overrides
    return only render-authorized signature facts, and an uncertified inferred
    local signature blocks weaker parsed-context override fallback instead of
    widening richer local struct facts. Focused regression, package tests for
    `r2types`, `r2engine`, `r2dec`, and `r2sleigh-plugin`, plus clippy for the
    touched/downstream crates and `make -C tests/r2r run` are green on 94
    plugin tests.
50. Tightened signature proof coverage accounting: `r2engine` now counts a
    certified signature only when `FunctionTypeFacts::render_authorized_signature()`
    accepts the current `merged_signature`, so stale or mismatched certificates
    cannot inflate proof metrics. The focused engine regression and
    `cargo fmt --check` are green for this checkpoint.
51. Closed the plugin writeback stale-certificate gap: signature/callconv
    mutation payloads now require
    `FunctionTypeFacts::writeback_authorized_signature()` rather than trusting
    certificate sources alone, and a stale external `SignatureCertificate` no
    longer mutates radare2 or emits an FFI signature fact. The focused stale-cert
    regression and full `cargo test -p r2sleigh-plugin` are green.
52. Closed the remaining broad summary-role signature-hint path: `r2types`
    exposes `signature_hint_for_semantic_artifact()` and requires a current
    non-name `SummaryRoleCertificate` before role identity or summary-kind
    signatures can influence inferred/writeback signatures; `r2engine` now uses
    that certified semantic-artifact helper instead of reading `role_identity`
    directly. Full `cargo test -p r2types` and `cargo test -p r2engine` are
    green.
53. Tightened summary-route certificate matching in `r2sym`: direct-summary,
    prefer-full, and standard summary-route eligibility now require a certificate
    whose route kind matches the policy, whose source is not `NameHint`, and
    whose evidence is usable. Stale-kind and name-hint certificate regressions
    were added; full `cargo test -p r2sym` and `cargo test -p r2engine` are
    green.
54. Tightened benchmark closure semantics: `--closure-gate` now requires at
    least one exercised source-gold expectation by default, instead of merely
    capping gold failures at zero. Focused benchmark gate tests are green.
55. Made source-gold owner attribution mandatory at manifest load time: each
    oracle expectation must name a canonical subsystem owner (`radare2`,
    `r2ssa`, `r2sym`, `r2types`, `r2engine`, `r2dec`, or `r2plugin`) so oracle
    failures cannot disappear into the `unknown` bucket. Full
    `python3 -m unittest tests.test_reversing_benchmark` is green and the
    checked-in source oracle loads with 18 owner-attributed expectations.
56. Closed the raw interproc call-output summary-view gap: `r2types`
    `InterprocSummaryView` no longer stores anonymous `out_param_indices`.
    Root and helper summaries now expose deterministic `SummaryOutParamFact`
    entries, each carrying the exact `InterprocSummaryEffect` source and
    evidence kind (`arg_write`, `memory_write`, or `transfer_dst`) that justifies
    the output parameter. Focused regression plus package tests for `r2types`,
    `r2engine`, `r2dec`, and `r2sleigh-plugin` are green.
57. Tightened native worker/region out-param certificate identity:
    `OutParamCertificateSource::NativeWorkerSummary` and
    `NativeRegionSummary` now carry summary kind and parameter index, and
    source authorization rejects mismatched native evidence or stale parameter
    claims. Focused regression plus package tests and clippy for `r2sym`,
    `r2types`, `r2engine`, `r2dec`, and `r2sleigh-plugin` are green.
58. Closed the remaining decompiler summary-comment output-parameter leak:
    the user-visible `out_args` count in semantic summary comments now comes
    from `FunctionTypeFacts::source_authorized_out_param_certificates()` rather
    than raw semantic claim rollups. A focused r2dec regression covers the
    previous uncertified-count behavior, and `cargo test -p r2dec -p
    r2sleigh-plugin`, clippy for both crates, and `make -C tests/r2r run`
    are green on 94 plugin tests.
59. Removed out-param proof double-ownership from `r2sym`: semantic claims can
    still seed type analysis, while certified out-parameter proof now
    comes only from `r2types::FunctionTypeFacts` source-authorized certificates.
    A focused r2sym regression, package tests for `r2sym`, `r2types`,
    `r2engine`, `r2dec`, and `r2sleigh-plugin`, and clippy for those crates are
    green.
60. Removed field/layout proof double-ownership from `r2sym`: semantic
    `StructField` type-seed claims do not authorize rendering. Certified field/layout proof now
    comes from `r2types::FunctionTypeFacts` field certificates and prepared
    render proof, not raw semantic claim rollups. A focused r2sym regression,
    package tests for `r2sym`, `r2types`, `r2engine`, `r2dec`, and
    `r2sleigh-plugin`, clippy for those crates, and `make -C tests/r2r run`
    are green on 94 plugin tests.
61. Historical: semantic report counters were separated from certified proof
    counters. Both detached counter and permission surfaces are now deleted;
    semantic reports remain advisory and exact owners plus typed seals govern
    rendering and writeback.
62. Made summary-projection output explicitly non-native-CFG: summary-rendered
    loops now say `summary projection (not native CFG)`, route comments include
    a render contract that native CFG/control was not reconstructed, and
    uncertified role identities render as `summary role hint` instead of
    `semantic role`. Certified summary roles still require exact
    `SummaryRoleCertificate` identity. Focused r2dec tests, full r2dec/plugin
    tests, formatting, clippy, `make -C r2plugin RUST_FEATURES=all-archs
    install`, and `make -C tests/r2r run` are green on 94 plugin tests.
63. Made plugin/debug signature authority explicit: type writeback JSON now
    reports `signature_render_authorized`, `signature_writeback_authorized`,
    certificate sources, and a `signature_writeback_refusal` reason when the
    visible signature is not safe to mutate into radare2. Render-only local
    certificates and stale exact certificates now have distinct tested outcomes.
    Focused plugin tests, full plugin tests, formatting, clippy with
    `all-archs`, `make -C r2plugin RUST_FEATURES=all-archs install`, and
    `make -C tests/r2r run` are green on 94 plugin tests.
64. Made summary route certificates carry their compatibility evidence:
    `SummaryRouteCertificate` now records the exact
    `route_evidence_kinds` worker-kind set and includes that set in its stable
    identity, so direct-summary/prefer-full authority is inspectable and changes
    when the non-name evidence changes. Focused r2sym regressions, package tests
    for `r2sym`, `r2types`, `r2engine`, `r2dec`, and `r2sleigh-plugin`,
    formatting, clippy for those crates, release plugin install, and
    `make -C tests/r2r run` are green on 94 plugin tests.
65. Promoted the source-gold closure loop into a checked manifest/gate:
    `tests/gold/closure_manifest.json` now drives the manual limit fixtures
    plus repo fixtures through `scripts/reversing_benchmark.py --closure-gate`,
    and the benchmark quality gate now treats missing summary render contracts
    as fake-semantics failures. The benchmark unit suite is green. The current
    local source-gold run is intentionally blocking, not ignored:
    `/tmp/r2sleigh-source-gold-closure-after-projection.json` reports average
    score 66.67, 54 hard failures, 8 residual decompiles, 2 proof coverage
    gaps, 2 undefined-return leaks, and 44 source-oracle failures.
66. Removed summary-family signature over-certification: `r2types` now preserves
    the projection source from semantic artifacts, so a strong certified role
    identity and a weak summary-kind fallback are no longer collapsed into the
    same `SummaryRole` certificate. `SummaryRole` certificates are render-only
    and no longer authorize radare2 writeback by themselves. This closed the
    source-gold signature drift for `parse_number` and `mem_scan2`, moved the
    closure report from 56.67 to 66.67 average score, and reduced owner-bucketed
    hard failures (`r2types` 18 -> 14, `r2sym` 33 -> 30). Focused `r2types` /
    `r2engine` tests, plugin tests, formatting, release plugin install, and the
    source-gold closure rerun were completed.
67. Removed false byte-transform hash-fold evidence: `r2sym` now refuses to
    emit `HashFold` worker summaries when the observed "accumulator" is only a
    literal operand such as `loaded_byte + 0x20`. Real accumulator identities
    still support additive folds, while parser/digit evidence remains available
    to its existing owner. The source-gold closure rerun confirms `fnv_fold`
    no longer gets misleading `HashFold` evidence; it remains an honest
    residual because the real FNV `xor` fold is still blocked by low-register
    alias provenance across the lowercase byte transform. Focused hash-fold
    tests, full `r2sym` tests, release plugin install, and the source-gold
    closure rerun were completed.
68. Fixed decompile/type signature drift in residual headers: `r2engine`
    decompile override selection now privileges the authoritative typed
    radare2 context before native-worker summary projections, and only accepts
    native projections that have render-authorized signatures. This keeps weak
    or unrenderable summary type projections from blocking a certified external
    signature. `fnv_fold` now residualizes with the correct `uint64_t` header in
    both `a:sla.dec` and `pdd`. Full `r2engine` tests, release plugin install,
    a live radare2 check, and the source-gold closure rerun were completed; the
    closure remains blocking at average score 66.67, but header mismatch
    failures are gone and source-oracle failures dropped 44 -> 43.
69. Promoted pointer-rooted table-walk evidence into the canonical route:
    `r2sym` now classifies argument-rooted pointer-width null checks as
    `TableWalk` evidence instead of byte string scans, while byte-width zero
    checks remain string scans. `r2engine` now treats bounded `StringScan` and
    `TableWalk` worker summaries with memory plus known terminators as
    renderable summary evidence, so `dbg.table_walk` moves from residual-only
    output to explicit `native_linear_summary` output in both `a:sla.dec` and
    `pdd`. Focused r2sym/r2engine regressions, full `r2sym` and `r2engine`
    tests, release plugin install, live radare2 checks, and the source-gold
    closure rerun were completed. The closure is still blocking at average
    score 66.67, but `table_walk` residual decompiles are gone, source-oracle
    failures dropped 43 -> 41, and the `r2sym` owner bucket dropped 30 -> 26.
70. Removed pointer/field-width additive false `HashFold` evidence from native
    worker summaries: `r2sym` now only promotes fold observations into
    `HashFold` when the loaded source is a byte-stream source with a real
    accumulator identity. Pointer-width and field-width arithmetic remains
    numeric/reduction evidence instead of being mislabeled as hash semantics.
    Focused hash-fold tests, full `r2sym` tests, release plugin install, live
    `dbg.table_walk` checks, and the source-gold closure rerun were completed.
    This did not move the aggregate score yet, but `table_walk` now reports no
    `HashFold` worker/region summaries and its native summary island count
    dropped 11 -> 9 without hiding residual return uncertainty.
71. Corrected summary-only table/list route ownership: `r2engine` now routes
    summary-only scan/table workers through `SummaryIslands` instead of the
    native-linear summary route, and `r2dec` now renders canonical worker
    summary comments alongside native region-island summaries when both facts
    exist. This keeps the output explicit that CFG/control was not
    reconstructed while still exposing the `string_scan` and `table_walk`
    evidence that r2sym proved. Full `r2engine` and `r2dec` tests, release
    plugin install, live `a:sla.dec`/`pdd` checks, and the source-gold closure
    rerun were completed. Source-oracle failures dropped 41 -> 37, the `r2sym`
    owner bucket dropped 26 -> 22, and `table_walk` hard failures dropped
    9 -> 6 with no residual decompile commands.
72. Closed the first sparse-switch source-shape tranche without weakening the
    proof gate: `r2dec` now keeps predecessor-specific return-register phi
    proofs when structuring branch returns, normalizes those structure-level
    return expressions through the same typed scalar return sanitizer, rejects
    address-of stack/parameter artifacts in scalar returns, proves the direct
    x86 sign-extended `idiv` dividend shape, folds repeated linear additions
    such as `a + a + a`, and rewrites only zero-guarded division branch returns
    to ternary form. The O2 `sparse_switch` path now renders the source cases
    without `t49900`/`t49a00` leaks; the O0 path fails closed with an explicit
    certified-render residual instead of emitting fake `&a - b` / `&b + a`
    scalar returns. Full `r2dec` tests, release plugin install, live radare2
    checks, and `make -C tests/r2r run` are green on 95 plugin tests.
73. Closed the opaque-layout timeout/refusal checkpoint at the engine boundary:
    plugin command paths now request full semantics uniformly, while
    `r2engine` owns the bounded refusal policy for opaque aggregate signatures.
    Opaque pointer signatures such as `Item*` no longer count as concrete
    layout evidence unless the typed context carries real struct/union/enum
    fields, and optional semantic work now requires bounded local memory/layout
    proof instead of relying on names or broad type hints. `r2ssa` fallback
    memory certificates now carry op-derived width/value facts, and `r2dec`
    propagates certified memory-read proofs through returned value dependencies
    instead of rendering unproved raw artifacts. Live `struct_nested_array`
    type/decompile commands dropped from the prior 20s-class blowup to roughly
    0.5s and now fail closed with an explicit certified-render residual instead
    of fake field/index C. `cargo test -p r2engine`, `cargo test -p r2ssa`,
    `cargo test -p r2dec`, `cargo test -p r2sleigh-plugin`, release plugin
    install, and `make -C tests/r2r run` are green. The source-gold closure gate
    remains intentionally failing at 66.67 average score with 29 source-oracle
    failures, 2 proof-coverage gaps, and 2 unresolved/temp-stack leaks; there
    are no timeouts, and every measured command is now under one second.
74. Closed the `struct_nested_array` source-gold checkpoint without adding
    fixture-specific rendering: `r2types` now proves external aggregate
    pointer strides, affine index factors, cross-block address identities, and
    nested external field/array certificates such as `Item.scores[2]`;
    `r2dec` renders external nested array members with access-size-aware layout
    proof, prefers concrete external layout over coarse radare2 field names,
    materializes only proven raw carrier definitions, and builds prepared
    render definitions from SSA facts instead of leaking `tmp`/`edx` carriers;
    `r2engine` skips full symbolic semantics for concrete-layout, acyclic,
    call-free functions when prepared/type proofs already satisfy the route.
    Live `struct_nested_array` now renders source-shaped `items[idx].scores[2]`,
    `items[idx].flags`, `items[idx].id`, `items[idx].scores[0]`, and
    `items[idx].len` under the active certified-render gate. The source-gold
    manifest confirms this expectation is green and the benchmark decompile
    time for the target dropped from 24s-class to roughly 0.08s.
75. Closed the post-struct validation checkpoint and advanced the loop from
    local correctness to the next source-gold blocker. `cargo test -p r2dec`,
    `git diff --check`, and `make -C tests/r2r run` are green; the plugin-facing
    r2r suite is 95/95. The recurring source-gold run remains intentionally
    failing at 66.67 average score, but the failure set is narrower: 23
    source-oracle failures remain, with hard failures only in `fnv_fold`,
    `out_param_parse`, and `table_walk`. `sparse_switch` no longer has hard
    source-gold failures after the certified return-cast cleanup; it remains on
    the list only because one residual route still needs exact proof closure.
76. Closed the `fnv_fold` source-gold checkpoint through upstream evidence
    repair rather than renderer special-casing. `r2sym` now treats the original
    memory-access width, not the widened SSA carrier width, as the byte-stream
    proof for hash-fold classification, and its worker dataflow tracks
    size-adapted SSA identities so a normalized one-byte low-register view can
    reuse the proven wider carrier provenance while kills remove stale views of
    the same identity. Live `fnv_fold` now renders the certified summary
    projection with the FNV offset basis, lowercase byte transform, XOR,
    multiply, and `return summary_hash;` under a `hash_fold` summary role. The
    source-gold closure run now reports 14 remaining source-oracle failures:
    hard failures are only `out_param_parse` and `table_walk`; `sparse_switch`
    is still a residual-proof cleanup item with no hard oracle failure.
77. Advanced `out_param_parse` from name/summary hints to canonical `r2sym`
    evidence. Worker dataflow now tracks pointer locations separately from load
    provenance, preserves proven `out + offset` locations through invalidation,
    records `MemoryWrite` summaries for stores through canonical argument
    locations, interprets two's-complement additive constants for byte/parser
    provenance, maps transformed equality checks back to source-byte values,
    classifies the numeric parser as base-10 with sign handling, and attaches
    `dst=out` when parser evidence is paired with multiple distinct writes to a
    different pointer argument. `r2dec` no longer renders an out-param parser as
    a fake parsed-value return. Focused `r2sym`/`r2dec` tests, full `r2sym`
    tests, release plugin install, live `a:sla.debug.types`/`a:sla.dec` checks,
    and the source-gold closure run were completed. The remaining
    `out_param_parse` failures are field/writeback and success-return proof
    gaps owned by `r2types`/canonical projection (`out->code/hash/count/hit`,
    success return, and removal of unresolved summary return).
78. Closed the `out_param_parse` summary-visibility gap without making the
    decompiler invent new semantics. `r2plugin` now imports DWARF base types
    through radare2 typed APIs before typed-context snapshotting, so source
    layouts such as `Result` and `Item` are available to the canonical type
    seam when present. `r2dec` now chooses worker-summary display rows by
    deterministic evidence coverage: the ordinary cap still keeps summaries
    bounded, but late `Parser(dst=out)` and `MemoryWrite` facts remain visible
    instead of being hidden behind earlier generic folds. A focused display
    regression and full `cargo test -p r2dec` are green, release plugin install
    is green, and live `a:sla.dec` now contains
    `worker summary: parser: dst=out mem=s` and
    `worker summary: memory_write: mem=out`. The source-gold rerun remains
    intentionally failing at 66.67 average score with 12 source-oracle failures:
    6 in `out_param_parse` (`r2types`) and 6 in `table_walk` (`r2sym`);
    `sparse_switch` has no hard oracle failure but still has one residual route.
79. Closed the `out_param_parse` result-field certificate gap through canonical
    summary/type projection instead of decompiler cleanup. `r2types` now projects
    exact `r2sym` `MemoryWrite` summary locations into external struct-field
    certificates when the typed signature points at a known layout, and
    `r2engine` applies the same augmentation on the bounded native-preprobe type
    route used by plugin type/debug requests. `r2dec` renders those as explicit
    certified field-access comments, not as invented executable C. Focused
    `r2sym`, `r2types`, `r2engine`, and `r2dec` tests are green, formatting is
    green, release plugin install is green, and the source-gold closure rerun
    now reports 8 remaining source-oracle failures: 2 in `out_param_parse`
    (`r2types`, exact success return and removal of unresolved return marker)
    and 6 in `table_walk` (`r2sym`, linked-list loop/field/return proof).
80. Closed the `out_param_parse` success-return checkpoint through a canonical
    `r2sym` parser-return predicate, not a decompiler guess. Worker dataflow now
    records zero-comparison guards and proves when a parser cursor is both
    non-zero and positioned at a zero terminator. That proof is included in the
    worker-summary stable content id, re-exported through the semantic contract,
    and consumed by `r2dec` only when the summary role is certified. Structured
    summary rendering now preserves the worker evidence comments that justify
    the projection and keeps the standard synthetic-local marker. Focused
    `r2sym`/`r2dec` tests, formatting, release plugin install, live radare2
    checks, and the source-gold closure rerun are green for the parser family.
    The current source-gold gate is intentionally still failing at 68.67 average
    score with one hard family left: 6 `table_walk` failures owned by `r2sym`.
81. Closed the `table_walk` source-gold family through canonical `r2sym`
    table-walk proof, not a pretty-output special case. Worker evidence now
    certifies the argument-rooted record walk, needle argument, `id`/`len`/
    `name`/`next` field offsets, match return (`field + count`), and exhausted
    negative-count return before `r2dec` may render a linked-list/string-match
    projection. `r2dec` resolves those offsets through the authorized external
    struct layout, so field names come from `r2types` context rather than
    hardcoded fixture names. Focused `r2sym` and `r2dec` tests, formatting,
    release plugin install, live `dbg.table_walk` decompilation, and the
    source-gold closure rerun are green. The current source-gold gate now
    reports average score 98.67, 13/13 source expectations passed, 0 hard
    failures, 0 fake-output counters, and a single remaining owner bucket:
    `sparse_switch` residual proof cleanup in `r2sym`.
82. Closed the `sparse_switch` residual proof cleanup by fixing certified
    return-register rendering at the `r2dec` lowering boundary. The bug was not
    missing source-oracle strings; it was that intermediate return-register
    writes inside native return blocks were still eligible for visible
    assignment rendering/proof comments. Return-context blocks now track those
    writes as ingredients for the final return expression and certify the final
    returned value instead of emitting unowned residual comments. The O2
    `dbg.sparse_switch` output now renders the source return cases with no
    `r2sleigh residual:` comments, while O0 still refuses unproved scalar
    structure rather than inventing fake C. Formatting, a focused `r2dec`
    certified-return test, release plugin install, live O0/O2 radare2 checks,
    and the source-gold closure rerun are green. The current source-gold gate
    reports average score 100.0, 13 source expectations passed, 0 hard
    failures, 0 owner buckets, 0 proof coverage gaps, and 0 fake-output
    counters.
83. Promoted the clean source-gold run into a recurring local acceptance target.
    `tests/r2r/Makefile` now has `make -C tests/r2r source-gold`, which builds
    the fixture links, installs the plugin into an isolated runtime directory,
    and runs `scripts/reversing_benchmark.py --closure-gate` against
    `tests/gold/closure_manifest.json` plus `tests/gold/source_oracle.json`.
    This makes the strict checks executable as one maintained command: complete
    report, score floor, no hard failures, no residual decompiles, no generic
    arg/type debt, no fake semantics, no summary certificate gaps, no proof
    coverage gaps, and exercised source-gold expectations. Validation is green:
    `make -C tests/r2r run` passes 95/95 and
    `make -C tests/r2r source-gold` reports average score 100.0.
84. Promoted the O0 `mem_scan2` native source-loop checkpoint into recurring
    source-gold closure. The fix is proof-owned rather than cosmetic:
    canonical `FunctionTypeFacts::stack_slots` now drives recovered stack-local
    byte signedness; same-address stack read-modify-write proof renders
    `count++` before placeholder repair can invent scalar deltas; materialized
    phi carriers do not become residual comments; and the tail-merge structurer
    rewrites the duplicated branch effect through the boolean identity
    `if (A) { if (B) T } else { T } == if (!A || B) T`. The O0 output now
    renders the native source loop as `for (size_t i = 0; i < n; i++)`,
    `uint8_t c = buf[i];`, `if (c == a || c == b)`, and `count++;` with no
    summary route and no fake loop/control output. Focused `r2dec` tests,
    release plugin install, live radare2 checks under the same local radare2
    library environment used by r2r, and `make -C tests/r2r source-gold` are
    green; the source-gold gate now reports 4 cases, 10 targets, average score
    100.0, and no owner work items.
85. Closed the remaining summary-only executable-C path in `r2dec`: worker and
    region summary evidence no longer emits synthetic `memcpy`, count/parser,
    hash, or table-walk C statements. Summary routes now use an explicit
    "summary facts only" render contract and keep effects visible as comments
    plus unresolved-return residuals until native render proofs own the CFG,
    values, and effects. Focused `r2dec` tests are green after this change.
86. Deleted the disabled summary projection implementation bodies from `r2dec`
    instead of leaving them as dormant code: count/parser/hash/table-walk helper
    loops, summary `memcpy` statement builders, and exact-summary probe paths in
    `consumer_summary` are gone. The remaining summary route implementation is
    comment/residual-only unless native proof-backed CFG rendering handles the
    function through the normal decompiler path. `cargo test -p r2dec --lib` and
    `cargo clippy -p r2dec --all-targets -- -D warnings` are green.
87. Promoted the O0 `fnv_fold` native source-loop checkpoint into recurring
    source-gold closure. The fix consumes canonical upstream evidence instead
    of recognizing the benchmark: the typed `rbp-17` byte stack slot now
    overrides widened SSA carrier integers, lifted `const:*` payloads are parsed
    as canonical hex unless explicitly marked decimal, tail factoring removes
    duplicated guarded loop latch effects, and side-effect-free assignment
    normalization renders `hash ^= c` / `hash *= 0x100000001b3U` without
    reordering calls or other side effects. Live `a:sla.dec` now renders the O0
    native loop as `for (size_t i = 0; i < n; i++)`, `uint8_t c = buf[i];`,
    `c += 32;`, and the FNV fold updates with no summary projection. Focused
    `r2dec` tests, release plugin install, live radare2 checks under the r2r
    runtime library environment, and `make -C tests/r2r source-gold` are green;
    the gate now reports 4 cases, 11 targets, 12 exercised source-gold
    expectations, average score 100.0, and no owner work items.
88. Hardened the next `sparse_switch` checkpoint without promoting bad C.
    Certified return proofs now require the returned value to have a renderable
    `ExpressionCertificate` at the rendered site, matching the existing
    call/assignment proof model. That initially exposed a real upstream r2ssa
    bug: subregister normalization could invent narrowed non-register temps
    such as a 4-byte `tmp:*` root that had no defining SSA instruction. The fix
    keeps width adaptation to real register-family roots and constants; concrete
    subpieces of temporaries must remain backed by actual SSA ops. O2
    `sparse_switch` is source-gold again under the stricter gate, while O0
    `sparse_switch` remains intentionally residualized on its remaining
    9-rendered/8-certified return provenance gap. Focused and full r2ssa/r2dec
    tests, r2ssa/r2dec clippy, release plugin install, live O0/O2 radare2
    checks, and `make -C tests/r2r source-gold` are green; the gate remains at
    4 cases, 11 targets, average score 100.0, and no owner work items.
89. Closed the O0 `sparse_switch` residual without bypassing certified
    rendering. The structurer now follows transparent SSA connector blocks only
    when they contain non-return temp/status-flag forwarding plus a typed branch
    target, avoids appending an unreachable shared merge block after terminating
    if/else arms, and accepts branch-arm returns only when a predecessor
    `ReturnValueCertificate` proves the returned register value. The return
    resolver can also recover edge-specific phi return candidates from the
    predecessor definition instead of accepting a path-insensitive guess. Live
    O0/O2 `dbg.sparse_switch` output now renders with no residuals. Validation
    is green: focused `r2dec` tests, `cargo test -p r2dec --lib`,
    `cargo clippy -p r2dec --all-targets -- -D warnings`, release plugin
    install, `make -C tests/r2r source-gold`, and `make -C tests/r2r run`
    pass. O0 `sparse_switch` remains outside source-gold only because the
    native expression still renders as `b + (a + (a + a))`; the next checkpoint
    is proof-owned arithmetic canonicalization, not a benchmark-specific
    expectation edit.
90. Promoted O0 `sparse_switch` into recurring source-gold through a general
    integer-linear expression canonicalizer. The fix is not target-specific:
    `r2dec` and prepared semantic expression rendering now collect pure integer
    scalar additions into deterministic affine terms, require integer type
    evidence for local decompiler terms, use parameter-backed aliases for
    prepared semantic terms, and refuse pointer, stack/IP, float, untyped, call,
    memory, and other side-effecting terms. Live O0 `dbg.sparse_switch` now
    renders `return a * 3 + b;` with no residuals. The O0 fixture was added to
    `tests/gold/closure_manifest.json`, the normal r2r O0 sparse-switch check
    now requires the source cases instead of accepting residual fallback, and
    validation is green: focused arithmetic tests, `cargo test -p r2dec --lib`,
    `cargo clippy -p r2dec --all-targets -- -D warnings`, release plugin
    install, `make -C tests/r2r source-gold`, and `make -C tests/r2r run`.
    The source-gold gate now reports 4 cases, 12 targets, 13/13 source
    expectations, average score 100.0, and no oracle failures.
91. Removed the remaining fake-summary route for the O2 `fnv_fold` and
    `table_walk` limit cases. `r2engine` now keeps exact summary-only hash-fold
    and complete table-walk workers on the native `Standard` route instead of
    letting dense worker summaries fall back to summary-authored C. `r2dec`
    no longer lets the summary preprobe short-circuit those standard routes, no
    longer overwrites the first proof failure with the later generic loop
    residual, and records do-while loop render proof against the natural loop
    header rather than the latch. The recurring oracle now requires explicit
    residual/refusal for O2 `fnv_fold` and `table_walk`, and forbids the old
    summary-only/table-walk synthetic source text. Current source-gold state:
    13/13 oracle expectations pass, average score is 92.5, and the only closure
    blockers are honest proof gaps: O2 `fnv_fold` needs real loop-carried
    phi/out-of-SSA return-value rendering, and O2 `table_walk` needs renderable
    return-expression certificates for the proven return values. Validation run
    in this checkpoint: focused `r2engine` route/preprobe tests, focused
    `r2dec` latch-loop/proof-anchor tests, release plugin install, live O0/O2
    `fnv_fold`/`table_walk` checks, and `make -C tests/r2r source-gold`
    showing oracle clean but closure still blocked by the two proof gaps.
92. Advanced the O2 `fnv_fold` cleanup by deleting two more fake-proof paths
    instead of restoring pretty output. Return-context ownership is now
    block-vs-edge aware, so a loop latch with both a backedge and an exit edge
    is no longer treated as an unconditional return block. `UseInfo` now counts
    phi operands as edge uses, and `r2dec::normalize` can materialize
    loop-header phi copies on critical backedges only when a dataflow liveness
    check proves the phi destination is dead on every non-target outgoing edge.
    Certified phi expression resolution also refuses divergent phi sources
    instead of choosing the "preferred" source, and certified control-only
    returns no longer fall back to returning the control target (`rip_1`).
    Live O2 `fnv_fold` now remains honestly residualized on the next blocker:
    the loop is recognized, but the rendered body is pruned because the final
    return merge is still not proven as a value expression. `table_walk`
    remains on the same certified return-expression blocker as checkpoint 91.
    Focused `r2dec` tests cover return-edge ownership, phi edge liveness,
    critical-backedge phi materialization/refusal, and certified divergent-phi
    refusal.
93. Advanced the no-hack `table_walk`/`fnv_fold` proof path without restoring
    synthetic summaries. `r2ssa` now allows renderable expression certificates
    to close loop-carried recurrence phis when the backedge expression is pure
    modulo the loop phi and the loop is backed by `StructuredLoopFact`.
    `r2dec` now computes region dominance from the current CFG snapshot instead
    of relying on possibly stale cached dominance, builds natural-loop bodies
    only from nodes dominated by the loop header, and absorbs only single-entry
    terminal return chains into a loop region. That fixes the concrete
    `table_walk` class where return-only exit chains made a reducible loop look
    irreducible, while preserving the guarded shared-exit loop tests. Prepared
    render definitions now refuse memory-shaped `Deref`/`Subscript`/member
    expressions as generic definitions, so memory and array C still require
    canonical memory/layout certificates.

    Live O2 status after reinstall: `fnv_fold` remains honestly residualized
    on missing memory/array certificates; `table_walk` moved forward from
    "loop CFG rendered without loop structure" to a stricter proof mismatch:
    one native loop is rendered, but the proof gate rejects the result because
    the inner string loop is not rendered and the outer rendered loop's
    terminal return-chain region does not yet line up with the canonical
    `LoopCertificate` body/exit/condition identity. Focused validations passed:
    `r2dec` table-walk CFG recovery, guarded shared-exit loop preservation,
    conditional return-context tests, loop-carried phi materialization tests,
    and `r2ssa` loop-carried recurrence certificate tests. `make -C r2plugin
    RUST_FEATURES=all-archs install` passed. Current source-gold is red by
    design rather than cosmetic: average `57.75`, proof gaps in O2 `fnv_fold`
    and O2 `table_walk`, missing nonvoid returns in O0 `fnv_fold` and O0
    `mem_scan2`, no raw temp/stack leaks, no fake loop/switch/stack/signature
    counters.
94. Closed the current `fnv_fold`/shared-return r2r checkpoint without
    reintroducing summary-shaped C. Shared terminal return blocks now recover
    edge-specific return expressions only from predecessor
    `ReturnValueCertificate` proof, fixing the O2 sparse-switch residual class
    without function-name templates. Typed pointer arithmetic now normalizes
    commuted `scalar + pointer` addresses into certified subscript form, so O0
    `fnv_fold` renders `buf[i]` through the normal memory renderer. The
    for-loop cleanup also drops generated, side-effect-free latch artifacts
    only when dead by a reverse liveness pass, which removes the bad
    `i++; value_*; continue` fnv shape instead of hiding it with a benchmark
    expectation. The O0 fnv source oracle now rejects `value_` artifacts and
    requires the folded uppercase guard. Validation completed for the focused
    r2dec/plugin tests, live radare2 O0/O2 fnv and sparse/sum checks, focused
    source-gold `fnv_fold`/`table_walk` closure, release plugin install, and
    `make -C tests/r2r run` green on 95 plugin tests. The full local
    `make -C tests/r2r source-gold` gate is intentionally still red at average
    `74.25`: remaining source-oracle failures are O0 `mem_scan2` loop shape
    (`r2dec`) and O2 `struct_nested_array` field/layout source shape
    (`r2types`).
95. Closed the stale O0 `mem_scan2` and O2 `struct_nested_array` source-gold
    tail while keeping O2 `fnv_fold`/`table_walk` honest residuals. The
    `struct_nested_array` fix is exact layout proof, not string cleanup:
    raw subscript expressions such as `(items + idx * 40)[3]` are promoted to
    `items[idx].len` only when the aggregate layout, element stride, field
    offset, and scalar-vs-pointer use are unambiguous. The O0 `mem_scan2`
    native loop still renders as the source loop with `uint8_t c = buf[i]` and
    `count++`. The standard proof gate now runs on prepared standard routes,
    and raw x86-64 extended-register artifacts such as `r8d_2` are classified
    as uncertified SSA register labels instead of slipping through the raw-name
    check. O2 `fnv_fold` now refuses before partial loop C leaks, with
    `unproven loop effects: empty loop body rendered`; O2 `table_walk` remains
    a structured-control residual. Validation in this checkpoint:
    `cargo fmt --package r2dec --check`, `cargo check -p r2dec`, focused
    raw-register and raw-subscript `r2dec` unit tests, release plugin install,
    live radare2 checks for `authenticate`, O0 `mem_scan2`, O2
    `struct_nested_array`, O2 `fnv_fold`, and O2 `table_walk`,
    `make -C tests/r2r run`, and `make -C tests/r2r source-gold`. The normal
    r2r suite is green on 95/95. The source-gold oracle is clean: 13/13
    expectations pass, no source-oracle failures, no raw temp/stack leaks, and
    no fake loop/switch/stack/signature counters. The gate remains red by
    design: average score `97.0`, residual decompiles `2`, proof gaps `1`, and
    the only hard family is O2 `table_walk` with owner buckets `r2engine` and
    `r2sym`. O2 `fnv_fold` is now an accepted explicit residual/refusal in this
    gate, but still remains future quality work before a gold-standard rating.

Next proof-closure work:

1. Finish O2 `table_walk` native loop/value proof closure. It is now an honest
   whole-function residual, not summary-authored C. The next proof owner is
   `r2sym`/`r2engine`: the canonical artifact must prove the nested string scan,
   linked-list successor, match/negative returns, and the value roots currently
   surfacing as certified residual comments before `r2dec` may render the loop.
2. Upgrade O2 `fnv_fold` from accepted residual/refusal to native proof-backed
   C. The current blocker is canonical value evidence for the loop-carried hash
   byte/multiply recurrence and final return merge, not caching and not a
   summary projection.
3. Fix the unrelated ARM64 stack-merge return regression in `r2dec` before
   using `cargo test -p r2dec --lib` as green evidence again. The failing tests
   are `test_observed_live_arm64_check_secret_full_decompile_returns_zero_and_one`
   and `test_observed_live_arm64_check_secret_with_plugin_context_returns_zero_and_one`.
4. Expand the clean source-gold set beyond the current manual/repo-fixture gate:
   generated kernel-like CFGs, wider switch forms, callsite provenance cases,
   and struct/array/out-param combinations should be added before any broader
   "gold standard" rating increases.
5. Promote the next dormant manual O0 source-loop expectations one family at a
   time. O0 `sparse_switch` is now recurring source-gold; continue with
   `out_param_parse`, `state_machine`, and O0 `struct_nested_array` only when
   their output is backed by canonical field, switch/control, and value proofs
   rather than summary projection.
6. Add each expanded case in a proof-owned group, with every new failing
   expectation routed to the canonical owner instead of weakening the gate.

What Is Done
------------

### 1. Canonical Semantic Ownership

Done:

- `r2sym` owns semantic policy and evidence
- `r2sym::SemanticArtifact` is the canonical semantic artifact
- query routing is planner-gated
- target-local narrowing has explicit ambiguity handling
- native worker summaries are first-class artifacts, not decompiler hacks
- semantic schema/fingerprint versioning is explicit

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
- prepared certificate surfaces now cover loops, switches, if regions,
  expressions, memory accesses, stack slots, callsites, and returns
- return-register writes at return-exit predecessors feed canonical
  `ReturnValueCertificate` evidence

Remaining:

- incremental recomputation hooks
- assumption-aware preparation
- stronger stable indexes for repeated metadata lookup
- broader validation on irreducible CFGs, kernel helpers, and obfuscated flows
- deeper array-index, phi/value, ABI argument, and jump-table proof extraction

### 3. Type System And Function Facts

Done:

- `r2types::FunctionFacts` is the advisory combined type+semantic report
- `r2types::SourceOwnedFunctionFacts` is the canonical runtime owner retaining
  the exact `Arc<r2ssa::SsaArtifact>` used to derive that report
- `r2types::FunctionTypeFacts` is the canonical type/layout/signature payload
- semantic role hints strengthen signatures and aggregate identity
- generated local aggregates no longer override authoritative semantic roles
- archived focused Coreutils type metrics were clean before the detached probe
  was removed; current type regressions require genuine host/compiled coverage
- field/layout certificates are retained through type facts and merged function
  facts
- proof coverage is available to downstream route/render decisions

Remaining:

- semantic type algebra V2
- better out-param, return-shape, and layout confidence inference
- typed assumption model integration
- replacement of large per-function role tables with a canonical role/signature registry
- stronger refusal logic for unsafe local struct candidates
- array-index, out-param, and signature certificates that are source-gold strong

### 4. Decompiler Routing And Rendering

Done:

- `r2dec` routes through canonical plans/facts
- native-linear bounded summary path prevents large worker timeouts
- summary-backed worker rendering exists
- VM path is honest about summary-driven routes
- decompiler/plugin integration is covered by r2r
- certified render gating is active for standard C output
- member rendering requires type/layout proof, while unproven array/subscript
  output becomes an explicit residual
- raw lowercase SSA/register artifacts are rejected before standard C is treated
  as certified

Remaining:

- structured semantic rendering for more loop/control islands
- helper-call simplification from interprocedural summaries
- VM semantic rendering V2
- less local planning where canonical upstream plans can decide
- delete downstream call argument and stack/type repair once upstream
  certificates are complete

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
- broad Coreutils strict gate at `max_binaries=108`, `max_functions=12`
- closure-gate benchmark thresholds for hard failures, residual decompiles,
  average score, setup/command ratio, and optional
  quality-aware PDG wins
- owner-bucket benchmark triage so remaining failures point at `../radare2`,
  `r2ssa`, `r2sym`, `r2types`, `r2engine`, `r2dec`, or plugin glue
- kernel smoke harness
- strict checks for generated output/corpus isolation

Remaining:

- recurring broad Coreutils closure gate in local acceptance
- CGC gate after broad Coreutils quality holds
- Juliet/CWE gate after CGC signal is stable
- recurring real kernel smoke gate, local-only
- trend reports that highlight slowest commands, residual families, host type
  regressions, owner buckets, PDG losses, setup bottlenecks, and candidate
  radare2 issues

What Is Not Done
----------------

The biggest remaining gains are whole-stack intelligence and scale:

- full certifying closure, not just the initial proof spine
- array-index, expression/phi, out-param, signature, and summary-role
  certificates
- loop/switch render closure against certificates
- source-gold closure for generated kernel-like and adversarial cases
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

`P0 certifying spine rewrite -> P1 whole-stack summary reuse -> P2 semantic
type algebra -> P3 replay/trace validation -> P4 VM rendering -> P5 native
radare2 surface -> P6 incremental/perf -> P7 broad corpus gates`

### P0 - Certifying Analysis Spine Rewrite

Goal:

Remove the remaining heuristic glue that makes the system look better than its
canonical facts, while preserving the existing crate ownership model. This is
the proof-first phase: render permissions, certificates, and closure gates
come before more pretty output.

Deliverables:

- proof kernel for checked claims, proof obligations, proof failures, and render
  permissions; initial spine is done, closure checks still need expansion
- control/expression/memory/layout/callsite certificates are surfaced; array,
  out-param, signature, and summary-role proof remain blocking
- single route and request-execution owner in `r2engine`
- evidence-first summary classifier in `r2sym`
- canonical callsite, stack-slot, return, memory-region, and switch facts in
  `r2ssa`
- one signature/type constraint path in `r2types`
- `r2dec` rendering from selected routes and canonical facts only
- `r2plugin` reduced to typed context collection, command dispatch, FFI, and
  applying/rendering engine results

Success criteria:

- no high-level C construct renders without the matching certificate or visible
  summary route
- route policy exists in one crate
- summary names are hints, not authoritative semantic ownership
- no decompiler-side stack/call-arg repairs are needed for benchmark-clean output
- fake switch cases, fake control flow, and placeholder type facts are rejected
  or rendered as explicit residuals
- focused Coreutils remains green while setup/command time improves

### P0a - Proof Kernel And Typed Output Seals

Goal:

Create the minimal internal proof system that lets every consumer distinguish
certified C, summary comments, residuals, and refusals.

Deliverables:

- done: exact source owners and typed certificate carriers
- done: closed-ledger failures with canonical owner buckets
- done: typed route facts and opaque typed-output seals across the runtime seam
- done: first output gates for proof residuals and raw SSA/register artifacts
- remaining: benchmark counters for all proof failures and fake-output classes
- remaining: recurring negative gates for fake loops, fake switches, fake stack
  slots, fake call arguments, fake signatures, and name-only summaries

Success criteria:

- a missing proof cannot silently fall back to plausible C
- proof failures are visible in reports and decompiler residuals
- benchmark closure fails closed when proof/fake-output counters are non-zero

### P0b - Engine Session Boundary

Goal:

Make `r2engine` the only subsystem that decides which artifacts are needed for a
function request.

Deliverables:

- route planning for decompile/type/query requests
- immutable request-local analysis preparation
- engine metrics for planning, SSA, semantic, type, and render costs
- migration of plugin decompile/type/query orchestration into `r2engine`
- removal of duplicated planner logic from plugin glue

Success criteria:

- plugin commands call `r2engine` for orchestration
- `r2dec` renders selected routes instead of owning global scheduling decisions
- repeated requests deterministically rebuild the same canonical artifacts
- small-function fast paths do not pay semantic-worker setup costs unnecessarily

### P0c - Shared Assumptions And Role Registry

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

Why this follows the proof kernel:

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
- summary-cache entries are computed once and consumed many times

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

- stronger typed summary reuse
- deterministic semantic fingerprints
- explicit dependency boundaries
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
- compare reports for every major closure phase

Why:

- focused Coreutils being clean is necessary but not sufficient
- gold standard requires broad and adversarial coverage

Success criteria:

- broad Coreutils stays green without generic/regression drift
- CGC/Julet results classify failures into owner buckets
- kernel smoke remains local-only and reproducible

Gold Closure Checklist
----------------------

This is the closure bar for claiming a closure phase moved the engine toward a real
gold-standard state:

- Coreutils broad closure gate passes with hard failures `0`, residual
  decompiles `0`, average score `>= 99.5`, and setup/command ratio `<= 2.0`.
- Closure gates fail if report status is incomplete, command or executable
  semantic-oracle timeouts are non-zero, or semantic-oracle failures are
  non-zero. Average score is never allowed to override these; source-shape
  advisories are reported independently.
- Fake-semantics counters are `0`: fake loops, fake switches, fake case values,
  fake stack slots, fake call arguments, fake signatures, and name-only semantic
  roles.
- Proof coverage is reported for rendered loops, switches, expressions,
  memory/layout projections, callsites, returns, and summaries.
- PDG comparison is run when r2ghidra is available; `decompile_sla` must have
  no systematic quality or quality-then-performance losses before the result is
  called a win.
- CGC and Juliet are run at least as discovery gates; every failure family is
  bucketed to its canonical owner before implementation work starts.
- Kernel smoke remains local-only and strict when a kernelcache is available.
- Benchmark reports include owner buckets, worst targets, slowest commands,
  residual/artifact counts, setup timing, summary reuse, and PDG deltas.
- Any fix that changes rendered C adds a regression that proves the output is
  backed by canonical facts or is visibly marked summary/residual.

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
- prepared certificate vectors now carry control, expression, memory,
  stack-slot, callsite, and return-value evidence
- return-value certificates cover return-exit predecessor register writes

Next:

- array-index, phi/value, ABI argument, and jump-table proof extraction
- certificate validation on irreducible CFGs and kernel-style control flow
- assumption-aware dataflow
- incremental recomputation hooks
- stronger indexed metadata for repeated lookups

### `r2sym`

State:

- semantic artifact authority is established
- native worker summaries and evidence algebra are much stronger
- broad Coreutils hot-worker timeout families now route through bounded
  summaries

Next:

- checked semantic evidence and summary-role certificates
- summary registry
- replay/witness validation
- more canonical summaries for broad corpus families
- summary composition across consumers

### `r2types`

State:

- canonical `FunctionFacts` path is established
- focused and broad Coreutils decompile closure is clean for hard failures and
  residuals; current type accuracy is checked through genuine host facts and
  compiled/differential fixtures rather than a detached type-report command
- generated aggregate leakage is fixed for current hot targets
- field/layout certificates are retained and exposed through merged function
  facts

Next:

- array-index, out-param, and signature certificates
- stronger propagation of return and layout proof into type decisions
- semantic type algebra V2
- assumption-aware type recovery
- role/signature registry extraction
- stronger layout confidence and refusal logic

### `r2engine`

State:

- initial crate exists for request orchestration, route planning, and shared
  engine helpers
- plugin decompile paths already use parts of the engine boundary
- proof coverage and render permissions are now part of the decompile route
- type proof coverage is merged into route/render decisions

Next:

- route all decompile/type/query decisions by proof coverage, render
  permission, budget, and refusal policy
- own all decompile/type/query route decisions
- absorb duplicated route policy from `r2dec` and plugin glue
- own request-local phase metrics and any future reuse only after realistic
  traces prove it lowers latency or RSS
- expose typed request/response APIs for plugin commands

### `r2dec`

State:

- planner/facts route is in place, but route policy still needs to move upward
- large-worker native-linear summary path prevents major timeouts
- summary-backed rendering exists
- certified render gating is active for standard C output
- member rendering can use certified type/layout proof
- array/subscript rendering residualizes when array-index proof is missing
- raw lowercase SSA/register artifact detection blocks false certified output

Next:

- close structured control and expression rendering against existing
  certificates
- consume array-index, out-param, signature, and summary-role certificates as
  they land upstream
- summary-backed helper-call simplification
- structured loop/control-island rendering only after proof gates exist
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
5. State the proof obligation or refusal reason for any rendered C change.
6. Push facts upstream instead of reconstructing downstream.
7. Add deterministic tests at the exercised layer.
8. Run benchmark comparison when behavior affects quality or performance.
9. Validate both repos if the seam crosses into `../radare2`.

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

Benchmark gate for Coreutils-focused closure phases:

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
- using summary-cache hits, caps, or average scores as substitutes for semantic
  proof
- rendering high-level C when the matching proof obligation failed
- adding per-function patches when a registry, summary, or typed seam is the
  correct owner

If a change improves the subsystem by deleting a command, moving an owner, or
rewriting a seam, that is progress.

Acceptance Standard
-------------------

The target plugin system should eventually have these properties:

- a user can rely on normal radare2 workflows and quietly get better analysis
- symex, types, decompiler, and replay agree on the same facts
- high-level C is proof-gated by checked canonical facts
- assumptions update the whole subsystem coherently
- summaries are reused across crates instead of rediscovered
- evidence and fallback reasons are visible and honest
- benchmark gates cover focused, broad, source-gold, and adversarial corpora
- incomplete status, timeouts, oracle failures, and fake-output counters block
  closure
- large functions stay bounded without losing useful semantic summaries
- the public command surface is smaller and smarter, not larger

That is the gold standard we should optimize toward.

Two Open Defects and the Seam They Share
----------------------------------------

Both remaining known-wrong renderings trace to the same seam, and neither is
fixable where it shows. Recording the evidence so the next attempt starts from
it rather than repeating the search.

**A dereference is dropped.** `int test_struct_field(DemoStruct *obj, int v)`
returns `obj->thirteenth + obj->first` and renders as `obj + obj[12]`: an
address added to an integer. The load itself is rendered correctly --
`render_canonical_load_expr` returns `Deref(Var("obj"))`, and the fold's
`get_expr` returns it unchanged. The wrong value enters through
`analysis/lower.rs::get_expr`, which is a second, independent answer to "what
does this name denote". It consults `forwarded_values` provenance before the
definition, and for a value loaded through a pointer that provenance names the
slot the *pointer* came from. Guarding the provenance is not enough: with the
guard in place the next branch, `render_semantic_value_for_var`, returns the
pointer too, because the semantic value recorded for the load result is the
address rather than what was read. The conflation is in the semantic-value
model, not at any one call site.

**Parameter names are withheld.** `process_string(char *s)` renders as
`process_string(int32_t arg0)` while `authenticate(char *password)` -- an
identical prototype in the same binary -- recovers its name. radare2 withholds
the whole function interface, and with it the presentation names, when
`stack_resources_complete` is false, which happens when two *local* frame slots
overlap. Removing that conjunct does deliver the names, and it also reveals why
it is there: radare2 then emits parameter-home slots that are zero-sized or
unbacked, which `SourceFunctionInterface::new` rejects. Relaxing the Rust
contract to match trades a missing name for a corrupted interface. The fix
belongs in radare2's stack-slot collection, which should either describe a
parameter home or omit the inventory, not emit a malformed one.

The common seam is the second lowering implementation. `analysis/lower.rs` and
`fold/op_lower` both derive what a name denotes, and they disagree; the frame
inventory and the prototype are likewise entangled across the snapshot
boundary. Collapsing each to one owner is the prerequisite, not a follow-up.

What a Certification Layer Would Have to Do
-------------------------------------------

The plugin carried a certification kernel: nine hand-written recognizers for
function shapes -- terminal return, and terminal return decorated with a guard,
a conditional, a switch, one loop, one direct call, one memory access, an
aggregate member, or a private-frame join -- each building a typed C AST whose
meaning could be evaluated against canonical SSA. It has been removed. The idea
is worth keeping and the implementation was not, so the reasoning is recorded
here rather than in the history.

Three things were wrong with it, and any replacement has to answer all three.

**It recognized shapes, so its reach was whatever had been written down.**
Roughly one function in ten matched. Coverage grew linearly in hand-written
modules while the space of function shapes did not, so the gap against the
ordinary renderer could not close by adding more of them.

**It was not a proof.** The differential evaluated the typed AST against SSA
over sampled state within bounds, which is a good falsification technique and a
weaker claim than the word certified suggests. Nothing was sealed; a run that
found no mismatch had found no mismatch.

**It checked an artifact nobody read.** Its C was written to be checkable --
explicit widths, every intermediate bound, arithmetic through helper functions
-- and once that stopped being what the reader saw, the check no longer said
anything about the output. Whatever it established, it established about a
rendering that was discarded.

A replacement worth having would check the rendering that is actually printed,
and would do so without a catalogue of shapes. Both are hard for the same
reason: the readable AST deliberately omits what a checker needs, so either it
grows those facts back -- becoming the thing that was deleted -- or the
SSA-to-AST lowering is validated once, generically, which is translation
validation and a research project rather than a refactor.

Until one of those is real, the honest statement is the one the renderer now
makes: this is a rendering, and here is what could not be shown about it.

The Value-Rendering Seam
------------------------

One question -- what expression does this SSA name denote -- is answered
independently in at least six places, and they do not agree. Fixing them one at
a time does not converge: each correction moves the defect to whichever path
runs next.

The paths found so far, in the order a returned struct-field read reaches them:

1. `fold::op_lower::get_expr`, the value renderer, which consulted forwarding
   provenance before the value's own definition.
2. `fold::op_lower::semanticize_visible_expr`, whose dereference arm accepted a
   candidate equal to its own operand.
3. `analysis::lower::LowerCtx::get_expr`, which builds the definitions the fold
   later consults, and which follows provenance first for the same reason.
4. `fold::op_lower::return_resolver::expand_return_expr_in_context`, a name
   ladder of its own.
5. The return-register site in `fold_block`, which expands and re-semanticizes
   `op_to_expr` output.
6. `structure.rs`, which synthesizes a trailing return from an expression it
   derived separately.

The first three now share one rule for the case where a read of memory defines
the name, which is why `obj->thirteenth + obj->first` lowers correctly; the
returned expression is still built by the last three and still prints the
pointer.

The fix is not another rule. It is one entry point for value rendering that
every path calls, with the context-specific adjustments -- return position,
call-argument position, condition position -- applied on top of a single
answer rather than replacing it. Until that exists, a correction anywhere in
this list is a correction to one caller, and the defect survives in the others.

Where the Leaked Names Come From
--------------------------------

The undeclared-name detector marks 55 constructs across three fixture
binaries. Two thirds of them are one symptom, and it was traced as far as
this before the trail ran into the value-rendering seam recorded above.

The symptom is a parameter assigned the address of its own frame slot:

    int bitwise_check(unsigned int x) { if ((x & 0xF0) == 0x50) ...

    int32_t dbg.bitwise_check(int32_t x) {
        x = local_10 + 8;          // <- not a statement the program makes
        if ((x & 240) != 80) {

What the machine does there is `str w0, [var_8h]` followed by two
`ldr w8, [var_8h]`: the prologue puts the argument in its home slot and reads
it back twice. Each read is rendered as an assignment whose left side is the
slot's name and whose right side is the slot's *address*.

Established by tracing:

- The load renderer is not at fault. `render_canonical_load_expr` returns
  `Var("x")` for both reads, which is right: the slot is named after the
  parameter, so reading it yields `x`.
- The name on the left is also right. The load's destination is aliased to `x`
  because it holds `x`.
- The statement nonetheless leaves the fold as `x = local_10 + 8`, so the
  right-hand side is replaced somewhere between the load renderer returning
  and the statement being assembled.
- `is_entry_arg_alias_store` exists to drop the prologue store for exactly
  this shape. Its third recovery path -- follow the stored value back through
  transparent copies to an entry register -- is unreachable behind an
  unconditional `return None;`. Enabling it changes nothing measurable, so
  something earlier already declines; the dead line is noted here rather than
  removed on speculation.

The remaining step is the same one the seam needs: a single value-rendering
entry point, so that what the load renderer answers is what the statement
carries. Until then the marker at least says the line is not program text.
