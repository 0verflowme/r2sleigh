r2sleigh Plugin RFE 2026
========================

Purpose
-------

This document proposes the next feature and integration wave for the `r2sleigh`
plugin and the surrounding analysis pipeline.

The goal is not "more commands." The goal is to make radare2 feel like it has a
first-class typed analysis cockpit built on:

- `r2il` as the canonical machine-semantics layer
- `r2ssa` as the canonical data/control-flow layer
- `r2sym` as the canonical semantic reasoning and witness layer
- `r2types` as the canonical type/signature/layout layer
- `r2dec` as the canonical rendering layer

The plugin should expose that stack cleanly to users without becoming a second
analysis engine.

Design Principles
-----------------

1. Facts have one owner.
   - `r2il` owns lifted instruction semantics.
   - `r2ssa` owns SSA, def-use, CFG risk, and interproc summaries.
   - `r2sym` owns symbolic state, semantic artifacts, evidence, and query plans.
   - `r2types` owns canonical type/layout/signature facts.
   - `r2dec` owns lowering, structuring, and rendering.
   - `r2plugin` owns orchestration, FFI, JSON shaping, and command routing.

2. Plugin improvements should prefer typed seams over plugin-side reconstruction.
   - If a feature needs missing core facts, extend `../radare2` or the owning
     Rust crate instead of parsing command output or duplicating policy in
     `r2plugin`.

3. The best plugin is workflow-oriented, not command-oriented.
   - Users should be able to ask "what does this function do?", "why is this
     branch taken?", "what type is this pointer?", and "find me an input that
     reaches this sink" with one coherent interface.

4. Evidence must be user-visible.
   - Decompiler, symbolic, and type results should expose why something was
     accepted, downgraded, or refused.

5. Determinism beats cleverness.
   - Output, naming, ordering, and plan selection must stay stable.

External Research Signals
-------------------------

These systems are useful reference points:

- Ghidra's p-code emulator uses the same p-code substrate as the decompiler and
  debugger, which reinforces the value of one canonical semantics layer.
- Ghidra also exposes structure-fill helpers directly from decompiler evidence,
  which is the right direction for `r2types`-driven struct recovery.
- Binary Ninja's workflow system shows the value of explicit analysis DAGs and
  plugin-extensible execution order.
- Binary Ninja's User-Informed Data Flow (UIDF) shows the value of letting the
  user seed assumptions and re-run analysis incrementally.
- Binary Ninja's WARP shows that fact exchange across binaries and teams can be
  a first-class workflow, not a loose export format.
- angr's exploration techniques and state plugins show the value of explicit
  exploration policy and typed state-owned merge semantics.
- angr's SimProcedures reinforce that library modeling is a first-class analysis
  concern, but must remain clearly distinguished from exact semantics.
- Triton shows the value of callback-rich dynamic symbolic execution, snapshot
  workflows, and hybrid trace-assisted reasoning.

Current Strengths
-----------------

The current stack is already unusually strong for an r2 plugin:

- Sleigh-backed typed lifting
- SSA and def-use pipelines
- canonical symbolic artifacts with evidence and planners
- canonical `FunctionFacts`
- typed type/signature/layout writeback
- decompiler planner/consumer split
- good radare2 command coverage
- end-to-end validation through `tests/r2r`

The next step is not "invent more infrastructure." It is to expose more of the
existing infrastructure as coherent workflows.

Problem Statement
-----------------

Today the plugin still feels stronger as an internal analysis stack than as a
user-facing reversing cockpit.

Main gaps:

- analysis results are powerful but scattered across many commands
- there is no single "combined facts" view per function
- user-driven assumptions are weak compared to the solver and SSA power already
  present
- debugger / trace / replay integration is underused
- type recovery is strong but not yet an interactive workbench
- symbolic execution is useful but not yet a first-class guided workflow
- fact exchange, collaboration, and report export are thin
- plugin extensibility is command-centric rather than workflow-centric

RFE Themes
----------

### RFE-1: Unified Function Analysis Cockpit

Add a canonical per-function combined report based on `FunctionFacts`,
`SsaArtifact`, decompiler plan, and semantic artifact.

Proposed commands:

- `a:sla.facts`
- `a:sla.facts.json`
- `a:sla.plan`

Payload should include:

- function identity and CFG risk
- decompile/query/type plans
- canonical diagnostics and residual reasons
- inferred signature, calling convention, locals, and struct candidates
- semantic regions, decisive targets, ambiguity markers
- decompiler route selection and fallback reason

Why:

- users need one place to understand "what the system knows"
- this is the foundation for IDE/panel integrations and reports

Owner:

- core data in `r2ssa`, `r2sym`, `r2types`, `r2dec`
- assembly and JSON shaping in `r2plugin`

### RFE-2: User-Informed Analysis

Add a typed assumption system inspired by Binary Ninja's UIDF, but grounded in
SSA vars, semantic targets, and type facts.

Proposed commands:

- `a:sla.assume <var|expr> <value-set>`
- `a:sla.assume.list`
- `a:sla.assume.clear`
- `a:sla.assume.apply`

Supported assumptions:

- constant values
- range constraints
- finite sets
- pointer target hints
- "this branch is taken" / "this branch is not taken"
- "this parameter is of type T"

Behavior:

- assumptions trigger incremental recomputation of affected analyses
- decompiler, type recovery, and symbolic plans consume the assumption set
- assumptions are explicit and serializable, not hidden comments

Why:

- this turns the stack into an interactive reverse engineering environment,
  rather than a batch analyzer

Owner:

- canonical model in `r2ssa` + `r2sym` + `r2types`
- persistence and command routing in `r2plugin`
- if persistence belongs in radare2 analysis metadata, add a typed seam in
  `../radare2`

### RFE-3: Guided Symbolic Query Workbench

Make symbolic execution a primary user workflow instead of a mostly expert-only
path query.

Proposed commands:

- `a:sym.reach <target>`
- `a:sym.solve <target>`
- `a:sym.why <target>`
- `a:sym.until <addr>`
- `a:sym.witness <target>`
- `a:sym.export.smt2 <target>`

Required behavior:

- show the selected `QueryPlan` / route plan
- show whether narrowing was exact, over-approximate, residual, or refused
- return witness inputs, register state, and memory layout when available
- emit canonical evidence and ambiguity reasons
- support multi-target batch ranking for "which sink is easiest to reach?"

Why:

- `r2sym` is now strong enough to support a real guided workflow
- this is the highest-leverage way to expose the semantic engine to users

Owner:

- `r2sym` for plans, evidence, witness generation
- `r2plugin` for command UX and JSON export

### RFE-4: Trace-Assisted Analysis And Replay

Integrate the plugin with radare2 debugging and replay to validate or seed
analysis.

Sub-features:

- import register/memory snapshots from debugger state into `ReplaySeed`
- record concrete traces and attach them to symbolic or decompiler sessions
- compare static semantic expectations against observed branch outcomes
- enable time-travel-style workflow when external trace engines are available

Proposed commands:

- `a:sla.trace.seed`
- `a:sla.trace.import <file>`
- `a:sla.trace.diff`
- `a:sym.replay <target>`

Why:

- trace-assisted reasoning is the cleanest bridge between static and dynamic
  analysis
- it gives users a way to validate symbolic witnesses and decompiler claims

Notes:

- this is the correct place for optional concrete oracles such as Unicorn or rr
  traces: as under-approximate witness engines, not semantic owners

Owner:

- typed debugger/trace seam may need `../radare2`
- replay/state logic in `r2sym`
- UX in `r2plugin`

### RFE-5: Type Workbench And Structure Fill-Out

Turn type recovery from passive inference into an interactive workbench.

Proposed commands:

- `a:sla.types.candidates`
- `a:sla.types.apply`
- `a:sla.types.struct.fill`
- `a:sla.types.diff`

Core features:

- show candidate signatures with confidence/evidence
- show field-offset evidence for struct growth
- allow applying one candidate or one field set selectively
- diff current applied types against inferred types
- surface why a field name was chosen or refused

Why:

- Ghidra's structure-fill workflow is popular because it turns decompiler
  evidence into a real analyst loop
- `r2types` already has the raw ingredients; the plugin needs to expose them

Owner:

- `r2types` owns candidates, evidence, and application rules
- writeback path may require typed `../radare2` extensions where current API is
  too weak

### RFE-6: Workflow Profiles And Incremental Scheduling

Move from loose mode flags to explicit workflow profiles.

Profiles:

- `triage`
- `reverse`
- `audit`
- `solve`
- `firmware`

Each profile selects:

- analysis depth
- decompiler aggressiveness
- symbolic budgets
- automatic writeback policy
- whether vulnerability or trace passes run

Why:

- Binary Ninja's workflow model is a good lesson: explicit pipelines are easier
  to reason about than scattered booleans

Owner:

- profile definition in `r2plugin`
- typed plan/profile propagation into `r2ssa`, `r2sym`, `r2types`, `r2dec`
- if radare2 should persist profiles, add a typed config seam upstream

### RFE-7: Vulnerability Intelligence Layer

Build a first-class vulnerability workflow on top of existing SSA, taint,
semantic plans, and witness generation.

Proposed commands:

- `a:sla.vuln`
- `a:sla.vuln.json`
- `a:sla.vuln.rank`
- `a:sla.vuln.solve <finding>`

Core capabilities:

- source/sink/sanitizer rule packs
- interprocedural taint-backed risk ranking
- solver-backed witness generation for selected findings
- SARIF / JSONL export
- comments / flags / bookmarks for findings

Why:

- this is the clearest differentiator versus "just another decompiler"

Owner:

- taint and symex logic in `r2ssa` / `r2sym`
- risk aggregation in a dedicated crate or `r2plugin` orchestration layer

### RFE-8: Fact Exchange And Collaboration

Add a canonical fact archive format for sharing analysis between binaries,
sessions, and teams.

Possible exports:

- names
- signatures
- calling conventions
- recovered structures
- comments
- symbolic witnesses
- proven predicates for specific functions

Proposed commands:

- `a:sla.export.facts`
- `a:sla.import.facts`
- `a:sla.export.report`

Why:

- Binary Ninja's WARP is a useful precedent: reusable analysis transfer is a
  major force multiplier

Design constraint:

- exchange the canonical typed artifacts, not ad hoc plugin JSON

### RFE-9: Rich Graph And Panel Surfaces

Surface more analysis directly into the r2 experience.

Candidate surfaces:

- SSA use-def overlays
- semantic-region overlays
- branch evidence coloring
- type-evidence view
- risk/finding list
- witness/memory snapshot viewer

Even if the terminal command surface remains primary, the data model should be
designed so UI layers can be added later without reworking ownership.

### RFE-10: Plugin Extension SDK

Expose a typed extension surface for third-party rule packs and analysis
augmenters.

Possible extension points:

- vulnerability rules
- library summary packs
- architecture-specific analysis helpers
- type archive sources
- report exporters

This should be workflow-oriented and typed. It should not be a stringly plugin
API living only in `r2plugin`.

Integrations Worth Pursuing
---------------------------

### High-value integrations

- `../radare2` typed collectors for richer function/type/debugger context
- rr / debugger trace import
- Frida or debugger-assisted replay for concrete witness validation
- SARIF export for audit workflows
- fuzzing harness or corpus export for AFL++ / LibAFL / libFuzzer
- fact archives for collaboration

### Optional integrations

- Unicorn as an under-approximate concrete witness engine
- Triton-style callback packs only if they map cleanly to `r2sym` ownership
- remote trace sources for firmware or mobile targets

### Integrations to avoid

- parsing plugin-visible JSON back into internal facts
- letting external emulators become semantic owners
- plugin-side type or decompiler policy duplication

Proposed Command Additions
--------------------------

| Command | Purpose | Canonical owner |
|--------|---------|-----------------|
| `a:sla.facts` | combined per-function fact view | `r2ssa` + `r2sym` + `r2types` + `r2dec` |
| `a:sla.plan` | explain route/analysis decisions | `r2sym` + `r2dec` |
| `a:sla.assume` | user-informed analysis seeds | `r2ssa` / `r2sym` / `r2types` |
| `a:sym.why` | explain why a target is or is not reachable | `r2sym` |
| `a:sym.witness` | concrete witness + memory/register state | `r2sym` |
| `a:sla.trace.*` | import/compare replay traces | `r2sym` + `../radare2` |
| `a:sla.types.candidates` | show type candidates and evidence | `r2types` |
| `a:sla.types.struct.fill` | interactive struct growth/apply | `r2types` |
| `a:sla.vuln*` | risk ranking and witnessable findings | `r2ssa` / `r2sym` |
| `a:sla.export.*` | fact/report exchange | typed artifact owners |

Priority Proposal
-----------------

### P0: make the plugin feel like one coherent system

1. Unified function facts + plan view
2. User-informed analysis
3. Guided symbolic query UX
4. Type workbench and struct fill-out

### P1: connect static and dynamic reasoning

1. Trace-assisted replay
2. Workflow profiles and incremental scheduling
3. Vulnerability intelligence

### P2: ecosystem and collaboration

1. Fact archive exchange
2. Panel/graph surfaces
3. Extension SDK

Required Upstream Seams
-----------------------

Some of the best improvements belong in `../radare2`, not in this repo alone.

Likely seam work:

- typed collector for debugger snapshot / trace state
- typed persistence for analysis assumptions
- stronger writeback for user-defined variables and types
- richer function metadata transport for reports and batch workflows

Success Criteria
----------------

The plugin becomes "best in class" when:

- a user can understand one function from one combined facts view
- a user can seed assumptions and re-run analysis without losing determinism
- a user can ask for a target witness and get evidence, not just a yes/no
- types can be reviewed and applied interactively
- dynamic traces can validate or seed symbolic results
- vulnerability findings are ranked, explainable, and reproducible
- all of this runs through typed seams with stable `r2r` coverage

Validation Strategy
-------------------

- add `r2r` cases for every new command surface
- add crate-local tests for planners, assumptions, and evidence transitions
- add replay/trace fixture coverage in `tests/e2e` only when `r2r` cannot
  express the workflow
- validate any `../radare2` seam change in both repos

References
----------

Primary references used for this RFE:

- Ghidra p-code emulator: <https://ghidra.re/ghidra_docs/api/ghidra/pcode/emu/PcodeEmulator.html>
- Ghidra JIT p-code emulator: <https://ghidra.re/ghidra_docs/api/ghidra/pcode/emu/jit/JitPcodeEmulator.html>
- Ghidra structure fill helper: <https://ghidra.re/ghidra_docs/api/ghidra/app/decompiler/util/FillOutStructureHelper.html>
- Ghidra debugger emulation notes: <https://ghidra.re/ghidra_docs/GhidraClass/Debugger/B2-Emulation.html>
- Binary Ninja workflows: <https://docs.binary.ninja/dev/workflows.html>
- Binary Ninja User-Informed Data Flow: <https://docs.binary.ninja/dev/uidf.html>
- Binary Ninja WARP fact exchange: <https://docs.binary.ninja/guide/warp.html>
- Binary Ninja time-travel debugging: <https://docs.binary.ninja/guide/debugger/gdbrsp-ttd.html>
- angr overview: <https://docs.angr.io/>
- angr exploration techniques: <https://docs.angr.io/en/v9.2.79/core-concepts/pathgroups.html>
- angr state plugins: <https://docs.angr.io/en/v9.2.148/extending-angr/state_plugins.html>
- angr SimProcedures: <https://docs.angr.io/en/v9.2.119/extending-angr/simprocedures.html>
- Triton overview: <https://triton-library.github.io/>
- Triton hooks: <https://quarkslab.github.io/tritondse/tutos/hooks.html>
