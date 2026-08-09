# ADR: Semantic Preservation Kernel Ownership

- Status: Accepted target architecture; implementation incomplete
- Date: 2026-08-06
- Baseline: r2sleigh `0cbe057efb8427b021e1c8cde4d721573fdb9fdd` with radare2 `62791dc54f6af6e95d9a61c997e5c1eda098775d`
- Rewrite branch: `codex/semantic-preservation-kernel`

## Context

The current certification path can check that rendered statements have attached
proofs. It cannot establish the stronger property that every live effect in the
canonical source representation survived structuring exactly once. A rendered
statement may therefore be individually justified while a call, memory effect,
return, control predicate, or loop-carried update has been silently lost before
rendering. The current `CertifiedC` label is stronger than that guarantee.

Output-by-output fixes cannot close this gap. Certification must start from a
complete source-driven inventory, and every later transformation must account
for that inventory without using text, names, or output shape as evidence.

## Decision

The semantic-kernel rewrite uses this ownership spine:

```text
immutable radare2 function snapshot
        |
        v
thin, versioned FFI
        |
        v
r2il / Sleigh lift
        |
        v
r2ssa canonical semantic graph + obligation inventory
        |
        v
r2sym evidence + r2types annotations
        |
        v
r2cert certified function + closed obligation ledger
        |
        v
r2dec proof-preserving structuring
        |
        v
typed semantic C AST
        |
        v
cosmetic normalization and rendering
```

### Authority and ownership

| Owner | Authority | Must not own or infer |
| --- | --- | --- |
| radare2 | One immutable, coherent function snapshot: signature, calling convention, register arguments, stack slots, callees, types/layouts, assumptions, and revision identity | r2sleigh-specific policy, lazy mutation during analysis, or a cache identity computed before the snapshot is complete |
| Versioned FFI | Boundary validation, explicit ownership, capability negotiation, request/response lifetime, and panic containment | Semantic recovery or duplicated hand-written data-model authority |
| `r2il` / Sleigh lift | Machine instruction effects expressed for canonicalization | C structuring or render permission |
| `r2ssa` | The canonical semantic graph, deterministic semantic IDs, liveness, complete initial `SemanticObligation` inventory, and the closed machine-expression vocabulary projected from that graph | Rendered-statement counts, source-like names, cosmetic AST facts, or arbitrary public construction of proof-bearing machine nodes |
| `r2sym` | Symbolic evidence keyed by semantic ID | Independent authority to grant rendering permission |
| `r2types` | Width, signedness, layout, provenance, and other type evidence keyed by semantic ID | Certification, string-based semantic recovery, or independent render permission |
| `r2cert` | `CertifiedFunction`, `CertifiedExpr`, `CertifiedEntity`, `CertifiedEffect`, `EffectDisposition`, `RewriteCertificate`, proof schema versions, refusal diagnostics, and obligation-ledger closure | Reconstructing semantics from rendered text or names |
| `r2dec` | Certified-region transformations, proof-preserving structuring, source-to-output obligation maps, residual obligations, and semantic-C rendering from validated machine entities | Silently dropping, duplicating, guessing an effect, or attaching optional metadata to an unrestricted syntax tree after lowering |
| Normalizer/renderer | Source-like names, formatting, literal spelling, and other cosmetic projection after semantic certification | Changing types, machine semantics, source IDs, dispositions, or certification |
| `r2engine` | Orchestration, cancellation/complexity budgets, and session reuse whose benefit is measured | A competing semantic graph or certification authority |

The machine-expression arena is an immutable, name-independent semantic layer
owned by `r2ssa`. Its checked builders project prepared SSA operations into
explicit bitvector operations and bind expression entities to canonical
producers and source obligations. `r2cert` validates and closes those entities;
`r2dec` structures and renders only validated roots. This avoids retrofitting
optional proof metadata onto the freely rewritable legacy `CExpr` tree.
Cosmetic normalization is a later projection and cannot retroactively change
types, operation policies, provenance, or certification.

### Source obligation contract

Every canonical instruction or effect receives exactly one initial state in
`r2ssa`:

- live obligation;
- proven dead;
- structural/control-only; or
- unsupported/unknown.

The live inventory covers observable memory reads and writes, calls and their
arguments/results, returns, control predicates and transfers, traps and
exceptional effects, volatile or unknown effects, loop-carried state, and all
live state transitions/value producers required by those root effects.

Semantic IDs are deterministic and independent of variable names, traversal
order, rendered text, and AST positions. Evidence and rewrite mappings refer to
these IDs.

Certification closes the source inventory. Every obligation has exactly one
final disposition:

- `Rendered`;
- `AbsorbedIntoExpression`;
- `AbsorbedIntoStatement`;
- `AbsorbedIntoCall`;
- `AbsorbedIntoControl`;
- `AbsorbedIntoReturn`;
- `AbsorbedIntoLoopState`;
- `AbsorbedIntoConditionalReturnState`;
- `Rewritten`;
- `Superseded`;
- `ProvenDead`;
- `Residualized`; or
- `Refused`.

Zero dispositions are lost effects. Multiple dispositions are duplicated
effects. Both are certification failures before rendering.
`AbsorbedIntoControl` closes ledger multiplicity only through sealed control
evidence; it remains pending semantic-AST/typed-region validation and is not
final output authorization.

### Rewrite contract

Each structuring pass consumes certified input obligations and returns:

- a structured region;
- a source-to-output obligation mapping;
- a new control-domain proof;
- any residual obligations; and
- a refusal reason when preservation cannot be shown.

The port order is straight-line blocks, if/else, simple while loops, for-loop
recognition, break/continue, multi-exit loops, switches, then irreducible CFGs.
The while-to-for rewrite must explicitly map a loop latch state transition to
the for-loop increment. Name suffixes and output shape are never evidence.

Unsupported semantics residualize or refuse. Irreducible control becomes a
controlled state-machine representation or a residual. It never becomes
invented executable C.

The first positive terminal-control subsets are:

- one explicit, final, direct, non-self branch to one existing canonical
  successor, owning `ControlTransfer/Whole`; and
- one explicit final `CBranch` with distinct existing non-self true and false
  successors, an exact two-successor topology, a false successor equal to the
  block-end fallthrough address, eight-bit `NonZeroIsTrue` truthiness, and exact
  ownership of both `ControlPredicate/Whole` and `ControlTransfer/Whole`.

The final raw operation, SSA operation, typed target/condition uses, topology,
successors, and source obligations must all agree. `r2dec` may form local direct
and conditional transfer regions exposing one or two arm-labelled open
successor ports. These regions account for the selected source-ordered body and
prove only their terminal transfer on normal body completion. They do not own
successor execution, prove a join or `if` structure, establish return behavior
or whole-function closure, or grant render permission.

The conditional false arm's address is certified as part of the explicit
`CBranch`; this does not turn obligation-free implicit fallthrough into an
instruction-owned effect. A separate topology-only fallthrough fragment may
expose one existing non-self structural successor while preserving mappings
unchanged. It fabricates no producer or obligation and leaves the successor as
an open composition port. A last block with no resolved successor is rejected.

The first structured composition is a strict three-block diamond: one certified
conditional header, two single-entry certified-transfer arms, and one shared
existing open join. Each arm may use an explicit certified branch or exact
topology-only fallthrough. True/false polarity is retained from the header, not
successor order. Divergent joins, side entries into either arm, return arms, and
overlapping source obligations reject. All three child proofs must retain the
same exact prepared-artifact origin, including its ordered semantic graph
payload, typed preparation mode, decompiler-preparation fact snapshot, and
ordered assumption replay context; coincident topology and stable IDs alone are insufficient. The
fragment does not own or execute the join and is not yet executable `if`/`else`
C.

The first loop composition is a carrier-free two-block header-tested natural
loop routing fragment. `r2cert` seals one exact structured-loop witness: a
conditional header, one direct-transfer body/latch back to that header, one
external predecessor port, one existing open exit port, exact continuation
polarity, and the shared prepared-artifact origin. `r2dec` composes only those
sealed witnesses and requires exact header/body mappings with no
`LoopCarriedState` or `LiveStateTransition` obligation. That open fragment alone
still owns neither entry nor exit and grants no executable `while` authority.

The sixth closed function subset closes the narrow invariant form of that
routing. Its exact four-block topology owns an entry preheader and sealed direct
transfer to the header, the carrier-free header/body backedge, and the sole
terminal-return exit. The eight-bit header condition must be the sole
producerless ABI parameter and match its revision-bound storage and semantic-C
type exactly. The loop body contains only the sealed backedge. The opaque
r2cert permit rechecks the preheader branch, header predicate/transfer,
backedge, and return evidence; requires complete disjoint mappings; and rejects
every residual/refused obligation, phi, carrier/state transition, memory, call,
stack input, unknown effect, side entry, extra exit/block, or open port. Strict
semantic C emits `while (condition != 0)` or `while (condition == 0)` followed
by the constant/void terminal return. This makes no termination claim: the
independent bounded differential explicitly distinguishes immediate exit from
an invariant loop still traversing its backedge when the bound is exhausted.
General stateful loops remain refused. The exact counted-loop subset below is
the only admitted carrier-bearing exception.

The seventh closed function subset is one canonical unsigned counted loop. Its
exact four-block topology contains a preheader that initializes one register
counter to zero and branches to the header, a header that compares the counter
with the sole full-width revision-bound ABI parameter using unsigned `<`, one
latch that performs the wrapping machine-width `counter + 1` update and branches
back to the header, and one terminal exit that returns the final counter through
the exact ABI return storage. `r2ssa` binds the initializer, header phi, bound,
condition, latch update, backedge, and return to stable producer/value/storage
identities. `r2cert::CertifiedCountedLoopState` exclusively owns the phi's
`LiveValueProducer`, `LoopCarriedState`, and exact latch
`LiveStateTransition`, and the closed control witness plus opaque permit require
complete one-to-one ledger closure. Strict semantic C emits a `while`; a `for`
rewrite is not admitted without separate explicit evidence for that rewrite.
The independent bounded differential probes zero, one, many, and
bound-exhausted iterations, while phase-manifest mutation tests prove that
dropped, duplicated, or reordered initialization, condition, update, or return
phases fail before rendering. Memory, calls, stack inputs, extra carriers,
extra body effects, alternate updates/comparisons, side entries/exits, unknowns,
and every more general stateful loop remain refused.

The eighth closed function subset is one exact conditional return funnel. One
entry predicate selects two polarized candidate producers; each arm may contain
at most one sealed empty forwarder, and both producers meet at one terminal
join. `r2ssa::ConditionalReturnFunnelFact` admits exactly one of two carriers:
an exact register phi or one declared private stack scalar whose two stores and
unique join load have exact reaching definitions, do not alias additional
accesses, and whose address does not escape. `r2cert` seals the control,
candidates, routing, return storage, carrier, and unary carrier-to-ABI
copy/zext/sext/trunc/cast/subpiece chain. The carrier's exact obligation union
is owned by `AbsorbedIntoConditionalReturnState` with identical sealed carrier
evidence; this disposition alone is not render authority.

`r2dec::CertifiedConditionalFunnelReturnFunction` requires exactly one sealed
funnel, a complete ordered predicate, true assignment, false assignment,
carrier merge, return-transform, and shared-return phase manifest, complete
one-to-one source mappings, and the dedicated opaque r2cert permit. Strict C
declares one scalar local at the phi width or declared private-slot width,
assigns it once on each selected `if`/`else` path, and emits one shared ABI
return. Return transforms are folded by walking `SemanticCExprKind` and
substituting only the exact `MachineValueBinding`; rendered names, substrings,
and textual occurrence counts are never proof or execution mechanisms. For the
private-stack carrier, the source stores, load, SP/FP-relative address, and
memory helpers stay sealed state and are not exposed in C.

This does not authorize general phi, stack-local, join, or memory lowering.
Multiple or ambiguous funnels, more than one empty forwarder, aliasing or
escaping stack addresses, extra accesses/effects/blocks, calls, nested control,
unsupported widths, unknowns, nonterminal joins, or return chains outside the
sealed unary vocabulary remain refused. The whole-function witness, permit,
renderer, compiled bounded differentials, mutation guards, and exact `r2engine`
production route are implemented. The engine reports the dedicated
shared-return funnel region and retains the same fail-closed refusal boundary
for every nonexact case.

The first closed function subset is one terminal block ending in an explicit
source `Return`, with no successor and an explicit source function interface.
An explicit void interface authorizes only `return;`. A register-return
interface authorizes only one exact full-width carrier whose producer is a
preceding operation in the same block and whose semantic expression has the
same binding and type. The return control and optional return value each have
one `AbsorbedIntoReturn` disposition and one exact typed-return mapping. A
closed terminal-return region owns those mappings, the exact certified-artifact
origin, and the final r2cert render permit. It does not generalize zero
successors into a return: `None` still denotes incomplete topology, and an
unresolved final block remains refused.

The second closed subset is one exact three-block function whose entry ends in
the certified conditional transfer above and whose polarized true and false
successors each end in one certified terminal return. The topology has no side
entries, extra blocks, join, or open port. All three children share one exact
artifact origin and source-interface revision; their mappings are disjoint and
cover the complete source ledger. The final r2cert permit binds the conditional
polarity, both returns, the combined mapping manifest, and the typed-region
schema. This authorizes one strict semantic-C `if`/`else`; it does not authorize
general diamonds, joins, nested control, or nonterminal arms.

The third closed subset specializes the single terminal-return block to exact
plain RAM effects. Every admitted load or store has one complete structured
access, byte addressing, known little/big endianness, a supported 8/16/32/64-bit
width, and one source-ordered helper-backed execution step. Its r2cert permit
binds the complete memory/return mapping manifest and its strict C renderer
emits exactly one width/endian helper invocation per source access. The source
differential path derives the return independently from canonical CFG/SSA
boundary facts and charges the total executed access width against its finite
memory budget. Word-addressed, guarded, atomic, ordered, stack/custom-space,
call/control, and incomplete memory effects remain refused.

The first positive call-boundary subset is one final direct call with an exact
source-owned raw-callsite identity, shared revision identity, nonempty calling
convention, ordered full-width register arguments, explicit completeness,
nonvariadic and non-`noreturn` flags, an explicit void result, and one existing
non-self fallthrough. `r2cert::CertifiedDirectCall` cross-checks the raw and SSA
call, resolved target, topology target/fallthrough, exact argument carriers and
values, and the complete `Call/Whole` plus `CallArgument` obligation set. These
obligations receive `AbsorbedIntoCall`. The witness ends at the call and exposes
fallthrough as an open port. `r2dec::SemanticCDirectCall` retains the same raw
identity, interface revision, calling convention, carrier-level argument
types/values, target, and fallthrough. `CertifiedDirectCallBlockRegion` owns
that typed node and the exact source-ordered prefix while exposing both the
callee and fallthrough as open ports. It grants no render permit and proves no
callee behavior, clobber/result state, source-level prototype type, or
executable C call.

The fourth closed function subset composes that exact direct-call boundary with
its sole fallthrough terminal-return block. The entry block must end in the
source-authorized void call, and the successor must be the only terminal return
with no side entry or extra block. The return is either void or an exact
call-independent constant register carrier produced after the call. The final
r2cert permit binds both blocks, call target and raw callsite identity, ordered
register arguments, source-interface revision, complete disjoint mappings, and
the typed-region schema. Strict C emits one callsite-specific external adapter
call followed by the terminal return. This proves neither callee execution nor
clobbers, call results, or a source-level callee prototype; the adapter is an
explicit boundary contract.

Indirect calls, call results, general switches/loops, and general whole-function
call composition remain outside the positive semantic-control/AST subset.
Apart from the exact conditional-return, direct-call/terminal-return,
switch-return, carrier-free-loop/terminal-return, counted-loop-return, and
conditional-funnel-return subsets, local direct, conditional, call, diamond,
loop, and switch fragments retain open ports and cannot be combined with a
terminal block until a generic whole-function composition proof owns every
reachable edge exactly once.

Switch topology is not selector proof. The open topology fragment therefore
remains non-executable: it retains one final `BranchInd`, nonempty unique case
labels, an explicit distinct default, pairwise-distinct existing non-self
targets, exact successor equality, source instruction-address association,
valid case-range metadata, and target addresses representable at the certified
machine width, but exposes every label as an open port.

The fifth closed function subset adds separate selector authority. A sealed
`CertifiedSwitchControl` requires the inferred and raw indirect selector to be
the same producerless value and match exactly one revision-bound ABI parameter
with matching storage and width; its indirect transfer is `AbsorbedIntoControl`,
never residual-authorized. The whole-function topology consists only of the
entry switch and one unique terminal constant/void-return block per ordered
case and default. The opaque permit rechecks the exact labels/default, selector,
return evidence, shared origin/interface revision, complete disjoint mappings,
and absence of residual/refused obligations, side entries, joins, fallthrough,
memory, calls, stack inputs, phis, unknown effects, and extra blocks. Strict
semantic C emits a `switch`, and the independent bounded checker exercises
every case plus a non-case default probe. General switch joins, shared or
nonterminal arms, fallthrough, heuristic/missing selectors, and open topology
fragments remain residual.

### Machine-semantic C contract

Each semantic C expression carries bit width, signedness, arithmetic policy,
cast semantics, shift semantics, comparison interpretation, address provenance
and address space, plus its source semantic IDs. Machine wrapping may not be
rendered as undefined signed C overflow. Constants are reconstructed from
bitvectors, and operations that C cannot express safely use explicit helpers or
residualize.

Observable memory access is statement semantics, not a freely repeatable
expression. The first admitted subset is an exact plain Load/Store with one
complete structured access, an explicit coherent typed address-space model,
known little/big endianness, checked widths, and no guard, atomicity, ordering,
trap, or unknown sibling effect. Its read/write obligation is
`AbsorbedIntoStatement`; a live load result remains separately bound to the
same source step as expression evidence. The statement requires exactly one
evaluation in certified source order through an address-space helper. An
ordinary C dereference is not preservation evidence and the expression-only
layer continues to report the memory obligation as open.

Object IDs and provisional address provenance retained from prepared analysis
are diagnostic/type inputs, not independent authority to synthesize a C lvalue.
The typed address value, address space, width, endianness, word size, exact
structured-access ordinal, and persistent obligation mapping remain the
execution identity. Mixed/custom endianness, unvalidated memory spaces,
incomplete provenance, and guarded/atomic accesses residualize.

Names, formatting, and source likeness are projections only. They cannot alter
the typed AST or satisfy an obligation.

The source function interface is explicit, versioned input rather than an
architecture heuristic. It records calling convention identity, ordered
full-width register parameters, exact non-overlapping stack slots, and an
explicit void or single-register return. Register carriers must match exact
architecture storage. Producerless machine inputs are classified only against
those resources; an unclassified input fails semantic-C construction. Stack
slots bind exact base/offset/size resources and an authoritative Local or
parameter-Home role. Home authority is its parameter index plus the exact
source-canonical register storage; names are cosmetic. These declarations
certify only the resource and accesses contained within its byte range. A
stack-pointer and frame-pointer declaration may still alias at runtime, and a
Home still requires proof of its initializing store and later reload before it
can replace an ABI carrier. Distinct source locals require a future
authoritative frame relation. Interface revision identity binds artifacts
together but is trusted source authority, not authentication.

Aggregate syntax is likewise downstream of proof. The first exact aggregate
projection in `r2ssa` joins a revision-bound pointer parameter and its canonical
register storage, the retained pointer/struct/layout/member IDs, complete
parameter-relative address provenance, and one exact plain-RAM load or store.
It retains the canonical access/instruction identity and the precise loaded or
stored value binding. Only a scalar member at one exact constant byte offset is
admitted; dynamic indices and array displacement remain unprojected.
Certification schema 14's sealed `CertifiedAggregateMemberAccess` contract
revalidates the complete natural scalar layout, exact ABI pointer carrier,
structured access object/site/direction/data, certified memory statement and
exactly-once helper policy, and source memory obligation. The fact is retained
by both full and projected certified functions, but it is not itself an lvalue
or render permit.

The ninth closed function subset composes those certificates with the exact
plain-memory terminal-return permit. Every memory statement in the single
block must map one-to-one to a member of the same revision, ABI pointer,
natural scalar layout, and source type graph. The ordered
`CertifiedAggregateMemberSemanticCFunction` manifest retains each access,
parameter carrier, layout/member identity, and return contract. It reuses the
exact closed plain-memory function permit and adds no independent authority.
Strict C emits canonical struct/member declarations and
helper-backed addresses such as `&arg_0->field_2`; source names are cosmetic.
Signed scalar ABI inputs and returns use the exact logical full-width or
low-bits carrier contract. The production engine attempts this specialized
region before generic memory and refuses to downgrade aggregate pointer
authority when any memory sibling lacks an exact member projection. Dynamic
addresses/indices, mixed pointers/layouts/revisions, unsupported layouts, and
all other incomplete manifests remain residual.

### radare2 and FFI contract

radare2 context collection is immutable and coherent. The completed, sized
`RAnalFunctionSnapshot` owns its copied payload and is hashed only after all
typed context has been collected and its epoch window is rechecked. A generic
decompiler-provider callback and selector replace r2sleigh plugin-name checks in
core. Analysis is read-only. The Stage-1 atomic mutation API validates a whole
batch, prepares allocations, commits call-convention and variable-rename
changes, and rolls them back allocation-free on conflict before publishing
epochs/events. Other mutation kinds are explicitly unsupported by that API
until their rollback contracts are implemented; legacy best-effort paths are
migration debt rather than transactional authority.

The replacement boundary is one generated V2 API table with ABI version,
structure size, capabilities, opaque session handles, request execution,
response inspection/freeing, and error retrieval. Every request carries
`abi_version` and `struct_size`; all pointer/length pairs are validated; returned
allocation ownership is explicit; and panics are caught before crossing into C.
The checked header is generated from the Rust declarations and C/Rust layout is
tested by a linked conformance executable. Production decompile and type
requests use this table and carry an exact function interface when the radare2
snapshot grants that capability. V2 source schema 5 requires a nonzero snapshot revision
equal to the immutable context hash and the exact requested function address.
Stack resources carry an explicit BP/SP kind and a named full-width base that is
canonicalized to `ArchSpec` storage; source register offsets are not assumed to
share Sleigh coordinates. Each resource is classified as an exact Local or
parameter Home; Home proof uses only its parameter index and source-canonical
register storage, while names remain cosmetic. The C provider rejects root functions above 200
blocks, 512 lifted operations, or 16 MiB of aggregate lifted input before
snapshot collection and charges interprocedural lifting against a remaining
whole-request budget. V2 validation additionally uses checked aggregate limits
for blocks, operations, context/nested items, strings, JSON, and allocation
arithmetic. radare2 snapshot schema 4 (public ABI 135) also captures generic raw
callsite contracts and a capability-gated, reachable logical type graph. The
graph binds parameter and return carriers to exact signed/unsigned scalar,
pointer, struct, aggregate-member, size, alignment, and offset identities under
the admitted x86-64/arm64 natural-layout model. V2 maps each raw instruction/target pair to exactly one
lifted block/op/target-storage identity, carries ordered full-width register
arguments and result/flag contracts, and revalidates every mapping in Rust.
The transported array is all-or-none relative to the immutable snapshot;
semantic completeness remains explicit per callsite, so incomplete entries
cannot certify. One native V2 request graph now carries the context, lifted
blocks, lift quality, interprocedural scope/plan, analysis depth, timeout, and
optional source schema 5 interface for either request kind. The historical V1
decompile/type aggregates, exports, manual C layouts, and migration shim are
deleted; source tests and a linked-library symbol-absence gate enforce that
deletion. Responses own their output, diagnostics JSON, outcome, and stable
eleven-entry timing inventory and expose borrowed views through the generated
response-info accessor. The generated execution-control capability covers the
relative request timeout plus session cancel/reset callbacks. The current
public limited radare2 snapshot collector preflights exact base-type and child
counts, all owned base/member/variant name and type strings, and assumptions
JSON with checked arithmetic before cloning global types. The original collector
is an unlimited wrapper for source compatibility. Native V2 resolves and
requires the limited symbol, passes its context/nested/string/JSON aggregate
caps, and fails closed instead of invoking an older unbounded collector.

### Admission to `CertifiedC`

A function may carry the semantic-kernel `CertifiedC` claim only when:

1. its complete canonical obligation inventory exists;
2. every obligation has exactly one valid final disposition;
3. each rewrite has a valid source-to-output map and control proof;
4. every reachable block exit and control edge is owned by one closed typed
   region rooted at the certified entry, with no open successor ports;
5. every pending semantic-AST obligation, including direct/conditional control
   and returns, is validated in the final typed AST;
6. its typed C AST preserves explicit machine semantics; and
7. all unsupported semantics are residualized or refused.

Until that path is implemented, the existing label is a legacy rendered-proof
claim and must not be interpreted as proof that every live source effect was
preserved. The legacy counter/render-token route is therefore incapable of
authorizing executable C in production. Final authorization is an opaque,
non-deserializable r2cert permit bound to the exact artifact origin, closed
ledger, typed-region kind and schema, and complete source-to-output mapping
manifest. Nine exact r2dec renderers cover only the closed scalar
terminal-return, plain-RAM-memory terminal-return, exact three-block
conditional-return, exact two-block direct-void-call/terminal-return,
switch-return, carrier-free-loop-return, counted-loop-return, and exact
conditional-funnel-return subsets above, plus the exact aggregate-member
terminal-return subset. The first eight use unsigned machine-width carrier
types; the aggregate specialization retains exact source scalar signedness.
All emit strict C11. `r2engine` currently receives authoritative
source interfaces and exact stack-resource declarations through the immutable
snapshot and V2 boundary and selects all nine renderers. Selected routes
report the exact r2cert region instead of a legacy rendered-proof permission.
Exact renderer selection depends on the prepared artifact's source facts and
opaque permit, not on legacy decompile-route metadata; that metadata is used
only as fallback behavior after every exact renderer declines the artifact.
The direct-call renderer additionally requires an authoritative source
callsite interface; V2 supplies it only after unique raw-to-lifted mapping and
revision/function-identity validation. Everything outside the nine routed
subsets safely residualizes or refuses rather than falling back to heuristic
executable C.

### Verification and quality policy

Semantic equivalence, obligation closure, compilability/undefined-behavior
policy, structural coverage, and type accuracy are hard gates. Readability,
exact names, literal formatting, and source likeness are soft metrics.

Static obligation closure and final `CertifiedC` admission are proof gates.
The target architecture requires callers to make differential verification a
falsification and regression gate before rendering; the current bounded block,
scalar terminal-return, memory-terminal-return, conditional-return,
direct-call-boundary, switch-return, carrier-free-loop, counted-loop, and
conditional-funnel checkers provide that evidence but do not grant production
authority. A mismatch disproves preservation,
while a finite successful run means only that no mismatch was observed for its
recorded input domain and semantic bounds.
Prepared canonical SSA and the typed semantic C AST are interpreted from the
same typed inputs, memory bytes and permissions, alias model, machine context,
external models, and semantic fuel. Checks compare return values, ordered
memory writes and relevant observable reads, calls/arguments, traps, final
observable memory, and bounded termination. Unsupported interpreter coverage
or exhausted fuel makes the run incomplete, never equivalent. Once integrated,
deliberately deleting, duplicating, or reordering any live effect must fail
before rendering or produce a differential mismatch under a covering input.

The first executable differential slice is deliberately narrower than that
whole-function target. Its base runner admits one certified open-exit
straight-line block, 8/16/32/64-bit integer operations, explicit wrapping
arithmetic, certified shift/cast/comparison policies, and byte-addressed plain
memory with known little/big endianness. A specialized closed-terminal runner
additionally admits the exact explicit-interface register/void return subset
and compares returned carrier values. A separate direct-call runner evaluates
the independently decoded source prefix and typed semantic prefix, compares the
source-owned call identity, interface revision, target, fallthrough, calling
convention, and ordered carrier bitvectors, and stops before the callee. It does
not model external execution or post-call state. The conditional-funnel gate
separately compiles and executes both exact carrier forms over bounded zero,
boundary, and deterministic-random inputs, including one sealed forwarder.
Outside such specialized whole-function gates, other calls, traps, general
phis or executable branches, and word-addressed or otherwise unknown memory
remain residual or incomplete.
The source interpreter takes operands and widths from canonical SSA and the
typed source `SpaceId` retained at the corresponding R2IL site; structured
access facts and the certified machine context are cross-checks and shared
machine inputs, not the source operand oracle.

The two evaluators use separate bitvector, signed-order, sign-extension,
shift, endian packing, and memory-range implementations. Address-domain width
is enforced before every access, including multi-byte boundary crossings.
Expression and memory-byte limits are run-wide. Failure reports retain ordered
observable prefixes so a shared eventual refusal cannot hide a prior read,
write, or final-memory divergence.

Every admitted/evaluated serialized case is bound to the exact certified-
artifact origin, exact semantic block-layer bytes, evaluator-contract version,
initial typed values and closed memory domain, block address, and limits. The
candidate identity is absent before a semantic layer exists. The requested-
artifact identity is absent when certification itself fails, rather than being
substituted from a foreign initial state. Addresses and bitvectors use canonical
hexadecimal strings, canonical instruction IDs use structural records, and maps
use sorted record sequences. Candidate admission, interpreter coverage, invalid
input/artifact, harness failure, observed mismatch, and a finite no-mismatch
result remain separate outcomes. `NoMismatchObserved` is a bounded falsification
result only and grants neither `CertifiedC` nor authority to execute an open
control-flow port.

Manual lift -> SSA -> evidence -> AST -> output backtracking remains mandatory.
O0/O2 coverage, boundary values, deterministic random inputs, aliasing, pointer
models, integer limits, and zero/one/many loop iterations are part of the hard
verification program. Deliberately mutated effect/edge tests exercise this
requirement inside the checkers, while production integration tests prove that
only the nine production-routed exact subsets emit semantic C through
`r2engine` and that an absent or incoherent source interface,
selector/condition storage, or callsite interface fails closed.

### Performance and caching

Timings are recorded separately for snapshot collection, lift, SSA, obligation
construction, symbolic evidence, type inference, certification, structuring,
normalization, rendering, and FFI conversion. Cold and warm measurements remain
separate. A fixed-runner CI contract first probes the live plugin ABI and all
measured command payloads, rejects empty/fallback/malformed samples, then gates
20-sample nearest-rank p95 command-body latency using radare2's in-process
timer. Cold/warm RSS is gated independently. The bounded O2 `fnv_fold` target is
the latency fixture; the intentionally over-budget O2 `mem_scan2` target is a
source-gold refusal assertion and cannot pass as a fast performance sample.

Engine analysis, type, decompile, refusal, and cache-hit reports always carry
the stable eleven-phase inventory with an explicit `executed`, `reused`,
`folded`, `not_executed`, or `refused` status. `folded` means work occurred
inside another measured span and is not a claim of zero cost; snapshot/lift and
FFI conversion remain `not_executed` at the engine boundary until their owning
layers report them. The V2 owner measures input conversion plus output `CString`,
diagnostics, timing-array, and response allocation, publishes that total both
explicitly and as the executed `ffi_conversion` phase, and preserves all other
engine phase statuses. A relative request timeout and session-owned
cancellation token are combined into one engine execution control; cancel and
reset callbacks give the caller explicit one-request control. Engine polling
covers SSA and symbolic solver/path/executor worklists plus semantic, type,
certification, semantic-kernel render attempts, and r2dec normalization,
assignment-consensus structuring, and rendering inner work. Refusal preserves
the exact stopped phase and reason, emits no partial C, leaves later phases
unexecuted, and does not mutate the session cache. An individual in-flight Z3
check remains non-preemptible, so the current control is not preemption at
every operation.

A cache remains only when a realistic session trace demonstrates meaningful
reuse and lower total latency/RSS. Algorithm-local memoization and measured
same-session analysis reuse are allowed; a speculative whole-artifact cache is
not. Shared immutable artifacts use shared ownership rather than large clones.
The 512 MiB stack thread and per-decompilation thread spawn are removed.

Phase 9 therefore retains one bounded, session-local cache of immutable SSA
analysis held by `Arc`. The checked
`realistic_session_trace_reuses_shared_analysis_without_artifact_cache` trace
runs SSA preparation, type analysis, and decompilation for the same function;
all warm operations reuse the same analysis allocation while request-specific
semantic facts, writeback plans, and rendered artifacts are rebuilt. The former
whole-artifact cache, its lookup path, and its live counters are absent. The
legacy zero-valued `artifacts` metrics member, the public
`ArtifactCacheKey`/`function_artifact_cache_key` aliases, and the serialized
`EngineCacheLayer::Artifact` variant are deleted. Plugin cache statistics now
expose only the measured analysis layer and its identical total.

Legacy `ProofCoverage` counters and `RenderPermission` values remain visible in
route/report diagnostics for compatibility, but they are not render authority.
In every build profile, a legacy `Standard` route receives only a residual
diagnostic; exact executable C requires an `r2cert` typed-region permit. Exact
semantic-kernel success clears the legacy fields, while a near-miss refuses even
if an injected compatibility record claims `CertifiedC`.

## Consequences

- The rewrite may temporarily break output, but each milestone restores a green,
  manually backtrackable checkpoint.
- `r2cert` becomes a new, small certification owner; certification leaves
  `r2types` and `r2dec`.
- Existing output-count certification and name/string-based semantic recovery
  are migration debt and are deleted once their replacements land.
- A safe residual is a correct result; plausible but uncertified executable C is
  not.
- Two competing semantic pipelines are not retained long-term. Legacy feature
  paths are removed soon after certified replacements cover them.
- Phase 0 freezes the real baseline. Phase 1 then makes omission and duplication
  detectable through the source-driven obligation inventory before further
  decompiler formatting work proceeds.
