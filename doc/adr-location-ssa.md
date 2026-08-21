# ADR: SSA over locations

Status: accepted, unimplemented
Branch: `arch/location-ssa`

## Context

A corpus of nine common hash routines — FNV-1a 32 and 64, CRC32 bitwise, CRC32
table-driven, djb2, Adler-32, MurmurHash3, and a caller chaining three of them —
was compiled at `-O0` and `-O2` for x86-64 and arm64 and rendered with `pdd`.
One of the thirty-six renderings is semantically correct, and it is correct only
because clang at `-O0` on x86-64 spills every live value to its own frame slot,
so the recurrence is memory traffic and the renderer transliterates it. Nothing
is recovered in that case.

The cliff is register residency rather than optimisation complexity. The same
function at `-O1` — twelve instructions, no unrolling, no vectorisation — renders
with an empty loop body and a return of the pre-loop seed.

Runtime instrumentation traced this to a single gap with three downstream
consequences. Details and evidence are in issues #47 through #61.

### What the evidence showed

SSA is built over Sleigh varnodes, so `EAX` and `RAX` are separate storages that
overlap. The value carrying a loop's meaning and the value carrying its uses are
different `ValueId`s. `canonical_storage` already records the truth on every
value and instruction and is consulted by fingerprinting and execution identity,
but by nothing that decides liveness.

Aliasing is instead repaired after SSA construction by splicing `Subpiece`
projections into predecessor blocks under synthesized names of the form
`tmp:regalias:phi:{block}:{phi}:{source}`. Those names are what reach rendered C.
The workaround and the symptom are the same object.

Because storage identity is wrong, three separate liveness decisions in three
crates each reject the accumulator for a different reason, and a value must
survive all of them. Of twenty-four phis at one loop header, exactly one passes,
and it passes only because it happens to be both a memory-address operand and a
loop-predicate operand.

Separately, obligations are counted during the fold, structuring then deletes the
statements, and the rendered proof line prints how many obligations are owned and
how many are unsupported with no word for the remainder. A gutted body reports as
clean.

### What the shape of the tree showed

The renderer is the largest crate in the project, at roughly a third of 288,000
lines, and carries 378 hardcoded register-name literals across ten files. Eight
distinct `Function*Facts` structs cross the boundary from types into the
renderer. Much of the renderer's bulk is re-derivation of things the layers
beneath it already know.

`AGENTS.md` already states the intent this ADR restores: one canonical fact has
one canonical owner, facts flow through typed contracts, and architecture seams
may be rewritten whenever the rewrite is cleaner. The code has drifted from it.

## Decision

### Locations replace varnodes as the SSA substrate

A location is a register family, a stack object, or a global. Each has a width
and a stable identity. Sub-width access becomes explicit rather than implicit:

    read    v = extract(loc_n, lo..hi)
    write   loc_{n+1} = insert(loc_n, lo..hi, v)

On both supported targets a 32-bit register write zeroes the upper half, so it
lowers to a plain definition; `insert` is needed only for x86 8-bit and 16-bit
writes, a small set the target model enumerates. There is exactly one definition
chain per location, so the use index is correct by construction and needs no
repair pass.

### Stack objects are locations in the same graph

Register recovery and stack-slot recovery are today two pipelines producing the
same kind of answer, and they are the reason `-O0` scores well while `-O1`
collapses. They become one graph. Address-to-location resolution happens once,
at lift, in the code that knows the frame, replacing the three fallback tiers and
the register-name substring match that currently answer that question.

Promoting a stack object to a location requires evidence that no pointer aliases
it. That is a memory disambiguation question, and it is where symbolic execution
belongs: as an oracle consulted during promotion, not as a whole-function summary
consulted after the fact. `r2ssa` does not currently depend on `r2sym`, which is
why no amount of solving has helped at these seams.

### Layers annotate; they do not veto

`r2ssa` owns structure: locations, definitions and uses, dominance, loops,
carriers, liveness. It is the sole authority, and each refusal it makes is
recorded once with a reason.

`r2types` owns types and names. It may attach a type to a value. It may not
decide that a value does not exist. The observable-reachability filter that
currently drops certified carriers is a liveness decision taken in the types
layer, and it moves or is deleted.

`r2dec` owns rendering: regions, statements, expressions, text. It may not
re-derive liveness or storage identity.

This is enforced by the shape of the interface rather than by review. The
renderer receives a read-only model whose API answers what something is and has
no method shaped like whether something should be rendered. Any predicate that
gates rendering lives upstream of the renderer. The eight facts structs collapse
into one model with sections, because eight lookup surfaces are eight
opportunities to consult the wrong one.

### Accountability is structural

Every obligation in the source inventory ends in exactly one terminal state,
recorded at the moment it is decided and by which layer decided it: rendered,
elided with a reason, or refused with a layer and a reason. The render boundary
asserts that the three counts sum to the total. There is no fourth bucket, so a
silently missing obligation is not representable; it is an assertion failure in
debug and a printed count of unaccounted obligations in release.

Code generation emits value handles rather than strings. An identifier that does
not resolve to a value cannot be constructed, so declaring a name the body reads
but nothing assigns stops being expressible. The pass that scans finished output
for identifiers naming nothing is deleted rather than fixed, because what it
detects can no longer be built.

Budget exhaustion becomes a refusal recorded against the obligations not yet
discharged, so the engine renders what it has and accounts for the rest. The
whole-function complexity ceiling that currently refuses ordinary code at three
basic blocks is no longer needed to keep cost bounded.

### The merge set shrinks, and the target is isolated

CPU flags are derived values, not stored ones, and are modelled as projections of
the comparison that defines them rather than as locations that acquire phis at
every merge. Sleigh temporaries are intra-instruction by construction; one
crossing a block boundary is a lifting defect to report rather than a value to
merge. Together these take the measured loop header from twenty-four phis to two,
which leaves the liveness rules two things to get right instead of twenty-four.

The renderer sees location identifiers and asks the model for display names. ABI
knowledge — argument registers, return registers, caller-saved sets — lives in one
target model supplied by the lifter. Adding an architecture becomes a Sleigh
specification and a target model, with no renderer change.

## Sequence

The ledger comes first. Unifying register and stack recovery in one change is
precisely the change that cannot be scored by reading output, so accountability
has to work before it lands.

1. Ledger, closure invariant, and typed identifiers in code generation.
2. Location model and use index in `r2ssa`, covering registers and stack objects,
   with symbolic execution consulted for stack promotion.
3. Delete the register-family repair pass. If it is not dead, step 2 is
   incomplete; this is the falsification test for step 2 rather than a cleanup.
4. Move the observable-reachability filter out of `r2types`.
5. Collapse the facts structs into one model and enforce the renderer's read-only
   contract.
6. Demote flags and temporaries, extract the target model, and convert the
   complexity ceiling into budget refusals.

Steps 1 and 3 through 6 are expected to be net-negative on line count.

## Consequences

The renderer should shrink substantially once it stops re-deriving storage
identity and liveness, though whether it does so on its own or needs deliberate
splitting is not yet known.

`writeback.rs`, at roughly 22,000 lines the largest file in the project, has not
been traced and its role under this design is unresolved.

The branch is long-lived against a tree other sessions edit concurrently, so
rebases will be frequent and staging must be by explicit path.

## Exit criteria

The `-O1` FNV-1a 32 case renders its loop body and returns the accumulator. The
thirty-six-rendering corpus is re-measured, and every rendering that is not
correct is accounted for by a ledger entry naming the layer that refused it.
