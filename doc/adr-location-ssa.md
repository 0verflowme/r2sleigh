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

### The FFI boundary is one typed contract

Linkage is already right: the plugin exports two symbols, `r2sleigh_api_v2` and
`r2sleigh_snapshot_wire_decode_v2`, and radare2's own added surface is three
`R_API` functions over one opaque snapshot and one view struct. What sits behind
those two symbols is not right.

Version numbers stop gating anything. `crates/r2source/src/radare_abi138.rs`
currently refuses a snapshot when `schema_version`, `abi_version` or
`accessor_schema_version` differs from a pinned constant, and three further
equalities are asserted at compile time in `r2plugin/src/ffi_v2.rs`. The
capability bitmask that follows those checks is itself an exact match, rejecting
any snapshot that advertises a capability the plugin does not know, so a new bit
in radare2 breaks the plugin as surely as a bumped number does. The header on the
radare2 side already argues against precisely this, and the C guard was corrected
to match while the Rust side was not.

Under this design the plugin negotiates: unknown capability bits are ignored
rather than rejected, struct growth is absorbed through `struct_size` together
with per-field capability bits, and no code path compares a schema number for
equality. The ABI number leaves the filename and the type names, because the
whole premise is that the number moves for reasons the plugin does not care
about.

The vtable stops mirroring internal structure. Sixteen of its thirty-seven
entries are field accessors — `lift_block_addr`, `lift_block_size`,
`lift_block_jump`, `lift_context_arch_name` and the rest — which is a call and a
maintained declaration per field on both sides. They collapse into view calls
returning `repr(C)` structs, which is the pattern radare2's own
`r_anal_function_snapshot_view` already uses across the same boundary.

One transport replaces three. Typed views carry structure. The serialized wire
format stays for the snapshot, and its C reader is generated from the Rust
definition so the existing byte-for-byte conformance test guards a build step
rather than two hand-maintained implementations. The JSON channel —
`diagnostics_json` and the analysis JSON constants, behind roughly two hundred
JSON-handling lines in the C wrapper — is removed, because facts crossing this
boundary should be typed contracts.

The C wrapper becomes registration and dispatch. `r_anal_sleigh.c` is presently
5,301 lines across 137 functions, one of which is 796 lines of command dispatch,
against only 22 distinct radare2 API calls in the whole file; that is the
project's own logic living in its least safe language on the far side of the
boundary. It moves into Rust. How much of the command dispatch is genuine
radare2 command-surface obligation has not yet been established, so no line
target is set here.

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

1. Ledger and closure invariant, with the symbol table that typed identifiers
   will be built on.
2. FFI boundary: stop gating on version numbers, collapse the accessor vtable
   into view calls, remove the JSON channel, generate the C wire reader, and move
   the C wrapper's logic into Rust.
3. Location model and use index in `r2ssa`, covering registers and stack objects,
   with symbolic execution consulted for stack promotion.
4. Delete the register-family repair pass. If it is not dead, step 3 is
   incomplete; this is the falsification test for step 3 rather than a cleanup.
5. Move the observable-reachability filter out of `r2types`.
6. Collapse the facts structs into one model and enforce the renderer's read-only
   contract.
7. Rewrite the fold: demote flags and temporaries, migrate expressions onto the
   symbol table, extract the target model, and convert the complexity ceiling
   into budget refusals.

The FFI comes before the location model because the snapshot enters the system
through that boundary and the location model consumes exactly what crosses it;
building locations first means building against a contract about to change shape.

Replacing `CExpr::Var(String)` with a symbol reference is bound to step 7 rather
than done in step 1, because it was measured rather than guessed: the change
produces 970 compile errors, of which 586 are in `fold/op_lower/mod.rs` and
`fold/flags.rs`. Those are the expression builder and the flag machinery, and
step 7 rewrites the first and deletes most of the second, so migrating them
first is migrating them twice. The symbol table lands in step 1 regardless, so
every step after it writes against a declared name rather than adding to the
debt, and `CExpr::Var(String)` stays the single implementation until it is
replaced rather than sitting beside a second one.

That measurement also produced the sharpest single finding of the attempt: much
of the renderer decides things by inspecting how an identifier is spelled.
`parse_address_from_var_name` recovers an address from a variable's name and
`linear_var_is_integer_scalar` recovers a type from one, which is the same
mistake as deciding a stack address by testing whether a register name contains
"sp". Symbols must therefore carry what those spellings were being used to
encode, or the migration will only move the string inspection somewhere else.

Every step except 3 is expected to be net-negative on line count.

## Consequences

The renderer should shrink substantially once it stops re-deriving storage
identity and liveness, though whether it does so on its own or needs deliberate
splitting is not yet known.

`writeback.rs`, at roughly 22,000 lines the largest file in the project, has not
been traced and its role under this design is unresolved.

Removing the JSON channel and the accessor vtable changes what radare2 sees, so
the plugin and the fork move together for step 2 and the wire conformance test is
the gate on that step rather than an afterthought.

The branch is long-lived against a tree other sessions edit concurrently, so
rebases will be frequent and staging must be by explicit path.

## Exit criteria

The `-O1` FNV-1a 32 case renders its loop body and returns the accumulator. The
thirty-six-rendering corpus is re-measured, and every rendering that is not
correct is accounted for by a ledger entry naming the layer that refused it.
