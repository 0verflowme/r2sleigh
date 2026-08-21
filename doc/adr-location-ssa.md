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

That repair pass turned out to do its dataflow job correctly. Dumping the SSA
showed it rewrites the loop body's read of `EAX` onto `RAX`, which leaves the
narrow phi genuinely dead and the wide one a complete single-value carrier. The
first published account of this defect blamed the resulting empty use list and
was wrong; that emptiness is right.

What per-slice identity actually breaks is every rule that has to decide whether
two values are the same place. The exit block merges a phi for `EAX` and a phi
for `RAX`, and the rule choosing the returned value wanted exactly one candidate,
found two, and certified that the function returned nothing. With no return among
the observable roots the accumulator's carrier was reachable from nothing, so it
acquired no binding, so nothing materialised it, so every operation feeding it
was dead and the loop body was eliminated. The rendered `void` signature had the
same cause. The loop index survived only because it is both a memory-address
operand and a loop-predicate operand, so the backward slice reached it twice.

The lesson for this design is that the defect is not in one liveness check. It is
that storage identity records a slice, and rules across three crates ask identity
questions of it that only a location can answer.

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
gates rendering lives upstream of the renderer.

The first draft said eight facts structs should collapse into one model, on the
grounds that eight lookup surfaces are eight chances to consult the wrong one.
That was a miscount. `FunctionFacts` is already that one model: the eight
`Function*Facts` types are its private fields, reached through methods, and one
value of it crosses the boundary rather than eight.

The read-only half of the contract also already holds, and holds structurally
rather than by convention. The renderer is handed `&'a FunctionFacts`, every
field is private, and the mutating methods take `&mut self`, so no borrow the
renderer has can reach them. The one place the renderer clones facts, edits the
copy and leaks it is a `#[cfg(test)]` helper, and the two other leaks in the tree
are inside test modules as well; none is on a production path.

What is left of this step is a guard against a future violation rather than a
repair of a present one: no method on the model should be shaped like "should I
render this", so a rendering decision cannot migrate back into the layer that
owns facts.

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
format stays for the snapshot.

The first draft said its C reader should be generated from the Rust definition.
There is no C reader. `snapshot_wire.c` is a writer, and 239 lines of it are
primitive encoders and buffer growth, which no schema generator would produce
anything better than. What could drift is the field order in `snapshot_walk.c`,
where 120 encoder calls describe a radare2 snapshot, and generating that from
Rust would require the Rust side to model radare2's structures rather than
merely read them.

It is already guarded, twice. `snapshot_wire_conformance.c` asserts the C writer
emits exactly the bytes r2source's writer does, and the same vector is asserted
from the Rust side, so drift on either fails a test rather than yielding a buffer
the other misreads. That is a weaker guarantee than generation and a much smaller
machine, and until the field order starts moving it is the better trade. The API
header is generated because it is a pure projection of Rust declarations; this is
not.

The JSON claim in the first draft of this decision was too broad and is
corrected here. `R2SLEIGH_ANALYSIS_BLOCK_OP_JSON_V2` and its neighbours feed
`r_cons_printf`: they are the JSON a user asked for, not facts being shipped
between layers, and removing them would delete a feature rather than a
transport. What is genuinely wrong is narrower and still worth fixing. The C
wrapper parses JSON that Rust has already produced, with `r_json_parsedup`, to
merge two documents into one and print the result. That is reparsing on a
boundary where the structured values were available on the other side, so the
merged document should be produced once, in Rust, and the roughly two hundred
JSON-handling lines in the C wrapper go with it. No user-visible output changes;
the same bytes are printed by whichever side is holding the values.

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

The size of that job was overstated in the review this decision came from. The
378 hardcoded register names it counted are 138 in code and 434 in test fixtures,
and of the 138 a fifth are already inside `fold/arch.rs`, which is the target
model in embryo. Three files hold most of the rest: `lib.rs`,
`analysis/use_info.rs` and `variable.rs`. So this is a bounded change rather than
a sweep, and the fixtures were noise in that count rather than architecture
leaking into the renderer.

Deciding what a condition code is belongs here too, and cannot be done before it.
Both copies of that test asked a list of names, and the surviving one still does.
Storage would answer it properly — a flag is a one-byte register whose family has
no wider member, which is arch-neutral and already computable — but several
callers hold only a name, not the value it names. Threading identity to them is
the same work as replacing `CExpr::Var(String)`, on the same call chains, so the
two are one job and not two.

## Sequence

The ledger comes first. Unifying register and stack recovery in one change is
precisely the change that cannot be scored by reading output, so accountability
has to work before it lands.

1. Ledger and closure invariant, with the symbol table that typed identifiers
   will be built on.
2. FFI boundary: stop gating on version numbers, collapse the accessor vtable
   into view calls, produce the merged diagnostics document in Rust instead of
   reparsing it in C, and move the C wrapper's logic into Rust.
3. Location model and use index in `r2ssa`, covering registers and stack objects,
   with symbolic execution consulted for stack promotion.
4. Delete the register-family repair pass. If it is not dead, step 3 is
   incomplete; this is the falsification test for step 3 rather than a cleanup.
5. Move the observable-reachability filter out of `r2types`.
6. Collapse the facts structs into one model and enforce the renderer's read-only
   contract.
7. Rewrite the fold, in this order: model function live-out from the target ABI,
   then demote flags and temporaries, then give each certified carrier one name,
   then migrate expressions onto the symbol table, then extract the target model
   and convert the complexity ceiling into budget refusals.

The FFI comes before the location model because the snapshot enters the system
through that boundary and the location model consumes exactly what crosses it;
building locations first means building against a contract about to change shape.

Replacing `CExpr::Var(String)` with a symbol reference is bound to step 7 rather
than done in step 1, because it was measured rather than guessed: the change
produces 970 compile errors, of which 586 are in `fold/op_lower/mod.rs` and
`fold/flags.rs`. There are 767 construction sites in code and the change is
atomic, so there is no green tree part of the way through it.

Separating the two meanings `Var` carries is a smaller move and can be made on
its own. Of those 767 sites, nineteen name something the function does not own --
an intrinsic the target defines, a marker the lowering emits where it has nothing
to say -- and those are not values a declaration could ever give. Adding an
`External` variant for them costs only the thirty exhaustive matches that have to
gain an arm, which compiles green and leaves the remaining sites all meaning one
thing.

That was attempted with a script over the thirty matches and reverted, because
the arms are not uniform: some open a block, some carry a guard, and the script
produced malformed patterns in five files. Done by hand it took thirty
decisions, two of which the compiler caught landing on the wrong match because
the two matches returned different types. It is worth recording that the arms
had to be decided rather than filled in: renaming skips an external name because
renaming moves names the function owns, the placeholder tests answer false
because they ask about names the renderer minted, and constant folding leaves it
alone because an intrinsic never spells a constant.

The split paid for itself immediately and not where expected. x86-64 `-O2`
renders 226 lines where it rendered 302, because the lane extractions that were
reaching the page as `tregalias` locals fold into named SSE values once the
passes treating `callother` as a variable stop doing so. Those leaks were being
held in place by the expression layer misclassifying the intrinsic they fed, not
only by the pass that created them.

It did not shrink the migration it was meant to open. Measured again afterwards,
replacing `Var(String)` with a symbol reference is 952 errors rather than 970,
and 579 of them are still in `fold/op_lower/mod.rs` and `fold/flags.rs`. The
change remains atomic over roughly 750 sites, each needing a decision of the
kind the thirty arms needed, so it is not something to begin without the room to
finish it. Demoting flags first would remove the 210 in `flags.rs`, which is the
only decomposition of it left that is worth anything.

What demotion cannot be is a deletion, and that was nearly concluded from a
corpus that could not see the difference. Instrumenting
`try_reconstruct_condition` over the nine hash functions counts 287 calls and
zero reconstructions, at either optimisation level on either architecture: it
walks every expression in every function and never fires. On code written to
materialise a flag -- a comparison stored as a boolean, a carry consumed by
arithmetic, a carry propagated across a loop -- it fires, five times on x86-64
and three on arm64, and is handed a flag expression eighteen times and eight.

So the reconstruction earns its keep on code the corpus does not contain, and
the corpus has a blind spot rather than the code having dead weight. The cases
that exposed it are kept in `tests/gold/flag_materialisation.c` so the next
measurement of this area starts with them.

Demotion therefore means asking whether the predicate facts `r2ssa` already
computes could deliver those conditions directly, so that nothing downstream has
to rebuild them. That is the 3,836-line question, not a removal. Those are the expression builder and the flag machinery, and
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

## Why carrier naming waits for the fold rewrite

A certified loop carrier is one mutable variable that the machine spells
differently on every edge, so an entry value, a phi, a latch update and a
post-loop merge are four SSA values and one C local. Giving them one name was
built and measured: on x86-64 `-O1` it turns three dead locals into a single
`rax` that is initialised once and assigned in the loop, and the duplicate
assignments beside it disappear.

It was withdrawn because it also names carriers that should not exist. At `-O0`
the value the source carries lives in a frame slot and the register beside it is
a copy nothing consults, so naming that register puts a variable on the page that
is written twice and never read.

The rule that separates them is the one this project already states: a value with
a single reader is propagated into that reader, and only a value with more than
one reader is declared. Applying it here needs to know which readers survive, and
at present a carrier's readers are mostly condition-code computations that are
themselves elided. A readership test cannot be written honestly until flags stop
being values that merge, which is step 7. Naming carriers therefore belongs to
step 7 and not before it.

## What the exit block showed, and what it changes

Removing merges nothing reads looked like the obvious way to shrink the merge
set, and it is wrong as stated. In the measured function every phi in the exit
block reports zero uses, including the one that carries the returned value. They
are not dead. They are live out through the calling convention, and the SSA has
no way to say so: the `Return` op targets the instruction pointer, and the fact
that a register carries the answer is an ABI property no operation records.

That is the same absence behind three separate failures already traced. A carrier
is not observable because no return is certified. A readership test cannot tell a
value that matters from one that does not. A phi that must survive is
indistinguishable from one that could go.

So step 7 needs function live-out modelled before any of its parts can be
written honestly, and the machinery for it is already here.
`collect_preserved_projection_defs` in `crates/r2ssa/src/optimize.rs` runs a
backward dataflow over register byte ranges, seeded at return blocks, merging
ranges as it goes. It exists to preserve width aliases and answers exactly the
question the readership test needs to ask. Nothing consults it about whether a
merge is read.

Live-out therefore comes first within step 7: seed it from the target model's
return and callee-saved registers, let the existing backward pass carry it, and
have readership, carrier naming and merge-set reduction all read the one answer.

## Moving the observable filter, and what the failures were really about

Step 5 says the observable-reachability filter in `r2types` is a liveness
decision taken in the wrong layer. Replacing it with the observation set from
`r2ssa` failed twice before it worked, and both failures were the new code
finding an older defect rather than causing one.

The first was in this design's own accounting: the observation set treated a
load as pure. The source obligation inventory carries `ObservableMemoryRead` as
something a rendering owes, so a load is an event whatever becomes of its
result, and a loop carrying a pointer through a chain of loads was classified as
observing nothing.

The second was in the live-out pass. A function with an early-return arm
reported one live value and one returning block it could not resolve. The
resolved arm wrote its result in the block that returned; the other produced it
in the block before, and a single edge needs no merge to carry it across. The
pass looked only at the returning block, said it could not answer rather than
answering none, and was believed. Walking back through predecessors until each
path names a definition took that function from one live value to seven and left
nothing unresolved. Across the corpus the two sets then agreed on every carrier,
and the filter moved.

Moving it renders three more obligations and leaves one fewer unaccounted. It
also cost one loop its `for` shape, and tracing that led to a third defect that
is not this design's: a materialised back-edge copy is emitted even when the
update it carries was already rendered in place, so a body reads `arg_c =
arg_c;` and then `arg_c++`. Self-assignments of that form were in the output
before any of this work, and deleting them at the end would hide the question of
whether two values wrongly share one name. The copy should not be produced, and
that belongs to the fold rewrite.

The general lesson is recorded because it cost three reverts to learn: when a
change that is architecturally right makes something worse, the first move is to
trace what the failing path actually reads. Twice here the answer was that the
new code was incomplete, and once it was that something older had been wrong all
along and nothing had been precise enough to show it.

## The last trace: one variable, two owners

Materialising one merge per register removed the self-assignment it was
producing, and left one loop rendering as a `while` where it had rendered as a
`for`. Tracing that named the next piece of the location model exactly.

The surviving carrier is `RAX_1 = phi(RAX_0, RAX_18)`, a loop counter that also
lives in a frame slot. At `-O0` the value cycles register, store, memory, load,
register, so the merge is a genuine SSA merge for the register and the register
really is read -- by the store. Nothing about it is spurious. But the program's
variable is the frame slot, and the register is a copy of it that is dead at the
loop header, because the first thing the body does is reload.

So the criterion that separates a carrier worth materialising from one that is
not is liveness at a program point: is this value read before it is overwritten,
here. Whole-function readership cannot express it, and neither can anything
currently in the tree. That is a real gap, and it is the same gap behind the
earlier attempt at naming carriers, which put a variable on the page at `-O0`
that was written twice and never read.

It also states what the location model has to be. A location is not only a
register family; a frame slot the compiler spills a register to is the same
place as that register for the span in which they mirror each other, and until
one thing owns that span two models will each claim the variable and each emit
its own version of the update.

## Why naming a carrier is not yet possible, whatever guards it

Giving every version of a certified loop carrier one name was attempted twice.
Both times it delivered clearly on optimised code -- on `-O1` the accumulator
collapses from three dead locals into a single `rax` initialised once and
assigned in the loop -- and both times it damaged `-O0`.

The second attempt added the guard the first one lacked: a carrier the loop
reloads from a frame slot is a copy, and the slot is the variable, so it is left
unnamed. That guard is right and is kept as `crate::mirror`. It is not enough.

What the `-O0` output showed is that one carrier had been given two program
variables:

    uint32_t rax = (int64_t)eax_3;   // the hash
    rax = arg_2c + 1;                // the inner loop counter

The machine reuses `RAX` for the accumulator and for an inner counter, and the
carrier spans both, because a carrier is state a register preserves and a
register is not a variable. Naming all its versions one C local does not merely
add a dead declaration; it says two different values are one, which is worse than
what it was fixing.

No guard on naming could repair that, because the fault was upstream of naming:
the carrier is real and the register is genuinely preserved. What was missing is
the thing this whole decision is about. A location has to be the span over which
a storage holds one value, not the storage itself.

That is now built. `StorageSpans` cuts each storage where it stops holding one
value, by the rule the dataflow already carries: a definition reading the storage
it writes continues what that storage held, and one reading none of its own
values begins something new. `carriers_spanning_a_reuse` names the carriers that
reach across such a cut, and naming skips them.

With both guards in place the conflation is gone and the duplication it was
built to remove goes with it. On arm64 `-O2` three assignments to `x0_2`, `x0_3`
and `x0_4` become one `x0`; on x86-64 `-O2` the same happens to `rax_2` and
`rax_3`; rendered output is thirteen lines shorter across the corpus and
identical across repeated runs.

The mirror test had to be asked the right way round twice before it worked, and
both wrong versions failed for one reason. Neither end of a spill names a carrier
value directly: what the loop stores is computed *from* a member, and a member is
computed *from* what the loop loaded. Testing set membership at either end
therefore sees nothing. Walking back from what the carrier holds until a
frame-slot read is reached sees it, and each value is visited once.

With that, `-O0` output is byte-identical to what it was before carriers were
named at all, which is the correct answer rather than a compromise: at that
optimisation level essentially every variable lives in its frame slot and only
passes through a register, so there is no register carrier there worth a name.
The `-O2` gains are untouched -- x86-64 falls from 308 rendered lines to 302 and
arm64 from 175 to 161 -- and repeated runs hash identically.

The renderer should shrink substantially once it stops re-deriving storage
identity and liveness, though whether it does so on its own or needs deliberate
splitting is not yet known.

`writeback.rs`, at roughly 22,000 lines the largest file in the project, has not
been traced and its role under this design is unresolved.

Replacing the accessor vtable changes what radare2 sees, so
the plugin and the fork move together for step 2 and the wire conformance test is
the gate on that step rather than an afterthought.

The branch is long-lived against a tree other sessions edit concurrently, so
rebases will be frequent and staging must be by explicit path.

## Step four ran its falsification test, and the answer is no

The sequence says to delete the register-family repair pass once locations
exist, and that if it is not dead the location model is incomplete. The test was
run, by disabling the pass and re-rendering the corpus. It is not dead, and what
it showed is more useful than that.

Measured as the share of source obligations a rendering accounts for:

    x86-64 -O0    67.0% with the pass    67.3% without
    x86-64 -O2    80.6% with the pass    80.6% without
    arm64  -O2    51.2% with the pass    45.4% without

On x86-64 the pass buys nothing. It costs 107 rendered lines and it is the sole
source of every `tmp:regalias` identifier that reaches the page: forty-four of
them in the `-O2` corpus, none without it. On arm64 it is load-bearing, worth six
points of rendering.

The first reading of that asymmetry was that the pass is redundant wherever a
zero-extension already relates the narrow and wide value, and busywork on x86-64
for that reason. Looking at what it actually leaks says otherwise, and the
correction matters more than the original claim.

Every one of the forty-four is a SIMD lane:

    uint32_t tregalias:1000007c0:2d:0 = (uint32_t)callother("userop_193", xmm1, xmm6_5, xmm2);
    uint32_t tregalias:1000007c0:2e:0 = (uint32_t)((uint128_t)callother(...) >> 32);

Those extract 32-bit lanes from 128-bit `xmm` registers, which is exactly the
`d2` and `q2` case on arm64 and nothing to do with sub-register writes. The
zero-extension case is already handled, by `preserved_narrow_family_roots_for_widening`,
which keeps the narrow roots alive across a widening write so reading `EAX` after
`RAX = zext(EAX)` needs no projection at all.

So the pass is doing real work on both architectures, for the one thing that
genuinely needs it: storage that overlaps at a relation no extension expresses.
It is not deletable and it is not conditional on spans either. What is wrong is
narrower and is issue 51: a lane projection reaches the page as an identifier
instead of rendering as the lane extraction it is. Two of those lines are not
even valid C, because a name carrying colons reached output without passing the
identifier sanitiser, which is its own defect.

The location model still has to absorb this, but as lanes rather than as a pass
to delete: a location is a span of one storage holding one value, and a lane is a
sub-range of a register that a vector operation writes as a whole. Until locations
can express a sub-range, the projections are how that is said, and the fix is to
render them rather than to leak them.

## Exit criteria

The `-O1` FNV-1a 32 case renders its loop body and returns the accumulator. The
thirty-six-rendering corpus is re-measured, and every rendering that is not
correct is accounted for by a ledger entry naming the layer that refused it.
