# Picking up the r2sleigh architecture rewrite

This is a handoff. It says what was wrong, what was decided and why, exactly
where the tree stands, and what remains before the rewrite can be called
finished. Work happens in the `r2sleigh-arch` worktree on `arch/location-ssa`;
the primary checkout stays on its own branch so a bad day here costs nothing.

Read `doc/adr-location-ssa.md` first for the original design. This document
records what changed once the design met the code.

## Where this stands now

This document is chronological and contains claims that later entries withdraw.
Read this section for the current state; read the rest for the evidence, and note
that several entries are corrections of the ones above them. Anything below that
disagrees with this section is superseded.

### Done

  * **One symbol table per rendered function.** Passes each held their own and
    the fold read a fourth that `mem::take` had emptied; identifiers now carry
    the table that issued them and resolving across tables is an assertion.
  * **Expressions name identifiers, not strings.** `CExpr::Var(SymbolId)`.
  * **One `UseInfo` builder.** There were two complete analyses separated by an
    early return, and production only ever ran one. The other, its two analysis
    modules and the 76 fixtures that drove it are deleted -- about 11,800 lines.
  * **A guard that a facts type never answers a rendering decision**, as a lint,
    verified by planting a violation.
  * **Flag demotion.** A flag is a one-byte register no wider register contains,
    computed from the register file rather than listed. The list it replaced was
    wrong in both directions on both targets.
  * **Target model extraction, partly.** Signature inference chose its ABI from
    the pointer width, so arm64 looked for parameters in `rdi`. It now asks the
    convention the lifter supplies.
  * **Four cost defects**, each measured: an exponential path count, a per-name
    block rescan, a per-question copy of every known name, and a per-question
    scan of every known name that was 64 per cent of a large decompile. A
    function that refused to decompile now renders 1328 of its 1329 obligations,
    and 9314 ops went from 48s to about 5s. The op ceiling moved with the
    measurements, 512 to 16384, never ahead of them.
  * **A loop carrier reaches its return.** `sym._fnv1a64` renders `return x0`
    rather than the value the accumulator held before the loop.
  * **A call's own definitions are not the next call's arguments.** A
    one-argument call rendered with eight.

### Open, each scoped by measurement

  1. **Nothing owns "what does this value render as".** Nine resolvers, about 260
     call sites, each with its own precedence; closing one hands the question to
     the next. This blocks `sum32`, which still returns the value its accumulator
     started with. The contract to state is that *a rendered expression is an
     answer, not a candidate*.
  2. **Thirty-eight places build a call expression**, which is why one call
     renders twice under two spellings. The certified path should own it.
  3. **The width layer.** A carrier written narrower than its phi -- `w8` into an
     `x8` carrier, `EAX` into `RAX` -- is not reconciled, which is what blocks
     the x86 accumulator loops and step 4's repair-pass work.
  4. **The 64-bit constant model.** A folded 16-byte constant has nowhere to
     live, which caps whole-register vector reads. The chosen shape is a wide
     literal in the AST; it is downstream of the tile composer, which is
     downstream of emission.
  5. **Budget as ledger.** A phase that runs out of budget discards its partial
     rendering, so `RefusalReason::BudgetExhausted` is never constructed.
     `render_engine_decompile_request` must return a rendering *and* a stop.

Items 1, 2 and 3 are the same defect at three levels: several implementations of
one job, disagreeing. So were the symbol table and the `UseInfo` builders, and
both were fixed by making one of them own the answer. Look for that shape first.

### How to measure here, which cost more than any single fix

  * **Sampling profiles mislead.** They name the functions most often on the
    stack, which are the small predicates called from everywhere. `is_dead` came
    top three times and is 21ms of a twenty second run. Count calls to separate
    "more work" from "slower work", then time named phases, then time the steps
    inside the phase. One run each.
  * **Mark, do not read.** Four candidate code paths were eliminated in three
    builds by giving each a distinguishing marker and seeing which reached the
    page. Four mechanisms reasoned from the rendering were all wrong.
  * **Mark from a complete list.** Three of those builds were wasted because a
    truncated grep made a file look empty.
  * **Use a linked binary, never an object file.** `radare2` splits a Mach-O
    object at an unresolved `bl`, and two false diagnoses came from decompiling
    half a function.
  * **Check the function boundary before believing a short rendering.**

## What was actually broken

Four rendering defects turned out to share a single cause. SSA is built over
Sleigh varnodes, and `CanonicalStorageId { space, offset, size }` records a
*slice of a storage*, not a location. Two writes to the same register at
different widths are two unrelated identities. From that one fact:

- `unique_return_value_phi_for_block` saw an `EAX` phi and a `RAX` phi in the
  exit block, wanted exactly one candidate, and returned `None`. The function
  reported zero returns, the accumulator was not observable, no carrier binding
  was made, the loop body was eliminated, and the signature rendered `void`.
- `arg_c = arg_c` — a parameter assigned from itself.
- SIMD lane projections leaked into the output.
- A `setcc` was dropped on x86-64: `setge al` writes one byte and `inc eax`
  reads four, so the write did not look like it reached the read.

Runtime instrumentation confirmed the first one end to end. The other three have
the same shape and are filed as issues.

There was a second, quieter problem. A rendered identifier was a `String`. A
machine register that escaped the fold looked exactly like a declared local, and
the only way to notice was to scan the finished text for words that resolved to
nothing. That scan could be satisfied by *declaring the word*, and that is what
the pipeline had started doing — two passes existed for it.

## The design choice, and why

**A rendered name is an identifier the table issued, not a spelling.**
`CExpr::Var` holds a `SymbolId`. A `SymbolId` is minted only by declaring a
name. An undeclared name is therefore unconstructible rather than merely
detectable, which is a stronger property than any scan can give you.

Three consequences fell out, and each deleted code:

- Renaming moves a spelling *in the table*, so every mention moves at once and
  nothing walks the body keeping declarations and uses in step. That removed
  273 lines from `post_rename.rs` and 150 from `lib.rs`, plus two whole
  pipeline passes whose job was declaring names the renderer had already
  written down.
- `post_rename.rs` no longer mentions `CExpr` or `CStmt`. Renaming stopped
  being an expression-level concern.
- Two smells became type errors: identifiers were compared case-insensitively
  to decide whether two variables were the same, and a linear case-folding scan
  answered "did anything read this?".

**Spellings are `Rc<str>`.** Reading a spelling is a refcount bump and the table
borrow ends at the call. This matters because reading a spelling and then
building an expression is the common shape, building mints, and a caller holding
a borrow across the mint deadlocks. The hazard is closed by construction rather
than by discipline, and nothing is copied to achieve it. This is not a cache:
the text is stored once and referenced.

**The boundary that governs the whole step, and was not in the ADR.**
Three separate things were all called "name":

1. a `SymbolId` — a declared C identifier that may appear in output;
2. an SSA display name such as `rax_3` — an internal key into analysis side
   tables;
3. an arch predicate argument — a question about the *shape* of a spelling,
   like `starts_with("local_")`.

Converting every name-taking helper to `SymbolId` conflated all three and had to
be backed out roughly sixty times. The rule that holds is: **a helper whose
backing store is string-keyed keeps a string key, and a rendered identifier
reaching one bridges through `spelling()`.** Re-keying those stores belongs with
the location model in step 3; doing it halfway *is* the conflation.

**Analysis mints.** Twenty-five free functions in `flag_info`,
`prepared_semantic`, `stack_info` and `use_info` build `CExpr::Var` with no
table in reach. The alternative — analysis emits spellings and a later layer
declares them — needs a second expression type, which is the parallel pipeline
the working agreement forbids. So the table is threaded in and analysis
declares. A candidate that gets dropped costs one unused table entry.

**`CFunction` owns the table behind a `RefCell`**, so a pass can read names
while mutating the body via disjoint field borrows. It is moved in when the
function is built, never copied.

## A collision worth knowing about

Three separate structs — `PassEnv`, `FoldInputs`, and local test fixtures — each
had a field named `symbols` holding the binary's *address-to-name map*, and the
migration added the rendered-name table under the same name. Passes that meant
"the names this function declares" were silently reading "what the binary calls
the thing at this address". All three are `binary_symbols` now.

This is the same defect class the migration exists to eliminate, and it was
invisible until the types finally differed. Expect more of these.

## Where the tree stands

`cargo build --workspace` is clean. `cargo test -p r2dec --lib` runs:
**the whole workspace is green** -- `cargo test --workspace` has no failing test
in any crate, r2dec at 706 and r2ssa at 401, down from 1323 compile errors and
83 failures when the suite first built. Forty-eight commits from `763b28d`, net
negative line count.

On the corpus, `pdd` renders 47 of 60 functions across x86-64 and arm64 at `-O0`
and `-O2`, and both flag binaries render completely. The thirteen that do not
fail at the lift, not the renderer: `Unable to resolve constructor`, `genuine
basic block contains instructions after a control terminator`, `machine-derived
CFG contradicts the owned advisory source CFG`. Those predate this work.

### An identifier now says which table issued it

The open question in the first draft of this document — that a `SymbolId` means
nothing outside its own table and nothing said so — is closed. `SymbolId`
carries a `TableId`, and reading one from another table refuses by name.

This was not bookkeeping. Turning the check on took failures from 36 to 42:
**six tests had been passing while resolving identifiers against the wrong
table.** Two tables of similar size resolve each other's identifiers to real but
wrong names, so a rendering says something it does not mean and never faults.
That class was live. The cost is four bytes per identifier and one integer
compare per lookup. Nothing in `r2dec` serialises the AST, so the brand cannot
reach output or disturb determinism — check that again before adding a field.

### Four root causes fixed, each a real defect

- The `structure` tests' `v()` helper built a table **per call**, so every
  reference it returned indexed a table already dropped. 31 failures.
- Writing `symbols.borrow_mut().declare_or_reuse(..)` inline holds the guard to
  the end of the statement, so a second declaration in the same statement
  deadlocks. `symbol::declare()` is a call, so the borrow drops at return —
  which is why `var_ref` was always safe. This makes the safe form the easy
  form and killed all 16 `RefCell` panics.
- Fixtures declared into a local table and then handed `CFunction` a fresh empty
  one. `generate_function` copies `func.symbols`, so codegen read an empty
  table.
- `make_ctx` in the `lower` tests leaked a table of its own while the fixtures
  declared into another.

### How the 83 failures were fixed

Every one was a real defect that the branding exposed, not churn:

- Two contexts reading one fixture each held their own table. The fold context
  owns its table behind an `Rc` now, so they share one. Cloning was the trap: a
  copy taken before the last name is declared is missing it, and the panic moves
  from a table mismatch to an index past the end.
- `structure`'s `v()` helper built a table **per call**, so every reference
  indexed a table already dropped (31).
- `single_evaluation`'s `call`, `assign` and `function` helpers did the same, so
  two references to one spelling were different identifiers and the structural
  comparisons could never hold (4).
- `symbols.borrow_mut().declare_or_reuse(..)` written inline holds the guard to
  the end of the statement, so a second declaration in the same statement
  deadlocks. `symbol::declare()` is a call, so the borrow drops at return —
  which is why `var_ref` was always safe. This makes the safe form the easy form
  (16).
- Fixtures declared into a local table then handed `CFunction` a fresh empty
  one; `generate_function` copies `func.symbols`, so codegen read nothing.
- `make_ctx` in the `lower` tests leaked a table of its own.
- Assertions grepped `format!("{expr:?}")` for a name. A reference carries an
  identifier, so the debug rendering no longer contains a spelling. The
  `spelled()` helper in `pipeline.rs` reads them back out of the table; that is
  what those assertions always meant.
- `test_use_info_deterministic` compared two runs under two contexts, so it was
  asking whether two tables have the same identity rather than whether the
  analysis is deterministic. One function has one table.

## What is left (superseded -- see "Where this stands now")

**Step 2 is not finished.** 83 failing tests, and the cross-table question above
is unanswered.

**Corpus validation now runs, and it found a production bug.** Read the trap
first: `pdc` is radare2's own pseudo-decompiler, not r2sleigh's renderer. It
answers happily with raw register arithmetic. Comparing `pdc` across two builds
of this plugin proves nothing, and I made exactly that mistake before catching
it. The command is `pdd`, driven as `r2 -qc "a:sla; aaa; s <fn>; pdd" <binary>`.

Driven correctly, the rewritten tree rendered **nothing** where the baseline
rendered thirty lines, and the reason was the table brand firing in production:

    identifier from table TableId(1) read in table TableId(5)

Every pass held its own symbol table. Analysis minted into one, the fold context
into a second, and handing `CFunction` its table with `mem::take` left the fold
context holding a third that the take had just emptied. The renderer was reading
identifiers no table it held had issued. Before branding this did not crash --
it resolved to a real but wrong name, and the rendering went out saying
something it did not mean.

There is now exactly one table per rendered function, an `Rc`, shared by every
pass that declares or reads a name. Sharing is a refcount bump; the copies it
replaced were the bug.

`sym._fnv1a64` at `-O2` renders its hash chain again -- the function whose empty
body and `void` signature began this work. Its ledger reads `122 source
obligations: 100 rendered, 0 elided, 2 refused, 20 unaccounted` against the
previous `100 of 120 owned, 2 unsupported`, and the junk locals `ESI`, `RSI_4`
and `tregalias_phi_156_1_0` are gone.

Across the corpus most functions render on x86-64 and arm64 at `-O0` and `-O2`.
The remaining empty ones fail at the lift, not the table: `Unable to resolve
constructor`, `genuine basic block contains instructions after a control
terminator`, `machine-derived CFG contradicts the owned advisory source CFG`.
Those are engine limits and predate this work.

### The undeclared-mention check, and what it found

`unrendered::names_mentioned_without_a_declaration` is a set difference: every
identifier the body mentions, less every one the function declares. It runs
after the last pass that can rename anything, and what it finds is written into
the rendering as a `r2dec defect:` comment rather than left for a reader to
notice.

This question could not be asked cheaply before. A reference was a `String`, so
the only way to ask was to scan finished text for words that resolve to nothing,
and **that scan could be satisfied by declaring the word** -- which is what the
pipeline had started doing. Two passes existed for it and both are deleted.

Twenty-three functions across the hash and flag corpora mention a name they
never declare. The names fall into three kinds, and they are three different
defects:

- **Raw machine registers**: `al`, `rax`, `rsi`, `cf_1`, `d2`, `q2`,
  `xmm6_5`. A register that escaped the fold. This is the original problem the
  symbol table was built to make visible.
- **Call targets rendered as variables**: `sub_2c4`, `sub_504`. The AST has
  `CExpr::External` carrying an `ExternalKind`, precisely so that calling
  something outside the function is a claim a reader can check. These are
  `CExpr::Var` instead, which bypasses it. `ExternalKind` is defined and, apart
  from two intrinsic sites in `analysis/lower.rs`, unused.
- **Placeholder text used as a name**: `register`, `stack slot`. `stack slot`
  contains a space and is not a C identifier at all. It does not reach the
  printed C, so something downstream drops or replaces it, but it is in the
  finished AST.

`arg_c = arg_c` no longer reproduces anywhere in the corpus -- zero
self-assignments across every rendered function.

### Where the undeclared-name work ended up

Three fixes landed and the defect is now fully characterised.

An induction variable a `for` introduces is declared, and so is a name assigned
in a `for`'s condition. Structuring rewrites loops *after* the pass that
declares carriers, so those names appear when nothing is left to notice them.
Extending the old collector to reach a `for`'s init changed nothing, and that is
what identified the cause as ordering rather than coverage.

**Only names the body assigns are declared.** A name that is only ever read has
no definition, and declaring it would turn a dangling reference into valid C
that reads uninitialised memory: the defect would compile and stop being
reported. Driving the count to zero that way was available and is wrong.

So every remaining report is a dangling read, by construction rather than by
observation. `sym._combined` refuses 117 of its 187 obligations and then reads
`local_28` and `t6080`, which no surviving statement writes. The comment names
that -- `N name(s) read with no definition` -- so it points at the dropped
definition rather than at the declaration that would have hidden it.

Counts across the two corpora: 23 functions and 55 distinct names down to 18 and
46. The names go to stderr under `R2SLEIGH_NAME_DEFECTS`, because the comment
renderer replaces machine tokens with prose and would otherwise print the
substitution rather than the name.

### One spelling table is gone; two came back

The phi picker asks the convention which location returns a value, and that
holds. `is_return_value_register` and `is_control_return_target` still match
`rax | eax | ax | al | xmm0 | st0 | x0 | w0 | r0 | v0` and `pc | lr | ra | x30 |
rip | eip`. I removed them, believed it verified, and had to put them back.

**Read this before trying again.** The removal was reported green by a check
that could not tell "nothing failed" from "nothing ran": the commit added a test
helper missing an `AddressSpace` import, so the r2ssa test binary never built,
and `grep -c 'test result: FAILED'` answered zero. Check compilation separately
with `cargo test --workspace --no-run` and read the `test result:` line, never a
bare FAILED count.

With the helper fixed, four control-return tests fail:
`prepared_function_certifies_unique_return_phi_at_control_return`,
`prepared_function_does_not_render_memory_backed_return_phi_at_control_return`,
`prepared_function_refuses_display_named_stack_reload_at_control_return` and
`prepared_return_register_subpiece_zext_chain_is_renderable`. They get past the
certificate lookup and fail on whether the expression is renderable, so it is a
real behaviour change rather than a fixture missing a premise. An instrumented
run shows `unique_return_value_phi_for_block` is never reached for them, so
whatever changes their result is on another path -- I did not find it.

Two pieces of the work were kept because they are independently right:
`ArchSpec::return_registers` lets an architecture state where it returns a
value, serde-defaulted so existing `.r2il` files read unchanged, and the fixture
arches state it. That was the missing third source; with it the chain can be
interface -> convention -> architecture with no hand-written link.

Two things learned while removing them, both still true and both worth keeping
whoever redoes it:

**One predicate was answering two questions.** Whether *this function* returns a
value here must respect a declared `Void`; whether a *call* left its result here
must not, because a void function still reads the results of the calls it makes.
The table serves both because it never consults a contract.

**`SourceFunctionInterface::return_kind()` is the right source**, not the
convention's `result_slot`: it is `Void` or `Register { storage }`, so it states
both whether there is a return value and where. The convention says only where a
caller *would* leave one.

### The xmm6 defect is not a lane-width problem

`sym._crc32_table` in `hashes_x64_O2.o` reads `xmm6_5`, `xmm6_7`, `xmm6_9`,
`xmm6_11` and `xmm6_13` and writes none of them. I assumed this was the leaked
lane projections -- a write lifted at one width and a read at another, which is
what `CanonicalStorageId` including `size` would cause. **That is wrong**, and
the lifted p-code says so plainly:

    a:sla.debug.json at 0x3eb   (pxor %xmm4, %xmm6)
    IntXor dst XMM6 offset 4992 size 16, a XMM6 ..., b XMM4 ...

    a:sla.debug.json at 0x3f8   (blendvps %xmm0, %xmm6, %xmm2)
    CallOther userop 193, inputs XMM2, XMM6 offset 4992 size 16, XMM0

The write and the read are the same storage: offset 4992, size 16, both. Nothing
is being split into lanes and nothing differs in width, so the sub-range model
would not change this case.

What is actually happening is an elided copy whose readers were not rewritten,
and the p-code shows the whole chain:

    0x3e7  movdqa %xmm2, %xmm6   ->  Copy   dst XMM6, src XMM2
    0x3eb  pxor   %xmm4, %xmm6   ->  IntXor dst XMM6, a XMM6, b XMM4

The `IntXor` renders: the body contains `xmm6_15 = xmm2_6 ^ *0xa70;`. The `Copy`
does not, and its readers still name what it defined -- `callother("userop_193",
xmm1_3, xmm6_5, xmm2_4)` reads `xmm6_5`, which the elided copy was going to
produce. Every missing version is a copy destination; every rendered one is the
result of real arithmetic.

Two explanations were tried and both are eliminated, so do not spend time on
them again:

- **Not a missing copy-root resolution in `get_expr`.** `use_info` records
  `dst -> src` for every `SSAOp::Copy`, and `resolve_copy_root_name_in_fold`
  walks the chain, so the machinery exists. Adding a fallback there changes
  nothing, and an instrumented build shows why: **`get_expr` is never called for
  these names at all.** Whatever renders `xmm6_5` into the `callother` argument
  list reaches it by another route.
- **Not a gap in SSA copy propagation.** `optimize::copy_propagation` removes
  copies and rewrites uses, and `CallOther` inputs are mapped along with every
  other operand, so a propagated copy does not leave its readers behind.

Instrumenting `var_ref` instead answers where they come from, and rules out the
copy story entirely:

    var_ref xmm6_3:  producer=Some("IntXor") def=true
    var_ref xmm6_5:  producer=Some("IntXor") def=false
    var_ref xmm6_7:  producer=Some("IntXor") def=false
    var_ref xmm6_11: producer=Some("IntXor") def=false
    var_ref xmm6_13: producer=Some("IntXor") def=false

Every one is produced by an `IntXor` -- the `pxor`, not the `movdqa`. So these
are not copy destinations at all, and the `Copy` from `movdqa` is beside the
point. The first version has a definition and the later ones do not, though the
producer is known for all of them.

`use_info` records a definition for **every** op with a `dst`, unconditionally
(`insert_definition_for_var`, around line 2662), so `info.definitions` should
hold all of them. What returns false above is the fold's `definition_for_name`,
which is a different lookup: it goes through `lookup_definition`, which takes a
resolution guard and refuses on a cycle. A `pxor` is `xmm6 = xmm6 ^ xmm4`, so
the definition of `xmm6_5` mentions `xmm6_3`, and a chain of them is exactly the
shape a cycle guard would cut.

**Start there:** find why `lookup_definition` declines for the later versions
while accepting the first. If it is the resolution guard, the question is
whether a self-referential register update should count as a cycle at all --
each version is a distinct value, so the chain terminates.

That is the dangling-read defect, and it is worth more than the lane model,
because it also explains the duplicated statements around it: the same
`callother(...)` appears once as an assignment right-hand side and again as a
bare statement, so the effect is rendered twice.

**How to look.** The inspection commands need the `a:` prefix and the debug
namespace: `a:sla.debug.json`, `a:sla.debug.info`, `a:sla.debug.arch`. Bare
`sla.json` never reaches the plugin and answers nothing, which I mistook for the
commands being broken; the plugin does say `use a:sla.debug.arch` if you invoke
`a:sla.arch`. This is the single most useful thing for questions like the above:
it prints the lifted p-code for the instruction at the seek, with varnode
offsets and sizes.

Whether a genuine lane-width case exists elsewhere is still open. It is one of
the four original defects, but this function is not an instance of it.

**Steps 3 through 7 are untouched:**

3. **Location model substrate.** Locations replace varnodes; lanes become
   sub-ranges. This is the fix for all four original defects and the point of
   the exercise. Everything so far is the substrate it needs.

   `CanonicalLocation` exists now (`r2source::contracts`) and
   `CanonicalStorageId::location()` returns it. Nothing reads it yet. I tried to
   spend it immediately on the obvious target and backed out; the reason is
   worth knowing before you try the same thing.

   `return_value_register_family` in `r2ssa::semantic` is a hardcoded table
   mapping `rax|eax|ax|al` to one family, `x0|w0` to another, and so on. It is
   spelling knowledge standing in for a location, and it only works on the
   architectures somebody listed. Replacing it with "same location" is exactly
   what the location model is for, and the machine context reaches the phi
   picker in two hops, which I threaded successfully.

   It does not finish, because the phi picker cannot reach the location that
   holds a return value. **The contract already models it**:
   `SourceConventionSlots::result_slot` is exactly the location the convention
   leaves a result in, alongside `argument_slots`. What is missing is plumbing --
   `SourceMachineContext` does not carry the convention slots, so nothing inside
   `r2ssa::semantic` can ask for them.

   Do not work around that by grouping every register phi by location and
   dropping the return-register test. It changes what the rule means: today a
   block with `rbx` and `rax` phis answers `rax` because `rbx` is not in the
   family table, and a location-only rule would see two locations and refuse.
   That trades a hack you can see for one you cannot.

   So step 3 begins by carrying the convention slots on the machine context.
   Then the picker asks whether a phi's location is the result slot's location,
   the family table deletes, and it deletes for every architecture rather than
   the eight somebody listed.
4. **Make the repair pass conditional.** Not deletable — it does real work for
   SIMD lanes — but it should not run unconditionally.
5. Guard that no facts method is shaped like a rendering decision.
6. Flag demotion, target model extraction, budget-as-ledger.
7. Collapse the `UseInfo` split: production takes one path and the tests take
   the other, so the tests are not exercising what ships.

Also open: issue #63, the dropped `setcc` on x86-64.

## How to work on this

Scripted transforms across this tree are dangerous, and I say that from
experience: seven of mine produced syntactically plausible damage, including
writing a parameter into `pub(crate)` twice, a `count=1` regex that deleted the
wrong function's binding across six files, and a receiver walk that emitted
`param.self.spelling(...)`. Two broke production and were restored from commits.

Three habits would have caught all of it:

- **Read the diff, not the error count.** The `count=1` bug sat in the tree
  while the count went *down*.
- **Scope every transform to `#[cfg(test)]` explicitly**, anchored on
  `#[cfg(test)]` immediately followed by `mod tests` — not the first
  `#[cfg(test)]` in the file, because several files carry it on individual
  fields.
- **Check `cargo build --lib` separately from `cargo test --no-run`** after
  every batch. A parse error makes rustc discard a whole `impl` block, which
  suppresses every real error inside it and looks like sudden progress.

Commit continuously. Every restore in this session came from a commit, which is
why nothing was lost.

### The dangling reads are two spellings of one location

The x86 fixture is gone, but the defect reproduces on ARM from a three-function
C file compiled at `-O2`, in `sym._xor_lanes`, which renders lines like

    r5204 = ((r5004_1 | (r5204 | r5084)) < reg_5084) * ~0;

Note `r5084` and `reg_5084` in one expression: two spellings of the storage at
register-space offset 0x5084.

Instrumenting the definition lookup settles what is happening:

    defprobe r5204_2:   hit=false  keys=["reg:5204_2"]
    defprobe reg:5204_2: hit=true  keys=["reg:5204_2"]

Same location, same SSA version, two strings. `UseInfo::definitions` is keyed by
`SSAVar::display_name()`, which spells an unnamed register `reg:5204`. The
renderer spells the same thing `r5204`, because `ssa_render_base_name` rewrites
a hex register alias to an identifier C will accept. Asking the definition table
with the rendered spelling therefore misses a definition that is sitting in it.

This is the three-way name distinction the migration is named for, showing up as
a defect: an SSA display name is a side-table key, a rendered spelling is what
goes on the page, and the two must not be confused. Nine call sites did confuse
them, in the form `definition_for_name(&self.spelling(*name))` -- take a
`SymbolId`, read the string it renders as, use that string as an SSA key.

**Do not conclude from this that the whole defect is explained.** Two separate
things are true and only the first is proven:

  * `reg:5204` **is** defined and the rendered spelling misses it.
  * `reg:5084` is **not** defined at all -- no SSA op anywhere in the function
    writes it. The definition keys for this function cover 0x5001-0x5010 and
    0x5018 byte by byte for the first four register slots, and only the 8-byte
    halves at +0x10 and +0x18 for slots four through seven. Nothing writes
    0x5080-0x508f. That is an upstream gap in the lift or in SSA construction,
    not a naming problem, and it is what the visible `r5084` reads come from.

### An identity-keyed lookup was built and then reverted

Recording the SSA display name on the `Symbol` at mint time and querying with it
(`Symbol::ssa_name`, `sym_for_var`, `definition_for_symbol`) is the right shape,
and it compiles and passes all 2417 tests. It was reverted because it is inert:
instrumenting it shows it fires only for parameters at version 0, where both the
spelling and the SSA name correctly have no definition.

    symprobe arg3 vs X3_0: byspelling=false byssa=false

The rendered-spelling lookup that actually misses (`r5204_2`) never reaches
those nine call sites -- it arrives through a caller that passes a bare `&str`
rather than a `SymbolId`, and that caller has not been found yet. Every raw-name
site inspected so far (`should_inline`, `is_simple_inline_candidate`, the
`lookup_definition` chain) correctly passes `var.display_name()`.

**Next step:** find the caller that reaches `definition_for_name` holding a
rendered spelling. A backtrace from inside the lookup, gated on the name not
being a key of `definitions`, will name it in one run. Then the identity-keyed
lookup above can be re-landed with a case that proves it.

### Both causes traced, one fixed

A backtrace from inside the lookup named the caller that asks with a rendered
spelling:

    3: definition_for_name
    4: is_simple_expr        mod.rs:3181
    6: should_inline         mod.rs:3116
    7: emitted_var_names     mod.rs:2000

`is_simple_expr` was already one of the nine converted sites. It stayed broken
because the identifier reaching it was never minted through `var_ref`:
`assignment_lhs_expr` builds the rendered spelling by hand and mints through
`name_ref`, which drops the SSA identity. The earlier "inert" reading was an
instrumentation artefact -- the probe only printed where an SSA name had been
recorded, so every site that recorded nothing was silent.

With every mint site carrying the value it renders, the lookup resolves, and
`is_simple_expr` stops treating an unresolvable name as simple. That alone made
`sym._xor_lanes` worse on the page, 27 undefined names to 36, because reads that
were always dangling stopped being hidden inside inlined expressions.

Cause two was then fixed at its origin. `RegisterFamilyInfo::member_for` looked
membership up **by name**, in a `HashMap<String, RegisterFamilyMember>`, while
the families themselves are built by union-find over overlapping storage ranges.
A varnode the architecture does not name -- spelled `reg:5084` from its offset --
therefore had no family, the alias repair pass skipped it, and its reads had no
reaching definition. Membership is a fact about storage, so it now falls back to
a sorted range index. `sym._xor_lanes` on arm64 went from 36 undefined names to
none, and the expressions built from them went with them.

### Composing tiled definitions was tried and reverted

What remains on x86 is a read wider than any single definition but covered by
several: `XMM0_Da` through `XMM0_Dd` are each defined, a 16-byte read of `XMM1`
is covered by all four, and `family_root_slice_for_range` requires one
containing definition. Its comment states the reason -- combining fragments
would invent a wide value without an explicit `Piece`.

Building that `Piece` chain (`family_root_tiles_for_range` plus a composer
emitting `Subpiece` per tile and folding them little-endian) compiles and is
architecturally the right shape, but it regressed every measurement:

    x86  sym._xor_lanes   3 -> 21 undefined,   78 -> 222 obligations
    arm64 sym._xor_lanes  0 -> 47 undefined,  105 -> 681 obligations

It fires on every read the slice resolver previously declined, not only on the
lane-wise case, and each synthesized temporary brings dangling reads of its own.
The missing constraint is that the tiles must be the lane-wise writes of one
generation of the same register. Reverted rather than left in.

### Fixture note

The original corpus lived in `/tmp` and is gone. `sym._xor_lanes` in
`/tmp/xmmfix/hashes.c` at `-O2` reproduces the whole family of defects on both
arm64 and x86-64, and is small enough to read.

### Constraining the composer fixed arm64 and left x86 unchanged

Requiring every tile to be storage the architecture declares (`declares_slot`,
checking `family_slots` for a slot of exactly that shape) removed the arm64
regression: `sym._xor_lanes` stayed at zero undefined names and 105 obligations,
so the composer no longer fires on accidental runs of adjacent definitions.

x86 did not move: still 21 undefined names and 222 obligations against 3 and 78
without the composer. Naming them says why:

    r2dec undeclared: xmm0_db_1, xmm0_da_1, xmm0_dc_1, xmm0_dd_1,
                      t80_2, t200_2, ... xmm1_3, xmm2_3, tregalias_2c0_68_1

`XMM0_DA_1` and its three siblings **do** have definitions -- the probe found
them in `UseInfo::definitions`. They are undefined *on the page*: the composer
makes the body reference them, and no assignment statement is ever emitted for
them, so C reads a name nothing wrote.

That is the standing rule that naming a value obliges declaring it, unmet. The
composer is not the defect; the emitter is. Until a value that is referenced and
not inlined gets an assignment, composing more references makes the rendering
worse, so the composer stays out of the tree.

**Next:** make emission total -- every name a rendered body mentions either has
its definition inlined at the mention or has an assignment statement. Then
re-land the constrained composer, which is already written and measured.

### The phi materialization gate is not the blocker either

`xmm1_3` on x86 is a phi destination, and `collect_definitions` records a
definition for every op with a `dst` but never for a phi, so a phi that is
referenced and not materialized is a dangling read by construction. That made
the third liveness gate in `normalize.rs` the obvious suspect: a phi becomes
mutable C state only if `render_facts.loop_carrier_for_value` certifies it.

Loosening it to materialize every non-degenerate merge -- every phi whose edges
do not all carry the same value, which is the honest definition of mutable state
-- was tried and measured. Defect counts did not move, and rendered obligations
fell everywhere:

    x86  sym._fnv1a64   111 -> 107 rendered
    x86  sym._xor_lanes  63 -> 61
    arm64 sym._fnv1a64    34 -> 32
    arm64 sym._xor_lanes  72 -> 70

Materializing more merges renders less, so the gate is not what is holding these
values back. Reverted.

### What the x86 case really needs: a value wider than 64 bits

Reading the machine code settles what the three remaining x86 names are. Before
the loop:

    pcmpeqd xmm0, xmm0        ; every lane all-ones

and inside it, `pmaxud`/`pcmpeqd` to build an `a >= b` mask and a chain of
`pxor` that the renderer already collapses correctly into

    *arg0 = xmm1_3 ^ xmm0 ^ arg1[0];

`xmm0` is a 16-byte read covered by the four lane definitions `XMM0_Da` through
`XMM0_Dd`, and each lane folds to a constant: `optimize.rs` already reduces
`IntEqual` with identical operands to a constant, so `pcmpeqd xmm0, xmm0` is
constant-folded per lane.

So the composer is the right instrument for this read -- and it cannot finish
the job, because a composed 16-byte constant has nowhere to live. `const_value`
returns `Option<u64>` and `make_const` takes a `u64`; the whole constant model
is 64 bits wide. Four folded lanes cannot be joined into the value the machine
actually has.

This is a real ceiling on what the location model can do for SIMD, and it is
worth stating plainly rather than working around: a register file with 16-byte
registers needs a value model that can hold 16 bytes. Until then, whole-register
reads of vector registers will resolve to a name with no expression behind it,
however good the family and location machinery gets.

**Two ways forward, and they are not equivalent.** Widening the constant model
fixes the class. Special-casing the all-ones idiom fixes this binary and leaves
the class open; it is the kind of thing that should not go in.

### Steps 5 and 7 are done; step 4's premise does not hold

**Step 7, the `UseInfo` split, is collapsed.** `UseInfoAnalysisMode` selected
which passes ran inside one function, so the two consumers read as one analysis
with parts switched off. They are not the same analysis: coalescing and
formatted definitions decide how a value is *spelled*, which only a renderer
needs. `analyze_value_facts` now yields the scratch, `name_values_for_rendering`
adds the naming decisions, `seal_value_facts` closes either one, and the enum is
gone. Rendering is byte-identical on both fixtures.

**Step 5, the facts guard, is in the dylint crate** as
`FACTS_METHOD_SHAPED_LIKE_A_RENDERING_DECISION`. It warns when a `*Facts` type
declares a method whose name starts with `should_`, `prefers_`, `wants_`,
`emit_`, `suppress_`, `elide_` or `inline_`. The tree is clean today -- the
survey found no violations -- so the lint is preventative, and it was verified by
planting `should_probe_the_guard` on `FunctionControlFacts` and watching it fire.

**Step 4 is not what it says.** "Make the repair pass conditional" assumes the
repair exists for width mismatches, so a function that never touches a register
family at two storage shapes could skip both the repair and the dataflow fixpoint
that feeds it. That precondition was written, and one test refuses it:

    register_alias_maximal_copy_retains_the_written_ssa_definition

It writes `RAX` at version 2 and then reads `RAX` at version 0 -- one family, one
shape, no width mismatch anywhere -- and expects the pass to rewrite the read to
the reaching definition. The pass reconciles *versions* as well as widths.

So the condition cannot be a syntactic property of the storage shapes; it is a
statement about reaching definitions, which is exactly the dataflow the skip was
meant to avoid. Any cheap sound condition strong enough to keep that test
passing is also weak enough to almost never fire. Reverted.

The useful reframing: the version reconciliation is there because SSA renaming
treats overlapping register names as independent variables. Fix that at
construction and the pass narrows to genuine width repair -- and *then* it is
conditional, on the property step 4 assumed it already had.

### Step 6: two of three landed, and what budget-as-ledger actually costs

**Target model extraction.** Signature inference chose its argument and result
registers with `ptr_bits == 64`, which is System V AMD64 for every 64-bit target,
so arm64 was told to look for parameters in `rdi`. The lifter already states the
convention; `SourceMachineContext` now answers `argument_register_names()` and
`register_name()`, and a probe confirms it holds `x0..x7` on arm64 and
`rdi..r9` on x86-64. `VariableRecovery::new` carried the same table inferred the
same way and had no production caller, so it is gone.

**Flag demotion.** The ADR's rule -- a flag is a one-byte register no wider
register contains -- is now computed from the register file rather than listed.
Measured, the list it replaces was wrong in both directions: it missed
`shift_carry` on arm64 and `c0`-`c3` on x86, and carried `nf` and `vf` that this
arm64 specification does not use. It also held both architectures' spellings at
once, and one test depended on exactly that, reading arm64 condition codes from
an x86-64 context.

One caller keeps the list. `is_call_arg_transient_name` tests for a flag beside
`starts_with("eax")`, `"rax"`, `"ecx"` and a dozen more x86 spellings; threading
the target into it opens a nine-function cascade, and converting the flag line
alone would leave the predicate no more arch-neutral than it is. That whole
predicate is one job.

**Budget-as-ledger is not a bookkeeping change.** `RefusalReason::BudgetExhausted`
exists in the ledger and is constructed nowhere -- a declared bucket nothing
fills. The reason is structural: a phase that runs out of budget returns
`DecompileExecutionStop`, `render_engine_decompile_request` returns
`Result<Rendered, Stop>`, and the engine discards the output and refuses the
whole function. There is no partial rendering to attribute obligations against,
and no ledger at all, because the ledger is built during the render that was
thrown away.

The complexity ceiling is the same shape and is easy to measure. A
straight-line function of 120 statements:

    /* r2dec fallback: skipped decompilation for fcn_188
       (decompile complexity limit exceeded: blocks=1/200 ops=1634/512) */

One basic block, 1634 lifted ops, nothing rendered. This is the case the ADR
means by "refuses ordinary code".

Deleting the ceiling is not the fix on its own. Cost is otherwise bounded only by
a deadline, and the deadline is optional -- `payload.timeout_us` may be zero, in
which case nothing bounds the work. So the honest sequence is: make rendering
able to stop and keep what it has, attribute the undischarged obligations as
`Refused { layer, BudgetExhausted }`, and only then delete the ceiling. The first
of those changes `render_engine_decompile_request`'s contract from
`Result<Rendered, Stop>` to a rendering plus a stop, which reaches every caller.

That is a design decision about the render boundary, not a mechanical change, and
it is the next thing this work needs.

### The loop-carrier defect has moved, and the three gates no longer explain it

The symptom is unchanged. `sym._fnv1a64` at `-O2` on arm64 still renders

    do {
        int64_t x0 = (int64_t)(((uint32_t)t2b380 ^ (uint32_t)*arg0) * 0x1b3);
    } while (arg1 != 1);
    return 0x739d0383;

with a dead body, a pointer that never advances, and a return of `0x739d0383` --
the low half of the FNV offset basis, which is the accumulator's value *entering*
the loop.

The standing diagnosis blamed three liveness gates, the first being
`loop_carrier_facts` discarding header phis with no recorded readers. Instrumenting
all three says that is no longer true. The header carries nineteen phis:

    carrier header=f4 phi=CY_1        uses=0  liveout=false
    carrier header=f4 phi=tmp:2b380_1 uses=0  liveout=false
    ... fourteen flags and Sleigh temporaries, all uses=0 ...
    carrier header=f4 phi=X0_3        uses=1  liveout=false
    carrier header=f4 phi=X1_1        uses=3  liveout=false
    carrier header=f4 phi=X8_2        uses=2  liveout=false

The fourteen flag and temporary merges die at the first gate for having no
readers, which is what should happen to them, and the accumulator survives. It
survives the other two as well:

    gate phi=X0_3 value=Some(ValueId(62)) certified=true
    gate phi=X1_1 value=Some(ValueId(64)) certified=true
    gate phi=X8_2 value=Some(ValueId(69)) certified=true

So the carriers are certified and materialised into edge assignments, and the
twenty-four-phi header the earlier work measured is now nineteen with five live.
Liveness is not what is losing the loop.

**Where to look instead.** The returned constant is the entry value of the
accumulator, so something at the render boundary resolves the merged value to
the value entering the loop rather than to the merge. That is the same shape as
the return-value picker worked on earlier in this branch, and it is downstream of
everything the three gates control. Instrument the return operand's resolution
before touching liveness again.

### The loop carrier is lost at the exit merge, not at any liveness gate

Instrumenting the return operand says what is actually rendered:

    retval block=108 idx=1
      raw=(IntLit(899) & IntLit(65535)) | IntLit(1939668992)
      certified=Some(ValueId(91))

`(899 & 0xffff) | 0x739d0000` is `0x739d0383`, the low half of the FNV offset
basis, assembled from the `movz`/`movk` pair that initialises the hash **before**
the loop. So the certified return value is `ValueId(91)`, the exit phi `X0_5`,
and the expression rendered for it is that phi's entry-edge source.

Two fixes were built for this and both are out of the tree.

**Refusing to inline a definition of a multiply-assigned name.** Materialisation
gives a carrier two edge assignments under one name, so `rebuild_definitions`
records one and silently overwrites the other. Recording which names were
assigned twice works and finds exactly the right ones:

    multiprobe ["X0_3", "X1_1", "X8_2"]

Those are the three certified carriers. It changed no output, because the return
resolves `X0_5`, a different phi, and not through that path.

**Refusing to resolve a non-degenerate phi to one of its sources.** A merge of
two different values is not either of them, and answering with a source is
exactly how the entry value reaches the return. Refusing it removes the wrong
constant and puts nothing in its place:

    return 0x739d0383;   ->   return pc;

with the undefined-name count going from one to two. So the wrong answer was the
only answer: nothing connects the exit phi `X0_5` to `x0`, the variable that
materialising the header phi `X0_3` created, even though both are certified
carriers of the same storage.

**That connection is the defect.** The exit merge of a materialised carrier must
resolve to the carrier's variable. Neither refusing the inline nor blocking the
overwrite helps until it does, which is why both were reverted rather than left
in as partial fixes.

### Two reasons the exit merge cannot reach the carrier

Connecting the exit merge to the materialised carrier was tried, on the argument
that materialising the header phi assigns the carrier on the entry edge as well
as the back edge, so the carrier holds the right value however control arrived
and is therefore exactly what the exit merge means. The argument is sound. It
does not apply, for two separate reasons, and instrumenting says both.

**The exit merge does not mention the carrier.**

    phiprobe name=X0_5 sources=["X0_2", "X0_4"]

The materialised carrier is `X0_3`. The exit phi merges `X0_2` and `X0_4`, so no
source of it names the carrier and no rule phrased over sources can find it. The
relation between them is that all four are the same storage, which is the
location model's job and not something the name graph can answer.

**A fact added to `UseInfo` does not reach the fold.** The same probe prints

    multi={}

while the analysis that computed it printed

    multiprobe ["X0_3", "X1_1", "X8_2"]

The fold reads `state.analysis_ctx.semantic()`, and that `UseInfo` is not the one
`analyze_value_facts` returned: `prepared_semantic.rs` builds a second analysis
and copies selected fields across, field by field. Any fact added to `UseInfo`
that nobody adds to that merge is silently absent downstream, which is how a set
that was correct where it was computed reads as empty where it is used.

This is the same shape as the symbol-table defect this branch already fixed,
where three passes each held their own table and `mem::take` left the fold
reading a fourth. One table, shared by `Rc`, fixed that. `UseInfo` still has the
older shape, and **it should be the same fix**: one instance per rendered
function, shared, rather than several merged by hand. Until then, adding a fact
to `UseInfo` and reading it in the fold does not work, and fails quietly.

## There are two UseInfo builders, and production reads the smaller one

Chasing why a fact added to `UseInfo` never reached the fold found the reason,
and it is bigger than the fact.

`FoldingContext::analyze_blocks_with_control` contains two complete analyses
separated by an early return:

    if let Some(prepared) = self.inputs.prepared_ssa {
        ...
        self.state.analysis_ctx = analysis::build_prepared_runtime_facts_with_control(...)?;
        return Ok(());
    }

    // Explicit pass order:
    // 1) UseInfo
    // 2) FlagInfo + StackInfo
    let mut use_info = analysis::UseInfo::analyze_with_control(...)?;

Both branches produce a `DecompilerFacts`. They share no code. `prepared_semantic.rs`
builds one with `seed_prepared_*`, `collect_prepared_runtime_facts`,
`populate_prepared_*` and `populate_prepared_render_definitions`; `use_info.rs`
builds the other with `count_uses_and_conditions`, `collect_definitions`,
`refresh_semantic_values`, `rebuild_definitions`, `coalesce_variables` and
`build_formatted_defs`.

**Production always takes the first branch.** Every `prepared_ssa: None` in the
tree is inside `#[cfg(test)]`, so the second pass order runs only under test.

    prepared_semantic.rs   5329 lines   what production reads
    use_info.rs           13089 lines   what the tests read

`use_info.rs` is not dead: `overlay_local_struct_semantics` calls it from inside
the prepared path, so in production the whole thirteen-thousand-line analysis
runs and then two of its fields, `semantic_values` and `ptr_members`, are copied
out and the rest is dropped. That is why adding `multiply_assigned` to
`rebuild_definitions` computed the right answer -- `multiprobe ["X0_3", "X1_1",
"X8_2"]` -- and the fold still read an empty set.

### Why this matters more than the defects above it

This is the parallel pipeline the working agreement forbids, at the largest
scale in the codebase, and it has three consequences that explain much of this
branch:

  * A change to `use_info.rs` can be correct, tested, and invisible in `pdd`.
    Several measurements in this document read as "inert" and may instead have
    been landing in the branch production does not read.
  * The test suite exercises a pass order that does not ship. Step 7 named this
    at the `UseInfoAnalysisMode` seam and fixed it there; the same defect exists
    one level up and is much larger.
  * Any fact the renderer needs must be added twice, and nothing checks that it
    was.

**The fix is the one this branch already proved.** The symbol table had the same
shape -- passes each holding their own copy, the fold reading one nothing had
written -- and one shared table fixed it. `UseInfo` needs one builder, not two,
and the prepared path is the one to keep because it is the one that ships. That
makes the work: move whatever `use_info.rs` computes that production needs into
the prepared builder, repoint the tests, and delete the rest.

That is a large deletion rather than a large addition, which is the right shape,
but it is not a change to start without agreeing the direction first.

## The loop-carrier fix, scoped from measurement

The exit merge and the carrier are two different phis over the same storage, and
the carrier is already correct at the merge. Instrumented on `sym._fnv1a64`:

    block=f4   X0_3 <- [f0:X0_2, f4:X0_4]     carrier, materialised
    block=108  X0_5 <- [e0:X0_2, f4:X0_4]     exit merge
    init carrier=X0_3 src=X0_2 into block=e0

`X0_5` merges "the loop never ran", carrying the entry value `X0_2`, with "the
loop ran", carrying the update `X0_4`. Its two sources are exactly the carrier's
entry and update values. The carrier's initialiser is placed in `e0`, which
dominates block `108`, so the carrier variable holds `X0_2` on the bypass path
and the updated value on the loop path: it is correct on both predecessors of
the merge. **`X0_5` is `X0_3` after the loop.**

Today `X0_5` resolves through its own sources and takes the entry constant,
which is where `return 0x739d0383` comes from -- the low half of the FNV offset
basis.

An earlier attempt failed for one reason worth writing down: it looked for the
carrier *among the merge's sources*, and the carrier is a third name that is not
either of them. Searching the sources cannot find it; the carrier fact must be
consulted.

**Scope.** One function in `crates/r2dec/src/normalize.rs`. After carriers are
materialised, a phi whose source set is contained in a carrier's
`entries` union `updates`, and which that carrier's initialiser dominates,
resolves to the carrier's variable. `entries`, `updates` and the initialiser
block are already on `CertifiedEntity::LoopCarrier`; nothing new is computed. No
contract change and no other crate.

The dominance test must be against the *merge's* block, not the loop's entries.
Using the loop's own dominance fact is the subtly wrong version that passes this
fixture and is wrong elsewhere.

### It is necessary but not sufficient on x86

`sum32`, the simplest accumulator loop there is, renders on arm64 exactly like
`fnv1a64`:

    do { x0 += 4; } while (arg1 != 1);
    return 0;

the pointer advances, the accumulator is absent, and `0` is the accumulator's
value before the loop. Same shape, second function, so the fix applies.

x86-64 is a layer worse:

    do { rcx++; rax = EAX_3; } while (arg1 != arg3);
    return rip_1;

The accumulator survives as `rax = EAX_3`, which is the 32/64 sub-register
split, and the return is the instruction pointer rather than a value. So the
merge fix lands the arm64 accumulator loops and `sym._fnv1a64`, and the x86 ones
need it **and** the register-width layer before they render. An earlier claim in
this document that the fix covers "every hash function at -O1 and above" is too
strong and should be read as the arm64 half.

### The exit-merge fix was built three ways and none of them landed

The scope above is right about what the merge means and wrong about what it
takes to render. Three attempts, each of which got further and exposed the next
layer.

**Rewriting the SSA.** A pass in `normalize.rs` that drops the exit merge and
inserts `Copy { dst: merge, src: carrier }` at the top of the block. It fires
exactly as intended:

    merge block=108 X0_5 -> carrier X0_3
    merge block=108 X1_3 -> carrier X1_1
    merge block=108 X8_4 -> carrier X8_2

and it breaks the certificates. Inserting an op shifts every op index in that
block, and the certified return is keyed by `(block_addr, op_idx)`, so the
lookup that read `Some(ValueId(91))` now reads `None`. Materialisation gets away
with inserting because it inserts into *predecessor* blocks, never into the block
holding the return. Any fix that edits a block containing a certified site has
to renumber the certificates, which is a much larger change than it looks.

**Aliasing the merge to the carrier.** `carrier_name_aliases` already maps every
member of a carrier to one name, so the exit merge can simply join that map:

    alias merge X0_5 -> x0
    alias merge X8_4 -> x8

No SSA edit, no index shift, and the mechanism is the one already there. It
changes nothing, because the return never *names* the value: it resolves it, and
resolution does not consult the alias map.

**Declining to resolve an aliased carrier.** If a phi carries a carrier alias it
is mutable state and must be read by name, so resolution should decline and let
the caller reference it. That produces

    return pc;

which is the third layer: when resolution declines, the return path falls back
to the branch target rather than to the value's name. The return resolver can
say "the answer is this expression" or fall back, and has no way to say "the
answer is this variable".

**So the blocker is the return resolver, not the merge.** The merge is correctly
understood and the alias mechanism reaches it; what is missing is a return path
that can answer with a name. That is where the next attempt should start, and it
should start by reading `get_return_expr` and `resolve_return_target_expr`
rather than by touching normalisation again.

All three attempts were reverted. Two were inert and one was worse, and the
measurements above are the whole value of the exercise.

### The carrier return is fixed for full-width carriers only

`sym._fnv1a64` renders `return x0` and updates the carrier in the loop body. The
fix is in two halves: `carrier_name_aliases` counts the post-loop merge as a
member of the carrier, and `merged_return_register_candidate_for_block` asks for
the variable rather than resolving the merge through its sources.

`sum32` still answers `0`, and it is not the same defect. Its machine code says
why:

    mov  w8, 0          accumulator is w8, 32 bits
    add  w8, w9, w8     the update writes W8
    mov  x0, x8         the exit copies X8, 64 bits, into the return register

The carrier phi is on `X8` while every update writes `W8`, so the update is not
among the carrier's certified values and the loop body renders without it. That
is the sub-register width layer, not the return path -- the same layer x86 needs,
reached on arm64 whenever the accumulator is a `w` register.

So the rule is: this fix completes the carrier return **for carriers that are
full width throughout**. A carrier written at a narrower width than its phi needs
the width layer first, and that is the location model rather than anything in the
return resolver.

### sum32 is a missing statement, not a wrong return

The width theory for `sum32` is wrong. Its carrier is certified at full width:

    member phi=X8_2 entries=["X8_1"] updates=["X8_3"]

so the accumulator is tracked, entry and update both. And the return is already a
constant before the return path sees it:

    retval block=90 raw=IntLit(0)

Four resolution paths were guarded against answering with a carrier's initialiser
-- `get_return_expr`, `merged_return_register_candidate_for_block`, the inline
gate in `should_inline`, and the top of `get_expr_with_depth` -- and none of them
changed the answer, so none of them is where the `0` comes from. All four were
reverted.

Reading the rendered body says why:

    do { x0 += 4; } while (arg1 != 1);

`x0` is the pointer. The accumulator's update, `add w8, w9, w8`, is not emitted at
all. So `return 0` is not a resolver preferring the entry value; it is the honest
answer for a body in which nothing ever writes the accumulator. **The defect is a
dropped statement, and the return is downstream of it.**

The next measurement is therefore why the op defining `X8_3` produces no
statement -- `is_dead`, `should_inline`, or the consumed-by-call set in
`emitted_var_names` -- and not anything in the return path. `sym._fnv1a64`
differs because its update *is* emitted, which is why fixing its return was
enough there.

### sum32, traced to one line, still unfixed

The missing update is a consequence, not the cause. Instrumenting statement
emission shows every accumulator op does produce a statement:

    emit X8_1 stmt=true dead=false uses=Some(3)
    emit X8_2 stmt=true dead=false uses=Some(1)
    emit X8_3 stmt=true dead=false uses=Some(2)

They disappear afterwards in `prune_unused_pure_locals`, which drops a local
nothing reads -- and nothing reads `x8` precisely because the return already says
`0`. So the return is the cause and the empty body is the effect, which is the
opposite of what the previous entry concluded.

The producer is one line. `last_ret_value` is set at exactly one site for this
function, the `Copy` for `mov x0, x8`, and because the *source* is not a return
register it takes `tracked_return_source_expr`, whose first act is `get_expr`:

    src X8_4 direct=IntLit(0) semantic=false definition=None alias=Some("x8")

That is the whole defect in one line. `X8_4` has **no** name-keyed semantic value
and **no** name-keyed definition, and it does carry the carrier alias `x8`, and
`get_expr` still answers `IntLit(0)`. So the zero arrives through a *value*-keyed
path -- `definitions_by_value` or `semantic_values_by_value` -- which every guard
tried so far, all name-keyed, cannot see.

**Six attempts, all reverted**, and their value is in ruling paths out:
`get_return_expr`, `merged_return_register_candidate_for_block`, `should_inline`,
the top of `get_expr_with_depth` keyed on multiply-assignment, and the same
keyed on the alias map. The last one is instructive: it fires, and it makes
`sym._fnv1a64` worse by leaking `tregalias_f4_4_0` into the loop body, because
returning the name for *every* aliased value is too strong -- the alias map holds
stack and parameter aliases too.

**Next probe, and it is one line of instrumentation:** print
`definitions_by_value` and `semantic_values_by_value` for `X8_4`'s value id at
the same site. One of the two holds the zero, and that is where the carrier guard
belongs -- keyed by value, and restricted to carrier aliases rather than the
whole alias map.

### Correction: there are two `get_expr`, and the fold calls the other one

Several attempts above guarded `LowerCtx::get_expr` in `analysis/lower.rs:185`.
The fold does not call it. `FoldingContext::get_expr` is a different function of
about 130 lines at `fold/op_lower/mod.rs:3206`, with roughly a dozen return
paths of its own. Any reasoning about "where `get_expr` answers" in the entries
above refers to the wrong function.

What the probes establish about `sum32`, all confirmed:

  * `X8_4` is the **exit merge**, the same shape as `X0_5` in `sym._fnv1a64`.
  * It is in `carrier_aliases`, so the carrier machinery does reach it.
  * It is not a constant, has no name-keyed or value-keyed definition, no
    name-keyed or value-keyed semantic value, and no forwarded value:

        val X8_4 const=false bits=None direct=IntLit(0)
            def_by_value=None sem_by_value=false forwarded=false

  * Guarding phi-source resolution on `carrier_aliases` -- the narrow map, not
    the general one -- leaves `sym._fnv1a64` correct and does not change
    `sum32`, so that is not its path either.

So the `IntLit(0)` is produced by one of the other return paths in
`FoldingContext::get_expr`, and every map it could plausibly read has been shown
empty for this value. **The next step is to bisect that one function**: print a
marker at each of its return points and run `sum32`. That names the branch in a
single run, which is what should have been done before any of the seven attempts.

`prune_unused_pure_locals` then removes the accumulator's statements because the
constant return leaves nothing reading `x8`, so the empty loop body follows from
this and is not a separate defect.

### Bisecting `get_expr` shows the defect is that nothing owns the answer

Marking all fourteen return points of `FoldingContext::get_expr` and running
`sum32` names the branch in one run, which is what the seven earlier attempts
should have started with:

    getexpr site 9  X8_4 -> IntLit(0)

Site 9 replaces a name judged low signal with its definition, and a carrier's
name is judged low signal because it is spelled like a register. Excluding
carrier aliases there moves the answer rather than fixing it:

    getexpr site 12 X8_4 -> IntLit(0)

Site 12 prefers a semantic value, which `render_semantic_value_by_name` computes
by resolving the merge through its sources. Guarding that too -- on
`carrier_aliases`, the narrow map -- makes `get_expr` stop being called for
`X8_4` at all, and `sum32` still returns `0`, because the value is now answered
somewhere else again.

**That is the finding.** At least three independent paths inside one function,
and more outside it, will each answer for a value, and closing one hands the
question to the next. There is no single authority for "what does this value
render as", so a carrier -- which has several defensible answers, one per path it
took -- gets whichever path is consulted first.

`sym._fnv1a64` was fixable because its return went through
`merged_return_register_candidate_for_block`, one specific site, and that site
could be told to ask for the variable. `sum32` reaches the same question through
`tracked_return_source_expr` -> `get_expr`, and there the question has no owner.

**So the next step is not another guard.** It is to give the fold one place that
answers "the rendering of this value", with the carrier rule stated once inside
it, and to route the paths that currently answer independently through it. That
is the same shape as the two defects this branch has already fixed -- one symbol
table rather than four, one `UseInfo` builder rather than two -- at the level of
expressions rather than names or facts.

All guards from this exercise were reverted. Eight attempts, and the eighth is
the one that says the seven before it were the wrong shape.

### The size of the single authority

Counting what currently answers "what does this value render as":

    get_expr                       4 definitions   103 calls
    var_ref                        2               226
    render_value_ref               2                20
    expr_for_ssa_name              2                17
    get_return_expr                1                15
    tracked_return_source_expr     1                 4
    render_semantic_value_by_name  2                26
    lookup_definition              4                47
    best_visible_definition        4                21
    resolve_expr_from_phi_sources  1                 8

`var_ref` answers a different question -- what a value is *called* -- and is not
part of this. The rest are nine resolvers with nineteen definitions and about two
hundred and sixty call sites, all answering the same question with their own
precedence, which is why closing one hands the question to the next.

Collapsing all of them is the same shape as the two collapses this branch has
already done, and roughly the same size as the `UseInfo` one.

**A smaller slice does what the loop carrier needs.** The four return-value
resolvers -- `get_return_expr`, `tracked_return_source_expr`,
`merged_return_register_candidate_for_block` and the `last_ret_value` sites --
are about forty call sites, and they are the only ones the carrier defect
reaches. Routing those four through one function that states the carrier rule
once would fix `sum32` without touching the other two hundred, and it would be a
step toward the full collapse rather than a special case, because the one
function is where the rest would move later.

### The slice was the same mistake in miniature

Routing the four return resolvers through one function was built. The authority
is reached and it answers correctly:

    auth X8_4 carrier=true

`tracked_return_source_expr` returns the carrier reference, and the rendered
return is still `0`, because `resolve_return_target_expr` takes that reference
and resolves it again, and `preferred_return_candidate` resolves whatever
survives that. Guarding those in turn is the same walk as guarding
`get_expr`'s fourteen return points, with fewer steps.

**So the shape of the fix is not "one place that answers" bolted beside the
existing resolvers.** It is that resolution must be final: an expression a
resolver has already chosen is not re-opened by the next one. Today every
resolver treats its input as a starting point and looks for something it prefers,
so an answer only survives if no later resolver has an opinion -- and for a
carrier, every one of them does, because a carrier genuinely has several values.

That is a contract, not a special case: **a rendered expression is an answer, not
a candidate.** Stating it means the return resolvers stop taking each other's
output as raw material, which is a change to how they compose rather than a rule
about carriers. `sym._fnv1a64` works today only because its answer happens to be
produced by the last resolver in its chain rather than the first.

Ten attempts on this defect are recorded above. The useful residue is this
paragraph and the bisection method that produced it; every guard was reverted.

### The remaining cost is diffuse, and that is the finding

Three cost defects were removed by profiling: the exponential path count, the
per-name block rescan, and the per-question copying of every known name. After
them the profile of an 18614-op function has no peak:

    11 ssa_name_parts        8 should_inline       7 is_dead
     5 find_ssa_name_for_rendered_alias            5 emitted_var_names
     9 r2types::register_alias_names               5 SSAVar::display_name

Fifty samples spread across a dozen functions, none of which dominates. The
superlinearity that remains -- doubling the function still costs about 2.6x --
is not one wrong data structure but the accumulated cost of building a `String`
for a map key on nearly every query, in functions each of which is individually
cheap.

One clear algorithmic waste was fixed and reverted for honesty:
`find_ssa_name_for_rendered_alias` sorts its candidates and then takes only the
first, and the comparator recomputes both operands' preference keys on every
comparison, where each key renders a semantic value. Selecting instead of
sorting is one key per candidate rather than one per comparison, and it measures
7.6s to 7.1s and 19.9s to 19.5s, which is noise. It is strictly less work and it
is not the bottleneck, so it is not in the tree.

**So the next cost work is not another hotspot hunt.** It is `display_name()`:
it allocates, it is the key of most of these maps, and it is called from every
predicate in the profile above. Removing that allocation -- interning the name,
or keying the maps by `ValueId`, which the graph already assigns -- is the change
the profile points to, and it is wide rather than deep.

Two further local changes were measured on this thread and rejected. Selecting
rather than sorting in `find_ssa_name_for_rendered_alias` is 7.6s to 7.1s and
19.9s to 19.5s. Skipping `to_uppercase` in `display_name` when the name is
already uppercase -- which is nearly always, and which allocates a second string
only to discover it -- is 7.6s to 7.6s and 19.9s to 20.0s.

Three local changes, three noise-level results. The cost is genuinely spread
across the map lookups themselves rather than sitting in any one of them, so the
only change that will move it is keying those maps by `ValueId` instead of by a
freshly built `String`. The graph already assigns the identifiers; what is
missing is that the fold's tables do not use them.

### The remaining cost is slower calls, not more of them

Four local changes measured at noise, so the hypothesis that any one allocation
mattered is wrong. Counting the calls instead of sampling the stacks says what is
actually happening:

    n=600    is_dead=18625   get_expr=2329
    n=1200   is_dead=37825   get_expr=4729

Both counts double exactly when the function doubles -- 2.03x -- while wall clock
goes from 7.6s to 19.9s, which is 2.6x. **The calls are linear and each one gets
slower.**

That is the signature of a `String`-keyed map growing: hashing costs the length
of the key, the tables grow with the function, and locality gets worse. It is not
the `format!` in `display_name`, which is why removing an allocation from it and
from the flag test changed nothing measurable.

So keying the fold's tables by `ValueId` is not a micro-optimisation, it is the
whole remaining superlinearity, and the graph already assigns the identifiers.
`use_counts_by_value` and `definitions_by_value` exist beside their name-keyed
twins; the fold reads the twins.

Measure it the same way afterwards: the call counts should stay linear and the
wall clock should follow them.

### Correction: keying by `ValueId` as described would not help

The recommendation in the previous entry was tested before being handed on, and
it is wrong. Asking `is_dead` for its use count by identifier instead of by
spelling measures 7.6s to 7.4s and 19.9s to 19.9s, which is noise, and reading
`exact_value_id_for_var` says why:

    if self.ambiguous_value_vars.contains(var) { ... }   hashes the whole SSAVar
    let value_id = self.value_ids_by_var.get(var)         hashes it again
    ...filter(|stored| *stored == var)                    and compares the string

Obtaining the identifier costs two `SSAVar` hashes and a string comparison, so it
is strictly more work than the one string lookup it replaces. The identifiers are
only cheap to *use*; they are not cheap to *obtain* from a var.

So the change worth making is not "key the tables by `ValueId`" but "carry the
identifier on the value", so that no lookup is needed to find it. That is a
change to `SSAVar` or to how the fold walks ops, not to the tables, and it is a
different and larger piece of work than the previous entry claimed.

Five local cost changes have now been measured and rejected: the alias sort, the
uppercase test in `display_name`, the flag base string, the borrowed flag base,
and this one. The call counts stay linear across all of them. Whatever makes each
call slower has not been found, and the next attempt should measure a single
predicate's cost directly -- time `is_dead` alone across the two sizes -- rather
than infer it from a sample or from a structural argument.

## The remaining cost is one predicate, and sampling never showed it

Timing the phases rather than sampling the stacks finds it immediately. On the
18614-op function, wall clock about 19.9s:

    phase normalize                   12ms
    phase recover                     12ms
    phase analyze_blocks             159ms
    phase analyze_function_structure   2ms
    phase emitted_var_names        12856ms
    phase primary_body              2408ms
    phase prune_locals                 0ms
    phase codegen                      1ms

and inside that one phase:

    should_inline calls=14184 total_ms=12714

Fourteen thousand calls costing nine hundred microseconds each, which is
sixty-four per cent of the whole decompile. `is_dead`, which the sampling profile
put at the top three times, is 21ms.

**Sampling was misleading throughout.** It reported the functions on the stack
most often, which were the small predicates called from everywhere, and never
surfaced the one whose individual calls are enormous. Five local changes were
measured and rejected on its advice -- the alias sort, two `display_name`
allocations, the flag base string, and keying a lookup by `ValueId` -- and none
of them touched anything that mattered. Two measurements found it: counting calls
separated "more work" from "slower work", and timing named phases found the
phase.

`should_inline` returns early when a value has no uses or more than three, so
the expensive path is only taken for values with one to three readers, and it
runs `call_result_source_for_ssa_name`, then `local_post_call_source_for_ssa_name`,
then `source_call_for_visible_owner_name`, then
`stable_owned_call_result_name_for_source`. **The next measurement is which of
those four costs the nine hundred microseconds**, timed the same way, and it
should be done before anything is changed.

Also worth knowing: `emitted_var_names` runs once but asks `should_inline` of
every operation, and the fold then asks the same question again while lowering.
Whatever the fix to the predicate, the answer being computed twice is a second
thing to look at.

### What the cost work ended at

Four cost defects were found and fixed, each by measurement rather than by
reading:

  * the exponential path count in `expression_dependency_path_count`
  * the per-name block rescan in `raw_local_post_call_source_for_ssa_name_in_block`
  * the per-question copy of every known name in `known_named_values`
  * the per-question **scan** of every known name behind
    `call_result_source_for_ssa_name`, which was 64 per cent of a large decompile

The op ceiling moved with the measurements each time, 512 to 4096 to 8192 to
16384, and never ahead of them. At the last size measured, 37000 ops renders
30968 of its 30969 obligations in 17.3s, and 18614 ops renders 15368 of 15369 in
about 6s, so the ceiling now refuses only what is genuinely slow rather than what
was slow before the defects were removed.

**On method, which cost more than the fixes.** Sampling profiles named `is_dead`
three times; it is 21ms of a twenty second run. Five changes were built and
reverted on that advice. What worked was cheaper and duller:

  1. count the calls, to separate "more work" from "slower work"
  2. time named phases, to find the phase
  3. time the steps inside it, to find the line

Each of those is one run. Reach for them before a sampler, which answers where
the code is rather than where the time is, and is actively misleading for a
predicate whose calls are rare on the stack and enormous individually.

### Withdrawn: arm64 call rendering is not empty

The entry below recorded a defect that does not exist, and it is left here
because the mistake is instructive. `radare2` split the test function in two --
`fcn.00000000` is thirty-six bytes ending at `eor w2, w19, w20`, before either
`bl` -- so decompiling address zero renders a prologue, correctly, and I read the
short output as calls being dropped. Always check the function boundary before
believing a short rendering.

Decompiling the half that holds the calls shows them rendering:

    uint64_t sub_24_result = sub_24();
    uint64_t t12280_3 = sub_24_result + w19
        + sub_30(sub_24_result + w20, W1, W2, W3, W4, W5, W6, W7);

**There is a real defect here, and it is a different one.** `sub_30` is handed
eight arguments where the call passes one, and they are exactly `W1` through
`W7`: the AAPCS64 argument registers, emitted as a list rather than intersected
against what the function actually sets. `SourceConventionSlots` says in its own
documentation that this is what its consumers must do -- "a consumer recovering
parameters from machine code intersects this candidate list against what the
function reads before writing" -- and the callsite path does not. The ledger
agrees that something is wrong: 81 obligations, 25 rendered, **50 refused**, and
a residual saying `uncertified callsite arguments at 0x24:49`.

That is the thread worth pulling, and it is much narrower than "call rendering".

### The withdrawn entry, kept for the method

Three calls and three arguments each:

    int driver(int n, int m) {
        int a = work(n + 1, m * 2, n ^ m);
        int b = other(a + n);
        return a + b + m;
    }

renders on arm64 as

    void sub_0(int64_t arg0, int64_t arg1) {
        t7b80_2[1] = x30;
    }

with 12 of 18 obligations rendered and 6 unaccounted. Both calls, all four
arguments and the return are gone.

`is_call_arg_transient_name` was the suspect, because it decides whether a call
argument's expression is low signal and it ends with

        || lower.starts_with('x')
        || lower.starts_with('w')

which on arm64 matches **every** register. Removing those two clauses changes the
rendering not at all, so it is not the cause here. The predicate is still wrong
-- it is a list of x86 caller-saved spellings with an arm64 catch-all bolted on,
and the target model already knows which registers are caller-saved -- but fixing
it is a tidiness change rather than this defect's fix.

**This is a new thread and it is a large one:** call rendering on arm64, measured
on the smallest function that shows it. It is not the loop carrier, not the
resolver contract and not the cost work; it should be measured from scratch, and
`calls.c` above is the fixture to do it with.

### Where the eight arguments come from, and where they do not

`certified_call_args_for_site` renders `cert.canonical_argument_values()`,
truncated by the call's arity when that is known. `sub_30` is an extern with no
prototype, so nothing truncates and every candidate renders.

The obvious suspect is that the candidates are the convention's whole slot list,
and that is **not** what is happening. `collect_call_argument_slots` in
`r2ssa/src/semantic.rs` already intersects: it walks the operations before the
call in its own block, stops at the previous call, and records an index only for
an operation that writes an argument register. That is exactly the intersection
`SourceConventionSlots` asks its consumers for.

So the question is why it yields eight. The rendering answers half of it:

    sub_30(sub_24_result + w20, W1, W2, W3, W4, W5, W6, W7)

The first argument is real and lowercase, a rendered expression. `W1` through
`W7` are **uppercase**, which in this renderer means a version-zero entry value:
a register the function never writes. So the collector is recording entry values
as arguments, for registers nothing in the block assigns.

Two candidates, and one run of instrumentation on `call_argument_value_for_op`
distinguishes them: either it matches the `bl` instruction's own lifted
clobbering of caller-saved registers as though those were argument writes, or the
values arrive through `stack_argument_locations`, which
`canonical_argument_values` merges in without the same intersection --
`by_index.entry(argument.index).or_insert(argument.value)`.

The second is the more likely of the two on reading, and it is a one-line check
to settle. The ledger is the measure to watch: 81 obligations with 50 refused
today.

### The eight arguments are the previous call's clobber

Instrumenting `canonical_argument_values` settles which half supplies them:

    args registers=8 stack=0 total=8

So it is the register path, not `stack_argument_locations`, and the guess in the
previous entry was the wrong one of the two.

`call_argument_value_for_op` decides what an argument write is:

    let index = canonical_abi_arg_index(&dst.name)?;
    let source = match op { Copy | ZExt | SExt | Trunc | Cast | Subpiece => .., _ => None }
        .or_else(|| graph.value_id_for_var(dst))?;

Any operation whose destination is named like an argument register counts, and
when the operation is not one of the transfer forms the fallback takes the
destination's own value. `collect_call_argument_slots` walks the operations
before a call and stops at the previous call -- but a call's lifted
caller-saved clobber is emitted **after** that call, so walking back from the
second call reaches the first call's clobber writes before it reaches the first
call itself. Those writes are named `x1` through `x7`, so each becomes an
argument, and each renders as the version-zero entry value it is:

    sub_30(sub_24_result + w20, W1, W2, W3, W4, W5, W6, W7)

**The rule that is missing is that a clobber is not an argument.** A register the
callee is permitted to destroy is written by the call, not for the next one, and
the walk cannot tell the difference because it looks only at the destination's
name. Two ways to tell it: stop the walk at the clobber rather than at the call
op, or require an argument's source to be a value the function defines rather
than an entry value.

`canonical_abi_arg_index` is also a hardcoded list of x86 and arm64 spellings and
belongs with the other target-model work, but that is tidiness; the clobber rule
is the defect.

### Correction: the eight arguments are not entry values

The entry above inferred from the uppercase spelling of `W1` through `W7` that
they are version-zero values, and built a discriminator on it: reject an argument
whose value the function never produced. Two forms of that were tried -- rejecting
only non-transfer operations, then rejecting any version-zero source -- and
neither changes the rendering or the ledger, which stays at 81 obligations with
50 refused. So the sources are not version zero, and the uppercase spelling means
something else.

What survives from that entry is the part that was measured rather than inferred:

  * the eight come from the register path, `registers=8 stack=0`
  * `call_argument_value_for_op` accepts any operation whose destination is named
    like an argument register
  * `collect_call_argument_slots` stops its backward walk at the previous call

What does not survive is the claim about clobbers and entry values. **The next
measurement is to print what the eight actually are** -- the operation, its
destination version and its source -- at the point `collect_call_argument_slots`
records them. That is one run, and it should have been the first thing done
rather than the third guess.

### The callsite defect was real, and the fixture was hiding a second one

Instrumenting what `collect_call_argument_slots` records found it in one run,
after two discriminators built by reading had failed:

    slot idx=1 op=W1_1 = CALLDEF  dst=W1_1  value_var=W1_1
    slot idx=0 op=X0_2 = ZEXT(tmp:12280_1)

`SSAOp::CallDefine` is how a call says the callee may destroy a register. Those
definitions are emitted after the call, so the backward walk from the next call
reaches them first, and their destinations are argument registers. Rejecting them
takes a one-argument call from eight arguments to one.

**The fixture was also lying, twice.** `radare2` splits a Mach-O object at an
unresolved `bl`, so `_driver` became `fcn.00000000` and `fcn.00000024` and the
first call's argument setup sat in the other half -- which is why that call
collected no arguments at all and looked like a second defect. Linking a real
binary instead of decompiling an object file fixes both: `/tmp/xmmfix/callsmain`
holds `driver3`, whole, and the arguments recover correctly.

    slots at 100000460:41 -> ["0=tmp:11b80_1", "1=tmp:28300_1", "2=tmp:20380_1"]
    slots at 100000460:90 -> ["0=tmp:12280_1"]

    sym._work(arg0 + 1, arg1 << 1, (uint32_t)arg1 ^ (uint32_t)arg0);

which is `work(n + 1, m * 2, n ^ m)` exactly.

**What that fixture does show is a real defect: every call is emitted twice.**

    sym._work(arg0 + 1, arg1 << 1, (uint32_t)arg1 ^ (uint32_t)arg0);
    sym._other(sym._work(...) + (uint32_t)arg0);
    uint64_t _work_result = sym__work(arg0 + 1, arg1 << 1, arg0 ^ arg1);
    uint64_t t12280_3 = _work_result + arg1 + sym__other(_work_result + arg0);
    return _work_result + arg1 + sym__other(_work_result + arg0);

Each call appears as a bare statement and again inside an assignment, under two
spellings -- `sym._work` and `sym__work` -- and `t12280_3` is declared and then
not used by the return, which repeats its expression instead. 85 of 144
obligations are refused. **Use a linked binary for call work, never an object
file**, and this is the fixture.

### Two renderings of one call, and where the second comes from

The duplicate emission has a single line behind it:

    // crates/r2dec/src/analysis/lower.rs:448
    SSAOp::Call { target } => CExpr::call(self.get_expr(target), vec![]),

The analysis layer lowers a call to a callee expression obtained from
`get_expr(target)` -- which for a symbol target is a **`CExpr::Var`** named after
the symbol -- with an empty argument list. The fold's certified path builds a
different thing for the same call: a **`CExpr::External`** with the arguments the
callsite certificate proves.

Both reach the page. The certified one becomes a statement, the definition-table
one is inlined into whatever reads the call's result, and the two spellings in
the output are the two representations:

    sym._work(...)     External, from the certified path
    sym__work(...)     Var, from lower.rs:448, lowercased and dotted by
                       assignment_lhs_expr into a legal identifier

**This is the same defect the branch has collapsed twice already** -- two
implementations of one job, disagreeing -- at the level of call expressions. The
certified path is the one to keep: it has the arguments and the callee identity.
`lower.rs:448` needs to stop building a second one, and the question to settle
first is who consumes it, because the definition table is read from many places.

The measure to watch is the ledger on `/tmp/xmmfix/callsmain`: 144 obligations,
47 rendered, **85 refused** today.

### Correction: `lower.rs:448` is not the second rendering

The entry above named `SSAOp::Call { target } => CExpr::call(self.get_expr(target), vec![])`
as the source of the duplicate. It is not. Replacing that line's callee with a
marker external and rebuilding leaves the rendering identical -- no marker
anywhere in the output -- so nothing that reaches the page comes through it.

The elimination is worth keeping, and so is the reason the guess was wrong:
`SSAOp::Call` carries only a target and has no destination, so
`populate_prepared_render_definitions` never stores its expression, and the
definition table cannot be the second renderer. That was checkable by reading the
recorder's `let Some(dst) = op.dst() else { continue }` and I did not check it.

What is still true and still unexplained: two spellings reach the output for one
call.

    sym._work(...)     an External callee
    sym__work(...)     a Var callee, lowercased with its dot replaced

The second is a `CExpr::Var`, so something builds a call whose callee is a
variable named after the symbol. **Find it by marking rather than reading**: give
`CExpr::call` sites in the fold a distinguishing callee and see which marker
reaches the page, exactly as above. That took one build to eliminate a candidate
and will take one more to find the real one.

### Thirty-eight places build a call expression

Marking eliminated four candidates in three builds -- `analysis/lower.rs:448`,
`analysis/use_info.rs:5357`, `use_info.rs:5631` and both sites in
`fold/op_lower/calls.rs` -- and none of their markers reached the page. Counting
properly says why that was never going to converge:

    21  crates/r2dec/src/fold/op_lower/mod.rs
    13  crates/r2dec/src/analysis/lower.rs
     3  crates/r2dec/src/structure.rs
     3  crates/r2dec/src/lib.rs
     2  crates/r2dec/src/fold/op_lower/lowering.rs
     2  crates/r2dec/src/fold/op_lower/calls.rs

Thirty-eight production sites construct a call expression. The twenty-one in
`op_lower/mod.rs` were never examined, because an earlier grep of that directory
was truncated at twelve results and I read the absence as evidence.

**That count is the defect, not a step toward finding it.** A call rendering
twice under two spellings is what thirty-eight independent constructions of the
same thing look like, and it is the same shape as the two collapses this branch
has already done and the resolver contract it has already scoped: no single
place owns the answer, so several answer, and they disagree.

The work is to make one of them own it -- the certified path, which has the
callee identity and the proven arguments -- and route the rest through it. That
is a larger job than the duplicate suggests, and the ledger measures it:
`/tmp/xmmfix/callsmain` renders 47 of 144 obligations with 85 refused.

**Method note.** Marking works and reading does not: four candidates eliminated
in three builds, against four wrong mechanisms reasoned from the rendering. But
mark from a complete list. Three of those builds were spent because the list was
truncated and I did not check it.

### Correction: two sites build this call, not thirty-eight

The count of thirty-eight was right as a count and wrong as a diagnosis. Putting
`#[track_caller]` on `CExpr::call` and recording `Location::caller()` says which
sites actually run, with no call-site edits and no list to get wrong:

    callsite crates/r2dec/src/fold/op_lower/lowering.rs:94
    callsite crates/r2dec/src/fold/op_lower/mod.rs:2962

Two, and both are certified paths:

  * `lowering.rs:94` builds the call and hands it to
    `lower_certified_statement_call`, which is the **statement** form.
  * `mod.rs:2962` builds `CertifiedCallExpr`, the **expression** form, which is
    then inlined wherever the call's result is read.

So the duplicate is not an uncertified path leaking. It is one call lowered twice
on purpose, once as a statement and once as an expression, by two functions that
disagree about the callee: `mod.rs` resolves it through
`resolved_callee_identity_expr_for_site`, giving the `External` spelling
`sym._work`, while `lowering.rs` uses `resolve_call_target_for_site`, whose
result renders as the variable `sym__work`.

**Two things to settle, in this order.** Whether a call should ever be lowered
both ways for one site -- if the expression form is used, the statement is
redundant, and the ledger's 85 refusals suggest the two forms are also being
counted against each other. And why two resolvers of the callee disagree, which
is item 1 on the open list wearing a different hat.

**Method.** `#[track_caller]` on a constructor is the cheapest possible version
of "mark, do not read": it needs no list, no distinguishing markers and no edits
to the sites, and it answered in one build what three builds of hand-placed
markers had not.

### The two callee resolvers disagreeing is not why the statement is bare

`lower_certified_statement_call` emits a bare statement only when
`materializable_call_result_expr_for_call_expr` finds no owner for the call, and
it is handed a call whose callee came from `resolve_call_target_for_site` while
the expression form used `resolved_callee_identity_expr_for_site`. Making both
use the certified identity changes nothing: the rendering and the ledger are
identical, still 47 of 144 with 85 refused.

So the owner lookup fails for some other reason, and the two spellings are a
symptom of the split rather than its cause.

**Eliminated on this defect so far:** `analysis/lower.rs:448`,
`analysis/use_info.rs:5357` and `:5631`, both sites in `fold/op_lower/calls.rs`,
and the callee-resolver mismatch. **Established:** exactly two sites build this
call, `lowering.rs:94` for the statement and `mod.rs:2962` for the expression,
and both are certified.

**The next measurement is `materializable_call_result_expr_for_call_expr`
itself** -- why it answers `None` for a call whose result is plainly consumed two
lines later. Time it or print its inputs; do not reason about it. Five mechanisms
have been reasoned out and all five were wrong, while every measurement has
answered in one build.
