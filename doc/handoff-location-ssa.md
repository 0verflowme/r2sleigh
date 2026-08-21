# Picking up the r2sleigh architecture rewrite

This is a handoff. It says what was wrong, what was decided and why, exactly
where the tree stands, and what remains before the rewrite can be called
finished. Work happens in the `r2sleigh-arch` worktree on `arch/location-ssa`;
the primary checkout stays on its own branch so a bad day here costs nothing.

Read `doc/adr-location-ssa.md` first for the original design. This document
records what changed once the design met the code.

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

## What is left

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

