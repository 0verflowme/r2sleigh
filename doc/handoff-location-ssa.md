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
**704 pass, 2 fail**, down from 83 failures when the suite first compiled.
Thirty-eight commits from `763b28d`, net negative line count.

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

### The 2 that remain

`fold::op_lower::tests::call_source_proof_raw_owner_recovery_rejects_alias_owner_without_function_facts`
and `final_call_normalization_uses_typed_printf_identity_not_rendered_name`.

Both build one fixture and read it from several `FoldingContext`s. A context
owns its table by value, so making two contexts agree means cloning one into the
other, and a clone is a **snapshot**: any name declared after it is missing, and
the panic becomes `index out of bounds: the len is 2 but the index is 2` rather
than a table mismatch. Chasing the clone to a later line only moves which name
is missing.

The fix is structural, not another clone. Either a `FoldingContext` should
borrow its table rather than own it, so several contexts can share one; or these
tests should build every fixture name before any context exists and hand the
same table to each. The first matches production, where
`build_function_internal_with_control` creates one table and passes it to
everything that renders the function. It is the last piece of the table-identity
work and worth doing properly rather than patching around.

### How the other 81 were fixed

Every one was a real defect that the branding exposed, not churn:

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

### A defect worth chasing next

`sym._sum_carry` in `flag_x64.dylib` renders `rax = (int64_t)eax_1;` where
`eax_1` is never declared. The table makes an undeclared name unconstructible,
so `eax_1` *is* in the table -- it is simply never emitted as a local. That is
the rule from the working agreement: a value with more than one reader is
declared as a typed local, and one with a single reader propagates into it.

This is now cheap to check exactly, which it was not before: walk the rendered
body, collect every `SymbolId`, and assert each appears in `params` or `locals`.
That check used to require scanning text for words that resolve to nothing, and
could be satisfied by declaring the word. It should be a test.

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
