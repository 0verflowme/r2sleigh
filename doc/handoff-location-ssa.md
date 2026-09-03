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

### Ground truth

Fourteen hash functions built at three optimisation levels on two architectures,
verified by compiling each rendering and running it against the reference digest
(`tests/corpus/verify_rendering.py`). This is the number to quote; the proof line
counts obligations, not correctness.

                     start    now
    x86-64 -O0         4       7
    x86-64 -O1         0       5
    x86-64 -O2         0       3
    arm64  -O0         0       7
    arm64  -O1         0       7
    arm64  -O2         0       6
                     ----    ----
                       4      35   of 54

Measuring it requires `make -C r2plugin install` and a fresh `sweep.sh` for every
configuration; see "How to measure" below, which cost four voided conclusions to
learn.

### Done

  * **The nine paired fact stores are one store each, keyed by identity.**
    `UseInfo` held every fact twice -- `definitions` beside `definitions_by_value`
    and eight more like it -- and `rebuild_id_mirrors_from_name_maps` cleared the
    value-keyed half and rebuilt it from the name-keyed one as the last thing
    before any consumer looked, so a read side written to ask the value first was
    asking a mirror. The rebuild is gone and each store keys itself where its
    fact is learned. Collapsing `copy_sources` stopped `crc32_bitwise` hanging at
    arm64 -O1: following a copy chain by name could step between two variables
    differing only in case. Three case-variant lookup ladders went with them, and
    `LowerCtx` lost eight duplicated borrows of maps `UseInfo` already owned.
  * **radare2's resolved jump tables reach the renderer.** `pdd` goes through the
    borrowed-snapshot provider, which serialises each block's switch cases;
    `r2source` decoded them and nothing read them, so the lift built blocks from
    image bytes alone and `murmur3_32` rendered four statements of thirty-five
    with `/* indirect branch target unresolved */`. It renders its tail switch
    with real case arms and a return now.
  * **A budget that runs out keeps what it rendered.** The partial rendering was
    discarded, so a function that ran out of time reported as one that produced
    nothing and the ledger that would have said so went with it. The stop is
    still recorded -- phase refused, route reason, refusal -- and the body
    survives.
  * **A speculative rewrite leaves no trace when it declines.** `Region::IfThenElse`
    tries three rewrites before structuring normally, and each structures the
    whole subtree to decide whether it applies. Their merge deferrals outlived
    them, so a real structuring nested inside a declined attempt saw a merge as
    already claimed and left it out -- `murmur3_32` lost its `return` entirely on
    both optimised arm64 builds. The deferral stack is now truncated back after
    the attempts. Partial: the merge is now emitted twice instead of not at all,
    because the region is still structured twice. See the section below.
  * **A merge reached from a branching predecessor is placed.** One unplaceable
    merge abandoned every merge in its block, and the backedge test required the
    target to dominate the predecessor, which refused every merge on a loop
    *exit* edge. `djb2` at x86-64 -O2 lost the counter leaving its first loop and
    with it the `+ rdx` that starts the remainder after the bytes already read.
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
  * **A carrier answers `value_has_something_to_render` by its own name.**
    Suppressing its definition and its semantic value, which is what stopped two
    tables erasing the accumulation, also made it fail the predicate that keeps a
    statement from being dropped when nothing can produce its value. arm64 -O2
    `djb2` folded back to its seed; it now keeps the recurrence.
  * **The proof line says `built`, not `rendered`, and prints the statements the
    body holds.** See the sequencing note below: the ledger cannot close before
    the location model, and until it does the line states the gap instead of
    implying there is none.

### Open, each scoped by measurement

  0. **The failures are eight causes, not one.** An earlier revision of this
     item claimed that eleven of twelve remaining failures were the spelling
     defect below. That was read off `out_x64_O0.txt` while it was stale. Fresh
     dumps at 35 of 54 give this distribution, and the spelling defect is three
     of eighteen:

     | cause | count | where |
     | --- | --- | --- |
     | `x30` stored through an argument | 2 | arm64 -O0 murmur3_32, xxhash32 |
     | `uint128_t` is not a C type | 2 | arm64 -O2 crc32_bitwise, xxhash32 |
     | narrow carrier member read after a loop (`eax_5`, `eax_8`, `eax_12`/`ecx_9`, `rcx_6`) -- **all fixed** | 0 | x64 -O1/-O2 |
     | `r8d` in a piece composition | 1 | x64 -O2 fnv1a64 |
     | `tmp_4700_7` / `tmp_11f80_4` -- the spelling defect | 3 | x64 -O1/-O2, arm64 -O1 xxhash32 |
     | `t11f00_10` / `t20380_4` -- murmur3's duplicated merge block | 3 | x64 -O0, arm64 -O1/-O2 |
     | `sym__rotl32` called with no declaration | 1 | x64 -O0 xxhash32 |
     | `tregalias_...` never declared | 1 | x64 -O2 crc32_bitwise |
     | wrong checksum | 1 | x64 -O2 pearson |

     **The first compile error is not the only one.** `verify_rendering.py`
     compiles one function per file and reports the first `error:` clang emits,
     so a function's entry in that table names its *first* symptom, not its
     defects. `xxhash32` at x86-64 -O0 reports `sym__rotl32` undeclared, which is
     genuinely a harness limit -- the helper is a sibling function the harness
     never compiles. But supplying only that helper and rebuilding shows what the
     limit was hiding:

     ```
     use of undeclared identifier 'edi_3'   (also edi_5, edi_7, edi_9, edi_17, edi_20)
     use of undeclared identifier 'eax_60'; did you mean 'rax_60'?
     use of undeclared identifier 'local_38'
     ```

     and the arm64 -O0 twin hides `t12280_9`, `t12280_17`, `t12280_19`,
     `local_30` and `local_40`. `eax_60` beside `rax_60` is item 0f exactly --
     the narrow member of a carrier -- so xxhash32 at -O0 belongs to that cluster
     too, and an earlier note in this document calling those two entries a pure
     harness artifact was wrong. Counting first errors understates the work.

     `uint128_t` [FIXED]. This document previously called it a width defect --
     "a 32-bit table read 128 bits wide" -- on the strength of
     `((uint128_t*)0x100000000U)[245]` looking wrong. It is not: `0x100000000` is
     the Mach-O image base, so that is a genuine table read, and arm64 -O2 really
     does load sixteen bytes at a time with a vector register. The 128-bit type
     was honest; `uint128_t` simply is not how C spells it. `CType::UInt(128)`
     now prints `__uint128_t` (and `Int(128)` prints `__int128_t`), which is what
     compilers call it. Both arm64 -O2 failures advance past the type error:
     crc32_bitwise to an undeclared `tregpiece_...`, xxhash32 to a mangled cast.

     That mangled cast was the harness's own. `verify_rendering.py` stashes
     `*(uintN_t *)` casts before rewriting bare dereferences, so its own
     `*(X) -> (*(unsigned char *)(long)(X))` rule cannot corrupt them -- but the
     protected list stopped at 64 bits, so a valid `*(__uint128_t *)` was
     rewritten into `(*(unsigned char *)(long)(__uint128_t*))t7400_2`, which is
     not an expression. The list now covers 128-bit and the optional `__`
     prefix. Corpus is 37 before and after, so no verdict depends on it: the fix
     stops the instrument corrupting valid output rather than changing what
     counts as correct.

     Worth watching when editing that file: writing the prefix as `__?` rather
     than `(?:__)?` makes the underscore *mandatory* and unprotects every
     ordinary `uint32_t` cast. That drops the corpus from 37 to 18 and looks
     exactly like a decompiler regression.

     With the cast intact, arm64 -O2 xxhash32 advances again, to
     `call to undeclared function 'callother'` -- a Sleigh CALLOTHER for an
     instruction the lifter does not model reaching the page. That is a real
     limitation rather than a rendering defect, and it is the first of its kind
     to surface in this corpus.

     `sym__rotl32` compiles once declared but cannot link, because the harness
     builds one function per file.

  0a. **[FIXED] `stp x29, x30` rendered as a store through an argument
     (arm64, non-leaf).** The cause was `variable.rs`, which decided whether a
     version-zero register was an argument register with
     `name_lower.contains(cc_reg)`. `"x29"` contains `"x2"` and `"x30"` contains
     `"x3"`, so every non-leaf arm64 function recovered its frame pointer and
     link register as its third and fourth parameters, while the real third
     argument -- spelled `w2` -- matched `"x2"` nowhere. `build_param_register_aliases`
     then pairs recovered parameters to declared ones by position, which handed
     `x29` the name `arg2`; from there every address held in `x29` rendered as
     that argument, and the prologue's frame save came out as a store through it.

     The trace that found it, in order: the store target resolves through
     `render_canonical_store_target_expr` to `AddrOf(Var(81)) + 8` with symbol 81
     spelling `arg2`; the definition is written at `prepared_semantic.rs:533` from
     `lower.op_to_expr`, one level down from `tmp:7b80_1`, whose own definition
     comes from site 3407; that resolves through `resolve_stack_var(-0x10)`,
     which answers `arg2` from prepared, external and map at once; the single
     alias-map entry at that offset carries `visible=local_10` but
     `arg_alias=Some("arg2")` with `kind=None`, which is the store-scan writer;
     and that writer's `param_register_aliases` contains `"x29": "arg2"`.

     Fixed by matching against the register's alias set -- `register_alias_names`
     already knows `x2` is spelled `x2` or `w2` and nothing else -- with a
     `register_token` helper so the qualified spelling `reg:x0` still matches.
     Regression test `frame_and_link_registers_are_not_recovered_as_arguments`;
     it fails on the old code with `["x0", "x1", "x29", "x30"]`.

     Corpus 35 to 36: x86-64 -O2 `pearson` goes from a wrong checksum to correct,
     because the widened match now also admits the 32-bit spellings on x86-64,
     which is what that function's arguments are. Both arm64 -O0 failures change
     identity rather than clearing: the false `arg2` is gone and the frame-record
     store now reads `((unsigned char *)t7b80_1)[1] = x30`, undeclared. Removing
     the false arg alias also removed the map's only entry at that offset, since
     the store scan was what created it, so the slot now has no visible name at
     all. What remains there is that the prologue's frame save should not be
     rendered as a program statement.

  0d. **[FIXED] arm64 -O0 rendered frame accesses as pointer arithmetic where
     x86-64 rendered named locals.** Two causes, one behind the other.

     The trace: `canonicalize_param_home_stack_slots` returns immediately when
     `register_params` is empty, and on arm64 it was. That list comes from
     `inferred_signature_abi_register_params`, which recognised only SysV
     x86-64 -- radare2 reports `arch="aarch64"` with the calling-convention
     field left *empty*, and the guard demanded a named convention. With no
     register parameters there are no ParamHome slots, so no `HiddenHome`
     bindings, so an empty stack alias map, so no names to render:
     `bindings=3 slots=0 entries=0` on arm64 against `bindings=7 slots=3
     entries=3` on x86-64 for the same function. Fixed by adding the AAPCS64
     table and treating an unnamed convention on aarch64 as AAPCS64, which there
     is only one of.

     That alone changed nothing, because a second cause sat under it: the stores
     the scan needs to see had no stack slot at all -- seventeen of them resolved
     to `None`, all addressed off `x29`. `x29` had no stack-address root, and
     neither did the temp it was copied from. The op is

         IntAdd { dst: tmp:11f80_1, a: sp_1, b: tmp:11e80_1 }

     where the displacement `b` is a *temp*, not a constant: AArch64 Sleigh
     materialises `add x29, sp, 0x60` as `tmp:A = 0x60; x29 = sp + tmp:A`.
     `signed_stack_delta` reads `constant_bits` off the operand and gave up, so
     the frame pointer never got a root and nothing derived from it did either.
     Fixed with `signed_stack_delta_through_roots`, which resolves the operand
     through the canonical value roots before giving up.

     Together these change the rendering completely. `murmur3_32` at arm64 -O0
     went from

     ```c
     long t11f80_1 = local_70 + 96;
     *(int64_t *)(long)(t11f80_1 - 0x8) = arg0;
     *(int32_t *)(long)(t11f80_1 - 0x14) = arg2;
     ```

     to

     ```c
     long local_28 = arg2;
     long local_38 = 4 == 0 ? 0 : arg1 / 4;
     for (long local_40 = 0; local_40 < local_38; local_40 = t11f80_3) {
     ```

     The corpus stays at 36 of 54, because neither arm64 -O0 function crosses the
     line yet: `xxhash32` now fails only on `sym__rotl32` being undeclared, which
     is the harness building one function per file rather than a defect, so it is
     at parity with x86-64 -O0; `murmur3_32` fails on an undeclared `x8_30`,
     several layers further in than where it was. Count and quality moved apart
     here, and the quality is the part that matters for what follows.

  0f. **The largest remaining cluster is one cause, and it is the location
     model.** Four x86-64 failures are the same shape, and they are the biggest
     group left:

     ```c
     return eax_5 | 1;                             /* -O1 adler32   */
     return (uint8_t)rcx_6;                        /* -O1 pearson   */
     return eax_12 | (uint32_t)(int64_t)ecx_9;     /* -O2 adler32   */
     ... (eax_8 ^ esi_1) * 0x85ebca6bU ...         /* -O1 murmur3   */
     ```

     Each reads, after a loop, a *narrow member* of a storage whose carrier was
     chosen at the wide name. In adler32 -O1 the loop body ends
     `rax = (int64_t)eax_4;` -- `rax` is the carrier and `eax_5` is the 32-bit
     member of the same place, so the value the return wants is carried under one
     name and read under another, and the name it is read under is declared
     nowhere. `ecx_9` in the -O2 line is the same value this document already
     recorded as adler32's blocker; it is not one function's problem but four.

     This is the location model in its most concrete form, and the substrate for
     it is already built. `CanonicalStorageId` separates the place from the
     width, and a dump over adler32 at x86-64 -O1 shows exactly that:

     ```
     EAX_1..EAX_6  CanonicalStorageId { space: Register, offset: 0, size: 4 }
     RAX_1..RAX_7  CanonicalStorageId { space: Register, offset: 0, size: 8 }
     ```

     Same space, same offset, different size. The two are one place at two
     widths, and the arch already carries the fact that makes that sound --
     `RegisterFamilyInfo::narrow_write_clears_register`, true on both x86-64 and
     arm64. What is missing is that *identity includes the size*, so carrier
     membership never recognises the narrow member. `exit_merges_for_carrier`
     spells the same assumption out: it skips any merge where
     `merge.dst.size != carrier.size`.

     The consequence is not only a name. In adler32 -O1 the loop carries `RAX_2`
     and the tail is `EAX_5 = EAX_4 << 16`, `EAX_6 = EAX_5 | R8D_3` -- the
     `(b << 16) | a` the source returns. `EAX_4` is defined inside the loop and
     read after it, so with the narrow member outside the carrier those tail
     statements are dropped and the return is left quoting a name nothing
     defines.

     **Half of this is now built.** `CarrierMemberView` in `normalize.rs` pairs a
     carrier phi with the phis beside it in the same header block over the same
     `{space, offset}` at a different size, and `get_expr_inner` resolves such a
     value to a cast of the carrier rather than to a name. On adler32 at x86-64
     -O1 that pairs `EAX_2` to carrier `rax` at width 4, and `R8_2` to carrier
     `r8d` at width 8 -- both directions, because a carrier may be held at either
     width. It is gated on `SsaArtifact::narrow_write_clears_register`, which is
     what makes the widening sound.

     Only a phi in the carrier's own header block counts. Treating *every* value
     at the place as the carrier is the whole-function renaming that measured 34
     correct down to 13; a header phi is the narrow point where the two widths
     are provably the same run of the same storage.

     Measured: 32 cast sites appear across x86-64 -O1 and -O2, the corpus holds
     at 36 of 54 with no regression, and adler32 -O2's failure moves from an
     undeclared `eax_12` to an undeclared `rax`. What remains is the *derived*
     values -- `EAX_5 = EAX_4 << 16` is not a phi, so it has no view, and the
     tail that computes it is still dropped.

     **Why the earlier attempt regressed 34 correct to 13, and what landing it
     whole means.** Aliasing the narrow member to the carrier's name is only half
     of it: `eax_5` is not `rax`, it is `(uint32_t)rax`. An alias map maps a name
     to a name, so it cannot express the truncation, and a change that only adds
     the alias renders `rax | 1` where `(uint32_t)rax | 1` was meant -- correct
     names, wrong values, which is what a corpus measured in checksums reports as
     a collapse. The complete change is therefore two things at once: membership
     by place, *and* resolving a narrow member to a cast of the carrier rather
     than to a bare name. The second half cannot live in `spell_var`, which
     returns a `String`; it belongs where expressions are produced.

     **What they are not.** `exit_merges_for_carrier` skips any merge whose size
     differs from the carrier's, which reads like the exact exclusion this
     cluster needs. It was widened to accept a merge over the same
     `{space, offset}` at any width -- gated on `narrow_write_clears_register`,
     with the narrow ones routed to `CarrierMemberView` so they render as a cast
     rather than taking the carrier's bare name. Measured: nothing moves. Corpus
     stays at 36 and every one of `eax_4`, `eax_5`, `eax_8`, `eax_12` and
     `rcx_6` fails exactly as before. Reverted.

     So these values are not phis, and not exit merges either: they are ordinary
     definitions, computed once and read after the loop, and no carrier fact
     covers them at all. Widening the carrier machinery is the wrong direction --
     the question is why a definition that exists in the SSA is not rendered,
     which is a liveness or elision question rather than a naming one. That is
     where the next attempt should start, and it should start by finding the
     defining op for `EAX_4` and asking what dropped it.

     **How far the trace got, so the next one starts here.** Taking `eax_4` in
     xxhash32 at x86-64 -O1:

     * Its definition is recorded and passes every filter:
       `DEFFILTER EAX_4 self=false safe=true carrier=false`.
     * The resolver behaves correctly: `GETEXPR key=EAX_4 def=true
       value_id=Some(878) use_count=8` and it hands back a bare `Var`, which is
       right -- eight uses should not be inlined, they should read a statement.
     * The op is `Subpiece { dst: EAX_4, src: tmp:4c780_17, offset: 0 }`, a
       truncation, and `op_to_stmt_impl` *does* reach it.
     * `assign_stmt` does *not* drop it: instrumenting all four of its
       `return None` paths shows only one firing in this function, for two other
       symbols.
     * The block-local prune in `aliases.rs` never sees it as a target, under
       either spelling.
     * Yet no pass in the pipeline ever sees `eax_4` as an assignment target --
       it is already gone at the first one.

     **[FIXED] The cause was the return-register rule.** Bisecting the emission
     loop with a probe per `continue`, as this item recommended, lands on one
     guard:

     ```rust
     // In return-context blocks, keep return-register writes as tracking-only.
     // Emit a single high-level return at the SSA Return terminator.
     if track_return_value
         && let Some(dst) = op.dst()
         && self.inputs.arch.is_return_register_name(&dst.name.to_lowercase())
     ```

     Every write to the return register in a return-context block was dropped, on
     the promise that one `return` statement would carry the value. But a return
     register is an ordinary register until the function ends, so the tail can
     compute in it and read the result again -- `EAX_4` is read eight more times
     by the statements that finish the hash. All eight were left reading a name
     nothing defined.

     Fixed by suppressing the write only when the return is the value's one
     reader (`use_count_of(dst) <= 1`).

     Measured: `eax_4`, `eax_5` and `eax_8` all resolve, and three x86-64 -O1
     functions -- adler32, murmur3_32 and xxhash32 -- go from *not compiling* to
     compiling and running. They return the wrong values so far
     (`9dd20001` against `9dd21488`, `ec1fbeef` against `7e4102af`), which is the
     next layer rather than this one. x86-64 -O2 adler32 advances from `eax_12`
     to `ecx_9`. Corpus holds at 36 of 54: three functions crossed from
     unbuildable to buildable, none yet to correct.

     Worth recording that reading the code predicted this wrongly twice -- once
     as block elision, once as the inline promise -- and the probe found it in
     one run. Bisect this loop rather than reasoning about it.

     The block is *not* the answer. `EAX_4`'s block, `0x1000009ec`, is folded
     normally with 196 ops, so nothing dropped it.

     Two further things were built and measured, and both are inert. The
     statement-emission loop skips an op when `should_inline(dst)` holds, and
     records what the reader promised to show -- except when the only rendering
     the op has is the destination's own name, in which case the recording is
     skipped and the promise cannot be kept. Emitting the op in exactly that case
     changes nothing here, so `should_inline(EAX_4)` is not what drops it.
     Reverted.

     Where it actually stops, and this is the puzzle to pick up: instrumenting
     the emission loop shows the op passing every guard at the top --
     `GUARD dst=EAX_4 frame=false inlined_call=false home_store=false
     shadow=false` -- and then never reaching the `is_dead` / `should_inline`
     block a hundred lines later, where a second probe never fires. Every
     `continue` between those two points is inside the Store or Load
     return-slot handling and cannot apply to a `Subpiece`. So the op leaves the
     loop somewhere that reading the code does not explain, and the next session
     should bisect that span with a probe per `continue` rather than reasoning
     about it -- the reasoning has now been wrong twice.

     Not in this cluster despite looking like it: `r8d` in fnv1a64 -O2 appears
     inside a piece composition, `(hi << 32) | (uint64_t)r8d`, which is the width
     layer rather than carrier membership; and `x8_30` in arm64 -O0 murmur3_32 is
     not a naming defect at all -- see 0g.

  0h. **[FIXED] The renderer was not deterministic.** Two `pdd` calls on the same
     function, in the same process, with nothing in between, produce different C.
     This is the most serious item in this document and it qualifies every
     measurement in it.

     ```
     r2 -c 'a:sla; aaa; s sym._adler32; pdd; pdd; pdd'   -> three different renderings
     ```

     Three consecutive renders of `adler32` at x86-64 -O2 hashed to three
     distinct outputs. It is not confined to failing functions: `fnv1a32`, which
     is CORRECT everywhere, rendered identically in two of three sessions and
     differently in the third.

     What it is not. It is not the SSA deadline -- the decompile path builds
     `SsaExecutionControl::default()`, which carries no deadline at all. It is
     not radare2's state: `afs` and `afv` for `adler32` are byte-identical before
     and after, and the type database is empty in both. It is not the lift or the
     facts: across two renderings that differ structurally, the proof line reports
     the *same* 169 source obligations, 149 built, 16 elided, 0 refused, 4
     unaccounted, while the statement count moves between 55, 56 and 57. The same
     facts are being rendered differently.

     Where it starts. Dumping per-pass state shows the two runs already differing
     at the first pass, `simplify_identities_in_function`, so it is upstream of
     every post-pass -- in analysis, folding or structuring. The differences are
     structural, not cosmetic: one run emits
     `if ((arg1 & 1) == 0) { return ...; }` followed by flat statements where the
     other emits `{ if ((arg1 & 1) != 0) { ...block... } }`.

     **The cause.** `MaterializedEdgeCopies` is a `HashSet`, and the loop in
     `FoldingContext::from_inputs` that gives each end of a materialised copy its
     carrier's name was a *single pass* over it that read and wrote the same map.
     A copy only carries a name when one of its ends already has one, so a chain
     `rax -> a -> b -> c` resolved only as far as the visit order allowed, and a
     `HashSet` yields its elements in whatever order its seed produced -- which
     differs between two sets in one process. The same copies, closed to a
     different depth.

     Bisecting to it: the prepared SSA hashes identically across renders (9
     blocks, 694 ops, 202 phis, same name digest), and so do the certified
     carriers including every member list, and both gate sets are empty. Yet
     `carrier_name_aliases` returned 9 aliases while the `PassEnv` that consumed
     them held 20, 21 or 22 on different runs -- the gap is this loop.

     Fixed by sorting the copies and repeating until nothing new is joined, so
     the answer is the transitive closure however the set is ordered. It now
     yields 24 every time, which is also *more* than any single pass reached: the
     old loop was under-propagating as well as varying. `adler32` at x86-64 -O2
     now renders identically across sessions and across repeated `pdd` calls in
     one session, and so does `fnv1a32`. Corpus unchanged at 36 of 54.

     Ruled out along the way, and left alone because neither changed anything:
     `SSAFunction::blocks()` already iterates an explicit order rather than its
     `HashMap`, and `FamilyRootState`'s `min_by_key` tie-break over a `HashMap`
     was made ordered as an experiment, measured inert, and reverted.

     What it did not invalidate. The corpus verdict was stable even while the
     text was not: three independent sweeps of x86-64 -O2 all scored 4. Aggregate
     numbers taken before this fix can be trusted; a single rendering quoted in
     this document from before it may not reproduce, and neither may a trace
     taken once.

     Supersedes an earlier claim here that rendering `djb2` before `adler32`
     changed `adler32`'s output. That was one sample per condition, and what it
     actually sampled was this.

  0i. **[FIXED] A carrier reached the return as its initialiser.** This is what the three
     x86-64 -O1 functions now fail on, having crossed from not compiling to
     compiling with the return-register fix. adler32 renders

     ```c
     r8d = 1;                       /* before the loop      */
     do { ...; r8d = r9d_3 - r9d_4; ... } while (arg1 != rcx);
     return eax_4 << 16 | 1;        /* wants `| r8d`        */
     ```

     and returns `9dd20001` against a wanted `9dd21488` -- the high half, which
     is `eax_4`, is right, and the low half is the accumulator's *initial* value
     instead of its final one. adler32 returns `(b << 16) | a`, so this is `a`
     read as 1.

     The constant is baked in before the return is reached: probing the
     `SSAOp::Return` arm shows `last_ret_value` already holding
     `Binary { BitOr, Var(..), IntLit(1) }`. So the write to the return register
     that produced it had already resolved `r8d` to its initialiser.
     `resolve_return_expr_from_defs` is *not* the culprit -- it only handles
     `Paren`, `Cast` and `Var` and returns `None` for a `Binary`, so it cannot
     rewrite inside this expression. Look instead at what `get_expr` answers for
     the `R8D` version that write reads, and at whether the carrier's
     initialiser has been recorded as that value's definition.

     It was `expand_return_expr_in_context`. That function expands a name into
     its definition to build a self-contained return expression, and had no
     carrier guard at all -- while the predicate path a few hundred lines away
     declines to expand a carrier and carries a comment describing this exact
     failure ("Every counted loop exited one iteration early on that"). A carrier
     holds a different value on each iteration, so its definition is only one of
     them; expanding it answers the return with whichever that is. This is the
     second table answering for one value.

     Fixed by declining to expand a name that is a carrier's rendered name.

     Measured: **corpus 36 to 37**. adler32 at x86-64 -O1 returns `9dd21488`,
     which is correct, and that configuration goes from 5 to 6. The other two
     still differ -- murmur3_32 -O1 returns `ec1fbeef` against `7e4102af`, and
     xxhash32 -O1 returns nothing against `e7583aa4` -- so they are a different
     defect rather than this one.

  0j. **[FIXED] A memory access did not say how wide it was.** Seven attempts,
     and the last one worked because a marker test finally located the defect.

     Two things were confused for one another here, and the record is worth
     keeping. `verify_rendering.py` line 76 rewrites every `X[Y]` in the dump
     into `(((unsigned char *)(long)(X))[Y])`, because the decompiler emitted a
     subscript on an integer and C will not compile that -- a byte is the
     harness's only available guess. So the `((unsigned char *)arg0)[i]` that
     several turns chased is a harness patch, not a decompiler defect. Read `pdd`
     output when asking what the decompiler renders; `verify/*.c` is rewritten.

     The real defect was that the decompiler emitted `arg0[t4900_2]` -- a
     subscript on a `long`, stating no pointee at all -- so every consumer had to
     invent a width, and murmur3's dword read became a byte read.

     Six fixes at the construction site were inert, and the reason was found by
     making the transform unmistakable rather than by more probing: returning a
     `CExpr::External` marker instead of a typed access, and grepping `pdd` for
     it. The marker *appeared*. So the return value did reach the statement all
     along, and something was normalising the typed accesses away afterwards.
     Tracing the three normalisers in `assign_stmt` shows exactly where:

     ```
     1-identity = Deref(Cast{ptr(UInt(32)), Cast{ptr(UInt(8)), arg0} + t4900_2})
     2-semantic = Subscript { base: arg0, index: t4900_2 }
     ```

     `semanticize_visible_expr` re-derives the access from its address and
     reaches the same place by a route that has forgotten the width.

     Fixed by having it decline: an access whose base is already a pointer cast
     states its pointee and is finished. murmur3's main loop now renders
     `*(uint32_t *)((uint8_t *)arg0 + t4900_2)`, the width the machine reads at
     the offset it uses. Corpus holds at 37 of 54 with the harness assuming one
     fewer width, and murmur3 still returns `ec1fbeef` against `7e4102af` --
     the remaining error is the tail below, not this.

  0k. **[FIXED] murmur3's tail switch had no selector at all.** This is what murmur3_32
     at x86-64 -O1 now fails on, and it is worth more than the `& 3` it looks
     like.

     The tail renders `switch (arg1)` where `switch (arg1 & 3)` is meant, so a
     61-byte message matches none of `case 1/2/3` and the whole tail is skipped;
     the function returns `ec1fbeef` against `7e4102af`. But the mask is not
     merely lost -- probing `infer_switch_selector_var` shows
     `SELECTOR block=0x10000085c target=R8_11 found=None` for both switch blocks
     in the function. There is no selector, and `switch (arg1)` is a fallback
     rendering chosen without one.

     Why the inference fails is visible in the same probe: the branch target is
     `R8_11 = R8_10 + R9_1`, the offset-table pattern -- `lea` the table, load a
     32-bit entry, add it to the base, jump. `infer_switch_selector_var_from_sum`
     is handed two register operands and gives up, where it needs to follow the
     one that is not the table base: `R9_1` is loaded from `[table + i * 4]`, and
     `i` is the masked length.

     Fixed by the two together, which is why each alone measured inert.
     `infer_switch_selector_var_from_sum` now follows *both* operands when
     neither is a constant, so the walk gets past the offset-table add and into
     the loaded entry's index; and `SSAOp::IntAnd` becomes a stopping point in
     the value walk, because a masked value is the selector rather than a step
     towards one. Either change on its own does nothing: without the sum the
     walk never reaches the mask, and without the mask arm it walks past it.

     Measured: the selector is inferred -- `found=Some("R8D_9")` where it was
     `None` -- and the tail renders `switch (arg1 & 3)`. The tail now executes,
     which moves murmur3_32 at x86-64 -O1 from `ec1fbeef` to `16a1e234` against
     a wanted `7e4102af`. Corpus holds at 37 of 54.

     The fallthrough that was recorded here next is also fixed. `structure.rs`
     ended every case with `CStmt::Break` unconditionally; a case whose region
     leaves into another case's entry falls through, and C says that by omitting
     the break. murmur3's tail now renders `case 3` and `case 2` without one and
     `case 1` with, which is what the source does.

     That fix changes no checksum here and is still worth having: the corpus
     message is 61 bytes, so `len & 3` is 1 and only `case 1` ever runs. It is
     wrong for every other length, which the corpus does not exercise.

     murmur3_32 at x86-64 -O1 still returns `16a1e234` against `7e4102af`, and
     the cause is now identified. The source opens the tail with
     `uint32_t k1 = 0;`, which the compiler emits as `xor ecx, ecx` at
     `0x10000086a`, and the SSA has it as
     `ECX_3 = IntXor(tmp:regalias:...:18:0_1, tmp:regalias:...:18:0_1)`. The
     rendering is `rcx = (uint32_t)arg3;` -- the register's *entry* value, read
     from a parameter murmur3 does not have -- so `k1` starts as garbage and the
     tail mixes it into the hash.

     The rule responsible is in the dead-value predicate in
     `fold/op_lower/mod.rs` and its own comment states the condition the code
     omits:

     ```rust
     // Eliminate explicit zeroing idioms when the value is never used
     // beyond setup/flag chains (e.g., eax = eax ^ eax).
     if let Some(expr) = self.definition_for_name(&key)
         && self.is_zeroing_expr(expr)
     { return true; }
     ```

     There is no check that the value is unused, so a zeroing whose result the
     switch reads is dropped anyway.

     Adding `&& self.use_count_of(&key) == 0` is the obvious fix and measures
     inert -- built, corpus unchanged at 37, the line unchanged, reverted.

     And the explanation offered for that is wrong, so do not act on it:
     `use_count_for_name` is *already* value-keyed -- it maps the name to a
     `ValueId` and reads `use_counts_by_value` -- and `count_uses_and_conditions`
     counts phi sources as well as op sources. There is no name-versus-value gap
     here.

     What the inert result actually means is that the zeroing rule is not what
     drops this statement -- and the real answer folds this defect into the
     location model rather than standing beside it.

     `rcx` is a certified carrier in this function, with members `RCX_1`, `RCX_2`
     and `RCX_3` (`CARRIERALIAS member=RCX_1 name=rcx`). The zeroing writes
     `ECX_3`, which is the *32-bit view of that same place* -- `{Register,
     offset 0}` at four bytes against the carrier's eight -- and is therefore not
     in the member set. So the carrier never sees its initialiser, takes the
     register's entry value instead, and `k1` starts as `arg3`.

     That makes murmur3's wrong checksum the same defect as item 0f, not a
     separate one: a narrow write to a carrier's place is not a write to the
     carrier. The `CarrierMemberView` work covers a narrow *phi* beside a carrier
     phi in the same header block; this needs the narrow *write* to count as an
     update of the carrier, which is a change to how carriers are certified in
     r2ssa rather than to how they are rendered in r2dec.

     Two candidates were tried against this line and both measured inert, so
     neither is the way in: guarding the zeroing rule on a zero use count, and
     the name-versus-value theory that guard was based on.

     **Where the change belongs.** Carriers are grown in
     `crates/r2ssa/src/semantic.rs`, in the fixpoint around lines 5178-5250 that
     accumulates `identity_values`, `entries`, `updates` and
     `dominating_initializers` before `function_facts.rs:4165` freezes them into
     a `CertifiedEntity::LoopCarrier`. Membership there is by exact value
     identity, so a write to the place at a different width is invisible to it.
     Admitting such a write as an update -- same `{space, offset}`, smaller size,
     gated on `SsaArtifact::narrow_write_clears_register` so the wide value is
     provably the narrow one zero-extended -- is the change, and it is in the
     semantic layer rather than the renderer.

     One correction to that plan, found by reading the growth code: the carrier
     `rcx` belongs to murmur3's *main loop*, and the `xor ecx, ecx` happens after
     that loop, in the tail. It is not a missing initialiser for the carrier --
     it is the register being **reused** for a different variable once the loop
     is over. `updates` and `entries` are built from the header phi's latch and
     non-latch sources, so a post-loop write was never going to appear there
     whatever width it had.

     That points at the span machinery instead, and reading it explains the empty
     gate. `carriers_spanning_a_reuse` builds its occupant set from
     `carrier_members(carrier)` and then filters those to the ones sharing the
     carrier's storage, so it only ever inspects values the carrier already
     claims. murmur3's `ECX_3` is not a member -- it is the write that *takes the
     register over* after the loop -- so it is not an occupant, the members it
     does see are all in one span, and the carrier is reported as not spanning a
     reuse. The detector cannot see a reuse by a value outside the carrier,
     which is the only kind of reuse there is.

     Asking the question of the *place* rather than of the members does answer
     it, and it is far too broad: extending the occupant set with every value
     whose canonical storage shares the carrier's run takes the corpus from
     **37 to 19**, with x86-64 -O2, arm64 -O1 and arm64 -O2 all falling to zero.
     That is exactly the failure the function's own comment describes -- carriers
     dropped from the name aliases and each loop rendered as the value it held on
     entry. Built, measured, reverted.

     The reason is that *every* register a function reuses anywhere now
     disqualifies its carrier, and a compiler reuses registers constantly.

     A live-range bound is the obvious repair and would not work either, which is
     worth saying before someone builds it: murmur3's `xor ecx, ecx` happens
     *after* the loop, so it is outside the carrier's range by construction. A
     rule that only counts occupants between the carrier's first and last member
     would not see it.

     Which points at the renderer rather than the gate, and dumping the members
     settles what the carrier actually is. All three are the loop counter:

     ```
     RCX_1 = IntZExt(ECX_1)          # i = 0, from the xor at 0x100000821
     RCX_2 = Copy(RCX_1)             # entry
     RCX_3 = RCX_2 + const:1         # increment
     RCX_2 = Copy(RCX_3)             # latch
     ```

     The tail's `xor ecx, ecx` at `0x10000086a` produces `ECX_3`, which is *not*
     among them. So the carrier is correct, the reuse is correct, and the defect
     is that a value which is not a member is nevertheless spelled with the
     carrier's name: two variables share the register, the carrier owns the name
     `rcx`, and `k1` is rendered as `rcx` too -- at which point its zeroing
     statement becomes a write to the carrier and resolves to the carrier's entry
     value.

     Tracing `spell_var` for `ECX_3` answers that and moves the question again:

     ```
     SPELL display=ECX_3 carrier=None var_alias=None param=Some("arg3") base=ecx
     ```

     `ECX_3` is *not* spelled `rcx` -- no carrier alias, no coalesced alias, and
     its own base name is `ecx`. So the `rcx = (uint32_t)arg3;` line is not this
     value's statement, and identifying which SSA value it does assign is the
     next step.

     But the same probe shows something to chase first: `param_alias(ECX)` is
     `Some("arg3")`. murmur3 takes three parameters and is rendered with five
     (`arg0..arg4`), so `ecx` is in `param_register_aliases` only because `rcx` is
     the fourth SysV argument register and parameter recovery claimed a fourth
     argument this function does not have. Any version-zero read of `ecx` then
     renders as `arg3` -- which is exactly what the lost zero looks like.

     Where the five come from, measured rather than assumed:

     ```
     PARAMS params=[arg0..arg4] recovered=[RDI, RSI, EDX, ECX, R8]
     r2 afv:  arg1 @ rdi, arg2 @ rsi, arg3 @ rcx, arg4 @ r8
     ```

     **radare2 itself reports four arguments for this three-argument function**,
     naming `rcx` and `r8` and omitting `rdx` entirely. So the over-recovery is
     partly inherited, not purely ours; our scan adds `EDX` back and keeps r2's
     two spurious ones.

     Why our scan sees `ECX`: `xor ecx, ecx` mentions the register twice at
     version zero, and the scan counts a version-zero mention as an entry read.
     Excluding self-zeroing operations from that scan is the obvious fix and
     **costs a function**: corpus 37 to 36, x86-64 -O2 from 4 to 3, and
     `murmur3_32` still recovers five parameters because r2's own four survive
     the change. Built, measured, reverted.

     So this cannot be fixed on our side of the seam alone. Either the recovered
     set has to be reconciled against something better than r2's `afv` -- the
     ABI plus actual entry liveness -- or the spurious names have to stop being
     usable as spellings for values that merely pass through those registers.
     The second is the smaller change and is where the lost zero actually shows
     up.

     A measurement note that cost an hour here: when `make -C r2plugin install`
     fails -- and it does, intermittently, with `codesign: internal error in Code
     Signing subsystem` -- copying the dylib by hand installs a *mixed* plugin
     and the corpus reads 19 regardless of what the code says. Both the failing
     install and the real regression produce the same number. Always check that
     the install actually printed `Installed to ...` before believing a
     measurement, and re-run it until it does.

     Note that the same width question is asked in a *third* place, which is an
     argument for putting it somewhere shared: `carrier_member_views` in
     `normalize.rs` applies it to header phis, `exit_merges_for_carrier` was
     widened to apply it to exit merges and measured inert because those values
     are not phis either, and carrier growth needs it for writes. All three ask
     the same question -- is this value the carrier's place at another width --
     and all three answer it separately.

     Also still recorded: using the selector value instead of
     `prepared_canonical_value_root` of it changes nothing, because there was no
     selector to root.

  0l. **A deferred merge block is rendered twice on arm64.** This is what
     `murmur3_32` fails on at arm64 -O1 and -O2, two of the sixteen remaining
     failures, and it is the known consequence of an earlier fix on this branch
     rather than a new defect.

     The same two statements appear in both places:

     ```c
     if ((arg1 & 3) != 0) {
         t20380_4 = ... ;          /* line 49, no declaration */
         t20380_5 = ... ;
     }
     long t20380_4 = ... ;         /* line 55, the declaration */
     long t20380_5 = ... ;
     ```

     The first copy reads names the second declares, so the file does not
     compile. `IfThenElse` pushes its merge onto `deferred_merge_blocks` before
     structuring the branches and emits it afterwards, and the
     `merge_owned_by_ancestor` guard that stops a nested construct re-emitting it
     is consulted **only in the `IfThenElse` arm**. A branch region that reaches
     the merge as a plain `Region::Block` has nothing to stop it.

     Applying the guard to `structure_region`'s `Region::Block` arm takes the
     corpus from **37 to 17** -- and it never touched this defect at all, because
     a branch region does not go through that arm. `structure_branch_region`
     routes a `Region::Block` to `structure_block_from_predecessor`, and the
     guard belongs there. Placed correctly it holds the corpus at 37 and halves
     the duplication: `t20380_4` appears twice instead of four times, and the
     merge is emitted once.

     What the duplicate was masking is now visible. The `else` branch returns a
     value the merge computes:

     ```c
     } else {
         long t20380_7 = (uint32_t)(int64_t)t20380_5 ^ arg1;
         return ...;
     }
     long t20380_4 = ...;      /* the merge, after the if */
     long t20380_5 = ...;
     ```

     so `t20380_5` is read before it is declared.

     The check recorded here has been run and it disproves the guess. Both
     branches reach the merge:

     ```
     MERGEREACH cond=0x1000007e8 merge=0x100000820 then=true else=Some(true)
     ```

     So the block really is a merge of both branches, and the mislabelling theory
     is wrong. What is wrong instead is the *extent* of the else region: if both
     branches flow into the merge, the correct shape is

     ```c
     if (cond) { then } else { else }
     /* merge: t20380_4, t20380_5 */
     /* finaliser, return */
     ```

     and what is rendered puts the finaliser and its `return` *inside* the else.
     The else region therefore contains blocks that belong after the merge, which
     is why it reads `t20380_5` before the merge declares it.

     So the question is why the else region extends past its own merge, and it is
     a region-building question. `analyze_conditional` in `region.rs` calls
     `analyze_region_recursive(false_target)` with no bound at all, and
     `analyze_region_recursive_inner` stops only on `self.processed` -- so a
     branch walks straight through the merge unless something has marked it.

     Marking the merge processed for the duration of the branch analysis, and
     unmarking it afterwards so the parent still emits it, is the obvious bound
     and **changes nothing**: corpus 37, and murmur3's `else` still contains the
     finaliser and its return. Built, measured, reverted. So either the branch is
     not reaching the merge through `analyze_region_recursive` at all, or the
     finaliser arrives in the else by some route other than region growth.

     **Why it is inert, read from the code rather than measured:** murmur3 does
     not go through `analyze_conditional` at all. A probe there prints nothing
     for this function, so the `IfThenElse` comes from the other construction
     site in `region.rs`, the bottom-up one that builds a `region_map` and then
     forms conditionals from it:

     ```rust
     let else_region = if Some(false_succ) != merge {
         region_map.remove(&false_succ).map(Box::new)
     } else { None };
     ```

     The else region is *taken already built*. Its extent was decided when the
     region for `false_succ` was constructed, before this conditional existed, so
     bounding branch analysis at the merge cannot affect it -- there is no branch
     analysis here to bound. Fixing this means splitting a pre-built region at
     the merge, which is a change to that algorithm rather than a guard anywhere.

     That inert result has since been re-measured with a verified
     `make install` -- the run printed `Installed to ...` on the eighth attempt,
     the `codesign` fault having failed the first seven -- and it holds: corpus
     37, and `murmur3_32` at arm64 -O1 fails on the same line with the same
     message. The bound is genuinely inert, not a stale reading.

     Practical note for anyone measuring here: `make -C r2plugin install` fails
     intermittently with `codesign: internal error in Code Signing subsystem` --
     sometimes once, sometimes for forty attempts in a row. **A failed install
     leaves the previous plugin in place, so the sweep silently reports the old
     build's number**, which is how two readings in this document were briefly
     wrong. Always loop until it prints `Installed to`.

     When it will not, this fallback is verified equivalent -- it reproduces the
     same corpus number as a successful `make install` on the same tree:

     ```sh
     codesign --force --sign - target/release/libr2sleigh_plugin.dylib
     cp -f target/release/libr2sleigh_plugin.dylib r2plugin/r2sleigh/
     cp -f r2plugin/r2sleigh/libr2sleigh_plugin.dylib \
        ~/.local/share/radare2/plugins/r2sleigh/
     for f in anal_sleigh arch_sleigh; do
       codesign --force --sign - ~/.local/share/radare2/plugins/$f.dylib
     done
     ```

     The last loop is the part that matters and the part an earlier attempt
     omitted: copying only the Rust dylib leaves the two C plugins signed against
     the previous one, and the corpus then reads 19 -- the same number a real
     regression produces. Signing in place works even when signing a fresh copy
     in a temporary directory does not, which is the whole of why the Makefile's
     step fails and this one does not.

     Do not reach for another guard in `structure.rs`: three have now been
     measured there, one at 37 to 17, one that landed, and this check, and each
     addressed a different defect behind the same rendered lines.

  0m. **[FIXED] pearson's return read the loop's exit merge by its own name.**

     ```c
     rcx = (int64_t)0;
     do { ...; rcx = (int64_t)t11e00_3; ... } while (arg1 != rax);
     return (uint8_t)rcx_6;     /* wants `(uint8_t)rcx` */
     ```

     `rcx` is a certified carrier with members `RCX_1`, `RCX_2` and `RCX_4`.
     `RCX_6` is a phi -- it has no defining op -- and is the loop's exit merge,
     but it is not aliased to the carrier, so the return prints a name nothing
     declares.

     `exit_merges_for_carrier` rejects it, and probing the three conditions says
     why:

     ```
     EXITMERGE carrier=RCX_2 cand=RCX_6 all=false any_entry=false any_update=true
     ```

     One of its sources is a certified update, but not all sources are in
     `entries ∪ updates`, and none is an entry. The likely reason is that the
     bypass path -- "the loop never ran" -- carries the value from *before* the
     header phi rather than the phi's own entry source, so it is a different
     `ValueId` and fails the membership test.

     **[FIXED]** The check recorded here was run. `RCX_6` is
     `phi(RCX_4 = ValueId(65), RCX_5 = ValueId(127))` where 65 is a certified
     update and 127 is neither an entry (42) nor an update. Admitting
     `dominating_initializers` alongside `entries` -- the narrow fix this item
     proposed -- does not help: 127 is not one of those either.

     What the bypass edge carries is simply "the loop never ran", and there is no
     reason for that value to be one the carrier certified. The test now asks
     only what identifies an exit merge: a phi over the carrier's storage with
     one of its updates on one edge and something else on the other. Corpus
     **37 to 38**, pearson at x86-64 -O1 returns `0d` and is correct, and no
     configuration regresses.

     This widened a gate whose comment warned against widening it. That warning
     was about a different axis -- claiming merges in unrelated *storage*, which
     the size and storage checks above still prevent -- and not about which
     values the non-update edge may carry.

  0n. **[FIXED] A single-use propagation counted readers in one list only.**
     `propagate_single_use_register_carriers` substitutes an assignment into its
     one reader and deletes it, and it counted readers only in `rest` -- the
     remainder of the statement list it is walking. A value computed in one block
     and read in a later one is read once *there* and many times overall, so the
     pass deleted it and left the reader quoting a name nothing declares.

     The pass already carried this mistake once. The `if in_loop { return; }`
     guard above the loop explains that "the rest of this list" is not all the
     readers, because a carrier is read again on the next iteration. The same is
     true across sibling blocks and enclosing scopes; the count is now taken
     against the whole function body as it stood when the pass began.

     adler32 at x86-64 -O2 was the case that showed it: `ecx_9` is computed in
     the tail and returned, `use_count_of` reported nine readers, and the
     statement was still removed. It now compiles and runs, returning `894a1488`
     against a wanted `9dd21488` -- the low half, the `a` accumulator, is correct
     and `b` is not.

  0g. **murmur3's tail switch renders with empty bodies.** This is what arm64 -O0
     `murmur3_32` now fails on, and the undeclared `x8_30` is a symptom of it
     rather than the defect. The rendering is

     ```c
     if ((arg1 & 3) != 1) {
         if (local_68 == 2) {
         } else {
             if (x8_30 == 3) {
             }
         }
     ```

     -- the three tail cases of `switch (len & 3)`, all with their bodies
     dropped. `x8_30` has no definition, no copy source and no rendered spelling
     (`def=None copy=None spelling=None`), and the unkeyed-write counter reports
     zero, so nothing was written under a name that could not be keyed: the facts
     were never recorded because the statements that would have carried them were
     elided. Do not fix the undeclared name; find why the case bodies are empty.

  0e. **Superseded: arm64 -O0 renders frame accesses as pointer arithmetic.** This is what both arm64 -O0 failures are now, after
     the argument-register and frame-record fixes above, and it is bigger than
     either of them.

     The same source function at the same optimisation level renders

     ```c
     long local_20 = arg2;                                  /* x86-64 -O0 */
     *(int32_t *)(long)(t11f80_1 - 0x14) = arg2;            /* arm64 -O0  */
     ```

     where `t11f80_1 = local_70 + 96` is the frame base itself, used as a value
     and never declared. The stack-address roots are present -- a trace at the
     store-elision gate reports `is_slot=true` with concrete offsets for these
     addresses -- so the offsets are known and it is the *names* that are
     missing. A dump of `stack_aliases_by_offset` for `murmur3_32` on arm64 held
     exactly one entry, and that one was created by the argument-home store scan
     rather than by r2's variables. r2 itself reports ten stack variables for
     that function (`afvs 96 var_60h`, `afvs 20 var_14h`, and eight more), so
     the ingestion from r2's sp-relative offsets into the frame-relative space
     the map is keyed by is what to look at first. Confirm the map is empty
     before assuming it, since the dump above predates the two fixes.

     Note for whoever picks this up: completing the frame-setup rule set in
     `is_stack_frame_op` is *not* it. `fp = sp + const` is genuinely missing
     there -- x86-64 establishes its frame pointer with `mov rbp, rsp` and is
     caught by the Copy arm, while arm64 writes `add x29, sp, 0x60` and matches
     nothing -- but adding it changes no rendered output, because Sleigh routes
     the add through a temp and eliding the add would not remove the uses of
     that temp. It was written, measured inert, and reverted.

  0c. **Superseded trace notes for 0a.**
     Both arm64 -O0 failures are this, and only this. The first statement of
     `murmur3_32` is

     ```c
     (((unsigned char *)(long)(arg2))[1]) = x30;
     ```

     which is the prologue's frame-record save, `stp x29, x30, [sp, 0x60]`, where
     the frame is `sub sp, sp, 0x70` and `add x29, sp, 0x60` follows. It appears
     only in non-leaf functions: `fnv1a32` and the other six correct arm64 -O0
     functions are leaves, never establish `x29`, and stay entirely sp-relative.

     The trace runs: `render_canonical_store_target_expr` is handed
     `addr=tmp:3a600_1`, whose raw definition is `AddrOf(Var(81)) + 8` with
     symbol 81 spelling `arg2`. Following that back, `resolve_stack_var(-0x10)`
     answers `arg2` from all three of its sources at once --
     `prepared=Some("arg2") external=Some("arg2") map=Some("arg2")` -- so this is
     not a precedence bug between them. The offset is what is wrong.

     Two offset spaces are in play and are being mixed. r2 names the third
     argument `arg3 @ x2` and reports `var_60h @ sp+0x60`; the plugin renumbers
     to `arg0..arg2`. In x29-space, `x29 - 0x10` is where r2's `arg2` (`x1`) is
     homed, which is why `-0x10` resolves to that name. The store being resolved
     is at `sp + 0x68`, which is `x29 + 8` -- offset zero plus eight, not
     `-0x10` plus eight. So the base was selected in one space and the
     displacement applied in another.

     What is *not* yet established is which producer writes that definition.
     `insert_definition_for_var`, the `SSAOp::Store` arm of `op_to_stmt_impl`,
     `render_call_arg_addr_for_definition` and the `stack_slot_addr_alias`
     closure in `resolve_visible_stack_addr` were each instrumented and none of
     them fires for this value; the definition arrives through some other route
     into `lookup_definition_raw`. Name that route before changing anything --
     `resolve_stack_var` already has a `saved_fp` name for exactly this slot, and
     an external r2 name is allowed to override it at `fold/stack.rs:778`, which
     is a tempting place to put a guard that would not be the cause.

  0b. **[FIXED] A value had two spellings, and the condition minted its own.**
     `resolve_prepared_predicate_operand_with_width` holds the operand as an
     `SSAVar` and was converting it to a display name for `origin_name_to_expr`,
     which mints from the raw string when the reverse index misses. That is how
     `tmp:4700_7` printed as `t4700_7` in the statement defining it and
     `tmp_4700_7` in the condition reading it, with the statement then dropped as
     dead because nothing appeared to read it.

     Fixed by `origin_operand_expr`, which asks `var_ref` for the value -- the
     same call the statement makes -- but only when nothing else already names
     it: no stack slot, no coalesced alias, no carrier, not a constant. That
     guard is the whole difference between this and the attempt that took
     x86-64 -O0 and arm64 -O0 from seven correct to zero: a stack-lifted value is
     named by its slot from the stack facts, not by `spell_var`, so routing
     *those* through `var_ref` prints the temporary they were lifted from.
     Paired with `sym_for_var` returning the identifier already minted for a
     value when the spelling matches, so the two sites converge on one name
     instead of the reverse index erasing itself.

     Measured: `tmp_4700_7` and `tmp_11f80_4` are gone from all three
     configurations that had them, `long t4700_7 = rdi + 4;` is emitted and read
     by its own condition, and every failure that was this defect advances to a
     different cause -- x86-64 -O1 to `eax_4` (the narrow-carrier-member cluster),
     x86-64 -O2 to a struct type error, and arm64 -O1 xxhash32 all the way to
     compiling and running, where it now returns 6c5cba44 against a wanted
     e7583aa4. Corpus holds at 36 of 54: three functions moved forward, none
     over the line.

     A value lifted into a stack local has both names: `local_28`, its rendered
     spelling, and `tmp:11f80_2`, the temporary it came from. Note that the
     example line this item used to quote,
     `for (int64_t local_28 = 0; t11f80_2 < arg1; ...)` in `fnv1a32`, no longer
     reproduces: the current tree renders `local_28 < arg1` there and `fnv1a32`
     is CORRECT in all six configurations. The defect survives as `tmp_4700_7`
     and `tmp_11f80_4` in xxhash32. Which is correct
     depends on context, and that context lives in `var_aliases`, a map each
     reader consults for itself. Any route that reaches the value without going
     through that map prints the wrong one.

     Three separate attempts to unify the spellings have failed on this same
     value, and all three failed for this reason: spelling at the mint, spelling
     at `origin_name_to_expr`, and recording which value an identifier renders at
     the analysis mint sites. Each takes x86-64 -O0 and arm64 -O0 from seven
     correct to zero, and each produces the same wrong line --
     `for (int64_t local_28 = 0; t11f80_2 < arg1; ...)`. The incremental path is
     ruled out too: making `definition_for_symbol` ask both routes is safe on its
     own and does not make the recording safe, because a third reader,
     `ssa_name_for_spelling`, exists precisely to resolve differently.

     **Why `for_ssa_name` does not rescue it.** `origin_name_to_expr` already asks
     the reverse index before minting, and the index is empty by the time it
     asks -- because it erases itself. `SymbolTable::declare` *uniquifies* rather
     than interning, so every request for a spelling mints a fresh `SymbolId`,
     and `note_ssa_name` deletes the index entry as soon as a second id claims
     the same SSA name. In xxhash32 at x86-64 -O1 the flag path mints an id for
     `tmp:4700_7` first, and the five later sites that mint `t4700_7` for the
     same value then remove the entry that would have connected them.

     Two things were tried against this and both are ruled out by measurement,
     not argument. Spelling the origin the way the renderer spells it cannot
     work, because `name_ref` goes through `declare` and would mint a *second*
     symbol spelled `t4700_7_1` rather than reaching the first. Making
     `sym_for_var` reuse the existing identifier when the requested spelling
     matches does stop duplicate-spelling mints from destroying the index, but
     it changes nothing here and nothing in the corpus -- the two spellings
     differ, so they were never going to collide on spelling. Written, measured
     inert, reverted.

     **The interface change was built, measured, and reverted -- and it named the
     next component.** `resolve_prepared_predicate_operand_with_width` already
     holds both `var` and `rooted` as `SSAVar`s and converts them to display
     names for `origin_name_to_expr` (the call is `flags.rs:887`, confirmed by
     tracing the caller of the mint). Resolving by value instead -- an
     `origin_var_to_expr` that calls `var_ref` -- together with the `sym_for_var`
     reuse above is the pair that makes the condition and the statement reach one
     identifier.

     Measured: **36 correct down to 22**, with x86-64 -O0 and arm64 -O0 each
     going from 7 to 0, and the line is the one this document has recorded three
     times:

     ```c
     for (long local_28 = 0; t11f80_2 < arg1; local_28 = t6b00) {
     ```

     That reproduces deterministically now, so the historical measurement was
     real rather than a sample of the nondeterminism fixed in 0h.

     Why it fails is now precise. `var_ref` spells through `spell_var`, and
     `FoldingContext`'s `NameSource::var_alias` consults only
     `var_aliases_map()`. The loop variable here is a *stack-lifted* value whose
     rendered name `local_28` does not live in `var_aliases` at all -- it comes
     from the stack facts, which the spelling path cannot see. So resolving the
     origin by value is right for a temporary and wrong for a stack local: it
     spells the temporary correctly and the stack local by its temp name.

     The third was then built on its own and measured too. `NameSource` gained a
     `stack_alias` hook, consulted by `spell_var` after `var_alias`, answered by
     `FoldingContext` from `stack_slot_for_name` and restricted to `Scalar`
     slots so an address-like value could not lose its `&`. It reaches **the same
     22**, and the loop header it was aimed at is *fixed* --
     `for (long local_28 = 0; local_28 < arg1; ...)` -- while a different line
     breaks: `local_1c = t11e00 ^ t11f00_2;`, where `t11f00_2` is now undeclared.
     A value that used to spell `t11f00_2` now spells `local_1c`, and the other
     value that shared that spelling does not, so a pairing that held by accident
     comes apart.

     **That is the finding, and it is the important one.** Three different
     partial applications -- spelling at the origin, resolving origins by value
     with identifier reuse, and adding a stack source to the speller -- each land
     on exactly 36 down to 22. The spelling layers are an additive ladder of
     fallbacks (`carrier_alias`, then `var_alias`, then `param_alias`, then a
     base name), and values that agree today often agree because they fall
     through to the *same* rung, not because anything decided they were the same.
     Adding a source to any rung re-sorts that agreement and desynchronises
     values that were previously consistent by accident.

     So the fix cannot be another fallback, however well-founded. It has to
     replace the ladder with one decision. That was then built and measured too,
     and the measurement corrects the instruction.

     A `decided_name` hook was added to `NameSource` and consulted by `spell_var`
     before anything else, answered by `FoldingContext` from the value's
     *canonical* var so that every SSA name for one value spells the way that
     value spells, decided once and memoised. It holds the corpus at 36 -- the
     first structural naming change here that does not collapse -- and the
     failure list is byte-identical. Instrumenting it explains why: over a whole
     function it fires **zero** times. `prepared_var_for_value_id` returns the
     var that asked, every time.

     **Value and var are one-to-one here.** "One name per value" is therefore
     already true at the var level, and was never the problem. The two spellings
     of `tmp:4700_7` are not two vars for one value; they are *one var spelled
     twice by different code paths* -- `spell_var` on one side, a mint from the
     raw display string in `origin_name_to_expr` on the other.

     That narrows the target and also sharpens the earlier 22. When the flag path
     was made to go through `var_ref`, and so through `spell_var`, it printed
     `t11f80_2` for the loop variable while the statement printed `local_28` --
     so the *statement* is not going through `spell_var` either. There are at
     least two things that turn a value into a rendered name, and they disagree.
     The single decision has to be at the level of "what renders this value",
     not "which var names it"; the ladder is one of the two producers, not the
     whole of the problem. Finding the second producer -- what gives a stack
     local its `local_28` -- is the next step, and it is a smaller question than
     the ladder rewrite this item previously called for.

     What is known to work is narrower and already landed: `for_ssa_name` lets a
     caller holding a raw SSA name reach the identifier already minted for that
     value, and `post_rename` no longer renames a value name into a storage name.
     Both are safe because neither changes which spelling wins.

     The fix is *not* that readers consult the alias map -- `spell_var` already
     does, asking `source.var_alias(&display)` before it falls back to a base
     name. A probe on that path shows `LowerCtx::var_name` answering `t11f80_2`
     for `tmp:11f80_2`, which means it asked and the map had nothing: the alias
     `local_28` is not known yet when the analysis lowering names that value.

     So this is an **ordering** problem rather than an ownership one. Aliases are
     established after the lowering that spells values has already run, and every
     later route that reaches the value by its SSA name finds the spelling that
     was chosen before the alias existed. Recording links, unifying spellings or
     re-keying stores all leave that ordering untouched, which is why all three
     regress on the same line.

     What wants doing is that a value's alias is settled before anything spells
     it. That is the same statement as the location model's -- one name per value,
     decided once -- and it is why naming registers by place regresses 34 correct
     to 13 while this is outstanding.

  1. **The same value is constructed more than once, by different layers, and
     nothing says which construction is the value.** The **call** instance of
     this is now **fixed**: `CExpr::Call` carries the site that makes it,
     `single_evaluation` asks which site an expression is rather than comparing
     shapes, and a bare statement for a site it has bound is dropped. A
     three-call function renders each call once, correctly, where it previously
     rendered each twice under two spellings.

     The **resolver** instance below is still open, and the worked example above
     does not transfer directly -- see the note after this list. Measured:

       * a call site has **three** expressions -- `fold/op_lower/lowering.rs:94`
         for the statement, `fold/op_lower/mod.rs:2962` for the expression, and
         `use_info().call_result_exprs` in the analysis layer -- and
         `single_evaluation` matches sites by expression equality against the
         third, so it binds one and leaves the others. That is the duplicate
         call, and every fix attempted at that seam failed for this reason.
       * a value has nine resolvers that will each answer for it with their own
         precedence, so closing one hands the question to the next. That is
         `sum32`, which still returns what its accumulator held before the loop.

     The contract to state is that **a rendered expression is an answer, not a
     candidate**, and the work is to make one construction own each value. Item 2
     below was previously listed separately and is the same defect.
  2. *(folded into 1)* One call renders twice under two spellings.
  3. **The width layer.** A carrier written narrower than its phi -- `w8` into an
     `x8` carrier, `EAX` into `RAX` -- is not reconciled, which is what blocks
     the x86 accumulator loops and step 4's repair-pass work.
  4. **The 64-bit constant model.** A folded 16-byte constant has nowhere to
     live, which caps whole-register vector reads. The chosen shape is a wide
     literal in the AST; it is downstream of the tile composer, which is
     downstream of emission.
  5. *(done)* **Budget as ledger.** A phase that ran out of budget discarded its
     partial rendering, so a function that ran out of time reported as one that
     produced nothing, and the ledger that would have said otherwise went out
     with the rendering.

     `Decompiler::decompile_input_keeping_partial` keeps what a rendering-phase
     stop had reached -- the C function is built by then, so generating it is
     what the caller wanted -- and `render_engine_decompile_request` returns it
     together with the stop. A stop while normalizing still has no body to keep
     and still falls back to a comment.

     The stop is not softened by keeping the body. The phases that finished are
     folded and the one that stopped is refused, exactly as the discarded path
     recorded; the route reason and the refusal both state the stop; and a
     warning says the body is what was reached. What changed is only that the
     reader gets it. The obligation ledger now prints against a stopped run --
     `2 source obligations: 1 built, 0 elided, 1 refused` -- which is the
     accounting this item existed to make possible.

**Does the call fix transfer to the resolvers?** Only partly, and the difference
is worth stating. The call defect was a *recognition* failure: two expressions
were the same call and nothing could tell, so giving a call an identity made the
sameness visible and a four-line fix followed. The resolver defect is a
*precedence* failure: nine resolvers can each answer for one value and they
disagree about which answer is better, and every one of them is looking at the
same value already. An identity does not settle a disagreement.

What does transfer is the method: do not guard each site. Four carrier guards
were built at four resolvers and each moved the answer to the next one, exactly
as the six call-seam fixes did. The equivalent move for the resolvers is to make
the wrong answer unrepresentable -- a value that is mutable state should not have
a resolvable expression at all, rather than having one that every resolver is
asked to decline.

**This is the shape of nearly everything left.** Five instances have been found:
symbol tables and `UseInfo` builders, both fixed by making one own the answer;
and expression resolvers, callee construction and call expressions, all three
scoped above. Each surfaced as a rendering bug that looked unrelated until it was
counted. Look for that shape first, and count before theorising -- five mechanisms
were reasoned out on the call duplicate alone and all five were wrong.

### The ledger cannot close before the location model

The ADR sequences the ledger first, on the argument that the location model
cannot be scored without it. Measurement says that ordering does not hold, and
the reason is worth stating because it moves work rather than adding it.

`Outcome::Rendered` is recorded when the fold *builds* an expression for an
operation site. Structuring and cleanup delete statements afterwards and nothing
revisits the claim, so `sym._siphash24` at x86-64 -O0 reported 1693 of 1754
obligations rendered with five lines on the page -- the highest claim in the
corpus attached to its worst rendering.

Witnessing a claim means asking whether the value a site produces is one the
finished body still names. A probe for that now runs under
`R2SLEIGH_DEBUG_UNOWNED` and reports `WITNESS fn=... claimed-rendered=N
witnessed=M body-statements=S named-values=V`. Measuring it settled the design:
`named-values=0` on every function measured, honest and hollow alike. There are
**230 `var_ref` call sites and three `declare_value` ones**, and `origin.value`
had no reader in the crate at all. `SymbolOrigin` was built for this and never
wired.

Wiring it is not the fix. A rendered name such as `x8` stands for a carrier that
many `ValueId`s write, so one `origin.value` cannot say what the name means, and
the one-to-many is one-to-many *precisely because* SSA is over varnodes rather
than locations. A name stands for a location; once locations exist, name to
location to the instructions writing it closes the ledger correctly. Before they
exist there is nothing sound to witness against.

**So the ledger's closure invariant is downstream of the location model, not
upstream of it.** What is achievable now, and is done, is to stop the line
claiming what it cannot show: the column reads `built`, and the statements the
body holds are printed beside it. The remaining work is one assertion once
locations land.

The corpus is the instrument in the meantime, and it is the better one: it
measures rendered output against source directly rather than asking the
decompiler to report on itself.

### x86-64 -O2 renders an unrolled loop and its remainder as two variables

`fnv1a32` at x86-64 -O2 is compiled as a four-way unrolled loop with a remainder
loop after it. Both bodies render **correctly** -- the unrolled one chains
`arg0[i]`, `(arg0+1)[i]`, `(arg0+2)[i]`, `(arg0+3)[i]` through the FNV multiply
-- and they use two different accumulators:

    do { ... rax = (int64_t)(uint32_t)t4c780_5; ... }        the unrolled loop
    do { ... rax_1000005f0 = ...; }                          the remainder

Nothing ever gives `rax_1000005f0` the value `rax` reached, so the remainder
starts from nothing. `carrier_name_aliases` is what names them apart: two
carriers over one register are two variables and the second takes a
header-suffixed name. That is right when the loops are independent and wrong
here, where one continues the other.

Detecting the continuation through the second carrier's `entries` -- looking each
entry value up in the aliases built so far -- was tried and is inert. The link
between the two carriers is not through `entries`, so the next question is what
does connect them: the exit merge of the first, the `updates` of the second, or
neither, in which case the certification treats them as unrelated and that is
where to look.

The same rendering had a second defect, since fixed: the unrolled loop's
condition read `while ((arg1 & -0x4) != 0)`, because `expand_predicate_vars`
resolved the counter through its definition. Both are now right, and what
remains on that configuration is a third, smaller thing.

`djb2` renders `31d5859a` against `31d585ac`, and `sdbm` `86d9741d` against
`86d9742f` -- off by one byte's contribution. The tail loop's preheader is

    rdi_1 = arg0;
    rdx = 0;

and the pointer has lost its offset: after the unrolled loop the remainder
starts at `arg0 + (arg1 & -4)`, not at `arg0`. So the tail re-reads the first
bytes of the buffer instead of the last few. The counter reset to zero is
consistent with a re-based pointer and is not itself wrong.

That is the entry value of the tail loop's pointer carrier, which is the same
family as everything else fixed here, and the arithmetic connecting the two
loops is what goes missing. Three renderings on that configuration are one
addition away.

### Four renderings have no return at all, and the loop above it is correct

The harness scored these as wrong values. They are not: a non-void function that
falls off the end leaves whatever was in the return register, and two unrelated
functions both produced `f7c33760` that way. The harness now reports `noreturn`
as its own verdict, which is what made the class visible -- four renderings, one
per configuration except x86-64 -O0 and -O2.

`fnv1a64` at arm64 -O0 is the clearest. Its loop is **exactly right**:

    local_18 = local_18 ^ arg0[i];
    local_18 = local_18 * 0x100000001b3;

and the function ends without returning it. The exit block folds to zero
statements, and the accounting says why:

    NORMOP block=0x100000648 idx=1  kind=Load   dst=X0_1   srcs=[tmp:6500_11]
    NORMOP block=0x100000648 idx=10 kind=Return dst=None   srcs=[PC_1]

    PROOFSITE idx=0,1,2,5,9      ELIDEDSITE idx=3,4,6,7,8

**idx 10 has neither a proof nor an elision.** The `Return` op produces no
statement and nothing accounts for it -- it is one of the eight unaccounted
obligations the proof line reports for this function.

Its target is `PC_1`, which is the link register: on arm64 -O0 the return
address is what `ret` reads, and the return *value* is in `X0_1`, loaded two ops
earlier.

Two candidates are ruled out. `op_to_stmt_impl`'s `Return` arm is

    SSAOp::Return { target } => Some(CStmt::Return(Some(...)))

which never yields `None`, so the statement is not declined there. And
`exit_block_is_control_only_epilogue` is false for this block, because its first
op is `IntAdd dst=tmp:6500_11` and that arm requires the destination to be the
stack pointer.

`fold_block` does **not** skip it either. Tagging all twelve of that function's
`continue` sites shows which ops leave early:

    FOLDSKIP idx=1 at=5   idx=2 at=11   idx=3,4,6,7,8 at=10   idx=9 at=11

and idx 10 is absent, as are idx 0 and idx 5. So three ops -- including the
`Return` -- reach `op_to_stmt` and produce statements, while `folded_block_stmts`
reports the block as empty.

**That is the fork to take next**: `fold_block` returns statements and the
structurer reads none. `folded_block_stmts` consults `folded_block_cache` before
folding, so either a cached entry for this block was stored empty by an earlier
pass, or two folding contexts are in play and the one that folded is not the one
that was asked. This branch has already found a function existing in two
versions and a map computed against the wrong one; a cache keyed per block is
the same shape.

Print `folded_block_cache`'s hit or miss for this address alongside the
statement count, and whether the two contexts share an identity.

Worth four cells, and the loops behind all four are already correct.

### x86-64's remaining failures are the narrow read, and arm64's were not

This explains the asymmetry in the corpus. arm64 went from no correct renderings
to eleven on naming fixes alone; x86-64 went from four to seven and has not moved
since. The reason is visible in one probe.

`fnv1a32` at x86-64 -O1 renders a **completely correct loop**:

    rax = 0x811c9dc5;
    do {
        rax = (arg0[rcx] ^ rax) * 0x1000193;
        rcx++;
    } while (arg1 != rcx);
    return 0x811c9dc5;

and returns the seed. `fnv1a64` and `djb2` do the same with their own seeds --
three of that configuration's failures are one defect. The loop header carries
both phis:

    MERGEPHI dst=EAX_1 size=4 carrier=false
    MERGEPHI dst=RAX_2 size=8 carrier=true

`EAX` and `RAX` are one location read at two widths, and only the wide one is
certified as a carrier. The function returns thirty-two bits, so the return
reads the narrow phi, which is not a carrier, and falls back to what it held on
entry.

That is the defect this branch was opened for, stated in the first paragraph of
this document, now measured on a live corpus. **It is not reachable by naming
fixes**, which is why x86-64 stopped improving while arm64 did not: arm64's
narrow reads go through the repair pass, which is wrong in other ways but does
reconcile them, and x86-64's do not.

So the corpus splits cleanly. Everything naming-shaped has been taken; what is
left on x86-64 is the location model and nothing else will move it.

**Two steps toward it, both landed and both inert.** A phi at the same header
over the same *location* at a narrower width was added to the carrier alias map,
and the probe confirms it lands:

    FOLDALIAS member=EAX_1 name=rax

The return resolver's carrier branch was then pointed at that map -- it checked
`var_aliases` only, so a value that is a carrier never took it. Together these
should make the return read `rax`, and the rendering does not change.

What that leaves: `merged_return_register_candidate_for_block` keeps
`EAX_1` (its guard does accept `eax` on a 64-bit target, contrary to a first
reading), the carrier branch now fires, and `spell_var(EAX_1)` answers `rax` --
yet `preferred_return_candidate` still prefers the constant already in `best`.
**The preference function is the next thing to print**, and it is the fourth
distinct component on this one return.

A third was then added: for a return, a carrier reference beats a constant,
because a carrier is mutable state and any constant for it is a value it held on
one path. With all three in place the probe shows the carrier reaching the
preference and being recognised:

    RETIN cur=[UIntLit(2166136261)] cand=[rax carrier=true]

and the rendering still returns the seed, because a **later** call arrives with
the constant on both sides:

    RETIN cur=[UIntLit(2166136261)] cand=[UIntLit(2166136261)]

So another producer supplies this return and wins without passing the carrier
branch at all. That is the sixth component on one return --
`merged_return_register_candidate_for_block`, the carrier branch inside it,
`spell_var`, `resolve_return_candidate_in_context`, the preference, and now
whatever else offers a candidate.

All three reverted, being attempted fixes rather than consolidations. Each is a
correct statement: a narrow phi over a carrier's location is the carrier, the
return resolver should consult the carrier map, and a carrier beats a constant.
That print was taken. Two sites offer a candidate, both inside
`merged_return_register_candidate_for_block`, and in this order:

    RETCALL from=return_resolver.rs:526 cur=[-]        cand=[UIntLit(2166136261)]
    RETCALL from=return_resolver.rs:519 cur=[UIntLit]  cand=[rax]

The constant lands first and the carrier is offered against it, so the
preference is decisive -- and applying only the carrier-beats-constant rule
still renders the seed. `merged_return_register_candidate_for_block`'s answer is
not what reaches the page: `op_lower/mod.rs:12825` takes `last_ret_value` first
and, failing that, passes the merged answer through
`resolve_return_target_expr`, which resolves again.

**That is seven components deciding one return value**, each able to override
the last: the two offering sites, the carrier branch, `spell_var`,
`resolve_return_candidate_in_context`, the preference, `last_ret_value`, and
`resolve_return_target_expr`. Every fix attempted at any one of them is correct
and inert, because the next one along re-decides.

This is the clearest case in the tree for the contract the ADR states as **a
rendered expression is an answer, not a candidate**. It cannot be fixed by
guarding a component; the seven have to become one, and that is the work. Four
correct changes are reverted waiting on it: the narrow-phi alias, the return
resolver consulting the carrier map, the carrier-beats-constant preference, and
`refresh_stale_operands`.

### arm64 -O0's four remaining failures are one spelling island

`fnv1a32`, `fnv1a64`, `sdbm` and `crc32_bitwise` at arm64 -O0 all fail on an
undefined `x9_3`, which is the loop counter loaded from its frame slot. The fold
emits the load and the use with **two different names for one value**:

    FSTMT 2 target=t5a00_2 reads=["local_20", ...]     the load, under the temporary's name
    FSTMT 3 target=t7100_2 reads=["x9_3", ...]         the use, under the register's name

and the two are the same value:

    RESOLVE key=tmp:5a00_2 via=forwarded source=X9_3

The SSA is `X9_3 = Load(tmp:6800_4)`. Five sites mint `x9_3` and all five spell
it identically, so this is not the display-name-as-spelling defect fixed earlier
-- the spelling is right on both sides. What differs is *which* of the two names
for one value each side chose: the definition took the forwarded temporary's,
the use took the register's.

That is the matched-pair problem stated as concretely as it has been. The rule
recorded earlier holds: a spelling site can only be fixed together with whatever
defines the value it spells, and here the two are visible in adjacent
statements. Worth four corpus cells.

**Two attempts at it, both reverted.** Reading the forwarding backwards -- a
value with no definition renders as whichever defined value was forwarded *from*
it -- is the obvious move and it fails twice over. In the fold's `get_expr` it is
inert, because `BARENAME` fires at `analysis/lower.rs:223` and the name is
produced by the analysis resolver, not that one. Moved to the analysis resolver
it takes x86-64 -O0 from six correct to three and leaves arm64 -O0 unchanged.

So the reverse link is not the answer even where it is the right resolver. On
x86-64 the same shape of pair exists and the *other* half is the one with the
statement, so following the link the same way moves the name off its definition
rather than onto it. Which of a forwarded pair carries the statement is not
fixed, and nothing in the pair says which.

That is the third time a change of this class has regressed rather than merely
failed, and the standing rule from those is unchanged: measure the corpus around
every single-site change here, never batch two, and expect the direction of a
link to differ between targets.

### djb2's hang on arm64 is the repair pass, not a fourth carrier defect

With the snapshot fix landed, arm64 -O2 `fnv1a32`, `fnv1a64` and `sdbm` are
correct and `djb2` still does not terminate:

    do {
        int64_t x0 = arg0 + 1;
        x8 = (uint32_t)0x1505 + ((uint32_t)0x1505 << 5) + *arg0;
        x1 = arg1 - 1;
    } while (x1 != 0);

All three carriers read their entry values, so nothing converges. The fold's
output for that block says why:

    FSTMT 0 target=tregalias:1000005b8:0:0_1 reads=["tregalias:1000005b8:0:0_1"]
    FSTMT 2 target=tregalias:1000005b8:4:0_1 reads=["tregalias:1000005b8:4:0_1"]

Two of the twelve statements are the register-alias repair pass's synthesised
temporaries assigning **themselves**. `djb2`'s loop opens with
`add w8, w8, w8, lsl 5`, a shifted-register operand, which is what puts the
repair pass on this path where `fnv1a32`'s loop does not.

So this is not a fourth carrier-naming defect to chase. It is the pass the ADR
schedules for deletion in step 4, whose synthesised names are the `tregalias`
identifiers already recorded as leaking into output, reached from a new
direction: they do not merely leak, they are self-referential, and a carrier
whose update depends on one falls back to its entry value.

That makes `djb2` at -O1 and -O2 a second falsification test for the location
model, alongside deleting the pass: when narrow reads are expressed at
construction, this loop should terminate.

### A carrier's one name cannot express a value read across its own update

arm64 -O2 `fnv1a32` renders

    do {
        x8++;
        x0 = (x0 ^ *(int8_t*)x8) * 0x1000193;
        x1--;
    } while (x1 != 0);

which hashes `p[1..n]` where the program hashes `p[0..n-1]`. Every arm64
accumulator loop is wrong by one byte for this reason, and the SSA is not:

    Copy    tmp:7400_1 <- X8_0        save the address
    IntAdd  X8_1 <- X8_0, const:1     post-index writeback
    Load    tmp:25400_1 <- tmp:7400_1 load through the saved copy

The load reads the *pre*-increment address and says so. What is lost is that
`X8_0` and `X8_1` are both members of the carrier and both spell `x8`, so
inlining the saved copy's definition into the load yields `*x8` -- and by then
`x8` holds the incremented value. A single name cannot say "the value this had
before the statement above".

Keeping the copy was tried, by declining to treat a copy into a temporary as a
redundant carrier self-copy. Inert: the copy is not dropped by that rule, it is
inlined, and the inlining is what collapses the versions.

So the constraint is on the naming, not on any one pass: **a carrier member
whose value is read after a later member of the same carrier is defined cannot
render as the carrier's name.** It needs a name of its own, which is exactly the
temporary the lifter already made and the fold already has. `carrier_name_aliases`
maps every member to the carrier name unconditionally and has no notion of a
member being superseded before its use.

That is an ordering property, and it is the same property the location model
needs for a different reason: a value read at one width across a write at
another. Both want the members of a storage to be distinguishable when the
program distinguishes them, and identical when it does not.

**Narrowed once more, with two more inert attempts.** The saved address is not a
carrier member -- `CARRIERALIAS` lists `X8_1` through `X8_4` and no `tmp:7400`
-- so excluding snapshot copies from the alias map changes nothing, and neither
does declining to treat a copy into a temporary as a redundant self-copy. Both
reverted.

The ops are

    Copy    tmp:7400_2 <- X8_2
    IntAdd  X8_3 <- X8_2, const:1
    Load    <- tmp:7400_2

and `tmp:7400_2` has exactly one use, so `should_inline` skips its statement and
the load inlines it to `X8_2`, which spells `x8` -- the same name `X8_3` spells.
Keeping that statement is the fix, and it renders

    t7400_2 = x8; x8++; ... *t7400_2

which is correct. So the rule wanted looked like an *inlining* constraint. It was built --
`should_inline` declining a value whose producer is a `Copy` from a carrier
member that a later member supersedes -- and the probe confirms it fires:

    CROSS key=tmp:7400_2 producer=Copy{..} src=X8_2 alias=Some("x8")
    CROSS key=tmp:7400_2 source_version=2 answer=true

The rendering did not change, because the decision is not taken there. The load
resolves its address through `get_expr`, which answers before reaching the
inline check:

    GETEXPR key=tmp:7400_2 answer=Var(..)

and the name it returns is the carrier's, not the temporary's own `t7400_2`.
The branch that gets there first is the **semantic value**: the saved address is
recorded as equalling `x8`, which is true at the copy and false after the
increment.

**Semantic values are timeless and a carrier's identity is not.** That is the
third table to answer for a carrier this way -- the recorded definition and the
forwarded value were the first two, and both already decline for a carrier
member. The semantic value does not, and it is the one that decides here.

That was built too -- the snapshot declining to inline *and* `get_expr`
returning it as itself, both together, because declining one table leaves the
others answering. Still inert, and the reason is a sixth table:
`render_canonical_load_expr_uncached` returns from
`prepared_named_memory_expr_for_value` or `render_authoritative_memory_access_by_name`
**before it ever uses the address expression**. The load never asks `get_expr`
about its address on the path that wins.

**Five interventions on this defect, every one inert, every one written before
the probe that would have ruled it out.** The tables that can answer for a
carrier snapshot now number six: the recorded definition, the forwarded value,
the semantic value, the fold's `get_expr`, the inline decision, and the memory
renderer's own two entry points. Suppressing any subset is indistinguishable
from a wrong fix while another answers.

That probe was then taken, and it narrows the defect to one line while leaving
one question open.

    LOADEXPR addr=tmp:7400_2 by_dst_or_addr=false fallback_rendered=false
             fallback_addr=Var(SymbolId { index: 13 })

Both memory-renderer branches decline, so the load *does* use `get_expr(addr)`.
Re-applying the snapshot guard with the probe running shows it firing and
returning the same symbol:

    SNAPSHOT key=tmp:7400_2 -> Var(SymbolId { index: 13 })

So `self.var_ref(var)` on the snapshot yields the same identifier the unguarded
path yielded. The name is decided by `spell_var`, before any resolver is
consulted -- which is why five interventions downstream of it were inert, and it
is the single most useful thing established about this defect.

**What is not established** is which of `spell_var`'s sources supplies it.
`carrier_alias` is ruled out: `CARRIERALIAS` lists `X8_1` through `X8_4` and no
`tmp:7400`. `var_alias` from `coalesce_variables` is ruled out: that pass only
considers `is_register_candidate_var`, and a temporary is not one. The
`var_aliases` insertion in `prepared_semantic.rs:2958` is ruled out: it returns
early unless `var.version == 0`.

That print was taken and it ends the trace:

    SPELL tmp:7400_2 branch=carrier -> x8

`spell_var` names the snapshot after the carrier on its *first* branch, before
anything else is consulted. `carrier_alias` reads
`PreparedSemanticView::carrier_alias_by_name`, which is built by
`carrier_name_aliases`, whose members are the carrier fact's `identity_values`,
`entries` and `updates`.

**So the carrier fact itself claims the snapshot is part of the carrier's
identity.** It is, at the moment the copy is taken, and it is not one
instruction later. `LoopCarrierFact::identity_values` records values that equal
the carrier without recording where they stop equalling it, and every layer
downstream believes it -- which is why six interventions in `r2dec` were inert:
each suppressed one consumer of a claim that was still true everywhere else.

The fix belongs in `r2ssa`, where the fact is made: a value copied out of a
carrier is not an identity value past the next definition of that carrier. Until
then no rendering change in `r2dec` can help, and this defect costs every arm64
accumulator loop one byte.

**One attempt at that, and what it rules out.** `exact_copy_identity_values`
walks copy chains with no condition beyond equal width. Refusing a copy that
crosses between a register and a lifter temporary looked like the discriminator
and is not: `prepared_expression_certificates_render_loop_carried_recurrence_phi`
builds `tmp:update_1 = RAX_2 + 1; RAX_3 = Copy(tmp:update_1)`, where the
temporary holds what the carrier *becomes* and is a legitimate identity. Both
cases cross the same boundary in the same direction, so the space is not what
tells them apart. Reverted.

What tells them apart is where the carrier is next written, which is a program
point. The failing test says so in its own message -- "at the latch program
point" -- so the codebase already knows this fact is position-sensitive and
`identity_values` records it as though it were not.

`StorageSpans` is **not** the piece that answers it: `join_with_same_storage`
unions `X8_2` and `X8_3` into one run, so spans cannot tell two versions of one
register apart, which is the whole question. `GraphInst` carries `block` and
`ordinal`, so "is this storage defined again between the copy and its use" is
answerable directly from the graph.

### Correction: the snapshot is not a carrier alias, and three maps agree

The entry above read `SPELL tmp:7400_2 branch=carrier -> x8` as proof that the
carrier map holds the snapshot. That reading was wrong. Two `SPELL` lines were
printed for one display name, which cannot be two branches of one call; they
were two different `NameSource` implementations.

Printed side by side, all three maps agree and **none** contains `tmp:7400`:

    CARRIERALIAS  recomputed in the debug block
    VIEWALIAS     PreparedSemanticView::carrier_alias_by_name, where spelling reads it
    FOLDALIAS     FoldingContext::carrier_aliases, with the materialised-copy extension

So `carrier_alias` declines and the spelling comes from the second branch,
`var_alias`.

**And the probe that produced the misread has a trap of its own.** It filtered on
the display name and nothing else, and `tmp:7400_2` is a real carrier member in
`djb2` -- a different function decompiled during the same run. The
`branch=carrier` line was that function's. Any probe keyed on an SSA name has to
be keyed on the function too; temporaries are numbered per lift and collide
freely across functions.

Three more sources of `var_aliases` were printed and none of them runs for this
function. The one that does is `prepared_semantic.rs:424`, seeding from
`env.carrier_aliases`, and printing it per function found the extra entries:

    PREPENV fn=0x100000548 entries=15
    PREPENV fn=0x100000548 member=tmp:7400_2 name=x8

Fifteen where the other three maps hold thirteen. `PassEnv` borrows the fold's
map, and the fold grows it in `extend_carrier_aliases_over`, which walks
`Copy` and `Subpiece` ops adding `dst -> carrier` for any source that is already
a member. That closure is what gives the saved address the carrier's name.

**Fixed there.** The closure now stops at a source the carrier has moved past --
another member of the same storage at a higher version -- because such a copy is
a snapshot and needs a name of its own. arm64 -O2 `fnv1a32` renders

    uint64_t t7400 = x8;
    x8++;
    x0 = ((x0 ^ *(int8_t*)t7400) * 0x1000193);

and the corpus goes from eight correct renderings to **fourteen**: arm64 -O1 and
-O2 each go from none to three, and nothing regresses.

The lesson is the one this document keeps recording. Eleven interventions were
written for this defect before the probe that found it, including two misreads
of probe output -- one that mistook two `NameSource` implementations for two
branches of one call, and one that read another function's data because the
filter was keyed on an SSA name and temporaries collide across functions. Key a
probe on the function as well as the value.

Six interventions, all inert, all reverted. The trace took seven steps and each
one narrowed it: the memory renderer's branches, `get_expr`, the inline
decision, the fold's carrier map, `spell_var`'s branches, `carrier_alias_by_name`,
and finally `identity_values`.

### Why the spelling cannot be unified at the mint, and what that leaves

Two attempts, both measured, both reverted.

**Spelling at the mint.** `symbol::declare` was made to run every incoming name
through `format_traced_name`, on the reasoning that it is idempotent for names
that are already spellings. x86-64 -O0 went from six correct renderings to zero,
and the diff says exactly why:

    -    for (int64_t local_28 = 0; local_28 < arg1; ...)
    +    for (int64_t local_28 = 0; t11f80_2 < arg1; ...)

`format_traced_name(name, var_aliases)` consults the alias map *first*, and the
symbol table has no alias map to give it, so the call passed an empty one and a
stack local reverted to the temporary it was lifted from. **The spelling of a
value depends on context the table does not hold**, which is why it cannot be
decided there. That is not a detail of this attempt; it is the reason the mint
is the wrong layer for the question.

**Fixing the sites after the read side was unified.** With every paired store
answering value-first and the name-keyed fallbacks removed, the third
display-name site (`origin_name_to_expr`) was retried. It still took six correct
renderings to zero, on the same undefined `t11f80_2`.

So the read-side consolidation was necessary and is not sufficient. The reason
is sharper than "two key spaces": the raw spelling is **self-consistent**.
Whatever defines a value spells it the same raw way the use does, so a use moved
to the spelled form is moved away from its own definition. Each spelling is an
island, and both islands work internally.

**What that leaves as the rule.** A spelling site can only be fixed together
with whatever defines the value it spells. `variable.rs:569` and
`op_lower/mod.rs:10344` moved together and the corpus went from four correct to
eight, because they were a matched pair. `origin_name_to_expr` alone is not,
and no amount of consolidating the stores beneath it changes that -- its
definition side has to move with it, and finding that side is the work.

### The spelling boundary is not uniform, and fixing it site by site is unsafe

Three sites handed an SSA display name to the symbol table as if it were a
spelling, minting a second identifier for a value that already had one. Two of
them -- `variable.rs:569` and `op_lower/mod.rs:10344` -- were changed to spell
through `format_traced_name`, and the corpus went from four correct renderings
to eight.

The third, `origin_name_to_expr` in `fold/flags.rs`, looks identical and is not.
Making the same change there took x86-64 -O0 from **six correct to zero**, every
one failing on an undefined `t11f80_2`. Reverted.

The reason is worth stating plainly, because the two outcomes look like the same
edit. Some tables in this pipeline are keyed by the SSA display name and some by
the rendered spelling, and which one a site should hand over depends on which
table its consumer will read. `origin_name_to_expr` feeds consumers keyed by the
raw name; spelling it correctly made the key stop matching.

So the sites are not instances of one defect that can be fixed one at a time.
They are symptoms of two key spaces that nothing reconciles, and a site is
"right" only relative to its reader. **The tables have to agree on a key before
any of these sites can be made consistent**, which is the same conclusion the
resolver traces reached from the other side, now with a measurement showing that
piecemeal work here is not merely inert but actively dangerous.

The rule this leaves: in this area, measure the corpus before and after every
single-site change, and do not batch two of them.

### pearson's undefined index, traced to three resolvers

`sym._pearson` at x86-64 -O0 renders

    for (int64_t local_28 = 0; local_28 < arg1; local_28++) {
        local_19 = rcx_4[0x1000019a0];
    }

with `rcx_4` defined nowhere. The chain, from probes rather than reasoning:

  * `RCX_4 = IntSExt(EAX_3)` at idx 28, and `EAX_3 = IntXor(EAX_2, ECX_2)` at
    idx 19, which is the table index `h ^ p[i]`. Both carry render proofs.
  * The fold emits a statement for `eax_3` and none for `rcx_4`: `RCX_4` is
    skipped at `fold_block` under "Skip if this will be inlined".
  * With `rcx_4`'s statement gone, nothing reads `eax_3`, so its statement is
    pruned as dead, and the reader prints a name with no definition.

Two fixes were built for the skip and **both measured inert**:

  * `should_inline` returns true for any caller-saved register without asking
    whether anything can render it, while the branch below it does ask. Adding
    the same guard changed nothing, because `value_has_something_to_render`
    answers *true* for `RCX_4`.
  * Replacing the prediction with the answer -- skip only when `get_expr` returns
    something other than the value's own name -- also changed nothing, because
    `get_expr` does resolve it, forwarding `RCX_4` to `EAX_3`.

So the skip is decided by one resolver and the statement is built by another.
The `Load` arm of `op_to_stmt_impl` builds its address through
`render_canonical_load_expr`, which resolves by its own rules; `should_inline`
consults `value_has_something_to_render`; `get_expr_with_depth` tries
forwarding, then semantic values, then definitions, then the name. Three
answers, and the one that decides whether to emit a statement is not the one
that renders it.

That is open item 1 -- a value has several constructions and nothing says which
is the value -- on a case small enough to hold in one screen. It is not fixable
at the skip site, which is what both attempts demonstrate. Both were reverted.

### Naming registers by location regresses the corpus, and why that orders the work

The ADR puts the location model at step three and the fold rewrite at step
seven. Measurement says those are the wrong way round, and the experiment is
cheap enough to repeat.

`varnode_to_name` keys the register map by `(offset, size)`, so `x9` and `w9`
are two names, and `RenameContext` keys its version stacks by name. That is the
root of every symptom this branch has chased: a write through `w9` never reaches
a read of `x9`, so the repair pass splices projections afterwards to reconcile
them, and its synthesised temporaries are the `tregalias:` names leaking into
the output.

Naming a register varnode by its place -- the widest entry at that offset, with
the varnode's own size saying how much was touched -- was built and measured.
The workspace stayed green apart from four offline lift fixtures, which is what
a naming change should move. Rendering did not:

    x86-64 -O0     4 correct -> 1 correct
    arm64  -O2     `fnv1a32` stopped compiling

Reverted. The reason is that a name is not only an identity here, it is also a
width: about seven hundred call sites key on `display_name()`, and they assume
the name says how wide the value is. Naming by place without expressing narrow
access explicitly at the same time leaves those sites reading a full-width name
for a four-byte value. Half the model is worse than neither.

**So the location model cannot land before the name-keyed stores are re-keyed,
and that is the fold rewrite.** Step seven is a prerequisite for step three, not
a sequel to it. The ADR's ordering has a cycle in it and this is where it shows.

**That conclusion was half right, and the half that was wrong matters.** The
name-keyed stores have since been re-keyed -- all nine paired stores are one
store each, keyed by identity, and the mirror rebuild is gone. Repeating the
experiment in that state is worse, not better:

    before re-keying   4 correct -> 1 correct   (x86-64 -O0 only measured)
    after re-keying   34 correct -> 13 correct  (all six configurations)

So the stores were not what stood in the way. Nor, it turns out, is the width
assumption, which is what the rest of this section used to claim.

Two things were checked rather than assumed. `display_name()` appears at **386**
production sites in `r2dec`, not seven hundred, and nearly all of them use it as
a *key* into the fact stores -- which are keyed by identity now and do not care
what the name says about width. The one helper that genuinely derives a width
from a spelling, `registers::register_bit_width`, has a single caller outside its
own file.

And the failures the experiment produces are not width failures. Naming by place
breaks `x86-64 -O0` with

    error: use of undeclared identifier 't11f00_4'

on `fnv1a32`, `djb2` and `sdbm` alike -- an undefined *temporary*, in the Unique
space, which register naming does not touch. The location model does not fail
because names stop carrying widths. It fails because merging values onto fewer
names multiplies the undefined-name defect that this document traces everywhere
else: a value inlined by one layer and named by another.

**So the ordering is the other way round again.** The location model is blocked on
the inline-versus-name disagreement, not on narrow-access expression, and that
disagreement is the same defect as `eax_12`, `eax_8`, `ecx_9` and `tmp_4700_7`.
It is one defect standing in front of the model, not a separate prerequisite.

The prerequisite for the location model is therefore expressing narrow access
explicitly -- a read of four bytes at the `RDI` location has to say so in the
value, not in the spelling -- and until that exists, naming by place leaves every
one of those sites reading a full-width name for a narrow value. Half the model
is still worse than neither, and now that is measured across all six
configurations rather than one.

The fixture failure is worth keeping too: `check_secret source ABI parameter x
in 0 must bind EDI` -- the source contract states parameter registers by
spelling, so a parameter that lives in the `RDI` location read at four bytes no
longer matches. That is the same contract gap already recorded for the
return-value location, now for parameters, and it wants the same answer: the
source should state the location, and bindings should be compared by location
rather than by name.

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

### The duplicate call is a third pass, and the measurement found it

Probing the owner lookup says it fails at its first step, for both sites:

    owner (100000460, 29) -> no stable owner name
    owner (100000460, 5a) -> no stable owner name

`stable_owned_call_result_name_for_source` has no name for either call result, so
`lower_certified_statement_call` falls through to `LoweredOp::Expr(call)` and the
call renders as a bare statement. That is correct behaviour for a call whose
result nothing is known to own.

But something does name the result, and it is neither of the two constructors:

    // crates/r2dec/src/single_evaluation.rs:327
    let base = format!("{callee}_result");

`single_evaluation::bind_each_call_site_once`, run from `lib.rs:3305` **after**
the fold, hoists each call site into a temporary named after its callee. That is
where `_work_result` comes from, and it is the third rendering of the same call.

So the sequence is: the fold emits a bare statement because no owner is known,
the fold separately builds an expression form, and single-evaluation then binds
that expression to a new name -- leaving the bare statement behind, with a callee
spelled as a variable because `introduced_name_for` reads
`CExpr::Var(id)` and the statement form spelled it `External`.

**The fix is at the seam, and it is small:** `bind_each_call_site_once` knows
which call sites it bound; a bare statement for a site it bound is a duplicate
and should go. Alternatively the fold should not emit the bare statement for a
site whose expression form is used, which needs the fold to know what
single-evaluation will do -- so binding it in the pass that already has the
answer is the better of the two.

Five mechanisms were reasoned out on this defect and all were wrong; three
measurements found it: `#[track_caller]` gave the two constructors, the owner
probe gave the reason the statement is bare, and one grep for the name shape gave
the third pass.

### Why the duplicate cannot be removed at the seam yet

Two changes were built for the seam and both are inert, and together they say
what actually blocks it.

**Dropping a bare statement for a bound site.** `bind_each_call_site_once`
records what it bound, so a bare `CStmt::Expr` for a bound site is a second
evaluation. Retaining against that map changes nothing, because the statement's
call is never recognised as the bound site:

    fn source_of(&self, expr: &CExpr) -> Option<Source> {
        for (candidate, source) in &self.entries {
            if *candidate == expr { .. }

The index matches call sites **by expression equality**. The statement form and
the indexed form spell the callee differently, so one call is two expressions and
no site lookup can connect them.

**Making both spell the callee the same way** does not fix that either, and the
direction is the opposite of what it looks like: the indexed call carries a
`CExpr::Var` callee -- which is why `introduced_name_for` derives `work_result`
from it -- while the bare statement renders `sym._work`, an `External`. So
`resolved_callee_identity_expr_for_site` is not what produced the `External`
spelling, and where it comes from is still unmeasured.

**This is open item 1, not a separate defect.** Nothing owns what a value renders
as, so one call has two expressions; a pass that identifies sites by expression
equality then cannot see that they are one; and the duplicate survives every fix
attempted at the seam. Fixing the representation fixes this without touching
`single_evaluation` at all, and fixing `single_evaluation` first would only teach
it to work around the representation.

Both changes reverted. The bare-statement drop is worth keeping in mind for after
item 1 lands: it is four lines and it will work then.

### Three call expressions per site, and the index matches a fourth thing

`#[track_caller]` on `CExpr::call`, filtered to external callees, shows both fold
constructors building the **same** callee:

    extcall fold/op_lower/lowering.rs:94  func=External { name: "sym._work" }
    extcall fold/op_lower/mod.rs:2962     func=External { name: "sym._work" }

So the earlier claim that they disagree about the callee is withdrawn; they
agree. The `Var` spelling comes from neither, and the reason is that
`single_evaluation` is not indexing either of them:

    let mut folded_call_sites = fold_ctx.call_result_exprs_map().clone();
    ...
    single_evaluation::bind_each_call_site_once(&mut c_function, &folded_call_sites);

`call_result_exprs_map` is `use_info().call_result_exprs`, built in the analysis
layer. That is a **third** call expression for the same site, and it is the one
`introduced_name_for` reads -- which is why the bound name derives from a
`CExpr::Var` callee while both fold forms carry an `External`.

So one call site has three expressions built in three places, and a pass that
identifies sites by expression equality is handed the analysis one and asked to
match the fold's. It cannot, so it binds one and leaves the other, and the two
spellings on the page are two of the three representations.

**This is the sharpest statement of open item 1 in this document.** Not "nine
resolvers disagree about precedence" but: the same call is constructed three
times, by three layers, and nothing says which one is the call. Every attempt at
the seam fails for that reason, and no amount of work inside `single_evaluation`
can succeed while it is given a different expression than the body contains.

### Aligning two of the three representations makes it worse, which confirms the count

Giving `single_evaluation` the expression the fold actually emitted, instead of
the analysis layer's, was built. It works, in the narrow sense: the pass binds
the fold's form and the bare statement disappears.

    uint64_t call_result = sym._work(arg0 + 1, arg1 << 1, (uint32_t)arg1 ^ (uint32_t)arg0);
    sym._other(call_result + (uint32_t)arg0);
    uint64_t t12280_3 = sym__work(..) + arg1 + sym__other(sym__work(..) + arg0);
    return sym__work(..) + arg1 + sym__other(sym__work(..) + arg0);

And the third representation is then unbound, so `sym__work` goes from appearing
once to appearing four times. The ledger does not move -- 47 of 144, 85 refused --
and the output is plainly worse, so the change is reverted.

**That is the confirmation the count needed.** Two representations can be
aligned and the defect simply moves to the third. There is no pairwise fix; the
three constructions have to become one, and that is the work item, not a seam
adjustment. It also shows the seam is capable of doing its job the moment it is
handed the right expression, which is worth knowing: `single_evaluation` is not
itself defective.

### Where the third representation comes from, as far as measured

Codegen prints an `External` verbatim, so `sym._work` on the page is an
`External` and `sym__work` is not: it is a `CExpr::Var` whose SSA name is
`sym._work`, lowercased with its dot replaced by the `_ =>` arm of
`assignment_lhs_expr`. So the third form is a **call whose callee is a
variable named after the callee**, and there is an SSA value carrying that name.

`#[track_caller]` on `CExpr::call` reports only the two fold sites, both
`External`, so this third call is not built through that constructor. The
remaining constructors are the `CExpr::Call { .. }` struct literals, of which the
production ones are in `single_evaluation.rs`; that pass rewrites expressions and
is the strongest remaining candidate.

**Next measurement**, and it is the same one that has worked every time: put
`#[track_caller]` on a small helper wrapping `CExpr::Call { .. }` construction,
or print the callee at each of `single_evaluation.rs`'s three struct literals,
and see which one produces a `Var` callee. One build.

What is established: three representations, the seam works when given the right
one, aligning any two relocates the defect, and the third is a call through a
variable named for the callee rather than an external. What is not: which line
builds it.

### Search the page, not the constructors

The hunt for what builds the third representation ran out of constructors.
`#[track_caller]` on `CExpr::call` reports two sites, both `External`; every
`CExpr::Call { .. }` struct literal in `single_evaluation.rs` is inside its test
module; and no production code outside those builds a call. So the `Var`-callee
call is an existing call whose callee was **rewritten**, and finding the rewrite
by reading means auditing nineteen `CExpr::External` sites in one file plus
sixteen elsewhere.

That is the wrong side of the problem. The next measurement should enumerate what
is actually on the page: walk the final `CFunction` body, print every
`CExpr::Call` with the variant of its callee, and compare against the two
constructed forms. Whatever is in the body and was not constructed is what a
rewrite produced, and the same walk can print the expression so it can be matched
back.

That is one probe in `lib.rs` beside `note_unproven_constructs`, it needs no
knowledge of which pass is responsible, and it answers the question the
constructor hunt could not.

**Recorded as a method note too, because it generalises:** when the question is
"where did this rendering come from", instrumenting construction only works while
the constructors are few. Enumerating the finished output is bounded by the size
of the output rather than by the size of the code, and it is the better first
move whenever a value can be rewritten after it is built.

### Both call forms exist before any post-pass runs

Enumerating the body rather than the constructors -- the method the previous
entry argued for -- answers it in one build. Probing immediately after the
`CFunction` is assembled and again near the end of the pipeline:

    early  External(sym._work) x2   Var(sym._work) x4
           External(sym._other) x1  Var(sym._other) x2
    late   External(sym._work) x2   Var(sym__work) x1
           External(sym._other) x1  Var(sym__other) x2

So **both representations are already present when the body is first built**.
The post-passes are not creating the second form; they are reducing it, four
occurrences to one. The `sym._work` to `sym__work` change between the two probes
is only identifier sanitisation, not a different expression.

That relocates the defect decisively: it originates in the fold, before anything
downstream touches the body, and `single_evaluation` and the renaming passes are
downstream of it. It also sharpens the puzzle, because `#[track_caller]` on
`CExpr::call` reports only two construction sites in the whole run and both build
`External` callees. A call with a `Var` callee is therefore in the body without
having been constructed by the only constructor, which leaves one explanation:
it is cloned from an expression built elsewhere -- an analysis `definitions` or
`semantic_values` entry -- and inlined by the fold.

**Next:** probe the same way at the analysis boundary. Print every `CExpr::Call`
in `use_info().definitions` and `semantic_values` before folding begins. If the
`Var`-callee form is already there, the analysis layer built it and the fold
merely inlined it, which makes this the same defect as the three call
expressions and not a fourth thing.

## The call duplicate, complete

Probing the analysis facts before folding finishes the diagnosis:

    factcall definition       callee=Var(sym._work)   x9
    factcall definition       callee=Var(sym._other)  x5
    factcall call_result_expr callee=Var(sym._work)   x2
    factcall call_result_expr callee=Var(sym._other)  x1

Every call the analysis layer holds carries a **`Var`** callee. Every call the
fold constructs carries an **`External`** one -- `#[track_caller]` reports exactly
two construction sites and both are external. The body then contains both,
because the fold emits its own form *and* inlines the analysis definitions.

So the sequence is complete and every step of it is measured:

  1. the analysis layer builds a call expression per site, callee as a variable,
     and stores it in `definitions` and `call_result_exprs`
  2. the fold builds its own, callee as an external, at `lowering.rs:94` for the
     statement and `mod.rs:2962` for the expression
  3. the body receives both, the fold's directly and the analysis one by inlining
  4. `single_evaluation` is handed the analysis form, matches call sites by
     expression equality, and so binds that one and leaves the fold's

Every fix attempted at step 4 failed because the defect is at steps 1 and 2, and
aligning any two of the three forms relocates it rather than removing it, which
was measured directly.

**This is the whole of open item 1, in one defect, with every link established.**
The renderer must have one construction per value. The fold's external form is
the one with the callee identity and the certified arguments; the analysis form
exists because the analysis layer needs *a* expression for its tables, and the
fix is that those tables should hold the same expression the body will contain
rather than a second one built for the purpose.

### Suppressing call expressions in the analysis definitions is not enough

The obvious reading of the diagnosis was tested: stop `populate_prepared_render_definitions`
from storing any definition whose expression contains a call, on the grounds that
the fold renders calls and a second copy only gets inlined.

It removes the `_work_result` binding, and it is net worse:

    uint64_t t12280_3 = tregalias_100000460_81_0 + arg1
        + sym__other(sym__work(..) + arg0);

A `tmp:regalias` temporary leaks into the body where the definition used to
stand, `sym__work` is still there, and undefined names go from two to three.
Reverted.

Two things it establishes. The `Var`-callee calls are not only in `definitions` --
`semantic_values` holds them too, and suppressing one table leaves the other. And
a definition carrying a call is doing real work: removing it without providing
the fold's expression in its place leaves the consumer with nothing, which is
where the leaked temporary comes from.

**So the fix is a substitution, not a suppression.** The analysis tables must
hold *the fold's* call expression rather than either their own or nothing, which
means the fold's construction has to happen before or during the analysis that
populates those tables -- or the tables must be filled from the fold afterwards,
before anything reads them. That ordering question is the actual design decision
in open item 1, and it is the first thing to settle.

## What the redesign actually requires

Substituting the fold's call expression into the analysis tables was built --
`call_result_exprs`, `definitions`, `semantic_values`, `semantic_values_by_value`
and `formatted_defs`, all of them. It binds the fold's form, and the second form
still proliferates:

    uint64_t call_result = sym._work(arg0 + 1, arg1 << 1, (uint32_t)arg1 ^ (uint32_t)arg0);
    sym._other(call_result + (uint32_t)arg0);
    uint64_t t12280_3 = sym__work(..) + arg1 + sym__other(sym__work(..) + arg0);

The substitution finds its targets by comparing expressions, because that is the
only handle the tables offer: they are keyed by name and by value, not by call
site. So a stored expression that differs in any detail from the one in
`call_result_exprs` is not recognised and is not replaced.

**That is the same failure as `single_evaluation`'s, and it is the point.** The
duplicate exists because two layers build different expressions for one call, and
every attempt to reconcile them afterwards has to identify "the same call", which
by expression equality it cannot do. Two independent mechanisms have now failed
for exactly this reason, which is as clear a statement of the requirement as
measurement can give:

> **A rendered value needs an identity that is not its shape.**

Every remaining approach follows from that. The tables must key call expressions
by call site, or a call expression must carry its site, or -- the version that
matches the rest of this branch -- there must be one construction per site so
that no reconciliation is needed at all. The first two make the duplicate
findable; only the third makes it impossible, and the third is what the symbol
table and the `UseInfo` collapse both did for their own defects.

This is the design decision that gates open item 1, and it is now stated in terms
of what has been measured rather than what was assumed.

### The cost of giving a call an identity

The requirement above -- a rendered value needs an identity that is not its shape
-- has an obvious implementation: a `CExpr::CallSite { block_addr, op_idx }` that
the analysis layer stores in its tables and the fold resolves when it renders.
The tables then hold the site, the fold holds the expression, and there is
nothing to reconcile because there is only one expression.

Adding that variant and building tells the type-level cost exactly:

    28 non-exhaustive match errors

That is small, and it is not the cost. Every pass that asks a question *about* a
call -- what its callee is, how many arguments it has, whether an expression is a
call at all -- would have to resolve a site before it could answer, and those
sites are not enumerated by the compiler because they match on `CExpr::Call`
and would simply stop matching. `is_certified_rendered_call_expr`,
`call_arg_expr_is_low_signal`, `expr_is_scalar_memory_candidate` and the flag and
call-argument predicates are all of that kind.

So the honest scope is: 28 arms the compiler names, plus an unenumerated set of
predicates that would silently stop seeing calls. **The second half is what makes
this a redesign rather than a refactor**, and it is why it should be started
deliberately rather than at the end of a long session. The variant was added,
measured and reverted; the tree is unchanged.

A cheaper variant worth considering first: leave `CExpr::Call` as it is and give
it a site field, so every existing predicate keeps working and only the
constructors and the reconciliation change. That trades the guarantee -- two
expressions for one site become representable again -- for a much smaller blast
radius, and it may be the right first step even though it is not the end state.

### Removing a carrier's expressions does not help either

The lesson from the call fix -- make the wrong answer unrepresentable rather than
declining it at each site -- was applied to the carrier: after materialisation,
remove every carrier member from `definitions`, `formatted_defs`,
`semantic_values` and `phi_sources`, so a carrier has only its name.

It is inert. `sum32` still answers `0`, its ledger is unchanged at 34
obligations with 5 unaccounted, `sym._fnv1a64` is unaffected and all 2334 tests
pass. Reverted.

**That is the fifth carrier approach to measure as inert**, after guarding
`get_return_expr`, `merged_return_register_candidate_for_block`, `should_inline`
and phi-source resolution. The bisection explains why: the answer comes from
`lookup_definition_with_depth`, which walks a *chain*. Removing the carrier's own
entry only makes the walk take one more step to the same constant, because what
is being resolved is not the carrier but the path from the exit merge back to the
initialiser.

**So the resolver instance is not the call instance in disguise.** The call
defect was two objects that could not be recognised as one; giving them an
identity fixed it in four lines. This is one object with a chain of derivations
behind it, any of which a resolver may prefer, and the fix has to be about what a
resolver is allowed to walk through rather than about what a value is. That is a
different piece of work than the one that just landed, and the four resolver
guards plus this removal are the evidence for it.

### A contradiction in the sum32 evidence, which is where to start

Stopping `lookup_definition_with_depth` from walking through a carrier -- one
place rather than the nine that consume it -- is also inert. That is six.

More useful than the sixth failure is a contradiction across the measurements
that has been sitting in this document unremarked:

  * bisecting `get_expr` shows it answering `IntLit(0)` for `X8_4`, first at
    site 9 and then at site 12 once site 9 was closed;
  * closing both makes `get_expr` stop being called for `X8_4` at all;
  * and the rendered output is `return 0` in every one of those states.

If the returned expression came from `get_expr(X8_4)`, the third observation is
impossible. So it does not: the `0` on the page is produced by something that was
never on the path being guarded, and every carrier fix attempted so far has been
aimed at a path that does not produce it.

The retval probe agrees and was misread at the time: it reports `raw=IntLit(0)`
already, meaning the return statement is built from a constant rather than from
anything resolvable, so whatever made that constant ran earlier still.

**Start by enumerating the output**, the method that solved the call defect after
six seam attempts had failed there too. Walk the body immediately after it is
built and print the return statement's expression; then walk it again before and
after `fold_constant_arithmetic_in_expr` and the other whole-function passes in
`lib.rs`. One of those transitions turns a carrier reference into `0`, and that
transition is the defect. Do not guard another resolver until that print says
which one.

### The return is already a constant before any whole-function pass

Tracing the return statement's expression through every pass in `lib.rs`:

    ret before-fold_constant_arithmetic_in_function   IntLit(0)
    ret before-simplify_identities_in_function        IntLit(0)
    ret before-propagate_single_use_register_carriers IntLit(0)
    ...
    ret late                                          IntLit(0)

It is `IntLit(0)` before the first of them, so no post-pass creates it and the
constant is there when the body is assembled. That eliminates the whole second
half of the pipeline, which four of the attempts above were implicitly aimed at.

Preferring `last_ret_value` over the target-derived value when it names a carrier
is also inert, which is the seventh. Taken with the earlier result that
`tracked_return_source_expr` returns the carrier name when guarded and the output
still shows `0`, the conclusion is narrow and firm: **something between
`last_ret_value` being set and the return statement being built replaces it, and
it is not `resolve_return_target_expr`.**

**The one measurement that has not been taken**, and it should be the next thing
anyone does here: print `last_ret_value` at the moment the return statement is
constructed, in the same place the `retval` probe already prints `expr`. The
`retval` probe reports `raw=IntLit(0)`; printing `last_ret_value` beside it says
whether the constant arrived as the candidate or replaced it, and those two cases
have completely different fixes.

Seven attempts on this defect in one session, and the last three were hypotheses
where the rule -- measure, do not guess -- called for a probe. The probe above is
four lines.

### sum32: the candidate is right and the answer is still wrong

The probe that had never been taken settles the first half. At the moment the
return statement is built, with `tracked_return_source_expr` returning the
carrier:

    siteB src=X8_4 is_ret_reg=false expr=Var(carrier)
    cand  expr=IntLit(0) last_ret_value=Some(Var(carrier))

**`last_ret_value` is the carrier and the return expression is the constant.** So
the constant does not arrive as the candidate after all -- the earlier reading of
this probe, before the guard was in place, was of a run where the candidate was
itself already `0`. With the candidate correct, something between it and `expr`
still produces the constant.

Three resolution points were then guarded so that a carrier reference passes
through unchanged: `tracked_return_source_expr`, `resolve_return_target_expr` and
`resolve_return_candidate_in_context`. All three together leave `sum32`
unchanged. Reverted.

**The unexamined step is the branch that chooses `expr`:**

    let expr = if self.is_control_return_target(target) {
        let control_return_value = last_ret_value.clone().or_else(..);
        if let Some(last) = control_return_value { self.resolve_return_target_expr(last, None) }
        else { self.resolve_return_target_expr(target_expr, None) }
    } else {
        self.resolve_return_target_expr(target_expr, last_ret_value.clone())
    };

Print which arm is taken for `sum32` and what each hands to
`resolve_return_target_expr`. If it is the `else` arm then `target_expr` is the
branch target and the carrier arrives only as `last_ret_value`, which
`preferred_return_candidate` then weighs against a resolution of the target --
and *that* comparison is the fourth place, and the only one not yet looked at.
One `eprintln!` in each arm answers it.

Ten guards and rewrites have now been tried on this defect across the session and
every one measured inert. Every measurement, by contrast, has narrowed it. The
next person should take the print above before writing any code at all.

### sum32, narrowed to one function

Instrumenting both guards together confirms they work and that the answer is
correct where it is built:

    guard1 fired for X8_4 -> Var(carrier) recognised=true
    guard2 fired for Var(carrier)
    arm control_target=true last_ret=Some(Var(carrier))
    arm=control last=Var(carrier)

So `expr` is the carrier reference at the point the return statement is
constructed. And the body's return statement is `IntLit(0)` before the first
whole-function pass runs. Between those two facts there are exactly two calls:

    let normalized = self.normalize_final_return_candidate(expr.clone());
    self.sanitize_final_return_expr(normalized, expr)

Guarding the first so a carrier reference passes through unchanged does not
change the rendering. **So it is `sanitize_final_return_expr`**, and that is the
last unguarded step on a path that is now instrumented end to end.

Everything on this path was reverted; the tree is unchanged. What the next
session inherits is a defect narrowed from "nine resolvers disagree" to one named
function, with four other resolution points proven not to be responsible and the
guards that prove it written out above.

**On method, and this is the honest part.** Ten guards were tried across the
session and every one measured inert, while every measurement narrowed the
defect. The measurements that mattered were: bisecting `get_expr`'s fourteen
return points, timing the whole-function passes, printing `last_ret_value`
beside `expr`, and printing which arm builds the return. None took more than one
build. Several of the guards were written after a measurement had already made
them unnecessary, which is the mistake to avoid repeating.

### What is left of sum32 is the width layer

With the return fixed, `sum32` renders

    do {
        x0 += 4;
        x8 = (int64_t)*arg0;
    } while (arg1 != 1);
    return x8;

The carrier reaches the return and the body assigns it. The assignment is still
wrong: the machine does `add w8, w9, w8`, so it should accumulate, and `x8 = *arg0`
is that add with its own operand missing.

Guarding `get_expr` so a carrier is read by name there too does not change it,
and the reason names the remaining defect exactly. The carrier's members are

    X0_0 X0_1 X0_2 X0_3   X8_1 X8_2 X8_3 X8_4

all `X` registers. The update writes **`W8`**, the 32-bit half, so the operand in
the add is not a carrier member, resolves on its own, reaches the initialiser and
folds `w9 + 0` to `w9`.

**So the remainder of `sum32` is the width layer**, which is already a scoped
piece of work: a carrier written at a narrower width than its phi is not
reconciled, and the same gap blocks the x86 accumulator loops. The return defect
and the width defect were one symptom and are two causes; the first is fixed and
the second is where it belongs.

### The width layer resists the carrier-by-name rule

Giving `LowerCtx` the carrier set and reading a carrier by name there, as the
fold now does, is inert: `sum32` still renders `x8 = (int64_t)*arg0` and nothing
else moves. Reverted.

The probe that motivated it says why it was worth trying and why it was not
enough. Only `X8_1` is ever asked of the fold's `get_expr`, and it answers
`IntLit(0)`, the initialiser -- so the carrier-by-name rule is the right shape for
that query. But the assignment being rendered is not built from that query: the
add's operand is a `W8` value, the 32-bit half, which is not a carrier member and
never reaches either `get_expr`.

So the carrier machinery cannot fix this, because the value in the expression is
not the carrier -- it is the narrow half of the carrier, and nothing relates them.
That is the width layer stated as precisely as this defect can state it, and it
is the same statement the x86 accumulator loops and the SIMD reads produce:
**a value written at one width and read at another is two values, and the graph
does not know they are one.**

Every approach that treats the carrier as the unit fails here. The unit has to be
the storage.

### Withdrawn: sum32's remainder is not the width layer

The previous entry attributed `x8 = (int64_t)*arg0` to a `W8` value that the
carrier machinery could not reach. That is wrong, and the measurement is
unambiguous. Scanning the graph for values whose canonical storage falls strictly
inside the carrier's finds none:

    narrow carrier=CanonicalStorageId { space: Register, offset: 16448, size: 8 } found=[]

There are no narrow halves. The SSA has already widened them, so `add w8, w9, w8`
is entirely `X8` operations by the time anything renders, and there is no
two-values-one-storage problem in this function at all.

So the remaining defect is the carrier resolution after all: the add's operand is
`X8_1`, a carrier member, and it resolves to `IntLit(0)`, its initialiser, so
`w9 + 0` folds to `w9`. Reading a carrier by name in `LowerCtx` was built for
exactly that and measured inert, which means the operand is resolved somewhere
that is neither `LowerCtx::get_expr` nor `FoldingContext::get_expr` -- the same
shape of question the return path took eleven attempts to answer, and the same
answer applies: **trace the whole path before guarding any of it.**

The three symptoms said to converge on the width layer are therefore two: the x86
accumulator loops and the SIMD whole-register reads. `sum32` is not one of them.

### The carrier's entry edge becomes a definition, and that is the defect

Tracing what `populate_prepared_render_definitions` records for the carrier:

    X8_1 = COPY const:0_0     -> IntLit(0)
    X8_2 = COPY X8_1          -> IntLit(0)
    X8_3 = ZEXT(tmp:12280_2)  -> Cast { .. }

`X8_2` is the copy that **materialising the carrier inserted on the edge into the
loop**. It is recorded as a definition whose expression is the initialiser, so
every read of the carrier that consults the definitions resolves to `0`. The
update is `ZEXT` of a temporary holding the 32-bit add, and that add's carrier
operand resolves the same way, which is how `x8 = x8 + *arg0` renders as
`x8 = *arg0`.

**This is the `multiply_assigned` idea from much earlier in this document, and it
now has the evidence it lacked.** A materialised carrier is assigned on the entry
edge and again on the back edge; the first assignment is recorded as its
definition and the second is not, so the definition says the carrier always holds
its initial value. Suppressing the definition was tried before this trace existed
and measured inert, because it was applied where the recorder is not -- the
recorder is `populate_prepared_render_definitions` in `prepared_semantic.rs`, the
builder that ships, and the earlier attempt guarded `rebuild_definitions` in
`use_info.rs`, the builder that does not.

**Next, and it is small:** record no render definition for a name that
materialisation assigns on more than one edge. The set is exactly
`carrier_aliases`, which the fold already has and the analysis can be given, and
the trace above is the check -- `X8_2` should have no definition, and then the
add keeps its operand.

### Suppressing the carrier's definition in the shipping builder is also inert

The guard the previous entry called for was applied where the trace said it
belonged -- `populate_prepared_render_definitions`, with `env.carrier_aliases` in
scope -- so that a materialised carrier records no render definition. `sum32` is
unchanged and `sym._fnv1a64` is unaffected. Reverted.

So the add's operand does not resolve through `definitions[X8_2]` either. The
remaining candidate is that the operand is not the carrier but a value derived
from it -- the 32-bit add reads a truncation, and that truncation has its own
definition recorded from the same initialiser.

**The trace to take next is one step further down the same path**: print what
`tmp:12280_2`'s definition is built from, in the same place `deftrace` printed
`X8_1`, `X8_2` and `X8_3`. Filter on `tmp:12280` rather than `X8`. That names the
operand exactly, and it is the last unexamined link between the carrier and the
rendered assignment.

Twelve interventions have now been measured on this defect and every one was
inert; every trace has narrowed it by one step. The next person should take the
trace and not write a guard until it prints.

### The operand is `tmp:12180_2`, and the add survives to the body

The trace one step further down:

    tmp:12280_2 = tmp:24e00_2 + tmp:12180_2
        expr = Binary { op: Add, left: Var(..), right: Var(..) }
    X8_3 = ZEXT(tmp:12280_2)
        expr = Cast { ty: Int(64), expr: Var(..) }

**The add is intact when its definition is recorded** -- two `Var` operands, not a
constant in sight. So nothing folds it there. One operand must *render* as zero
later and then be simplified away by `x + 0 -> x`, and the operand in question is
`tmp:12180_2`, the narrow read of the carrier.

That completes the chain end to end:

    X8_1 = 0                      the initialiser
    X8_2 = COPY X8_1              the edge materialisation inserted, definition 0
    tmp:12180_2                   a narrow read of the carrier
    tmp:12280_2 = tmp:24e00_2 + tmp:12180_2
    X8_3 = ZEXT(tmp:12280_2)      the update

and identifies the single value to look at: **`tmp:12180_2` renders as `0` and
should render as the carrier.** Suppressing `X8_2`'s definition did not achieve
that, so `tmp:12180_2` has its own recorded expression derived from the same
initialiser, and the trace to take is the one above filtered on `12180`.

Twelve interventions inert, five traces each narrowing by a step, and the target
is now one named SSA value rather than a layer. That is where this ends today.

## sum32, traced to the end

The last trace names the operand:

    tmp:12180_2 = COPY tmp:regalias:80:4:0_1     expr = IntLit(0)

`tmp:regalias:...` is the **register-alias repair pass's** synthesised temporary:
the subpiece it inserts so a 64-bit register can be read at 32 bits. So the width
layer is involved after all, and the withdrawal two entries above was wrong in an
instructive way -- there are no narrow *canonical storage* values in this graph,
but there is a repair temporary doing the narrowing, and no carrier rule reaches
it.

Extending carrier membership transitively through `Copy` and `Subpiece` from a
carrier member was built to reach it, and is inert. The reason is structural and
is the finding:

> `carrier_name_aliases` is computed from `prepared.function()`, and the
> `tmp:regalias` temporaries do not exist there. They are inserted by
> `normalize_register_alias_sources` into the **normalised** function that the
> fold walks. The alias map is built from one function and consumed against
> another.

That is the same defect this branch has now found five times in different
clothes: two things that should be one, and nothing saying which is which. The
symbol table had four copies, the `UseInfo` had two builders, a call had three
expressions, and here a function has two versions and the facts are computed
against the wrong one.

**The fix is to compute the carrier aliases from the function the fold walks**,
after normalisation has inserted its repair temporaries, rather than from the
artifact. Then the closure above reaches `tmp:regalias:80:4:0_1`, the narrow read
renders as the carrier, and `x8 = x8 + *arg0` follows.

Thirteen interventions were measured on this defect and every one was inert; six
traces each narrowed it by one step and the sixth reached the cause. Take traces.

### Extending the alias map over the walked function is also inert

Both orderings were built: extending `carrier_aliases` transitively through
`Copy` and `Subpiece` over the blocks the fold walks, first after the facts are
recorded and then before them. Neither changes `sum32`. Reverted.

So the closure does not reach `tmp:regalias:80:4:0_1` even when it is run over
the function that contains it, which means either the repair temporaries are not
in those blocks by then, or their source is not a carrier member under the name
the map uses. **One print settles which**: dump `carrier_aliases` and the ops of
the loop block together, at the point `extend_carrier_aliases_over` runs. That is
the fifteenth intervention's worth of information for the cost of a build, and it
is the next thing to do.

Fourteen interventions on this defect have now measured inert. Six traces each
narrowed it and produced, in order: the four-point return chain (fixed, and it is
why `return x8` renders at all), the operand `tmp:12180_2`, the repair temporary
behind it, and the observation that the alias map is computed against a different
function than the fold walks. The cause is understood; what is not is why the
obvious repair does not take, and that gap is exactly one print wide.

### sum32's last operand, and the table that still answers

With the carrier's narrow reads named and their definitions suppressed, the add
still records

    tmp:12280_2 = tmp:24e00_2 + tmp:12180_2
        expr = Binary { op: Add, left: Var(..), right: IntLit(0) }

`tmp:12180_2` is a carrier alias by then and has no render definition, and
`to_pass_env` does pass the extended map, so the suppression is reached. It still
lowers to `0`.

`LowerCtx::get_expr_with_depth` tries, in order: constant, address literal,
**forwarded value**, semantic value, definition, and finally the name. Definitions
and semantic values are suppressed for carrier members, so the remaining route is
`forwarded_values`, and that is the table to check next -- the same
all-parts-together lesson this defect has now taught twice, and the four-point
return chain taught before it.

**The pattern is worth stating once more because it has held every time here.**
A value has several tables that can answer for it, and suppressing a subset
leaves the rest answering, which is indistinguishable from the fix being wrong.
The return needed four points guarded; the carrier's narrow read needed the alias
map extended *and* the definition suppressed; this needs those *and* whatever
`forwarded_values` holds. Count the tables before changing any of them.

### sum32: the add is built correctly and dropped afterwards

The previous entry named `forwarded_values` as the remaining table answering for
the carrier's narrow read. That was right, and instrumenting it settled the whole
chain. In `collect_prepared_runtime_facts` the copy arm records

    fwdtrace-ps tmp:12180_2 <- const:0_0

so the narrow read of the carrier forwards to the constant the loop was entered
with, exactly as the return did before it. Suppressing that record for a carrier
member -- the same guard already used for definitions -- makes the read resolve
to a name, and the add's recorded definition changes from

    Binary { Add, left: Var(..), right: IntLit(0) }

to two `Var` operands. The constant is gone.

**It still renders `x8 = (int64_t)*x0`, and the reason is further downstream than
any of the tables.** Tracing the statement build in `binary_stmt_typed` shows the
assignment leaving `op_lower` intact:

    bintrace tmp:12280_2 op=Add l=Deref(Var) r=Var
    bintrace tmp:12280_2 raw_names=["x0", "x8"]
    bintrace tmp:12280_2 final=Binary { Add, Deref(Var), Var }

`identity_simplify_binary` does not fold it -- `is_literal_zero_expr` is purely
syntactic and the operand is a `Var` -- and `assignment_rhs_with_type_policy`
leaves it alone. By the time the single-use substitution in `lib.rs` sees the
same value, the statement has become

    subtrace t12280_2 = Deref(Var)

So `+ x8` is dropped by a pass **between `op_lower` and that substitution**. That
is the boundary to instrument next, and it is a narrow one: the statement is
correct on the way out of one pass and wrong on the way into another, with the
list of passes between them short enough to bisect by printing the statement at
each.

The forwarding suppression was reverted with the probes. It is a genuine defect
and the guard is a one-line addition in the copy arm, but on its own it changes
no rendered output, and the standing rule is that a partial fix which does not
change behaviour does not stay in the tree. Re-apply it together with whatever
fixes the dropping pass, and the two together should render the accumulation.

A caution worth leaving behind: `cargo fmt` in this worktree reformats far more
than the file being edited, and the resulting diff buries real changes among
hundreds of formatting hunks. Do not run it while a fix is in progress.

### The carrier defect is closed, and what it cost to find

The previous entry put the drop "between `op_lower` and the substitution". That
was one call too coarse: `binary_stmt_typed` prints its result *before* calling
`assign_stmt`, and the loss is inside `assign_stmt`. Instrumenting its three
steps named the step exactly:

    asgtrace in    Var(x8)
    asgtrace ident Var(x8)
    asgtrace seman IntLit(0)

`semanticize_visible_expr` replaces a name with the semantic value recorded for
it, and for a carrier that value is what the loop was entered with. Together with
the forwarding record described above, that is **two tables speaking for the
carrier's name**, and either one alone is enough to erase the accumulation --
which is why suppressing only the forwarding measured inert and was reverted.

Both are now suppressed for a carrier, and the results are visible:

    sum32     x8 = (int64_t)*x0          ->  x8 = (int64_t)(*x0 + x8)
    fnv1a64   empty loop body            ->  x0 = (x0 ^ *(int8_t*)x8) * 0x1b3

Preserving the names exposed a second, smaller defect: an initialization that a
later store overwrites before anything reads it now printed twice. That is a
genuine dead store, so `drop_overwritten_assignments` removes one where the
statements between neither read nor branch. The two identical `expr_is_side_effect_free`
predicates it needed -- one in `structure.rs`, one in `op_lower` -- were collapsed
into one, the sixth instance of "one job, many implementations" found in this
rewrite.

2334 tests pass. The remaining defects on `fnv1a64` are separate and already
named elsewhere in this document: the pointer increments twice (`x8++` and
`x8 = x8_2 + 1`, with `x8_2` read undefined), and the FNV basis prints as
`0x739d0383`, its low half, which is the 64-bit constant model.

**The method that worked, stated once.** Seven traces, each narrowing by one step,
and no guard written until a probe printed. Every intervention attempted ahead of
a trace during this defect measured inert. The trap specific to this codebase is
that a value has several tables that can answer for it, so a fix to one is
indistinguishable from a wrong fix while another still answers -- count the tables
first, and change them together.

### fnv1a64's `x8_2`: two identifiers minted for one value

The undefined `x8_2` in fnv1a64's loop is not an SSA name that escaped, and it is
not a carrier member that missed the alias map. The fold's map is complete:

    maptrace [("X0_2","x0") ... ("X8_1","x8"), ("X8_2","x8"), ("X8_3","x8"),
              ("X8_4","x8"), ("tmp:7400_2","x8"), ("tmp:regalias:f4:4:0_1","x0")]

Probing the symbol table shows what actually happens. `declare_or_reuse` is
called twice for the same value, once with `X8_2` and once with `x8_2`, and
`by_name` is case-sensitive, so **one value gets two identifiers**. Neither call
went through a speller: several sites pass an SSA display name straight into the
symbol table, among them `prepared_semantic.rs` lines 1713, 1951, 2094, 2308 and
`variable.rs:569`.

So this is the naming-layer instance of "one job, many implementations". There
are at least three spellers -- `LowerCtx::var_name`, the `var_name` in
`return_resolver.rs`, and `format_traced_name` -- plus a set of call sites that
use none of them. Only the second consults the carrier map.

**What was ruled out, so it is not retried.** Adding the carrier lookup to
`LowerCtx::var_name` cannot fix it: instrumenting that function shows it never
spells an `x8_N` name at all, and threading `carrier_aliases` through all ten
`LowerCtx` constructions changed no output. Adding the same lookup to the
`return_resolver` speller also changed nothing. Both were reverted. The fix has
to be at the sites that bypass the spellers, which means giving them one speller
to call rather than adding a fourth.

Two measurement mistakes are worth recording because both read as "absence of
evidence". A release-build `Backtrace` carries no file paths, so grepping its
output for `r2dec/src/...` discarded every frame and made a probe that had fired
look silent. And a probe placed on one branch of `format_traced_name` says
nothing about the branch a register name takes. Print first, filter second.

### Measured state after the naming rewrite

Rendering every function in the fixtures on hand, rather than the two that were
being worked on:

    arm64  fnv1a64    34 rendered, 0 refused,  4 unaccounted, 0 defects
    arm64  sum32      29 rendered, 0 refused,  5 unaccounted, 0 defects
    arm64  xor_lanes  72 rendered, 0 refused, 33 unaccounted, 1 defect
    x86    fnv1a64   111 rendered, 1 refused, 20 unaccounted, 1 defect
    x86    sum32      34 rendered, 1 refused, 15 unaccounted, 1 defect
    x86    xor_lanes  63 rendered, 0 refused, 15 unaccounted, 1 defect

**The x86 accumulator loops improved without being worked on.** This document
said earlier that x86 rendered `rax = EAX_3` with an empty body. It now renders

    do {
        rax = (int64_t)(rax + arg0[arg3]);
        rcx++;
    } while (arg1 != arg3);

so the accumulation and the indexed load are both there, and the width layer is
a smaller problem than the entry above it describes. Two defects remain in that
function: the return resolves to `rip_1` instead of `rax`, and `arg3` -- which
stands where the counter belongs -- is read with no definition.

The remaining SIMD gap is the largest single number here: `xor_lanes` leaves 33
of 105 obligations unaccounted on arm64 and 15 of 78 on x86.

### The ledger was not telling the truth, and three defects it was hiding

Four fixes landed together, and the first one changes how every number in this
document should be read.

**Elisions were recorded only when a debug environment variable asked for them.**
`note_elided_op_site` returned early unless `R2SLEIGH_DEBUG_UNOWNED` was set, and
the comment there said the map was read by nothing else. The obligation ledger
reads it. So every elision the fold performed was reported to the reader as
*unaccounted*, and the counts quoted throughout this document are wrong in the
same direction. With the gate gone, arm64 `fnv1a64` reports 34 rendered, 4 elided,
0 refused and **nothing unaccounted**, where it used to claim four obligations it
could not explain. They were flags it had deliberately elided all along.

**A wide read of a register whose lanes were written separately resolved to the
value the function was entered with.** No refusal, no marking, a clean ledger, and
wrong C: `xor_lanes` rendered `dst[i] = a[i]` on both architectures with the xor
silently gone. The parts are all present, so the family repair now emits the
explicit `Piece` its own comment had asked for, combining parts in adjacent pairs
so every intermediate width is one C can spell. The x86 loop now renders the xor
and the compare masks it is built from.

**The prune at the end of a block starts its live set empty**, so a definition
whose readers are in another block looked unread and was deleted -- after its
render proof had been recorded, which is how the ledger claimed those obligations
were rendered while twenty-one names dangled. Names another block reads are noted
before the walk, and the lane definitions render.

**Return recovery was block-local.** A function whose accumulator already sits in
the return register writes nothing in its epilogue, so x86 `sum32` returned
`rip_1`. The resolver now walks back to the last write to the return register and
returns `rax`. arm64 was never affected because its epilogue moves `x8` into `x0`.

**`xor ecx, ecx` was read as evidence of a parameter.** RCX is the fourth integer
argument register, so the operand of a zeroing idiom made the loop counter print
as `arg3`, an argument the function never had. A register cleared by cancelling
itself is not read.

Measured now:

    arm64  fnv1a64    34 rendered,  4 elided, 0 refused,  0 unaccounted, 0 defects
    arm64  sum32      29 rendered,  4 elided, 0 refused,  1 unaccounted, 0 defects
    x86    sum32      34 rendered, 13 elided, 1 refused,  2 unaccounted, 0 defects
    x86    fnv1a64   111 rendered, 18 elided, 1 refused,  2 unaccounted, 1 defect
    x86    xor_lanes 179 rendered, 39 elided, 0 refused,  4 unaccounted, 21 defects
    arm64  xor_lanes 632 rendered, 38 elided, 0 refused, 11 unaccounted, 96 defects

**Two things measured inert and were reverted, so they are not retried.** Refusing
to compose when every part is an entry value does not reduce arm64 `xor_lanes`'s
96 undefined names, so those lanes are not all entry values and that case needs
its own trace. And making symbol identity case-insensitive is wrong outright:
`CONST:4_0` and `const:4_0` are a register-shaped name and an SSA constant, and
the classifier depends on telling them apart.

Still open, in the order I would take them: the arm64 lane names; the doubled
induction step (`rcx += 2` where the machine increments once, and the same shape
as fnv1a64's two `x8++`); the definition skipped on an unverified promise that its
single reader will inline it (`mod.rs:12755`, whose reader is depth-capped at 2);
and the spurious third parameter in x86 `sum32`.

### arm64's ninety-six names: lane storage has no merge

The x86 fix does not apply here, and neither does refusing to compose entry
values -- both were tried and measured inert. The trace says why.

The undefined names are `reg:5001_0` through `reg:500f_0` and three more runs of
fifteen, all **version zero**, while lane zero of each run is absent from the
list. The lanes are not undefined in SSA: `reg:5001_1`, `_2` and `_3` all have
definitions. And the entry read is in **the same block** as two of those
definitions:

    def        reg:5001_1   block 0x194
    def        reg:5001_2   block 0x194
    read-entry reg:5001_0   block 0x194
    def        reg:5001_3   block 0x1e4
    read-entry reg:5001_0   block 0x1e4

Block 0x194 is the loop body. A read that precedes the writes in a loop body is
reading what the *previous iteration* left there, which is a merge -- and there is
no phi for lane storage, so renaming hands it the value the function was entered
with, on every iteration. The composition then faithfully concatenates fifteen
entry lanes with one live one, and the ninety-six names are the honest report of
that.

**That reading was wrong, and the correction matters more than the claim.** The
phis are there: `reg:5001_1` is a phi at 0x194 and `reg:5001_3` is one at 0x1e4.
The grep that found `reg:5001_0` "in the loop body" was matching the phi's own
incoming edge, where the entry value belongs. No operation reads it directly.
Renaming is doing its job.

What the ops actually show is the vector operation lifted as a per-lane
read-modify-write, and one lane treated differently from the other fifteen:

    op 172  B0_2       = Subpiece(Q0_2) | reg:4800_2     <- lane 0, from the wide value
    op 173  reg:5001_2 = reg:5001_1     | reg:4801_2     <- lane 1, from its own phi
    op 174  reg:5002_2 = reg:5002_1     | reg:4802_2

Every lane is OR-ed with what that lane held before, so all sixteen are
loop-carried, and each carries its own phi whose entry edge is an undefined
function-entry lane. Lane zero escapes because the family repair rewrote its
source to a `Subpiece` of the wide `Q0_2`; lanes one to fifteen keep their narrow
phis, because `family_root_slice_for_range` takes the *smallest* containing slot
(`min_by_key(width, offset)`) and each lane has a width-1 slot of its own.

So the ninety-six names are honest: those lanes really are read before they are
written, under this modelling. The defect is that the modelling gives one machine
register sixteen carriers. The fix is to present a loop-carried vector as one
carrier over the whole storage rather than one per byte -- the same "one variable
per storage" rule the naming and carrier work has been applying everywhere else,
which is what makes it the right next piece rather than a special case for SIMD.

### Why lane zero behaves and fifteen do not, and what blocks the fix

The asymmetry has an exact mechanism. `ldp q0, q1, [x9, -0x20]` writes the whole
sixteen bytes, and `seed_family_roots` records a root for that slot and for every
*named* sub-slot inside it. `0x5000` is named -- it is `B0`, the byte view of `v0`
-- so lane zero gets a root pointing at the wide value. `0x5001` through `0x500f`
are unnamed varnodes, so they get none.

Then `eor3 v0.16b, v0.16b, v16.16b, v4.16b` is lifted per lane, and the first
lane write calls `kill_overlapping_family_roots`, which is

    state.retain(|slot, _| !family_slots_overlap(*slot, written));

so writing one byte throws away the whole-register root the load had just put
there. The remaining fifteen lanes now have nothing to resolve through and keep
their own phis, whose entry edges are undefined function-entry lanes. That is the
sixty names, and the ledger reports them honestly.

**Invalidating only the written range fixes most of it and cannot be kept yet.**
Splitting each overlapping slot around the write -- retaining roots for the parts
the write did not touch -- takes arm64 `xor_lanes` from 96 undefined names to 66
and removes 120 synthetic obligations, with every other fixture unchanged. It also
breaks `post_call_stack_store_does_not_fabricate_call_result_owner`, and that
failure is correct: on x86-64 a 32-bit register write **zero-extends** into the
full 64-bit register, so the upper half after `mov eax, ...` is zero, not what it
held before. Preserving it is wrong, and the SSA cannot tell that case from a
vector lane write because the p-code writes only the four bytes.

So the prerequisite is modelling the zero-extension where it belongs -- a 32-bit
x86 write defines the whole register -- after which range-precise invalidation is
correct everywhere and can go back in. Splitting only for non-GPR families would
buy the same numbers today and is the kind of arch-conditional the rest of this
work has been removing, so it was not taken.

The change is reverted; the mechanism above is what to build against.

## How to measure, and two ways it silently lies

Both faults below produced *plausible* numbers, not obviously broken ones, and
between them they made four consecutive experiments read as "changes nothing"
when three of them had not been run at all.

The plugin is not deployed by copying `libr2sleigh_plugin.dylib` into
`~/.local/share/radare2/plugins/`. radare2 skips that file and loads
`anal_sleigh.dylib` and `arch_sleigh.dylib`, which the Makefile links against the
Rust cdylib in the `r2sleigh/` subdirectory and then re-signs. Use
`make -C r2plugin install`. A hand copy leaves the signature invalid, and on this
machine that surfaced as `sla: no architecture loaded` for arm64 while x86-64
kept working -- half the corpus quietly disappearing rather than an error.

`tests/corpus/verify_rendering.py` does not run `pdd`. It reads `out_<cfg>.txt`,
which `sweep.sh` writes. Regenerate all six dumps after every build, or the score
describes whatever the plugin was when the dumps were last written.

So a measurement is only worth reporting when `make -C r2plugin install` and a
fresh sweep both ran between the edit and the score, and when it covers all six
configurations -- a change that moves nothing on the one configuration that
prompted it has moved something on another more than once.

## Spelling an undefined name is not fixing it

`origin_name_to_expr` in `fold/flags.rs` hands a condition the raw SSA name when
it cannot parse the origin back into an expression, which is how `RDI_5` ended up
in a `while` beside the `rdi_5` the body had declared. Routing it through
`format_traced_name` -- the same rule the statement path spells by -- is the
obvious repair and it is wrong. Measured properly, x86-64 -O0 goes from six
correct to none.

The reason is worth keeping. The names it emits have no declaration either way.
Raw, `tmp:11f80_2` is not a C identifier and something downstream still resolves
or replaces it; spelled, `t11f80_2` looks like an ordinary local and is simply
undeclared, so every rendering on that configuration stops compiling. The change
does not give the value a definition. It only makes the absence harder to see,
which is the same failure as declaring undefined names to satisfy a detector.

The condition referencing a value with no rendered definition is the defect, and
it belongs with `RDX_5` above -- fixed where the definition is lost, not where
the name is written.

## The defect that now dominates: a value with two answers

Seven of the eleven renderings that do not compile fail on one name apiece --
`eax_8`, `t11f00_10`, `tmp_4700_7`, `tregalias_...`, `x30` -- and they are not
all the same defect underneath. Two shapes have been separated.

`RDX_5` in `djb2` was used and never defined anywhere, in the op stream or the
rendering. That one is fixed: the merge carrying it out of its loop could not be
placed, and now can be.

`eax_8` in `murmur3_32` is the other shape and is still open. It *is* defined --
`EAX_8 = ESI_1 >> 16` -- but no assignment is ever emitted for it, because the
fold chose to inline it. Two of its three appearances in the return expression
are the inlined `(uint32_t)esi_1 >> 16`; the third is the bare name `eax_8`,
which nothing declares. The value has two answers inside a single expression.

It is not the pruner. `PRUNED` never names it, and disabling the pre-structuring
prune outright takes x86-64 -O2 from three correct to none, so that pass is
load-bearing and its per-block empty live-out is not the fault here.

Where it goes has been narrowed by elimination, and the answer is not any of the
obvious candidates. The assignment *is* built -- a probe on the site that spells
an assignment's left-hand side fires exactly once for `eax_8`, and the statement
is returned. By the time the first post-fold pass runs
(`simplify_identities_in_function`) it is already gone, so it is lost inside
`fold_block`. It is not `propagate_ephemeral_copies`, which rewrites in-block
uses but keeps the statement. It is not `prune_dead_temp_assignments`, whose
`PRUNED` listing for this function names twenty-nine values and not this one. It
is not `prune_redundant_return_slot_assignments`, which only touches stack slots.
It is not the `lhs == rhs` self-assignment drop, which never fires here.

So something between statement production and the assembled block list discards
it, and whoever assembles the return expression -- the seven components this
document already records, each able to override the last -- still spells the
value by name. Until one of
them owns the spelling, inlining a value in one operand and naming it in another
will keep producing exactly this. That is the same lesson as the carrier work --
a value is spelled by its own name wherever it appears -- and the return
expression is where it has not yet been applied.

Worth keeping in view: the rendering says so itself. `murmur3_32` prints
`/* r2dec defect: 1 name(s) read with no definition */` above a ledger reading
`129 built, 9 elided, 0 refused, 7 unaccounted`. The obligation ledger catches
this class rather than letting it pass as plausible code, which is why it is
findable at all.

## Phase 2's write side, measured rather than assumed

The read side was settled by making every paired store ask the value-keyed half
first and deleting the name-keyed fallbacks. What was left was recorded as "the
write side", with the note that re-keying the string-keyed stores belongs with
the location model and that doing it halfway is the conflation itself.

Every production write writes both halves, but not all of them go through the
helpers in `analysis/mod.rs`. `collect_prepared_runtime_facts` in
`prepared_semantic.rs` writes `use_counts`, `condition_vars`, `forwarded_values`
and `semantic_values` inline, pairing them through `bind_prepared_value_id`
instead. That is duplicated logic rather than divergence -- both halves are
written either way -- so the halves cannot drift by a missed call site, which is
what "two stores" suggested. The duplication is still worth removing: a fifth
store added to that function has to remember the pairing by hand.

Getting there took two wrong turns worth recording. A `grep` written as
`grep -r pattern path --include=*.rs` has zsh glob the `--include`, so it
silently searches nothing and matches nothing; the first version of this section
concluded "only test fixtures write one half" from a command that never ran.
Re-running it correctly surfaced the inline sites and produced the opposite
error -- they read as single-half until the surrounding lines are read and the
value-keyed write is there all along.

They can still drift where the write resolves no `ValueId`: it writes the name
and skips the value key, and the entry then exists only in the string half. That
was the reason to believe the string half could not yet be derived. It is now
counted at the helpers *and* at the four inline sites, which the first version of
the counter missed entirely. `UseInfo::unkeyed_writes` reports **zero** over
every function of all six hash binaries. Not one paired write in the corpus fails
to resolve a canonical identity.

### The one store where the halves are not the same fact

Four of the five inline pairings in `collect_prepared_runtime_facts` now go
through a single helper each -- `note_use_for_var` twice, `note_condition_var`,
and a new `insert_semantic_value_for_name_and_value_if_absent` that keeps the
first-write-wins behaviour the call site relied on. The pairing rule for those
stores is written once.

`forwarded_values` is the exception, and it is not duplication at all. The two
halves are given *different provenance*:

- the name key gets `source_prov`, which is what following the forwarding chain
  arrived at, falling back to `src` for the fields that chain did not fill;
- the value key gets `exact_prepared_copy_provenance(src, src_id, ...)`, which is
  the immediate copy source and nothing followed.

So the string half answers "where did this value ultimately come from" and the
value half answers "what was copied into it here". Deriving either from the other
changes what is recorded, which is why this one cannot be folded and why the
store cannot simply lose its string-keyed half. Whether both facts are wanted, or
whether one of them is a bug that predates the split, is the question to settle
before the derivation finishes -- and it is a question about the location model,
which is where the handoff always said this belonged.

That reads like the string half is nearly derivable. It is not, and the reason
was found only by trying it.

### The dependency runs the other way

`seal_value_facts` -- the last thing that touches `UseInfo` before any consumer
sees it -- calls `rebuild_id_mirrors_from_name_maps`. That function clears and
repopulates **nine** value-keyed stores from their string-keyed counterparts:
`use_counts`, `semantic_values`, `copy_sources`, `ptr_arith`, `condition_values`,
`stack_slots`, `stable_memory_values`, `forwarded_values` and
`call_result_source`. Its name says exactly what it does. The value-keyed halves
are mirrors.

So the string-keyed half is the source of truth today and the value-keyed half is
derived from it -- the reverse of the direction this step is written in. The read
side asking "value first" is asking a mirror.

This explains three things that were otherwise puzzling. Whatever
`collect_prepared_runtime_facts` writes into a value half is discarded before
anyone reads it, so an experiment giving `forwarded_values` the same provenance
in both halves passes the whole suite and moves no rendering -- not because the
two facts agree, but because the one that disagreed was already being clobbered.
`exact_prepared_copy_provenance`'s result never reaches a consumer. And
`unkeyed_writes` reading zero says less than it appeared to: those writes are
overwritten regardless, so the count measures a path whose output is thrown away.

The counter stays, because it will matter once the direction is reversed. But the
claim it was supporting was wrong. Deriving the string half from the value half
is not mechanical and is not unblocked; it requires deleting the mirror rebuild
and making the value-keyed stores authoritative, which means every write that
currently resolves a name has to resolve an identity instead. That is the
location model, which is where the handoff said this belonged, and the reason is
now concrete rather than a caution.

What this does not establish is that the corpus exercises every path. It is
fourteen hash functions across two architectures and three optimisation levels,
and a binary with indirect calls, unions or varargs may well produce writes that
resolve nothing. The number to watch is `UNKEYED total=`.

## Eight stores collapsed, and why `definitions` is the ninth

Every value-keyed store used to be rebuilt from its name-keyed twin by
`rebuild_id_mirrors_from_name_maps`, called from `seal_value_facts` as the last
thing before any consumer saw `UseInfo`. That is gone, and with it the pretence
that the read side asking "value first" was asking anything but a mirror.

Eight of the nine paired stores are now one store each, keyed by identity:
`ptr_arith`, `forwarded_values`, `condition_vars`, `copy_sources`, `use_counts`,
`call_result_source`, `stack_slots`, `semantic_values`. Each was measured on its
own -- the corpus and the full suite -- and `copy_sources` moved a rendering:
`crc32_bitwise` at arm64 -O1 stopped hanging, because following a copy chain by
name could step between two variables differing only in case and never
terminate. The corpus is 34 of 54.

Three case-variant ladders went with them: six lookups for a use count in
`return_resolver.rs`, four for a semantic value, four for a definition. Each
existed because the fact was filed under whichever spelling its writer held.
`LowerCtx` shed eight duplicated borrows of maps `UseInfo` already owned and now
reaches these facts through the `UseInfo` it holds.

`definitions` was attempted and reverted. It is the store entangled with the
boundary this document already warns about: a caller may hold a *rendered*
spelling like `t11f80_19` where the fact was filed under the SSA display name
`tmp:11f80_19`, and the name-keyed store answered both because `lookup_name_key`
matched loosely. Collapsing it leaves seven tests failing, and they are the right
tests -- they pin colliding display names, alias precedence, and rendered-name
lookup, which is exactly what a second store was papering over.

Making an identity answer to both its SSA and rendered spellings fixes one of the
seven. It was measured on its own, and it is wrong.

Binding `t11f80_19` to the same identity as `tmp:11f80_19` puts a second, looser
key back into the name map, and arm64 -O1 falls from seven correct to six: the
`crc32_bitwise` hang returns. That hang is the one collapsing `copy_sources`
removed, and it comes back for the same reason it existed -- a rendered spelling
that two values can share is a name-shaped match, and following a chain through
one steps between values that differ in ways the spelling does not show. Widening
name resolution reintroduces the defect the collapse eliminated, one layer down.

So the way to `definitions` is not a wider name map. A caller holding a rendered
spelling has to reach the identity through the symbol table, which knows the SSA
name that spelling came from and says `Ambiguous` when more than one value was
minted to it -- refusing exactly where the map wrongly answered.

Taking that route, `definitions` collapsed too, and all nine paired stores are
now one store each. `ssa_name_for_spelling` on the fold context is the bridge;
`names_by_value_id` lets a value bound only through a name still be spelled back
out, which the passes that iterate definitions by name need, since a caller
reaching a value by spelling never gives it a variable.

Eight tests changed and each says something worth keeping. Two handed `LowerCtx`
private maps with `use_info: None`, so `make_ctx` now seeds a `UseInfo` from
them. Three hit the ordering hazard: filing a fact under a name mints an
identity, so binding the variable afterwards collides and makes the name
ambiguous -- bind first, then file. And
`exact_value_id_binding_does_not_use_colliding_display_names` asserted that a
display name two values share still answers through the name-keyed store; it now
asserts that it answers nothing, which is what the test was written to want.

`rebuild_id_mirrors_from_name_maps` is gone, and `lookup_name_key` -- the
case-insensitive matcher these stores were read through -- has one caller left,
for `var_aliases`, which is a name-to-name table rather than a paired store.

## adler32's missing compose is the return resolver, not the pruner

`adler32` at x86-64 -O2 returns `00009dd2` where `9dd21488` is wanted: the low
half holds what the high half should, and the other half is absent. The machine
composes its result in the block it returns from --

    shl eax, 0x10
    or  eax, ecx
    ret

-- and the rendering ends `return rax`, with neither instruction anywhere in the
body.

The block is lifted correctly and folded: `NORMOP` shows
`EAX_12 = IntLeft(subpiece(RAX_11), 16)` and the zero-extension after it, and
`FOLDPOST` shows the block entering the pruner with four statements and leaving
with one. So the ops exist, are understood, and are then discarded.

The obvious reading is that the pruner is wrong, because it decides liveness by
walking a block backwards and a value read only by the return has nothing in the
block that reads it. Seeding it with `FunctionLiveOut` -- which computes exactly
"what leaves through the return registers of every returning block" -- was built
and measured, and changes nothing. Reverted.

The reason it changes nothing is the finding. The statements are removed by the
whole-function pruner, not the per-block one, and they are dead *there* because
the rendered return does not read them: the return resolver has already answered
`rax` on its own. Given that return, pruning the compose is correct. The compose
is not missing because it was pruned; it was pruned because the return was
already wrong.

So this belongs to item 1 above -- a value with nine resolvers that each answer
with their own precedence -- and not to the width layer or the pruner, which is
where it looks like it belongs from the symptom. Worth recording because two
plausible fixes sit closer to the symptom than the defect, and both are inert.

### The fifth carrier guard behaves like the first four

`resolve_return_candidate_in_context` opens with

    if self.expr_is_carrier_reference(expr) { return expr.clone(); }

which short-circuits every other resolver. `rax` is `adler32`'s accumulator
carrier, so the compose is never considered. The narrow correction is that a
carrier is the value on *entry* to the returning block, and a block that writes
the return register itself has produced a newer one -- so the short-circuit
should not apply there.

That was built, with `current_return_block_redefines_return_register` deciding.
A probe confirms it does exactly what it was written to do: it fires once for
`adler32`, reporting `return_block=true redefines=true`, and the short-circuit is
bypassed. The rendering is byte-identical. Reverted.

This is the fifth carrier guard built at a resolver and the fifth to move the
answer rather than change it, and it is the first where the guard was
instrumented and shown to fire. That distinction matters: the earlier four could
be doubted as never having engaged. This one engaged, the precedence moved, and
`rax` came back by another route.

**Whatever the guards are for, one more of them is not it.** The list above says
the shape is to make the wrong answer unrepresentable -- a value that is mutable
state should not have a resolvable expression at all. Nothing measured here
contradicts that, and one more datum now supports it.

There were **four** copies of the short-circuit, not one:
`resolve_return_candidate_in_context`, `resolve_return_target_expr`,
`normalize_final_return_candidate` and `sanitize_final_return_expr`. That is why
guarding one moves the answer to the next, and it is the same duplication this
document keeps finding -- one question with several places answering it.

They now share `carrier_answers_the_return`, so the next attempt is one edit
rather than four. The predicate is still just the carrier test.

### The fifth path was a deliberate preference, and it is now conditional

None of the four was what answered `rax`. `fold_block` chooses between
`last_ret_value` and the merge over the return register, and it prefers the merge
*because* it is a carrier:

    (Some(last), Some(merged))
        if self.expr_is_carrier_reference(&merged)
            && !self.expr_is_carrier_reference(&last) => Some(merged)

That was written for `fnv1a32` at x86-64 -O1, which returns its seed when
`last_ret_value` short-circuits the merge. `adler32` wants the opposite, and both
are right about themselves: the difference is whether the returning block went on
to compute the result *from* the carrier.

`current_return_block_computes_result` decides it -- a write to the return
register that no carrier claims. The coarse form of that test, any write at all,
takes arm64 from thirteen correct to nine, because a loop latch writing `w0` in
the returning block is the carrier; excluding carrier members is what makes it
say the intended thing.

`adler32` now renders `return eax_12 | (uint32_t)(int64_t)ecx_9`, which is the
right shape, on both configurations where it was silently wrong. It does not
compile: `eax_12` is inlined rather than assigned, and the return names it
anyway. That is the same defect as `eax_8` in `murmur3_32` -- one value with two
answers inside one expression -- so `adler32` has moved out of "returns a
plausible wrong hash" and into an open defect that is already recorded and
visible.

### Where the bare name comes from, narrowed

`get_expr` in the fold is not the source. It keeps `inlined_renderings` -- what a
statement left out on the promise of being inlined would have shown -- and
answers with that. A trace on `EAX_12` shows `get_expr` is **never called** for
it, so the name never passes the resolver that knows.

The name comes from `LowerCtx::get_expr_with_depth`, which inlines only when
`should_inline(&key)` and `definition_for_var(var)` both hold and otherwise emits
`var_ref`. Its `BARENAME` probe reports, for `EAX_12`:

    inline=false has_def=false

`has_def=false` is the one to chase. `definition_for_var` answers from the value
store, and `unkeyed_writes` is zero across these functions, so the definition is
not being dropped for want of an identity. Two `LowerCtx` sites in `use_info.rs`
still passed `use_info: None` while borrowing `scratch.info` field by field;
lending them the whole `UseInfo` is legal and was measured -- `has_def` is still
false and the corpus is unchanged, so that was not it either. Reverted.

Ordering was the next hypothesis and it is also wrong, in a way that narrows
things further. `insert_definition_for_var` is never called for `EAX_12` at all,
so nothing is racing: no definition is ever *attempted* for it.

`rebuild_definitions` in `use_info.rs` would have built one, and it never runs on
this path -- a probe in its loop prints nothing for any value in the function.
The live path is `prepared_semantic.rs`, and the three places there that file a
definition each write the value-keyed store under `if let Some(value_id)`. Those
guards had no counter after the store collapse, which is a blind spot worth
closing regardless; they now count, and they read **zero** across `adler32`,
`murmur3_32` and `xxhash32`. So the definition is not being dropped for want of
an identity either.

The op *is* visited. `populate_prepared_render_definitions` reaches it and then
declines, and a `DEFFILTER` probe on the site says which test declines it:

    DEFFILTER EAX_12 self=false safe=false carrier=false

`prepared_render_definition_is_safe` refuses any expression mentioning the stack
or frame pointer, an argument register, a caller-saved register, the **return**
register, or a temporary. `EAX_12` is `eax << 16`, and its operand is a slice of
`RAX_11` -- `rax` is the return register, so the definition is refused.

Refusing it is defensible on its own terms: the expression reads mutable state
and a definition for it would render what the register held on one path. What is
not defensible is what follows. Nothing else defines the value, and it is still
rendered *by name*, so `adler32` returns `eax_12 | ...` with no `eax_12`
anywhere. **Refusing to define a value does not stop it being named**, and that
gap is the defect -- the same shape as declaring undefined names to satisfy a
detector, arrived at from the opposite direction.

Pinning the value when the definition is refused, so that it must be assigned
rather than inlined, was the obvious repair and is wrong twice over: `eax_12` is
still not assigned, and `adler32`'s return degrades from
`eax_12 | (uint32_t)(int64_t)ecx_9` to `eax_12 | 1`, so pinning perturbed a
neighbouring value into a constant. Reverted.

Two more levers were tried against it and both are inert on the corpus.

Dropping the return register from the refusal list makes `safe=true` and the
definition is filed -- `DEFFILTER` confirms it -- and the output is unchanged.
Aligning `LowerCtx::should_inline` with the fold's rule, which inlines a value
read up to three times where the analysis required exactly one for anything
register-named, is also unchanged. Both reverted.

The reason both miss is the number the probe now prints. `EAX_12` is read
**seven** times:

    BARENAME key=EAX_12 name=eax_12 depth=0 uses=7 inline=false has_def=false

Seven is above every inline threshold in the codebase, so no inlining rule was
ever going to apply, and neither the analysis nor the fold is wrong to decline.
A value read seven times is one that must be **assigned**. The fold builds no
statement for it: `FOLDPOST` reports four statements from that block, `eax_12` is
not among them, and the pruner never reports removing it.

So the question is no longer which resolver names it or which rule declines to
inline it. It is: why does the fold build no statement for an op whose
destination is read seven times?

### Answered: the return register is skipped wholesale

`fold_block` contains

    if track_return_value
        && let Some(dst) = op.dst()
        && self.inputs.arch.is_return_register_name(&dst.name.to_lowercase())
    { continue; }

Every write to the return register is skipped, on the reasoning that the return
statement represents it. That is right for the `mov eax, X` before a `ret` and
wrong for an intermediate step: `adler32`'s `shl eax, 0x10` writes `eax`, is read
seven times, and is skipped, so every one of those reads names a value no
statement assigns.

Narrowing the skip to writes nothing else reads -- `use_count <= 1` -- was built
and measured, and the result is genuinely mixed. At x86-64 -O2 `adler32` becomes
`return rax << 16 | (uint32_t)(int64_t)ecx_9`, with the shift present and
correct, failing only on `ecx_9`, which is the same defect one register over. At
-O1 it turns two visible failures into silently wrong hashes: `adler32` renders
`9dd20001` and `murmur3_32` `ec1fbeef`, because there the missing operand
resolves to something plausible instead of nothing.

The corpus total is unchanged either way, so the trade is two loud failures for
two quiet ones, and that is the wrong direction. Reverted.

**The skip is the cause and `use_count` is not a sufficient condition for
narrowing it.** What the condition wants to express is that the return statement
is the value's *only* consumer, which is not the same as it being read once --
the return itself is a read.

That condition was then written properly: a cached set of every value some op
other than a `Return` reads, and the skip applies only when the destination is
absent from it. It is the right condition and it measures the same as the
use-count proxy -- x86-64 -O1 still turns two visible failures into silently
wrong hashes -- so it is reverted with it.

The reason is the coupling, and it is the thing to know before trying again.
`adler32`'s compose has two operands and each is undeclared for its own reason.
`eax_12` is skipped because it writes the return register. `ecx_9` is not the
return register at all: it has a definition, nine uses, is not inlined, and is
still never assigned -- it is inlined into one consumer and named by another,
which is the same "one value, two answers" shape in a third place.

So fixing one operand makes the compose *look* right and compute the wrong thing,
because the other operand still resolves to whatever is at hand. **This defect
cannot be fixed one register at a time.**

And the two halves do not want the same repair. They want opposite ones, which is
the sharpest statement of why every single-sided guard has failed.

`shl eax, 0x10` is computed *in the returning block*, so its result is the value
the return wants, and answering with the `rax` carrier drops it. `or eax, ecx`
reads whatever `ecx` holds after the preceding branch, which is the **carrier**
`rcx` -- and the renderer answers with `ecx_9`, one branch's value, inlined at its
single in-branch use and named at the return where it does not exist.

One operand wants the block's computed value over the carrier; the other wants
the carrier over a branch's value. A guard that prefers either one uniformly
fixes one operand and breaks the other, and the corpus has now said so four
times.

What separates them is where the value is defined: `EAX_12` is defined in the
returning block, `ECX_9` in a predecessor. A value the returning block computes
is that block's answer; a value merged into it from elsewhere is spelled by its
carrier. That is a checkable rule, and checking it closes the loop rather than
opening a fix.

`ECX_9` cannot be spelled by its carrier, because it is not one of the carrier's
members: the members are `RCX_2`, `RCX_3` and `RCX_14`, all sixty-four bits, and
`ECX_9` is thirty-two. `varnode_to_name` keys the register map by
`(offset, size)`, so `ecx` and `rcx` are two storages and nothing connects them.

**So `adler32`'s remaining half is downstream of the location model.** The rule
that would fix it needs one name per place with width carried separately, which
is the model this branch is named for -- and that model's own prerequisite,
narrow access expressed in the value rather than the spelling, is measured above
at 34 correct falling to 13 without it.

That is the honest end of this trace. `adler32` is understood from the machine
instruction to the missing declaration, both causes are named, one of them cannot
be repaired until the location model lands, and the other must not be repaired
alone because doing so returns a plausible wrong hash. Narrowing it to
exclude a block that writes the return register itself was built and measured
twice: the coarse form takes arm64 from thirteen correct to nine, because a loop
latch writing `w0` in the returning block *is* the carrier; excluding carrier
members restores arm64 and still leaves `adler32` unchanged, the answer arriving
by a fifth path. Neither narrowing is carried, because neither has a case that
wants it.

## The undefined names are one mechanism, and it is `resolve_undeclared_carriers`

`xxhash32`'s `tmp_4700_7` is the case to follow, because unlike `adler32` it has
no register-location dependency: `tmp:4700_7` is a Unique-space temporary.

It is defined -- `IntAdd RDI_3 + 4` -- and read four times, so no inlining rule
applies and it needs a statement. The fold builds one: an `OPSTMT` probe reports
`built=true`, and the value is neither dead nor inlined. Walking the post-fold
passes shows exactly where it goes:

    prune_dead_temp_assignments_in_function_body   present
    prune_unused_pure_locals                       present
    resolve_undeclared_carriers                    gone

`drop_dead_undeclared_carriers` removes an assignment whose target is undeclared
and absent from `collect_function_local_reads`. That read set does walk `if`,
`while`, `do`, `for` and switch conditions, so the read is not being missed for
want of a traversal. It is being missed because **the assignment and the read
spell the same value differently**: the assignment names `t4700_7`, the project's
rule; the read carries the raw SSA name, which `unrendered::spell_as_identifier`
later turns into `tmp_4700_7` by replacing `:` with `_`. Neither spelling ever
sees the other, so a live assignment looks dead and is dropped, and the read is
left undeclared.

That is the whole mechanism, and it is the same one behind `eax_8`, `eax_12` and
the temporaries that break the location-model experiment.

Making `spell_as_identifier` use `format_traced_name` first is the obvious repair
and does not work: that function does not round-trip these names, and
`tmp:4700_7` comes back as `tmp`, so the rendering gets worse rather than better.
Reverted. The unification has to happen where the raw name is *emitted*, not
where it is sanitised afterwards.

`origin_name_to_expr` is that emitter, and spelling it there was retried in this
much-changed tree -- after the nine stores were collapsed, the mirror rebuild
removed and a dozen defects fixed -- on the theory that the original 6-to-0
regression might have been downstream of something since repaired. It is not. The
result reproduces: x86-64 -O0 and arm64 -O0 both fall to zero correct, and the
error is `use of undeclared identifier 't11f80_2'` -- the *correctly* spelled
name, undeclared.

That is the finding. Both spellings have partial declaration support and neither
has all of it: a raw name reaches a declaration by one route, a rendered name by
another, and moving a read from one spelling to the other loses whichever support
it had. Spelling the read correctly is not an improvement while the declaration
of the correct spelling is missing.

So this is not a site to fix; it is the non-uniform spelling boundary already
recorded above, and it now has a second measurement on two configurations saying
the same thing. **The boundary has to be made uniform before any single site on
it can be corrected**, and the retry rules out "enough else has changed" as a
reason to try again site-by-site.

## The legacy comparison-provenance path is dead, and its tests do not notice

Chasing `origin_name_to_expr`'s raw spellings led to `FlagCompareProvenance`,
which holds `lhs` and `rhs` as **strings** while the prepared path beside it holds
them as `ValueId`s. That is the paired-store shape again, in a store outside the
nine.

It is not merely a second path. It is a dead one.

`FlagInfo::compare_provenance` has **no production writer**. Production builds
`FlagInfo::default()` in `prepared_semantic.rs` and the only field it ever fills
is `flag_only_values`; the map is written in four places and all four are tests
in `fold/tests/pipeline.rs`. So `lookup_flag_compare_provenance` always returns
`None` in production, and the nine call sites that guard on it, together with
`collect_matching_flag_compare_provenance` and the `compare_provenance_expr`
family, never run.

The corpus confirms the first half: returning `None` from
`lookup_flag_compare_provenance` unconditionally leaves 34 of 54 unchanged on
every configuration, because on real input the map it consults is empty.

**A stronger claim was made here and it was wrong.** The suite also passed under
that stub, and this section previously read that as the four tests passing with
the feature switched off. Deleting the map itself disproves it: those four tests
fail immediately. Stubbing one reader is not turning the feature off --
`simplify_condition_expr` reaches the provenance by another route, and that is
what the tests were exercising all along. The stub measured one path, not the
feature, and the conclusion drawn from it did not follow.

What survives is narrower and still worth having. `FlagInfo::compare_provenance`
has no production writer, so on any real function the map is empty and every
reader of it returns nothing. The four tests that populate it by hand are the
only things that make the path run at all. They are not vacuous -- they fail when
the map goes -- but what they cover is a path production never takes.

Removing it means removing every reader, not stubbing one, and re-pointing those
tests at the behaviour they should be guarding. That was attempted and reverted
here, because the attempt was built on the claim above.

## A narrow load is unsigned unless something says otherwise

`pearson` returned `f8` for `0d` on x86-64 -O0 while rendering a loop that reads
correctly:

    local_19 = *(int8_t*)(0x1000019a0U + (local_19 ^ t11e00_3));

The machine reads that table with `mov al, byte [rax + rcx]` -- a plain byte, no
sign extension. Rendering the pointee as `int8_t` makes C sign-extend where the
machine does not, so any table entry at or above `0x80` goes negative and
corrupts the index of the next round.

The default came from `type_from_size`, which is signed, while
`analysis/lower.rs` reaches for `uint_type_from_size` at the same question. Two
answers for one property again, and this time the machine settles it: Sleigh
emits `IntSExt` explicitly when a load is sign-extended, so a bare `Load` is
unsigned and the signed default was simply wrong.

One line, and x86-64 -O0 goes from six correct to seven with no other
configuration moving. It is worth noticing what made it findable: `pearson` was
the only remaining failure whose rendering was *structurally* right, so the
defect had nowhere to hide. The undefined-name cases have structure missing as
well, which is why they resist this kind of reading.

## Both arm64 `noreturn` failures are one block that folds and is never emitted

`murmur3_32` at arm64 -O1 and -O2 renders no `return` at all, so the harness
reports `noreturn` and clang reports a non-void function falling off the end.

The function's only `Return` op is present in the SSA -- `kind=Return
srcs=["PC_1"]`, at block `0x100000924` on -O2 and `0x100000820` on -O1 -- and its
block *is* folded: `FOLDPOST` reports seven statements built and three kept. None
of the three reaches the output.

So the block is folded and then not emitted. That is not the undefined-name
family and not the switch gap: radare2 recovers no jump table for this function
on arm64 (eleven blocks, no `switch_op`), and the tail compare-and-branch chain
*is* rendered -- as nested `if`s with empty bodies, which is the same block
disappearing at each arm.

The ledger does not catch it. Both configurations print `116 built, 18 elided, 0
refused, 2 unaccounted`, so a block carrying three statements and the function's
return is recorded as neither rendered nor refused. `RefusalReason::BlockNotRendered`
exists for exactly this and is not reached, which is the second time this
document has found a refusal reason that nothing constructs.

Narrowing it further gets close. `structure_block(0x100000924)` is entered
exactly once -- a `#[track_caller]` probe puts the call at `structure.rs:945`,
the merge-block arm of `Region::IfThenElse` -- and returns three statements: two
assignments and `Return(Some(...))` carrying murmur3's whole finaliser, correctly
built. `append_stmt_body_flat` then appends it into that region's prefix.

And it never arrives. Counting `CStmt::Return` in the function body after each
post-fold pass gives **zero at the first one**, so nothing downstream removed it:
the statement was already gone before `simplify_identities_in_function` ran. A
parent region discards the sub-region that contains it.

So the defect is one region dropping another's result during structuring, not a
pass deleting a return. The empty `{ }` arms in the rendering are the same thing
seen from outside.

### The region is structured twice and the second answer wins

Tracing every `Region::IfThenElse` as it is structured shows the region whose
condition block is `0x1000008ec` and whose merge is `0x100000924` -- the block
holding the return -- structured **twice**:

    MERGEAPPEND merge=0x100000924 prefix_len=4 cond_block=0x1000008ec
    IFREGION cond=0x1000008ec merge=Some(0x100000924) owned=false terminate=false
    ...
    IFREGION cond=0x1000008ec merge=Some(0x100000924) owned=true  terminate=false

On the first visit `merge_owned_by_ancestor` is false, the merge is appended, and
the prefix holds four statements including the return. On the second it is true,
so the merge is suppressed -- correctly, because by then an ancestor has claimed
it. The output keeps the second result.

Nothing is dropping the region, then. The region is structured more than once and
the visit that omits the merge is the one that survives, while the ancestor that
claimed the merge does not emit it either. Both visits behave correctly in
isolation; what is missing is that a region structured twice has two different
right answers and nothing decides between them.

That is the same shape as everything else on this branch -- one question with two
answering paths -- and here it is worth two renderings.

Where the second visit's ownership comes from is worth one more line, because it
rules out the obvious reading. It is not a `Sequence` deferring the merge to its
next element: a probe on `sequence_owned_merge` never fires for this block. The
only region whose `merge_block` is `0x100000924` is the one at `0x1000008ec`
itself, and the push that makes the second visit see `owned=true` is that
region's *own* push, at the line before it structures its branches.

So the region is re-entered while its own deferral is live. That is a
self-nesting visit rather than an ancestor claiming a descendant's merge, and it
means the two answers come from the same region seeing its own bookkeeping.

Tracking the two callers pins them exactly. The first visit comes from
`try_structure_if_else_with_register_merge_returns` at `structure.rs:3051`, a
*speculative* rewrite that structures both arms to decide whether it applies. The
second comes from `structure_region_from_predecessor` at `1177`, the ordinary
path. The speculative visit runs in a different ownership context, appends the
merge, and its work is discarded when the rewrite declines.

Making the two contexts agree -- deferring the merge inside the speculative
attempt as the ordinary path does -- was built and measured. The corpus is
unchanged and the return is still absent, because now *neither* visit appends the
merge rather than one appending it and being thrown away. Reverted.

That eliminates the speculative visit as the cause. Instrumenting every push and
pop of `0x100000924` narrows it once more:

    DEFERPUSH 0x100000924 depth=4 from structure.rs:940
    DEFERPOP  0x100000924 depth=5 from structure.rs:947
    DEFERPUSH 0x100000924 depth=8 from structure.rs:940
    DEFERPOP  0x100000924 depth=9 from structure.rs:947

Both pushes are the region's *own*, both balanced, and nothing else ever defers
this block. So no ancestor claims it and no sequence defers it -- the two visits
simply happen at different nesting depths, four and eight, and the second is
nested inside the first's push window, which is why it sees the merge as already
owned.

Printing every region entry with its depth and caller shows what actually
happens, and it is not recursion into itself:

    depth=2  entry=0x1000008f4  from structure.rs:3049
    depth=4  entry=0x1000008ec  from structure.rs:3050
    depth=6  entry=0x1000008f4  from structure.rs:1176
    depth=8  entry=0x1000008ec  from structure.rs:1176

`try_structure_if_else_with_register_merge_returns` structures an entire subtree
speculatively, from lines 3049 and 3050, to decide whether its rewrite applies.
When it declines, the ordinary path at 1176 structures **the same subtree again**
from scratch. `0x1000008f4` and `0x1000008ec` are each structured twice, and the
second structuring is what reaches the page.

So the duplication is not a region nested in itself. It is a whole subtree
structured once to answer a question and once to produce output, with nothing
carrying the first answer to the second. That the two differ is the defect;
`murmur3_32`'s return is in the first and not the second.

One refinement matters before acting on that. The `MERGEAPPEND` probe fires
**once** for this block, during the speculative visit. The ordinary visit does not
append the merge at all -- it finds `merge_owned_by_ancestor` true and skips it --
so the two structurings do not merely differ in some detail: the only code path
that ever emits this merge is the one whose result is thrown away.

That also explains why deferring the merge inside the speculative attempt changed
nothing. It removed the one append that existed rather than adding the missing
one.

So reusing the speculative result is not a drop-in either: its arms were built
with the merge *not* deferred, so it carries the merge inside an arm, while the
ordinary shape expects the merge appended after both arms. The two are not
interchangeable.

That question is now answered, and it corrects a claim made twice above. Printing
the deferred stack at the moment of the check gives:

    OWNCHECK merge=0x100000924 owned=false stack=[8d4, 8d4, 904, 904]
    OWNCHECK merge=0x100000924 owned=true  stack=[8d4, 8d4, 904, 904, 924, 90c, 904, 904]

`0x100000924` is at index four of the second stack: pushed by the first visit and
**still live**, with three further pushes on top of it. The push and pop are
balanced, but the pop comes after the second visit, not before -- reading the
push/pop trace as balanced-and-therefore-disjoint was the error, twice.

So the second visit *is* nested inside the first's window. The region appears
twice on one structuring path: the speculative attempt at `3049`/`3050`
structures a subtree, and inside that subtree the ordinary path at `1176` reaches
the same region again. Both readings recorded above are half right -- it is one
subtree structured twice, and the second structuring is nested in the first.

The consequence is what makes it fixable. The outer visit is the one that appends
the merge, and it is doing so correctly; the inner visit skips it, also
correctly, because from where it stands an enclosing region has claimed it. The
enclosing region is *itself*, one level up, and that region's result is the one
discarded when the speculative rewrite declines.

So the defect is that a speculative attempt structures a subtree while holding
deferrals that the real structuring of that same subtree will then observe. The
speculative attempt has to leave no trace -- deferrals included.

**Half fixed, and the half matters.** `Region::IfThenElse` now records the
deferral depth before its three speculative rewrites and truncates back to it
after they decline. `murmur3_32` renders its return at both arm64 -O1 and -O2 and
the two `noreturn` verdicts are gone.

But the merge block is now emitted **twice**. Before the change `t20380_4` appears
nowhere in the rendering; after it, once as a bare assignment inside the `else`
arm and again as a declaration after the `if`/`else` -- and the assignment comes
first, so it does not compile. The underlying defect is untouched: a region is
still structured twice, and truncating the deferrals only changed which copy
survives. Losing the block and duplicating it are both wrong.

Keeping the change is a judgement, not a clear win. The return is present, the
ledger is honest about the body, and the failure is visible rather than a
silently absent function tail; the corpus is 35 of 54 either way. What it does
not do is fix the structuring, and the entry above that reads as a clean fix
should be read with this.

The corpus total does not move -- 35 of 54 either way -- because the same two
functions still do not compile. What changed is that a function which produced no
return at all now produces one, and the ledger's account of it is honest for the
first time. Five hypotheses are eliminated on the way here: a pass deleting
the return, a sequence deferral, an ancestor claiming a descendant's merge, the
speculative visit's ownership context, and any external deferral.

The `PASS after=... returns=N` probe added for this is kept, because "when did
the return disappear" turned out to be the question that made the search finite.

## What murmur3 fails on now: a pointer parameter typed as an integer

With the return restored, `murmur3_32` at arm64 -O2 fails to compile on

    t3e80_4 = (uint32_t)(arg0 + (arg1 & -0x4))[1] << 8;

`arg0` is declared `int64_t` in the rendered signature, so this subscripts an
integer and C refuses it. The C source takes `const uint8_t *key`.

The subscript itself is built correctly. `subscript_expr_for_base_and_index`
casts its base through `cast_expr_if_needed` whenever the source type is not
already a pointer, and `cast_needed` answers true for `(Pointer, Int)`. But this
expression does not come from there -- it comes from one of the two *certified*
subscript builders in `memory_renderer.rs`, which construct `CExpr::Subscript`
directly from a certified array fact and a parameter name, on the reasonable
assumption that a parameter certified as an array base is typed as one.

Two things were measured and reverted on the way to that. Making `cast_needed`
answer true for a pointer target with an unknown source is defensible on its own
-- a cast to a pointer is what makes a subscript legal, so declining it because
the source is unknown cannot be right -- and it changes nothing here, because the
source is not unknown; it is `int64_t`. And `int_meta` returning `None` for
pointers means the integer-comparison branch never swallows the pointer case, so
that was not it either.

So this is a signature-inference defect rather than a rendering one: the
parameter is used as a pointer base and typed as an integer, and every layer
downstream is being consistent with the type it was given. It is a different
family from the undefined names, and it is what stands between `murmur3_32` and
compiling on both optimised arm64 builds.

Where the uncast subscript is *built* is still not found, and the search is worth
recording because it eliminates the obvious answers. Four places construct
`CExpr::Subscript`: `subscript_expr_for_base_and_index` casts its base through
`cast_expr_if_needed`; `analysis/lower.rs:1192` casts unconditionally with
`CExpr::cast(CType::ptr(elem_ty), base_expr)`; and the two certified builders in
`memory_renderer.rs` do not. Adding the same cast to the certified linear builder
was measured and is inert, so the expression does not come from there either.

Codegen is not stripping it. `CExpr::Subscript` emits its base through
`emit_expr(base, my_prec)` at postfix precedence, and the rendering shows
`(arg0 + (arg1 & -0x4))` correctly parenthesised -- so a cast on that base would
have survived and printed.

The fifth site is `prepared_load_access_expr_from_visible_addr` in
`prepared_semantic.rs`, which turns an address expression into a subscript or a
deref and casts neither. It is a free function with no type context, but it does
not need one: it is given `elem_size`, so the pointee is known. It now casts the
base to `uintN *` before subscripting.

`murmur3_32` stops failing on the subscript at both optimised arm64 builds and
fails instead on `t20380_4`, an undeclared name -- the family recorded above. The
corpus stays at 35 of 54 for that reason, and 2334 tests pass.

The cast is not blanket noise: it is skipped when the base is already a pointer
cast, and every other subscript builder in the tree does the same thing already.
This was the one that did not.

## An identifier can now be found from the SSA name it renders

The two spellings of one value -- `t4700_7` from the project's rule and
`tmp_4700_7` from sanitising the raw SSA name -- could not be unified at either
end. Spelling the emitter costs six correct renderings; sanitising to the
project's rule collides with the symbol that already holds that name; and
`SymbolTable::follow_renames` refuses to rename onto an existing name, on the
rule that *"two names cannot become one, or two variables would"*. The table has
no merge, deliberately.

So the second symbol must never be minted. The table already records, per symbol,
the SSA value it was minted to render; it had no reverse index. It has one now --
`by_ssa_name`, maintained by `note_ssa_name`, dropping any name minted for more
than one value rather than answering for it -- and `for_ssa_name` reads it.

`origin_name_to_expr` uses it: an origin is an SSA display name, so if an
identifier already renders that value, the origin is that identifier rather than
a fresh one from the raw string. `xxhash32`'s undeclared `tmp_4700_7` is gone.

### What that exposes: an origin without a version is not a value

The same rendering now fails on `tmp_4700`, and the missing version is the point.
That origin names `tmp:4700` -- a *storage*, with no SSA version -- so it cannot
identify a value at all, and no amount of spelling unification will connect it to
a versioned assignment. `for_ssa_name` correctly finds nothing.

That is a sharper statement of this whole family than "two spellings". Some
origins are values and resolve; some are storages and cannot. The fix for those
is upstream of spelling: whatever records the origin has to record which version
it meant.

Two searches for the producer came back empty and are worth recording so they are
not repeated. `name_ref` never receives `tmp:4700` -- a `#[track_caller]` probe on
it fires for no such call -- and neither does `SymbolTable::declare_or_reuse`. So
the symbol carrying that name is created by neither of the two obvious routes,
and the name reaches the page through `spell_every_name_as_c`, which sanitises
`tmp:4700` to `tmp_4700` because it is a symbol name that is not a legal
identifier.

`SSAVar::display_name` always appends `_{version}`, so `tmp:4700` cannot have come
from a display name at all.

Four probes now come back empty for it: `name_ref`, `SymbolTable::declare_or_reuse`,
`SymbolTable::declare` (which carries its own `NAMEDECLARE` trace), and the
`NAMEDECL`/`NAMEMINT` sites in `variable.rs` and `prepared_semantic.rs` that fire
for ordinary names like `rdi_5`. None of them ever sees `tmp:4700`, `tmp_4700`,
`t4700` or `tmp:4700_0`.

Two further routes are eliminated. `SymbolTable::rename` carries the same
`R2SLEIGH_TRACE_NAME` probe and never fires for it either. And
`CExpr::External`, the variant that carries a raw `String` past the symbol table
-- "a marker the lowering emits where it has nothing to say" -- is only ever
built here with fixed strings (`return`, `__unhandled_op__`), never with a
temporary's name.

So six routes are ruled out: `name_ref`, `declare_or_reuse`, `declare`, `rename`,
the `NAMEDECL`/`NAMEMINT` sites, and `External`. The identifier reaches the page
without passing any of them.

Dumping the table settles it. A symbol named `tmp:4700` does exist, beside
`t4700_1`, `t4700_7` and the rest -- and the trace that finds it is
`NAMEFOLLOW tmp:4700_7 -> tmp:4700`. Nothing mints that name; a **rename**
produces it.

`post_rename::build_rename_map` drops the version suffix when a base has exactly
one version, which makes `x10_2` read as `x10`. Applied to a raw SSA name it
turns a value into a storage: `tmp:4700_7`, the seventh value in that temporary,
becomes `tmp:4700`, the temporary itself. `spell_every_name_as_c` then sanitises
that to `tmp_4700`, while the same value's other symbol keeps `t4700_7`, and the
two spellings diverge further than they started.

`should_exclude_name` now excludes any name containing a colon. A raw SSA name is
not a rendered identifier, and a pass that exists to make rendered names readable
has no business renaming one it cannot spell. The condition keeps its version --
`tmp_4700_7` rather than `tmp_4700` -- so a value is no longer renamed into a
storage.

It does not fix the failure. `xxhash32` still fails on `tmp_4700_7`, which is the
two-spelling problem this section opened with, and the corpus is 35 of 54
throughout. What it removes is a pass actively making that problem worse.

### Why the reverse index does not reach this case

`for_ssa_name` resolves an origin only when some identifier has been *noted* as
rendering that value. Two refinements to make it answer here were built and are
both inert: keeping the first identifier minted for a value rather than dropping
the entry as ambiguous, and preferring whichever of them is a legal C identifier.
Neither changes the rendering.

The reason is that the rendered symbol `t4700_7` never has `note_ssa_name`
called for `tmp:4700_7` at all, so there is nothing for the index to find and no
preference rule can invent it. The index works where the link is recorded -- it
removed the earlier `tmp_4700_7` failure in the state before `post_rename` was
corrected -- and this value is not linked.

So the remaining work on this family is not in the index or its tie-breaks. It is
that a symbol minted to render a value does not always record which value it
renders, and until it does, nothing downstream can tell that two identifiers are
one value.

**And recording it is not free.** The fold's `sym_for_var` notes the link;
`analysis/lower.rs` mints the same kind of identifier at two sites with the
`SSAVar` in hand and notes nothing. Making those two sites note it takes x86-64
-O0 and arm64 -O0 from seven correct each to zero -- fourteen renderings.

The reason is `definition_for_symbol`, which asks `ssa_name(id)` first and falls
back to the spelling. An identifier with no recorded value is looked up by its
spelling; giving it one silently moves it to a different lookup, and for these
values the spelling was finding the definition that the SSA name does not.

That is the shape of the whole family in one measurement. The two spellings are
not merely inconsistent -- each is *load-bearing* for a different set of lookups,
and unifying them moves values between routes that answer differently. Nothing
here can be fixed by making one site agree with another; the routes have to agree
first.

Making them agree was tried, and it is not one route but three.
`definition_for_symbol` was changed to ask the value name *and then* the
spelling, instead of one or the other, so recording a link could never cost an
identifier its old lookup. That change is safe on its own -- 35 of 54, unchanged
-- and it is still not enough: noting the link at the analysis mint sites on top
of it takes both -O0 configurations to zero exactly as before.

The third consumer is `ssa_name_for_spelling`, which `definition_of` uses to
resolve a rendered spelling back to its SSA name, and there is no fallback to add
there -- resolving differently *is* its purpose. So the link is read by at least
three places with three different meanings, and recording it changes all of them
at once.

Both changes are reverted, and looking at *what* breaks ties this thread to the
one at the top of this section. The canary is always `t11f80_2`, and the damage
is always the same shape:

    for (int64_t local_28 = 0; t11f80_2 < arg1; local_28 = t6b00)

`tmp:11f80_2` and `local_28` are one value. The stack local is its rendered
spelling and the temporary is what it was lifted from, and recording the SSA link
lets a reader reach the value by a route that bypasses the alias. That is exactly
the diagnosis recorded for the mint attempt -- *the spelling of a value depends on
context the table does not hold* -- reached now from a third direction, and it
explains the `origin_name_to_expr` attempts too. All three failed on this one
name for one reason.

So the readers do not disagree about the record; they disagree about **which of a
value's spellings is the one to print**, and the alias is not in the table. Until
it is, any route that reaches a value without going through the alias map will
print the wrong one of its two names.

That is the reconciliation: the alias has to be something the table owns, not
something each reader consults separately. It is the same statement as the
location model's, one layer up -- one name per value, with the context that
chooses it held in one place.

The corpus is 35 of 54 throughout -- this moves `xxhash32` from one undeclared
name to another rather than to a rendering that compiles.
## Open items carried forward, after Track D closed at fifty-four of fifty-four

Recorded here rather than left in a conversation, so the next session starts from
them. None of these blocks the corpus; every one of them is a thread that was
opened deliberately and not finished.

**The dependency patch is on a fork, and the corpus depends on it.**
`Cargo.toml` carries a `[patch.crates-io]` pointing `libsla` and `libsla-sys` at
branches of two pull requests -- mnemonikr/libsla#18 and mnemonikr/libsla-sys#8 --
which expose the language's user-defined operation names. A `CallOther` states
only an index, and the index is assigned by the compiled specification, so
without those names the two NEON cells cannot be identified and refuse. Both
pull requests are open and unreviewed. Until they land and release, this branch
does not build against published crates. The options are to wait, to ask, or to
vendor the two crates under our own control; the last is cheap for `libsla` at
around 1400 lines, and does not remove the dependency on Ghidra's C++ underneath.

**Nothing has been pushed.** The branch is 1092 commits ahead of master. Whether
that lands whole or in stages is unresolved.

**The radare2 sub-register widening was dropped and still deserves a PR.**
radareorg/radare2#26621 was narrowed to a case-folding fix and then closed
entirely, because the maintainer showed the real defect was ours: upper case is
`RReg`'s alias namespace, and this plugin was publishing the Sleigh
specification's own spelling. Fixed here. What was dropped along the way is a
genuine improvement: resolving *any* sub-register to its parent, not only a
32-bit one, so 8- and 16-bit argument spills are recovered. It is not landable as
it stood -- on a function that already carries a DWARF prototype it recovers the
same parameters a second time, and `dbg.palya` rendered with four parameters for
a two-parameter function -- so it needs a guard against double-counting against
debug info. That guard is the whole remaining work.

**The register roles are half sourced.** The program counter is now read from
the processor specification's `<programcounter register="..."/>` rather than
guessed from a list of spellings; all thirty specifications this plugin ships
declare it, so nothing was lost by dropping the guess. The stack pointer, the
frame pointer, the argument registers and the link register are the same kind of
fact and live in the `.cspec`, which `sleigh-config` did not export --
mnemonikr/sleigh-config#8 adds that, and once it lands those lists can go the
same way. Until then they remain guesses, and the three collisions they have
already produced are recorded in the plan.

**Two radare2 defects are noted and unraised.** A fully recovered signature is
discarded for name-linked, non-DWARF functions at `libr/anal/function.c:3949`.
And `SNAPSHOT_MAX_CALLEE_SNAPSHOTS 4` truncates callee bodies, so a caller past
the fourth callee learns nothing about it. Each is its own upstream contribution.

**Undefined behaviour in emitted C, found and not chased.** UBSan on the
vectorised renderings reports two things. The `NEON_ushl` expansion evaluates
both the left and the right shift before selecting between them, so the discarded
branch shifts by a negative count. And several `__uint128_t` loads are misaligned.
Both currently render correct values on this target and neither affects the
corpus, which is exactly why they are easy to forget.

**What fifty-four of fifty-four does and does not say.** The verifier rewrites
the C it checks: `map_image_data` cuts the image's bytes into a blob and rewrites
absolute addresses into it, which is how any function reading a constant table
passes. So the score does not say those cells emit self-contained, independently
compilable C. The diagnostic column likewise compiles with warnings off after a
repair pass. The corpus remains a canary and not a specification.

**The name-keyed role registries are gone; one name-keyed check is not.** Two
tables answered for a function's role by matching its symbol name against
hardcoded GNU coreutils and gnulib internals: `r2types`'s `role_registry`, 381
signature entries keyed on names like `xalloc_die` and `canonicalize_filename_mode`,
and `r2sym`'s `native_worker` family registry, roughly 290 names in
`has_native_worker_summary_family` plus a 335-name `semantic_family_worker_summaries`
dispatch and the `is_direct_*` matchers behind the summary route policy. Both
were unreachable for the same reason: every path into them required
`FunctionSemanticSummary.linkage == Imported`, and production never sets that --
`interproc.rs` writes `Unknown` at all four construction sites, all eight
production mentions of `Imported` are comparisons, and every assignment sits
behind `#[cfg(test)]` or `#[cfg(kani)]`. Their last consumer,
`NativeWorkerNameRouteFacts`, was written by the engine's decompile probe and
read only by tests. Deleting them removed 9,660 lines and left all fifty-four
rendered outputs byte-identical, which was checked by measuring the parent
commit and comparing `section_sha256` per cell rather than by reading the four
scores.

What survives in `native_worker` is the libc and XNU import models, which key on
an actual import marker rather than a bare name, and that is ordinary decompiler
practice.

`semantic_typedef_is_authoritative` is the part that did not go. It is a raw
`matches!` over a list of coreutils type names -- `cp_options`, `fts`, `ftsent`,
`cycle_check_state` -- with no evidence, linkage or confidence gate, and it is
live at seven sites on the emitted-C path. Deleting it is not a uniform refusal.
At `facts.rs:1000` and `:1052` and `writeback.rs:9968` a `false` answer declines
cleanly, but at `facts.rs:1280` the synthetic `sla_struct_N *` then stays in the
output where a real typedef pointer would have landed, at `writeback.rs:3278` a
typedef parameter is rewritten to `void *` and dropped from the variable-typing
context, and at `writeback.rs:9833` the polarity is inverted, so every listed
typedef would become eligible for struct re-badging. It needs a derived source
for "is this typedef a real named aggregate" before it can go;
`external_named_aggregate_has_real_layout` is already the OR-fallback at two of
those sites and is the obvious candidate.

**Fabricated pointee types are gone from the summary-kind signatures.** Those
signatures dispatch on a recovered kind, which is sound, but they named their
pointee with types private to coreutils -- `sortfile`, `keyfield`, `line`,
`linebuffer`, `arguments`, and a `printf_status_t` return. A structural kind
proves a parameter is a pointer and not what it points at, so those are now
`void *` and `int`. The standard and system spellings the same tables use
(`FILE`, `size_t`, `uintptr_t`, `__va_list_tag`, `FTS`, `FTSENT`) stay.

**One compensation was removed at the consumer because its cause was already
fixed.** `is_zero_expr` treated a variable spelled `"0"` or `"elf_header"` as the
integer zero, `elf_header` being radare2's flag for address 0 in a base-0 ELF.
The producer was the pre-rewrite `FoldingContext::const_to_expr`, which looked
every constant up in the symbol table, and its `ram:` sibling, which did so with
no magnitude guard; both were deleted in 69c80ab, and `lookup_symbol`,
`lookup_function` and `extract_call_address` no longer exist. A constant now
reaches the AST only as a literal, and the single site that mints a `Var`
spelling sanitizes it through `c_identifier_for_presentation`, which prefixes a
leading digit, so `"0"` is unreachable by construction. The arm's only remaining
match was a genuine parameter named `elf_header`, which it would have rendered as
a signed-negative test of an unrelated value -- a wrong answer rather than a
missing one.

**What the sweep found and did not fix.** Three things are named here so they
are not rediscovered. The x86 register knowledge is spread across roughly
fourteen independently maintained hand-written tables --
`seed_x86_low_register_aliases` at `r2ssa/src/function.rs:3997` is the largest,
`writeback.rs:8698` duplicates it outright, and `function.rs:3564` matches
`rbp`/`rsp`/`ebp`/`esp` without gating on the architecture at all -- while
`RegisterFamilyInfo::from_arch` in the same file already derives families
correctly by union-find over overlapping `arch.registers` ranges. Consolidating
onto that derivation is the fix. Second, `r2sym/src/loops.rs:1551` classifies a
memory term by testing whether a region's display name contains `argv`, `stdin`
or `input`, when `MemoryRegionKind::Input` already carries that as a typed field.
Third, several bounds have no derivation: `STACK_RESOLVE_MAX_DEPTH = 8` in
`r2plugin/src/lib.rs:1697` justifies itself with "in practice, most stack
accesses resolve within 2-4 levels" while the `visited` set beside it is what
actually prevents the recursion, and `r2engine/src/route.rs` decides whether a
function gets real C or a summary on a dozen unsourced thresholds. The nearby
`is_stack_reg_name` calls any register whose name merely *contains* `sp`, `bp` or
`fp` a stack register.

**The FFI boundary was audited and is sound.** All thirty-one `into_raw` sites
reclaim, error paths included: the fallible steps run before `into_raw`, so a
failure drops an owned `Box`, and the one place a raw pointer is live across a
fallible call is covered by a `Drop` impl on `R2SleighAnalysisResultV2`. The
allocator mismatch worth fearing -- Rust memory freed by C `free()` -- cannot
occur, because only two symbols are exported and C never receives Rust memory:
it copies through `sleigh_byte_view_v2_copy` into its own `malloc` and frees
that. Handles are synthetic tokens rather than addresses, with lift and engine
spaces disjoint by parity, so `from_raw` never runs on a pointer C supplied and
a stale token merely misses the map. Repo-wide there is no `transmute`, no
`get_unchecked`, no `unwrap_unchecked`, no `Vec::set_len`, and no `unsafe impl`;
the ingress decoder for the untrusted wire buffer is entirely safe Rust under
`unsafe_code = "deny"`. `Weak` is absent and correctly so: `SymbolId` is a copy
index rather than a pointer, and the one recursive `Rc`, `ConstraintNode::parent`,
has a single write in which a fresh node adopts an existing one, so every edge
points from newer to older. That last one matters beyond leaks, because three
functions walk the spine in unguarded `while let` loops and a cycle would hang
the symbolic explorer rather than merely leak it.

`crates/r2source/src/radare_abi138.rs` is the exception worth removing. It is
2,923 lines holding 134 unsafe lines, the largest concentration in the tree, and
it is the callback-based predecessor of the flat wire buffer. Nothing calls
`capture_radare_abi138` or `RadareAbi138SnapshotInput`, but a few of its
constants -- `RADARE_SNAPSHOT_CONTRACT_VERSION` and
`RADARE_FUNCTION_SNAPSHOT_SCHEMA_VERSION` -- still have external users, so
deleting it means extracting those first. Doing so would cut the unsafe surface
by roughly a third.

**Two latent defects found in the API audit, neither yet fixed.** They are
recorded here because both are traceable to a single cause and neither is
visible in the corpus.

The first is that `writeback_type_name_is_generic` and
`writeback_apply_type_name_is_generic` disagree today. The first matches an
exact list of spellings; the second ends with `normalized.starts_with("int")`,
so `int64_t` is generic to one and concrete to the other. Both spacings of every
entry are enumerated in each, which is the tell that they are parsing a
rendering rather than reading a type. The same seam has six divergent register
alias tables, six C-type-spelling parsers and four architecture-name
normalizers, and two of them disagree already: `prepare.rs:302` omits `sp` from
the `rsp` family while `writeback.rs:8704` includes it. The cause is that every
writeback candidate carries `var_type: String` and `param_type: String` while
`CTypeLike` and `MachineArch` exist; the fix is to make the candidates carry the
types and render to a string only at the radare2 edge.

The second is `ssa_var_key` at `r2types/src/prepare.rs:286`, which builds its
key as `format!("{}_{}", var.name.to_ascii_lowercase(), var.version)`. That
drops both `size` and `rename_disambiguator` -- and `rename_disambiguator`
exists precisely to tell apart "two exact source storages that project to the
same display name and width", which is its own doc comment. So the key collides
on exactly the case the field was added to prevent, and `DefUseInfo` then
encodes the resulting ambiguity at runtime as `Option<usize>` while keeping its
typed `exact_definitions` and `exact_uses` maps private and unserialized. The
key drives about twenty maps in `prepare.rs` and crosses the crate boundary as a
public field on five request types.

**Where the clones actually are.** The count is unremarkable in aggregate -- one
`.clone()` per ninety-nine production lines -- but it concentrates badly in two
places. `placement.rs:1951`, `:1954`, `:1995`, `:2035` and `:2168` deep-copy the
whole `CFunction` AST per binding per demotion round; the trial-and-rollback
design is right and the mechanism is what costs. And `FunctionFacts`, which
carries three whole-program tables, is passed by value and deep-cloned five or
six times per function, including once at `function_facts.rs:1481` purely to
compare against a rebuild and throw away. `Arc<SsaArtifact>` one level up in
`SourceOwnedFunctionFacts` is the pattern to copy. The redundant AST clone in
`codegen.rs` was the one cheap case and is fixed.

**Boundary hygiene, measured.** Of 916 items re-exported from `r2ssa`, `r2sym`
and `r2types`, 505 are never named by another crate. The cause is visible in the
visibility counts: `r2dec` uses `pub(crate)` 702 times against 197 `pub`, while
`r2ssa` is 35 against 939, `r2types` 17 against 633 and `r2source` 0 against
440. `r2dec` is the in-tree proof the discipline works. Separately `r2engine` is
two files for 25,000 lines, and its `EngineSession` is a zero-sized unit struct
carrying twenty `&self` methods across about 990 lines with no state at all.

**One instance of the banned pattern survives.** `rewrite_summary_arg_labels` at
`r2dec/src/lib.rs:1629` byte-scans already-emitted C for a literal `arg<N>`
token and substitutes names, and `is_known_lowercase_register_version_label`
nearby reconstructs from a rendered identifier whether it was an SSA-versioned
register by matching a hardcoded sixty-entry register list. Both re-derive from
text what was structured data three layers earlier. The binding plan already
owns the naming decision, so the renderer should emit the final name once.

**Four decisions taken for the remaining cleanup tracks.** They are recorded
because each one changes what "done" means for the work that follows.

*A justified fix may move rendered output.* Byte-identical stays the default
expectation and a diff has to be argued in its own commit, but a fix is no
longer blocked by moving output: the differential oracle is the correctness
check, and the per-cell change is measured and reported rather than avoided.
This is what unblocks the two predicates that disagree and the identity key that
collides, both of which are behaviour changes by construction.

*There will be one type model.* `r2dec`'s `CType` folds into `r2types`'
`CTypeLike` rather than the two continuing side by side with two renderers. The
enum needs `BitVector` and function signatures before that is lossless, and the
call sites move from tuple variants to struct variants. The reason to pay for it
is that the two renderers already disagreed about 128-bit integers and nothing
would have caught the next divergence either.

*The snapshot baseline is blessed at the current fifty-four outputs.* It had
been stale since output legitimately improved, so every cell reported
`snapshot=mismatch` and the column detected nothing. It now passes its own gate,
which means an unintended output change in the remaining tracks trips
immediately instead of hiding inside a column that was already all-mismatch.
Blessing it is only safe because the four scores are at parity and the
differential oracle passes on all fifty-four; the baseline records what is
believed correct today, not what is proven correct.

*`semantic_typedef_is_authoritative` gets a derived replacement rather than
deletion.* A typedef becomes authoritative when the external type database
actually holds a layout for it -- `external_named_aggregate_has_real_layout`,
which is already the OR-fallback at two of the seven sites -- instead of when
its name appears in a list of about two hundred coreutils spellings. Deleting
the list outright was rejected because it is not a uniform refusal: at
`facts.rs:1280` and `writeback.rs:3278` it degrades output silently rather than
declining, and at `writeback.rs:9833` the polarity inverts.

**The last name-keyed coreutils table is gone.**
`semantic_typedef_is_authoritative` was a list of about two hundred spellings --
`cp_options`, `cycle_check_state`, `randread_source`, alongside standard ones
like `size_t` -- that decided whether a typedef was concrete enough to keep
rather than replace. A name on the list was authoritative for every binary and a
name off it for none, whether or not the binary carried the type.

`type_db_resolves_type_name` answers the same question from evidence: the C
language resolves the name, or the external type database holds a real layout
for it, or a typedef entry that eventually names one. Two spellings are
authoritative by construction rather than by evidence -- `allocation_ptr` and
`memory_ptr` -- because this decompiler mints them itself and defines them in
the emitted prelude, so no binary could declare them.

Wiring it in meant threading the database to the three consumers and their
callers, about twenty sites across `facts.rs`, `function_facts.rs` and
`writeback.rs`. Two places take it as a disjoint field borrow beside a mutable
one, and `build_type_writeback_analysis_inner` binds it after the last mutation
of the parsed context so it is borrowed rather than copied -- the database is
per binary and that function runs per function.

Three tests changed, and each says something worth keeping. Two now build a type
database that declares the type they depend on, rather than relying on a
spelling being on a list. The third,
`exact_role_signature_prunes_generated_aggregate_override`, now asserts the
opposite outcome: with nothing declaring `FTS`, the locally inferred
`sla_struct_fts` layout is the only description of that parameter anything can
point at, so it is kept rather than pruned. That is the behaviour the list was
hiding.

**Two clone findings that measurement did not support.** An architecture audit
reported `FunctionFacts` being deep-cloned five or six times per function and
recommended `Arc`. Counting the actual sites finds eight `.clone()` calls in the
whole tree that touch `FunctionFacts` or its `type_facts`, and most of the
places the audit pointed at pass the struct *by value* -- a move, which costs
nothing. `Arc<FunctionFacts>` is not warranted, and wrapping it would add
indirection to buy nothing.

The one large clone that is real is `function_facts.rs:1484`, where the seal
clones the whole report, rebuilds the source-owned evidence into the copy, and
requires the two to match on seven fields. That is not waste. It is the same
independent-re-derivation pattern the binding plan uses, and its own comment
says why: a stale row could otherwise validate against itself. A proof that
shared the construction's working would prove nothing, and the clone is what
keeps the second derivation independent.

The genuinely expensive clone is in `placement.rs` -- `:1951`, `:1954`, `:1995`,
`:2035` and `:2168` copy the whole `CFunction` AST per binding per demotion
round. That one is also deliberate, and the comment above `:2035` states the
reason: dropping a declaration can leave an undeclared identifier, so the tree
is asked before anything is removed. Making it cheaper means implementing
rollback instead of trial-on-a-copy, which is an optimisation with a correctness
property to preserve rather than a defect to fix. It is the right next
performance target and it is not a small change.

**`slot_type_overrides` is the one field left as a `String`, and the attempt
that failed says why.** Converting it to `CTypeLike` is only about ten
production sites, and all of them convert cleanly. What does not survive is
`local_external_struct_reconciliation_prefers_external_names`: after the change
the reconciliation stops replacing a locally inferred `sla_struct_deadbeef` with
the external `node` it structurally matches, so a binary with real type
information gets the worse name. That is a regression in output quality, not a
test encoding an old behaviour, so the change was reverted whole.

Two things were learned on the way and are worth keeping, because both are
traps for the next attempt. `render_signature_type` materializes before it
renders, so using it to build a structural key turns every pointer to a
locally-inferred `sla_struct_*` into `void *` and makes all of them look
identical to each other -- `render_c_type_like` is the renderer for any
comparison key. And the slot field profile and the slot type override are
compared against one another as spellings, so whichever renderer is chosen has
to be the same one on both sides; they disagree about the space before a star.

The remaining cause is not yet found. The suspicion is
`local_structs_from_external_type_db`, which used to build its field types with
`normalize_external_type_name` -- collapsing an opaque placeholder to `void *` --
and now parses them faithfully, so an external struct's signature may no longer
match a local one that still carries the collapsed form. Confirming that means
printing both signatures on either side of `structurally_compatible` for that
test, which is where the next attempt should start.

**Superseded: the trap user-operation is built.** `SsaArtifact` carries
`user_operations` with a public `user_operation_name`, populated on the trusted
decompile ingress in `function.rs`; the lift expands both trap user-operations
into `SSAOp::Breakpoint`, which the obligation ledger already seeds as
`Kind::Trap`, and `r2dec` renders `__builtin_trap()`. The `pc` question was
answered by mapping the trap onto the breakpoint the pipeline already models
rather than giving the write a new disposition. Verified on the binary:
`sym.func.100003844` no longer refuses as unrepresentable and now stops at a
later cause. The section below is what was true before that landed, kept for
the reasoning rather than the plan, and it cost an agent time before the
staleness was noticed.

**What rendering a trap user-operation needs, mapped and not built.** Twelve of
the sixteen refusing real functions on `/bin/ls` now stop at one place:
`fold/op_lower/implementation.rs:2339` refuses `SSAOp::CallOther` outright. The
two user-operations this binary uses are `SoftwareBreakpoint` and
`UndefinedInstructionException`, both traps, and `sym.func.100003844` is the
clearest case -- an arm64e signature check that ends `brk 0xc471` on the failing
edge.

The pieces exist and do not yet meet.

`op_to_stmt_impl` is the right place to emit the statement, and
`observed_input` beside it is how each operand gets accounted to the observation
journal. `FoldContext::callee_declarations` already produces the `externs` on
`CFunction`, so a declared `void __r2sleigh_brk(uint32_t)` can be emitted and the
result still compiles standalone, which is what the corpus requires.

What is missing is the user-operation's *name*. `SSAOp::CallOther` carries only
`userop: u32`, and the index is arch-dependent, so matching on it would be
exactly the kind of magic constant this project refuses. The name lives in
`ArchSpec::user_ops`, which reaches `TrustedSsaArtifact` as a private field and
stops there -- `SsaArtifact`, which is what `r2dec` is handed, does not carry it.
Carrying the user-operation names onto the artifact is the first step and is
bounded.

Two further obligations have to be satisfied, and each is a proof the tree
checks rather than a detail. The trap writes `pc`, which is Sleigh's way of
saying control leaves for an exception handler, so that write needs a
disposition -- most likely the block simply has no successor and the value is
unobserved, but that has to be shown rather than assumed. And a call has
effects, so the effect ledger has to account for the statement.

This was mapped and deliberately not started: it is a three-layer change, and
the two multi-layer conversions attempted late in the same session both had to
be reverted whole. It is worth doing next, from a clean start, in that order.

**Where the /bin/ls refusals actually are, after the trap and duplication
work.** The headline count is 114, and 88 of those are the sixteen-byte import
thunks in `__TEXT.__auth_stubs`. Of the 48 real functions, 22 render. The
ROADMAP's coverage table carries the per-cause breakdown; what matters for the
next session is that no single remaining real-function cause accounts for more
than seven functions, so the work from here is a series of small, separately
traceable fixes rather than one large one.

**The import thunks are one cause, and the reason they are not taken is
recorded rather than forgotten.** Each is `braa x16, x17` after loading `x16`
from `__auth_got`. Sleigh writes that as `AuthIA(x16, x17); pc = x16;
goto [pc]`, so `pc` is properly defined -- the refusal is not an undefined read
but `ExactUseRequiresRenderedOccurrence`: nothing in the renderer has a shape
for a branch through a value, so the value the branch reads is never rendered.
The honest C is a tail call. Claiming it needs a proof that the target is not
one of this function's own blocks, because an unresolved jump table arrives in
exactly the same shape, and radare2's own resolution is advisory. Two candidate
proofs were considered and neither taken: a single-block function has nowhere
inside itself to jump to, which is exact for these thunks but not a general
rule; and the `__auth_got` slot carries a relocation naming the imported symbol,
which is real evidence but yields a thunk that calls the symbol radare2 has
already named the thunk after. The value of rendering them is low either way,
which is why the count is large and the priority is not.

**Diagnostics that paid for themselves and are worth reaching for again.** Two
temporary probes found both defects fixed in this stretch faster than reading
would have. Printing every `PcodeOp::BranchIndirect` the lift produced, with the
instruction address, showed that Sleigh emits 97 of them on `/bin/ls` and that
84 are `braa`, 9 are `brk` and one is a jump table -- which is what separated
the trap cause from the tail-call cause. Note that `crates/r2sleigh-lift/src/
pcode.rs` is *not* the live translation path; `translate_pcode_op` in
`disasm.rs` is, and a probe placed in the former never fires. Printing the three
components of an incomplete return boundary showed all four of its functions
failing on `values=0` against `slots=1`, which led straight to the liveout walk
reading past a call.

**Three real-function refusals traced but not fixed.** Each is a separate
defect with a diagnosis good enough to act on directly.

*A call argument the function only passes through can never be discharged.*
Four functions on `/bin/ls` -- `fcn_100003110` is the smallest, thirty-two bytes
that call one function and return one -- refuse with a `CallArgument` obligation
scored `BlockNotRendered`. The cause is a seam. `obligation.rs` seeds a
`CallArgument` obligation for a `SourceCallArgumentValue::PreservedEntry`
argument with an empty input list, and says why: the function never defines the
carrier, so no SSA value is named for it, but the call reads it either way. The
occurrence classifier in `fold/context.rs` requires `!obligation.inputs.
is_empty()` and that every input appear in the rendered call's `proof_values`, so
an obligation with no inputs cannot be satisfied by any rendering. The
certificate carries no argument either, so the call renders as
`sym_func_1000038c0()` with the argument dropped. The honest C passes the
function's own parameter, which means the parameter has to exist: interface
recovery derives parameters from entry *reads*, and a carrier that is only
passed on is never read. Fixing this properly spans `recover_interface` (a slot
a call passes through as `PreservedEntry` is a parameter), the call-argument
rendering (which is keyed by `ValueId` and has none here), and the classifier.

*A stack write with no stack observation.* `fcn_1000040d8` and `fcn_100004080`
refuse in placement with `unobserved_binding_write` on a binding named
`stack_m40` that owns no values. The audit finds the symbol written in the tree
with no `StackAccess` observation active on that statement -- the observations
present are one `Write` naming a different binding and several `Other`. The next
step is to find where the assignment to a stack object is emitted without
recording its `StackAccess` target.

*A conflicting value behind the placement refusal.* Suppressing the
`unobserved_binding_write` refusal on `fcn_1000040d8` does not render it; the
seal then refuses with `ConflictingValue`, so there is a second finding behind
the first and both belong to the same investigation.

**Rendering a direct tail call: designed, measured, and not taken.** Refusing
the transfer is in the tree; rendering it is not, and the blocker is exact.

Modelling the exiting branch as the call it is turns out to be a one-place
change in `r2ssa`: `CFG::from_blocks` is the single funnel every SSA
construction passes through, it has the whole block set, and rewriting the
block's `R2ILOp::Branch` into `R2ILOp::Call` there is enough for the op, the
terminator and every consumer downstream, because everything after it reads the
CFG rather than the original IL slice. The fallthrough a call terminator claims
must be cleared in the same pass when the address after the call is not a block,
or the linear form emits a jump to a label nothing declares.

That was written and measured, and it made `/bin/ls` worse: 123 refusals became
125, and the comparator went from one refused obligation to eighty-one. A call
boundary is complete only when a source-owned callsite interface exists for that
site and its raw identity matches, and radare2 reports no call at a branch. An
incomplete boundary is seeded `VolatileOrUnknownEffect` and then
`taint_incomplete_boundary_inputs` spreads a live-value obligation across
everything reaching it, which is where the eighty-one come from.

So the remaining work is not in `r2ssa` at all: the source-facts layer has to
offer a callsite interface for a direct branch that leaves the function, the way
it does for a call radare2 reports. Until it does, the branch rewrite is a
change that renders nothing new and refuses more, and it was reverted rather
than left in the tree.

**The composed return value is the top corpus refusal, and it is diagnosed.**
Eighteen of the eighty-two refusing functions in `tests/coverage` stop at the
same line: `fold/op_lower/implementation.rs` declines a return boundary whose
`register_compositions` is not empty. The evidence line says which -- `at_
mismatch=false incomplete=false compositions=1 values=0` -- so the boundary is
complete and the value is simply assembled rather than written whole.

`gate_one` at x86-64 `-O1` is the shape: `xor eax, eax` then `sete al` leaves
the returned `int` as a thirty-two bit zero with a one-byte result laid over its
low end, which is the ordinary way a compiler materialises a boolean. The facts
needed to render it are already built and already validated --
`SourceReturnRegisterCompositionFact` carries the base definition and the
overlays in order, and `validate` checks them against the graph -- and the
renderer has no form for it, so it refuses. Rendering one is
`(base & !mask) | (overlay << shift)` per overlay, in the recorded order.

This is the largest single cause in the deterministic gate and the next thing
to take.

**Rendering a composed return value: mapped, and larger than it looks.**
Eighteen of the corpus gate's refusals stop at one line, and the evidence names
the shape exactly -- `at_mismatch=false incomplete=false compositions=1
values=0`. The boundary is complete; the returned value is assembled from a
full-width base and ordered contained-slice writes over it. `gate_one` at
x86-64 `-O1` is the case: `xor eax, eax` then `sete al`.

The facts are all built. `SourceReturnRegisterCompositionFact` carries the base
definition and the overlays in order, `validate` checks them against the graph,
and `obligation.rs` already seeds the `ReturnValue` obligation with every value
in the composition. Rendering one is `(base & !mask) | (overlay << shift)` per
overlay, with the shift taken from `offset_bytes` on a little-endian target and
refused otherwise, because `offset_bytes` is a physical register-space offset
and its meaning as a shift depends on the specification's layout.

What makes it big is a single-value assumption downstream.
`ReturnValueCertificate` has one `value` field, `collect_return_value_certificates`
skips any boundary with compositions outright, and that one value is threaded
through the render plan's `ReturnValueRenderFact`, the binding plan, placement's
`certificate.value == value`, and the observation journal's
`symbol_for_value(certificate.value)`. Rendering a composition means making that
field hold an ordered set in five places, which is the shape of change this
document already records being reverted whole when attempted late in a session.
Take it first, from a clean start, in that order.

Implementing the five components: where each one hooks in
---------------------------------------------------------

Written after the dropped-call defect was fixed, with the hook points found
rather than guessed. The decisions these obey are recorded in
`doc/decbench-plan.md` and were taken by the user directly: radare2's analysis
is load-bearing provided the proof line marks what came from it, a type may be
asserted from use evidence with a conflict refusing that value alone, an
unknown-signature call takes its arity from the convention's live argument
registers, and aggregate recovery goes all the way in the first pass.

**Component 1, the call-boundary model -- done for the dropped calls.** All 26
calls in `bzip2recover` at `-O0` now render, format strings included. What
remains of this component is the arity rule for a callee no prototype describes:
`prepared_call_max_arity` returns `None` for a variadic callee and
`canonical_call_authoritative_args` then takes every argument the facts supply,
which is right; a callee with *no* signature reaches the same path with no facts
at all. The live-argument-register rule belongs there.

**Component 2, the data reader -- half done.** String literals already work end
to end and render inline: `OwnedFunctionImage::string_literals` is filled from
radare2's snapshot API in `snapshot_walk.c`, crosses the wire in
`snapshot_wire.c`/`snapshot_wire.rs`, and reaches the renderer through
`DisplayNames::insert_string`. Named globals do not, so `progName` still renders
as `0x6000` and `stderr` as `*(uint64_t*)0x5020`.

The channel to build is a mirror of the string one, and every piece of it
already exists except the payload:

* a data-symbol view on radare2's function snapshot, beside
  `r_anal_function_snapshot_string_literal_view` -- this is in our radare2 fork
  and is Sleigh-specific plumbing rather than a correctness fix, so it does not
  need its own upstream pull request;
* `walk_symbols` in `snapshot_walk.c`, beside the string-literal loop;
* a `data_symbols: Box<[(u64, String)]>` field on `OwnedFunctionImage`, with the
  wire's version bumped;
* `DisplayNames::insert_symbol`, which already exists and is never called;
* in the renderer, a constant that names a known data address renders as that
  symbol rather than as its address.

Provenance is the new part: the proof line has to say the name came from
radare2. Nothing in the tree marks a fact's origin yet, so this component builds
that machinery and the three after it use it.

**Components 3 and 4, types and stack locals.** `recover_interface` mints the
interface and is where signedness, pointer-ness and width belong; `r2types` is
where a value's type is carried. The evidence rules are the ones the user
settled: a value used as a load address is a pointer, a signed comparison proves
signedness, an access width proves the width, a strided access off one base
proves an array, and consistent offset access off one base proves a struct. A
conflict refuses that value's type and leaves today's default, per value rather
than per function. `stack_m16` becoming a named typed local is the same work
seen from the frame's side, and DecBench weighs it directly -- the ground truth
for `bzip2recover` has 39 stack variables and we align none.

**Component 5, expression folding.** `ZF_1 = (a - b) == 0; if (!ZF_1)` folding to
`if (a != b)` is the flag case, and the unoptimised spill-and-reload round trip
is the other. Both are protected by the corpus differential oracle, and both
have to answer the ledger question the duplicated-tail work already answered
once: one rendered expression discharging several source obligations is a fold,
not a loss, and the accounting has to say so.

**Component 5 needs a machine-expression materialiser, and that is the whole of
it.** The paragraph below was written before the policy was tried, and it is
wrong about where the work is. Extending the inline disposition to computed
values was implemented and reverted: the plan accepted it, the corpus stayed
green, and nothing changed in the output, because
`fold/op_lower/lowering.rs` materialises a planned inline *only* when the
machine expression is a `Constant` and answers `InvalidPlannedInline` for every
other kind. Five values in one `-O0` function qualified under the rule and none
of them could be rendered.

So the missing piece is a materialiser from `MachineExprKind` -- arithmetic,
comparison, casts, shifts, selects, concatenations, extracts -- to a C
expression. That is a second renderer beside the operation lowering, and it is
why `Inline` has only ever meant a literal. Build it first; the policy change
below is then a few lines and is already written once in this document.

**The policy, once the materialiser exists.** Folding
`ZF_1 = (a - b) == 0; if (!ZF_1)` into `if (a != b)` looks like an expression
rewrite, and `reconstruct_flag_conditions_in_function` already tries it, but the
reason it cannot succeed is upstream: `binding_plan::construction` gives
`ValueDisposition::Inline` only to values with `constant_bits()`. Every computed
value is `Bound`, so it gets a local, so a flag or a temporary is a statement
before it is ever an expression. That is why 93 per cent of rendered functions
carry `tmp_*` chains and 58 per cent expose CPU flags as C.

The change is to extend the inline disposition to a computed value that has
exactly one use, whose defining operation is pure -- no memory access, no call,
no trap -- and whose use cannot be reordered past a redefinition of anything it
reads. The last part is the question `rules::set_outlives_a_redefinition`
already asks for coalescing, and the answer belongs beside it: the rule goes in
`binding_plan/rules.rs` so construction and seal both call it, which is the
arrangement that exists precisely so a policy like this cannot drift between the
two derivations.

Two consequences to plan for. The obligation ledger counts one rendered
occurrence per source effect, and an inlined value folds two statements into
one, so the accounting has to accept a fold the way it now accepts a duplicated
tail -- the machinery for saying "this is one execution, not a loss" is already
there. And placement stops declaring a local that no longer exists, which is the
path that is already exercised whenever a value is `Inline` today.


**The materialiser is built; the policy that uses it needs the journal.** A
planned inline is no longer limited to a literal:
`materialize_machine_expr` in `fold/op_lower/lowering.rs` renders arithmetic,
bitwise and boolean operations, comparisons, shifts, negation, copies and
selects, and recurses back into the plan at a `Source` leaf, which is where the
machine expression stops and the plan's own answer for that value begins.
Anything outside that set -- a memory read, a merge, a division that traps, a
width change or a flag whose C form depends on a type the expression does not
carry -- still keeps its statement, and the set is stated once so the plan can
be made to mark exactly what the renderer can take.

Wiring the policy to it was implemented and reverted twice, and the second
attempt found the real remaining blocker. The first attempt did nothing, because
the disposition loop set `Inline` and a later loop over binding components
overwrote it with `Bound`; the fix for that is to exclude inlinable values from
`rules::component_eligible_values`, exactly as constants are excluded, so the
rule that decides eligibility and the rule that decides inlining are one place.
With that done the disposition survives and the renderer materialises it -- and
the whole-binary gate then reports every function refusing with
`missing program-variable authorization`.

That is the last piece: the observation journal authorises a rendered value
through its occurrence, and an inlined value is read where another value's
statement is emitted rather than in one of its own. Until the journal accounts
for that, the plan cannot mark anything inline. Take that first; the policy is
already written twice in this document and the materialiser is in the tree.


**Wiring the inline policy: three blockers, found in order, each hidden behind
the last.** The attempt was made three times and reverted three times. Nothing
of it is in the tree except the materialiser, which is committed and inert. The
value of the attempts is the order, because each blocker is invisible until the
one before it is fixed.

*One.* The disposition loop in `construction` sets `Inline`, and a later loop
over binding components overwrites it with `Bound`. Nothing changes in the
output and nothing refuses, which reads as the rule not matching. The fix is to
exclude inlinable values from `rules::component_eligible_values`, exactly as
constants are excluded -- and to put the inlining rule *inside* that function so
the eligibility question and the inlining question cannot be answered
differently.

*Two.* With the disposition surviving, the seal disagrees: it categorises a
non-constant value as nothing at all, so `build_shadow` fails and every function
refuses with `missing program-variable authorization`. The fix is an
`UpstreamValueDisposition::InlineExpression` beside `InlineConstant`, produced
from the same shared rule, and mapped through the shadow report -- where
`NormalizedValueObservation::InlineNonLiteral` already exists and had never had
a producer.

*Three, and still open.* With construction and seal agreeing, every function
still refuses with the same message from a different place: the rendered-identity
audit, which authorises a rendered value through an occurrence of its own. An
inlined value is read inside another value's statement and has no occurrence to
authorise it. That is the piece to build first next time, because the two above
are known and cheap once it exists.

The materialiser handles ten expression kinds today. A width change, a flag, a
memory read, a merge and a trapping division are deliberately outside it, and
the set is stated in one place so the plan can be made to mark exactly what the
renderer can take.

**Where the rewriting layer belongs, decided by measurement.** Folding was built
on the emitted C tree, and it worked: `gate_one` at x86-64 `-O0` went from
seventeen statements to seven, every `tmp_*` chain gone, the flag folded into
its `if`, and the effect ledger reporting nothing refused. Then the differential
oracle reported twenty-one of fifty-four corpus cells computing the wrong
answer.

The cause is the layer, not the bugs. In SSA a value is written once and the
version says so. In the emitted C the same value is a named local that is
written again, so moving an expression down past a write to something it reads
returns the new value instead of the old. Adding a span analysis -- what the
value reads, whether it touches memory, whether anything between assigns to it,
whether a call intervenes, whether a control edge is crossed -- took the wrong
answers from twenty-one to six, and six is still six. That progression is the
diagnosis: it is SSA's guarantees being rebuilt by inspection, and each addition
recovers a little more of what SSA knew for free.

So the one rewriting layer the user asked for belongs on the SSA side, where
"written once" and "nothing redefined in between" are structural rather than
inferred. `rules::inlinable_values` already computes exactly that correctly, and
the attempt that used it failed only on the journal's contract -- which the user
has since settled: a folded obligation's occurrence *moves with the expression*
rather than being elided, and the journal is to accept an occurrence found at a
site other than the statement that originally carried it.

That makes the remaining work specific. Take the SSA-side rule, the
materialiser that is already committed, and the seal category that accepts a
computed inline; then change the journal so a moved marker discharges its
obligation where it now sits. The AST experiment is not the thing to finish --
it is the evidence for not finishing it.

**The SSA-side attempt, and the exact probe it stopped on.** With the layer
question decided, the plan side works: the rule marks the right values, the seal
accepts a computed inline once it derives the same rule itself, and the
materialiser renders the expression. Four blockers fell in order. The fifth is
where it stands.

An inlined value's expression contains operand reads, and placement refuses them
as `unobserved_binding_read` because the observation that authorises a read is
attached to the statement being emitted, and that statement no longer exists.
Marking them at the site they now occupy is what the decided model calls for --
the occurrence moves with the expression -- and the mechanics are:
`observe_optional_normalized_input_uses_expr` wants a `NormalizedOpSite` and an
input index, the site is found by scanning the current block for the operation
whose source instruction is the inlined value's definition, and the input index
must come from `graph.use_sites(operand)` rather than from the defining
instruction's operand list, because a machine expression is a tree over the
arena and its leaves do not stand one-to-one against SSA inputs.

That works for some operands and returns nothing for others: for one function,
`ValueId(16)` used by inlined `ValueId(19)` finds no use site at that
definition, while a neighbouring case resolves cleanly. The next step is to
print, for a failing pair, what `def_inst` and `use_sites` actually hold -- the
answer decides whether the leaf names a value the definition does not read
directly, in which case the operand's use has to be located through the arena's
own structure rather than through the SSA instruction.

Nothing from any of this is in the tree. The materialiser is committed and
inert; everything else was reverted, and every gate is green.

**Expression folding: eleven blockers cleared, the patch kept, the count still
open.** The work is saved as `doc/wip/expression-folding.patch` rather than
described, because describing it has twice proved less useful than the diff.
Apply it to resume; every gate is green without it.

What it contains, in the order the blockers fell. The shared rule marks values
with one use, a movable definition and nothing rewritten in between. Component
eligibility excludes them, so a binding component no longer overwrites the
disposition. The seal derives the same rule itself and accepts a computed inline
beside a literal one, which needed an `InlineExpression` category carried through
the shadow report. The materialiser renders ten expression kinds and recurses
into the plan at a `Source` leaf.

Then the part that is genuinely new, and is the decided model made concrete. A
read inside a moved expression has no use to authorise it, because the use
belongs to a statement that is no longer emitted. Three attempts to reuse the
existing machinery failed for instructive reasons: the normalized-input path
marks by projection index and the leaves of a machine expression do not stand
one-to-one against SSA inputs; the certified-value-read path requires a boundary
read and this is not one; and the emitting block cannot be read from ambient
state because the materialiser is reached from callers that carry none -- it
comes from the value's own definition, which the inlining rule guarantees sits
in the same block. What works is a new observation target, `InlinedValueRead`,
carrying the value, its binding, its symbol and the block, mapped to a placement
target that authorises a read of that binding. With it, declaration placement
passes, which had been the wall since the first attempt.

What remains is the journal's invariants, and the way to take them is not one
at a time. Each is an assumption that every value has a statement of its own,
and satisfying them in the order they surface has now cost fifteen cycles: a
bound value whose only appearance was an inlined operand has no value cell, so
the cell is marked at the read; the inlined value itself then has no cell, so it
is marked where it is rendered; the uses inside the vanished statement then have
no rendered occurrence, so they are marked there too; and the next one is
waiting behind that.

The patch carries all of those. The remaining work is to stop discovering them:
enumerate what `first_unaccounted_render_observation` and the exact-use audit
require of a value, list which of those assume an emitted statement, and satisfy
that set together rather than chasing the next refusal. That is a reading task
against one file, and it is what the next session should start with rather than
another build-measure cycle.


**The reading paid off, and named the next failure exactly.** Reading the audit
instead of chasing its refusals showed it asks three things of the tree, not
one: every value has a cell, every recorded use has one, and every instruction
with an output has a write cell. A definition rendered where its value is read
fails all three, and the fourth requirement is the effect ledger's -- nothing
asks an unemitted statement for its obligations, so they score as refused.

Answered together, one function folds end to end: `gate_one` at x86-64 `-O0`
renders seventeen statements as fourteen with `ZF_1` gone into its `if`, and the
proof line reads `0 refused`. That is the first time any of this has worked
through the whole pipeline.

It is not landable. Thirty-nine of the fifty-four corpus cells then fail at
generation, and two name-resolution unit tests fail. The generation failures are
the thing to take next, and the likely cause is in the same place as the fix:
`observe_inlined_definition_expr` asks `rendered_use_observation` and
`rendered_write_observation` for every operand and output of the definition, and
either can answer `Refused` for a disposition the plan never intended to render
here -- which turns a fold into a hard generation failure rather than a decline
to fold. The rule that marks a value inlinable should require those dispositions
to be renderable, so the plan and the renderer agree before the tree is built,
which is the same discipline that fixed the seal.

**Folding now reaches forty-seven of fifty-four, and the three that are wrong
are the ones this project has been wrong about before.** Marking a constant leaf
of a moved expression -- it is rendered by the materialiser rather than as an
operand of a statement, so nothing else marks it -- took the blocked cells from
thirty-nine to five. Forty-seven compile, forty-six agree with the oracle, and
three do not: `crc32_bitwise` on both architectures and `pearson` at x86-64.

Those three are loop carriers, and they are the same functions
`rules::values_read_together` and `rules::set_outlives_a_redefinition` were
written for. The inlining rule's safety check is a weaker relative of both: it
asks that nothing between the definition and the use writes a location the
expression reads, which is exact within one pass through a block and says
nothing about a value that is carried around a back edge. Extending the read set
to every leaf of the rendered expression, rather than the defining
instruction's own inputs, did not change the three -- so the hazard is the
carrier, not the leaves.

The next step is to ask the existing rules rather than to invent a third: a
value whose definition and use straddle a carrier must not be inlined, and
`set_outlives_a_redefinition` already knows how to phrase that question for a
set of values. Ask it for the single value here.

**Folding lands: fifty-one of fifty-four, none wrong, and two thirds of the
statements gone.** The three cells that computed the wrong answer were not the
carrier hazard the section above expected. They were two renderings of one
value disagreeing about signedness: `fold::op_lower` renders `IntSLess(x, 0)`
with `(int32_t)` casts from the operation, while the materialiser re-derived
the same value from the machine arena, whose `interpretation` field says how a
value is later *read* rather than how the operation computes it. The casts
vanished and a comparison that was sometimes true became one that never is.

The fix was the smaller of the two the previous session named: the fold now
moves the expression the operation lowering already produces, by lowering the
defining operation in expression mode at its own site. Nothing is derived
twice, so nothing can disagree. It also gives the operands their ordinary
observations at the definition's site, which is what authorises reads that end
up nested inside another statement.

One thing had to change for that to work at all. Expression mode delegates to
statement lowering, which spells a left-hand side before it builds the
right-hand side, and an inlined value has no left-hand side -- the plan
withheld its symbol precisely because it is written nowhere. Every ordinary
arithmetic operation therefore refused. `FoldingContext::inlined_definition`
now suppresses the left-hand side and collapses the assignment to its
expression, so statement form and expression form come out of one body and
cannot drift.

Four separate defects surfaced on the way, each fixed at its origin rather than
near the symptom:

`CTypeLike::Bool` rendered as `bool`, which is a macro from `<stdbool.h>`, and
the emitted translation unit includes no headers of its own. Thirty-four cells
failed to compile the moment a predicate reached a cast. It is `_Bool` now.

The snapshot's data-symbol walk in the radare2 fork skipped every flag spelled
`sym.`, discarding the objects it exists to report: a compiler-emitted lookup
table carries a `sym.` flag exactly as an imported function does. The reference
decides now -- a data or indirect-code reference whose target is not a function
entry -- so `pearson`'s table renders as `&_pearson_tab` instead of a bare
address the recompiled program dereferences and dies on. That is
`radare2@ef38a98bb9` on `anal/subregister-argument-spills`.

An inlined *literal* returned straight to its caller from `planned_value_expr`,
skipping every cell it and its defining instruction owe.

`carry_outer_expr_observations` carries only a source expression's leading
markers. That is right when the replacement keeps the source's subtrees and
wrong when it discards them: folding a cast chain down to one literal, or an
address into `&name`, deletes the nodes the inner markers sat on.
`carry_all_expr_observations` collects every marker in the collapsed subtree,
because the replacement renders everything the source rendered.

**What is still open.** Three cells refuse -- `murmur3_32` at x86-64 and arm64
`-O0`, `xxhash32` at x86-64 `-O0` -- and six functions regress in whole-binary
coverage, 239 of 313 against a baseline of 245. All nine are one cause, traced
but not fixed.

The trace, so it does not have to be repeated. Both refused obligations in
`murmur3_32` are `LiveValueProducer` on a `Copy` whose output the plan inlines.
The marker for each *is* allocated -- `allocate_effect_targets` runs, and an
instrumented seal shows the id present in `targets` and absent from the final
AST -- so the fold and its accounting are working. What is missing is the
statement. `murmur3_32` renders through the unstructured fallback in
`consumer_structured::primary_body_for_semantic_route`, whose residual comment
reads `rendered control-domain occurrences do not exactly cover block
0x100000a61`; that path calls `rollback_tentative_structure` and re-renders
through `linearize_function_body`, and the emitted body contains no `push rbp`
store at all. The value was folded into a statement that this rendering does
not emit, so its occurrence has nowhere to live.

Things already ruled out by bisection, each with an env-gated switch that was
removed afterwards: none of the five `cleanup_recurse` rewrites, none of
`simplify_identities_in_function`, `reconstruct_flag_conditions_in_function`,
`normalize_redundant_return_carrier_casts`,
`normalize_declared_assignment_literals`,
`normalize_comparison_operand_order`, or `fold_constant_arithmetic_in_function`
drops these markers. `fold_block` reports eighteen statements built for the
entry block and only about ten survive, so the loss is between `fold_block` and
the sealed body, on the linearized path.

`rules::inlinable_values` already declines to fold into an instruction a
certificate elides, via `certified_elided_read_instructions`. That predicate is
the right shape and the wrong reach: the frame store here is not covered by
`stack_frame_round_trips`, `machine_return_controls` or `stack_geometry` in this
function. The complete question is whether the *use instruction will be
emitted*, and the honest place to answer it is the same set the observation
journal builds when it seeds `elided_uses` -- which is computed from the
certificates plus `plan.use_disposition`, both available to
`inlinable_values`. Extracting that seed into `binding_plan::rules`, so the
journal and the plan read one statement of the rule instead of two, is the next
step. Do not answer it at the ledger: an obligation nobody rendered is not a
detector to be silenced.

Two measurements worth keeping. Folding is where nearly all the statement
reduction lives, and copies are where nearly all of folding lives: the nine
x86-64 `-O0` corpus functions render in 1014 statements unfolded, 1002 with
copies excluded from folding, and 367 with folding complete. Excluding copies
is therefore not an option -- it buys a green gate for one percent of the
benefit. And test fixtures throughout the tree were built from single-use
values, which fold away entirely; each one that needed something bound gained a
second reader, which is a fixture correction rather than a concession.

**The corpus is green with folding on, and the two remaining coverage
regressions are narrower than the earlier note said.** The dead frame slot was
the whole of the corpus failure:
`certified_dead_frame_slot_accesses` names the `push rbp` store that the effect
ledger elides as `DeadFrameSlotStore`, so `certified_elided_read_instructions`
reports it and the plan no longer folds anything into it. Fifty-four of
fifty-four cells now pass every gate, and whole-binary coverage is 243 of 313
against a baseline of 245.

The two left are `branchy_arm64_O2::sym._inverted_goto` and
`hashes_x64_O1::sym._siphash24`. In `siphash24` the orphans are two address
computations that fold into one load, `InstId(594)` and `InstId(595)` reaching
`InstId(596)` at block `0x100000ae3`. Three explanations were tried and each is
recorded here because each is wrong and cost a build to find out:

Declining every use whose disposition is `MachineUseDisposition::MemoryAddress`
does clear the refusal and is far too broad. An ordinary `*(uint8_t*)(base + i)`
carries the same disposition and does render its address, so the nine x86-64
`-O0` corpus functions went from 367 statements back to 912 -- most of folding,
given up to fix two functions.

Declining only the addresses whose access the renderer answers without reading
them -- `certified_stack_owner_expr_for_memory_fact`, which returns a slot's
name, and the certified array fact with a base or index -- is exact and does
not fire here. The probe says the load's fact exists, names `ValueId(644)` as
its address and `ObjectId(0)` as its object, and neither branch claims it. So
this access does reach `certified_memory_address_expr` and its address
expression is asked for.

Carrying the dropped observations through the address rebuild does not fire
either. `render_certified_structured_memory_expr` takes the address apart with
`certified_linear_address_components` and puts it back as `base[index]`, which
looked like the same marker leak `carry_all_expr_observations` was written for,
but adding the carrier at both rebuild sites changed nothing measurable --
coverage stayed at 243 -- so it was reverted rather than left in the tree.

What that leaves is the question nobody has answered directly for these two:
whether the markers are allocated at all. The instrumentation that settled it
for `murmur3_32` is worth rebuilding rather than guessing again -- a
`R2SLEIGH_DEBUG_DROPPED` env check in `seal_preserving_effects` that collects
the `RenderObservationId`s the walk sees and prints every `ObservationTarget::
Effect` in `targets` that is missing from that set. Allocated-and-missing means
the statement is dropped and the search is for which pass drops it; never
allocated means `planned_value_expr` was not asked, and the search is for who
renders that load instead.

**Where `siphash24` actually loses its two markers, measured.** The markers are
allocated and then absent from the sealed AST, and the neighbouring operations
at that block -- `Op(36)`, `Op(37)`, `Op(40)`, `Op(41)`, `Op(42)` -- are not
among the missing, so the load's own statement is rendered. Printing the
expression at `observe_effect_expr` names the shape exactly: each marker sits
on a `Binary { op: Mul }`, the index scaled by the eight-byte element stride.
The rendering of that load turns the address into a subscript and divides the
stride out, and the multiplication the marker was on ceases to exist.

Two rebuild sites do that and both were tried with
`carry_all_expr_observations`, extended to skip ids the replacement still
holds so a surviving subtree is not counted twice: the pair inside
`render_certified_memory_expr_for_fact` (the structured branch and the
byte-address branch), and `typed_subscript_access`, whose `index_in_elements`
divides the stride out directly. Neither changed the outcome -- coverage stayed
at 243 -- so both were reverted.

That leaves one path, and it explains why every carrier missed:
`render_certified_semantic_array_expr(fact)` takes only the fact. It is reached
before `certified_memory_address_expr` is ever called, builds `base[index]`
from the certified array fact's own base and index values, and never sees the
address expression at all. There is nothing to carry there, because the
expression is not passed in. So the fix belongs in the plan: a value whose one
reader is the address of an access rendered from an array fact must not be
folded, exactly as for the dead frame slot.

That guard was written and did not fire, which is the next thing to
understand rather than to rewrite. It asked
`source_owned.report().render()` for `array_accesses_by_op` at the fact's own
`(block_addr, op_index, is_write)` and matched the same four fields the
renderer's `certified_array_fact_for_memory` matches, plus the
`base.is_some() || index.is_some()` test that
`render_certified_memory_expr_for_fact` adds. Either those render facts are not
the ones the fold context reads through `self.inputs.render_facts()`, or the
match differs in a field. Print both sides for that one op before changing the
predicate again.

**More of `siphash24` ruled out.** The load at block `0x100000ae3` op 40 takes
neither the stack-owner branch nor the array branch --
`certified_array_fact_for_memory` returns `None` for it -- so it reaches
`certified_memory_address_expr`, which calls `planned_value_expr` on the
address and therefore does ask for the folded value. Printing the access
expression on both sides of `typed_subscript_access` shows it unchanged and
fully marked: `*(uint32_t*)(...)` with the whole observation chain intact. So
op lowering hands the statement over with the markers on it.

Bisecting every pass between there and the seal did not find the loss either.
None of `simplify_identities_in_function`,
`reconstruct_flag_conditions_in_function`,
`normalize_redundant_return_carrier_casts`,
`normalize_declared_assignment_literals`, `normalize_comparison_operand_order`
or `fold_constant_arithmetic_in_function` changes the outcome, and neither does
any of the five `cleanup_recurse` rewrites.

The remaining inconsistency is the thing to resolve first, because one of the
two measurements must be wrong: `Op(40)`'s own marker survives, so the load's
statement is in the sealed AST, and the markers for `Op(38)` and `Op(39)` sit
inside that same statement's right-hand side when op lowering returns it, yet
the seal reports them missing. Either the surviving statement came from a
different rendering than the one printed -- `planned_value_expr` is called
several times for this value and each call allocates fresh marker ids, so the
ids that reach the AST need to be matched against the ids the seal reports
missing rather than assumed to be the same ones -- or the walk in
`inspect_render_observations` does not reach them. Check the id sets against
each other before touching either the plan or the renderer again.

## Component 3, type inference: measured, started, and where it stops

The baseline is exact and worth stating plainly. Across the fifty-four corpus
cells the typed-recovery score is **zero parameter matches and six return
matches**. Every object is declared `CType::machine_bits(width)` -- the
unsigned integer of its storage's width -- and `lib.rs` says why in a comment
at the parameter site: asserting an inferred type made `-Werror` reject the
function as a signedness-changing conversion on its own argument, so the
contract became "a parameter is an unsigned integer of the register's own
width, and signedness, pointer-ness and names are never asserted".

The engine to replace that with is already there. `r2types::evidence` runs a
real constraint solver -- a type arena, union-find equality classes, callee
prototypes, memory widths, allocation element widths, and up to four
refinement rounds that use a solved pointer to decide which operand of an
address computation is the base. What is missing is not inference. It is the
wiring from the solved types to the declarations, and the rendering that has
to follow once a declaration is no longer an unsigned machine word.

Two slices were built and measured. Both work, both are saved as patches, and
both are blocked on the same thing.

**Declarations from the evidence** -- `doc/wip/typed-declarations.patch`, 376
lines. A shared `rules::declaration_type_for_binding` asks the evidence for
the type its members agree on and admits it only when its width matches the
storage, with a pointer admitted at the pointer width; both construction and
the seal call it, and the seal's five `declaration_type == machine_bits(width)`
checks become width checks, since the width is the part a second derivation of
the *plan* can confirm and the evidence's meaning is not. Parameters then
declare `int8_t* X0_0` where they used to declare `uint64_t`, which is real
pointer recovery reaching the emitted C.

It exposed two genuine defects, both fixed in the patch. `cast_needed`
returned `false` when the source type was unknown, which is a conclusion drawn
from not knowing, and for a pointer target it is exactly the case where C
requires the cast. And `project_machine_use` casts a use to the unsigned
integer of its carrier width even when the slice is the whole carrier at
offset zero -- nothing is being projected -- which spells `(uint64_t)p` for a
pointer object; a whole read of a pointer is now spelled at the declared type,
which also keeps the identity copy `p = (int8_t*)p` legal where `p = p` would
trip `-Wself-assign`.

Eleven cells still do not compile, and the shape names what is left:
`(int8_t*)X0_0 + (int8_t*)tmp_12380_1`. Once a declaration is a pointer, an
address computation has to render as pointer arithmetic with an integer index,
not as both operands cast to pointers -- only one operand of an address is the
pointer, and the evidence solver already knows which. That is the next piece,
and it is the same work component 4 needs for array indexing.

**Return width** -- `doc/wip/return-width-recovery.patch`, 185 lines. A
function returning `uint32_t` on x86-64 leaves its result in `eax`, which the
lift models as a zero-extension into the `rax` the ABI returns in, so reading
the declaration off the carrier says `uint64_t` for everything.
`semantic_return_bits` follows the returned value back through zero-extensions
and whole-width copies to the value the function actually computed, and
`narrowed_return_type` narrows an unsigned return to it. Note that
`ReturnValueCertificate::width` is **bytes**, not bits, and is the carrier's
width either way -- it is not the fact wanted here.

That takes return matches from **six to thirty-five of fifty-four**, and the
corpus differential stays at fifty of fifty-four with nothing wrong. It costs
four cells to one precisely located inconsistency: the callee declaration the
*caller* emits is built from the call result's machine width, deliberately, so
that caller and callee agree when both are decompiled into one translation
unit -- and narrowing the callee's own definition breaks that agreement.
`uint32_t sym__rotl32(...)` against `uint64_t sym__rotl32(uint64_t, uint64_t);`
is a hard `conflicting types` error.

Measuring the same thing from the caller's side does not work: the call result
value has no use sites at all in the graph -- it reaches its readers through
another value -- so `use_sites(result)` is empty and there is nothing to
narrow by. The resolution is cross-function and belongs with component 1: the
callee's recovered return width has to reach its call sites, either through
the type writeback that already exists or by measuring the callee's own
`semantic_return_bits` when its analysis is available. Until then the two
answers disagree, which is exactly the duplicated-predicate shape this project
resolves by making one answer rather than by choosing a winner.

Both patches are off the tree, which is green: fifty-four of fifty-four on
every corpus gate and 2236 of 2236 tests.

### Typed declarations: eight compile errors from landing

`doc/wip/typed-declarations.patch` is now 865 lines and takes the corpus from
eleven blocked cells to eight, with four more defects fixed at their cause
along the way. Every one of them was hidden by the old contract that a
declaration is always an unsigned machine word, and each is a rule the emitted
C needs whatever the declarations say:

*C adds an integer to a pointer, never a pointer to a pointer.* Both operands
of an address sum can be pointer-declared honestly -- a value used as an
address anywhere is a pointer wherever it is read -- and the sum is still one
base and one offset, so `binary_stmt_typed` integerises the right operand when
both look like pointers.

*The operand's projection comes before the assignment's conversion.* The
projection says which bits of the source are read; the conversion says what
the destination is. Run the other way round, as `SSAOp::Copy` did, it re-wrapped
a value already converted to the destination's type back into the source
carrier's integer: `int8_t *p = (uint64_t)(int8_t *)q;`.

*A pointer-valued expression assigned to an integer needs its conversion
spelled too.* `cast_expr_if_needed` asked only the recorded source type, and an
unrecorded one meant no cast, so `uint64_t n = p + i;` went out unconverted.
The expression itself is the evidence when nothing else recorded it.

*A store converts to the declared type of the object it writes.* A store's
left-hand side is a certified access rather than a variable, so the assignment
policy had no `dst` to ask and skipped the conversion entirely; the object
behind the access has a declaration, and it is what the compiler reads.

The eight that remain are three shapes, all cast placement rather than
inference: a stack store whose conversion does not fire because
`stored_object_declaration_type` fails to match the access fact by address; a
`uint32_t` register alias initialised from a pointer, which needs the pointer
narrowed through `uintptr_t` rather than cast straight to a smaller integer;
and a load result assigned to a pointer-declared object without the pointer
conversion, which is the same missing rule as the store had.

One further thing the measurement shows: parameter matches stay at zero even
with pointers recovered, because the evidence spells the pointee `int8_t`
while DWARF says `const uint8_t *`. Two facts are missing rather than one --
the pointee's signedness, which the zero-extension on every loaded byte
decides, and `const`, which is exactly "no store through this pointer
anywhere in the function". Both are local and derivable, and neither is worth
starting before the eight cast errors are gone.

### Typed declarations: six of eight cast placements fixed, eight cells left

The patch is 1438 lines and holds at eight blocked cells out of fifty-four,
with forty-six agreeing with the oracle. Three more rules were added and each
is right independently of type recovery:

*A store converts to the declared type of the object it writes*, found by the
access fact for the current op rather than by matching the address value,
which never matched.

*A pointer is cast to its carrier's integer before it is sliced.*
`project_machine_use_of` takes a flag saying the object is a pointer and
converts first; slicing a pointer directly is `-Wpointer-to-int-cast`, and the
width comes from the memory model's `default_address_bits` rather than from
`FoldArchConfig::ptr_size`, whose units are ambiguous enough that reading them
wrong produced casts to `struct r2sleigh_bits_512`.

*A pointer narrowed to a smaller integer goes through the pointer's own
width*, in both `cast_expr_if_needed` and `cast_expr_to`.

What is left is two shapes and neither is inference:

`uint32_t tmp_regalias_..._4_0_1 = (uint32_t)(int8_t*)X1_0;` -- a register
alias, minted in `r2ssa::function` around line 4344 as
`tmp:regalias:{block}:{op}:{source}`, narrowing a pointer. The narrowing cast
is emitted by neither `cast_expr_if_needed` nor `cast_expr_to`, both of which
now insert the pointer-width step and neither of which fires here, so the
alias has a lowering path of its own that has to be found before it can be
fixed.

`int8_t* X11_6 = (uint64_t)(uint8_t)...(uint8_t)tmp_25500_5;` and
`stack_m24 = (uint64_t)(int8_t*)RSI_0;` -- a load result and a store whose
conversion to a pointer-declared destination is still missing. Applying
`assignment_rhs_with_type_policy` to the load's result was tried and is wrong:
`source_type_for_var` answers with the carrier's 512-bit vector for these
temporaries and every cell then fails. The destination's *binding declaration*
is the thing to convert to, not whatever `source_type_for_var` reports.

Neither shape needs a new fact. Both are the same rule the Copy path already
follows -- convert to what the destination is declared as -- applied at the
two sites that still do not.

### Typed declarations: four cells from green

`doc/wip/typed-declarations.patch` is 2099 lines and holds at **four blocked
cells of fifty-four, fifty agreeing with the oracle and none wrong**, with
pointer types recovered onto parameters, locals and stack slots. Four more
rules were added, and one of them caught a wrong answer that had nothing to do
with declarations:

*Machine address arithmetic counts bytes; C pointer arithmetic counts
elements.* `(int32_t *)p + 4` moves sixteen bytes where the instruction moved
four, and `xxhash32` at arm64 -O1 computed the wrong hash from exactly that.
Neither operand of an address add or subtract stays a pointer now -- the
arithmetic is done on the addresses as numbers, which is what the machine did,
and the destination's declaration puts the pointer back. It settles the two
shapes C rejects outright as a side effect: a pointer added to a pointer, and
a pointer subtracted from an integer.

*A `Subpiece` at offset zero narrows through `cast_expr_to`*, which knows a
pointer has to be converted at its own width first. A register alias is a
`Subpiece` at offset zero, so taking the low half of a pointer-declared
register was `(uint32_t)(int8_t *)p`.

*The conversion to the destination's declaration goes outside the machine
write projection, not under it.* The projection spells how the machine writes
the carrier -- a lane, or a zero-extension into the full register -- in the
carrier's unsigned integer, and that is the last word only while the object is
that integer.

*A store converts toward a pointer and never away from one.* Saying the
conversion in the other direction undid the pointer the read projection had
just given, which cost a cell rather than fixing one.

The four that remain are two shapes:

`stack_m16 = (uint64_t)(int8_t *)RDI_0;` in three cells. The slot is declared
`int8_t *`, the value is a pointer, and something between the two spells a
`(uint64_t)` that neither the read projection (which produces the
`(int8_t *)`) nor the store conversion (which now only converts toward
pointers) accounts for. The next step is to find which write path renders a
store to a *stack object* -- the evidence so far says it is not
`SSAOp::Store`, because that path's every cast is now accounted for.

`EDI_2 = (int8_t *)(uint64_t)(uint32_t)(int8_t *)(...)` in one cell: the same
value converted to a pointer, back to an integer, and to a pointer again. The
innermost `(int8_t *)` is the assignment policy converting to the destination,
and it should not be there when the write projection is going to convert
again outside it.

Nine defects have been fixed at their cause on the way to this, every one of
them a rule the emitted C needs whatever the declarations say. None of the
four remaining needs a new fact; all four are cast placement.

## Component 3 landed: types from the evidence reach the C

The declaration half of type inference is in the tree and green. Fifty-four of
fifty-four on every corpus gate -- generation, raw, diagnostic, differential,
effect obligations, placement and render refusal -- with 2236 tests passing and
whole-binary coverage unchanged at 243 of 313.

Sixteen corpus cells declare `uint8_t *` for a parameter that used to be
`uint64_t`, and stack slots holding addresses are declared pointers too. The
typed-recovery score still reads zero parameter matches, and the reason is now
spelling rather than inference: DWARF says `const uint8_t *` and `size_t` where
the rendering says `uint8_t *` and `uint64_t`. `const` is derivable -- it is
exactly "no store through this pointer anywhere in the function" -- but
`CTypeLike` has no qualifier to carry it, so adding it touches parsing,
rendering, sizing, the lattice and writeback. `size_t` against `uint64_t` is a
naming question and not a recoverable fact; whether DecBench's `type_match`
counts them equal is worth measuring before spending anything on it.

Eleven defects were fixed at their cause getting here, each a rule the emitted
C needs whatever a declaration says. The full list is in the two commits; the
three worth remembering are that `expr_type_hint` answered `None` for a bare
name and so left every pointer-aware conversion blind to the one expression
that names an object; that arithmetic on an address is arithmetic on a number,
because C counts elements where the machine counted bytes and every operator
other than pointer-plus-integer rejects a pointer outright; and that a pointee
takes its signedness from the extension its loaded value reaches, since the
access width says how many bits are read and nothing about what they mean.

Three harness rewrites had to keep up, each of them the verifier failing to
recognise a better rendering rather than the decompiler emitting a worse one:
the diagnostic path retyped every parameter to `long` including the pointers,
its runner passed every argument as `long`, and the image-literal evidence
recognised `*(uint8_t *)p` but not the plain `*p` a typed pointer renders,
which made an address the program does read through look unmapped.

### What is still open in component 3

The return width, `doc/wip/return-width-recovery.patch`, takes return matches
from six to thirty-five of fifty-four and stays off the tree. Its blocker is
now precisely understood and is not in that patch. A caller builds the callee
prototype it emits from the call result's machine width, deliberately, so that
caller and callee agree when both are decompiled into one translation unit.
Narrowing the callee's own definition breaks that agreement, and the caller
cannot measure what to narrow to: `known_signature_for_site` answers only from
a prototype radare2 recorded, which a local static callee has none of, and the
call result value has no use sites in the graph to infer a width from. The
zero-extension that proves the width lives in the callee's body.

So this needs the callee's recovered return type to reach its call sites. The
writeback path in `r2types::writeback` is where that belongs, and it is
component 1's call-boundary work rather than component 3's. Note that ordering
alone will not rescue it in the corpus sweep, which decompiles callees last.

## Component 4, measured: where aggregate recovery actually stops

Stack-frame recovery already produces named locals, and after the type work
above it produces named *typed* locals -- a slot holding an address is declared
a pointer. What is missing is the aggregate half, and a three-function fixture
compiled at -O0 shows exactly where it stops. The fixture is a byte buffer
copied into and summed, a struct passed by value, and a pointer walked as an
array; the interesting one is the buffer.

`uint8_t buf[16]` on the stack, written at `buf[i]`, renders as this:

```c
uint64_t tmp_4e80_4 = (uint64_t)-0x20 + (uint64_t)(int64_t *)RBP_1;
uint64_t tmp_4f00_4 = (uint64_t)tmp_11f80_15;
uint8_t *tmp_5000_4 = (uint8_t *)((uint64_t)tmp_4e80_4 + (uint64_t)tmp_4f00_4);
*(int8_t *)tmp_5000_4 = (uint8_t)tmp_6980_5;
```

That is frame-pointer arithmetic with the index added to it, and it is what a
reader has to decode back into `buf[i]` themselves. Every scalar slot beside it
recovers fine -- `stack_m72` is the loop counter, `stack_m88` the total -- so
the gap is precisely a stack object accessed at a *varying* index.

The pieces to build it with are all present and none of them is wired to this
case. `ObjectKind::FrameObject { base, offset }` models an object at a constant
frame offset. `MemoryAccessCertificate` names the object an access reaches.
`render_certified_semantic_array_expr` and `certified_array_fact_for_memory`
already render `base[index]`, and `certified_stack_owner_expr_for_memory_fact`
already renders a slot by name. What is missing between them is the *recovered*
array fact: the aggregate projections those renderers consult come from
`r2types` aggregate facts, which come from declared or DWARF types, so a stack
buffer with no declared type has none and the access falls through to the raw
address form above.

So the work is: recognise a stack region whose accesses share a frame base and
a constant element stride and differ by a non-constant index, certify it as one
object with an element width and an extent, declare it `uint8_t name[n]`, and
route its accesses through the array renderer that already exists. The
declaration side now has somewhere to put the type, since
`declaration_type_for_stack_object` already asks the evidence and would only
need `CTypeLike::Array` admitted alongside the scalars it admits today.

Two smaller observations from the same fixture. The stack pointer itself is
declared `int64_t *` because it is used as an address, which is true and reads
as noise; a frame or stack pointer is a role the certificates already know and
could be declared at. And `int64_t *RAX_1 = (int64_t *)*(uint64_t *)&__DATA_CONST;`
is the stack-guard load, which names the segment rather than `__stack_chk_guard`
because the data-symbol walk found the segment flag and no symbol flag at that
address.

### Array indexing: the renderer is one folding decision away

Two changes toward `src[i]` were written, measured inert, and reverted, and
both are worth writing again the moment the thing blocking them moves.

The first renders a one-byte pointer plus an index as a subscript, in
`render_certified_memory_expr_for_fact` before the byte-address fallback. It is
restricted to a one-byte pointee and a zero offset on purpose: C scales a
subscript by the pointee and the machine did not, so a wider element would move
the wrong distance. The second widens `certified_pointer_base_expr`, which
decides which operand of an address is the base. It asks upstream certificates
for a parameter with a recovered pointer type or a loop carrier, because no
object used to be *declared* a pointer; one is now, and an object declared a
pointer is a pointer wherever it is read.

Neither fires, and the reason is not in either of them. The address never
reaches the dereference as an expression:

```c
uint8_t *tmp_4a00_2 = (uint8_t *)((uint64_t)RAX_3 + (uint64_t)tmp_4900_2);
uint8_t tmp_11e00_2 = *tmp_4a00_2;
```

`certified_memory_address_expr` asks the plan for the address value and gets
`Var(tmp_4a00_2)`, which decomposes into no base and no index. The sum is a
statement of its own because the plan bound that value instead of inlining it,
and `rules::inlinable_values` skips it before any of its own tests run: the
`let [use_site] = graph.use_sites(value.id) else { continue }` at the top means
the value has some number of uses other than one. Eighty-eight load addresses
in `fnv1a32` reach that probe and every one of them is a stack slot; the
buffer's is not among them. Finding that second use is the next step, and it is
a small one.

The stack buffer is a separate and larger problem. `uint8_t buf[16]` written at
`buf[i]` resolves to `ObjectKind::EscapedUnknown { space: Ram }` -- the object
model does not recognise a frame base plus a constant plus a variable index as
an access into a frame object, so there is no object to name, size or declare.
The pointer parameter's pointee, by contrast, is already
`ObjectKind::Parameter { index: 0 }`, which is why indexing through a parameter
is the reachable half and the stack buffer is not.

### Correction: array indexing is not one folding decision away

The section above is wrong about what blocks `src[i]`, and the measurement that
corrects it is worth keeping so nobody repeats the search.

`inlinable_values` is not the obstacle. Every one of the eighty-eight load
addresses in `fnv1a32` passes all seven of its tests, and none is lost to an
earlier disposition -- only stack-geometry bases and unobserved values are, both
correctly. The address the byte load actually uses is `ValueId(85)`, and it is
`Bound` for a good reason: it has **two** uses, the load and a phi. It is the
loop's pointer, advanced each iteration and carried round the back edge, so
folding it would evaluate the address computation twice.

That means the rendering is already right for what the machine does. The source
wrote `data[i]`; the compiler at -O0 walks a pointer, and the decompiler
faithfully shows a pointer walked:

```c
uint8_t *tmp_4a00_2 = (uint8_t *)((uint64_t)RAX_3 + (uint64_t)tmp_4900_2);
uint8_t tmp_11e00_2 = *tmp_4a00_2;
```

Recovering `data[i]` from that is induction-variable analysis -- recognising a
pointer whose every definition is the same base plus a monotonically stepped
index, and rewriting its dereferences in terms of the base and the index. That
is a real decompiler feature and a much larger one than "render a subscript
where the address is a base plus an index", which is all the reverted renderer
change did.

So component 4's aggregate half has two independent pieces, and neither is
small. Induction-variable recovery is one. The stack buffer is the other, and
it is blocked earlier still: `uint8_t buf[16]` written at `buf[i]` resolves to
`ObjectKind::EscapedUnknown { space: Ram }`, so no object exists to name, size
or declare, and the object resolver has to learn that a frame base plus a
constant plus a variable index is an access into a frame object before anything
downstream can help.

### Why the stack buffer escapes, to the exact function

`function.rs::stack_address_root_from_add` is where it happens. A stack address
root is recorded for `base + delta` only when `signed_stack_delta_through_roots`
can fold `delta` to a constant:

```rust
if let (Some(base), Some(delta)) = (
    stack_root_from_operand(a, ...),
    signed_stack_delta_through_roots(b, ...),
) {
    return Some(StackAddressRoot { base: base.base, offset: base.offset + delta });
}
```

`buf[i]` is `frame_base + (-0x20) + i` with `i` a loop variable, so the second
add has no constant delta, no root is recorded, and
`semantic.rs::object_for_address_value` falls through to
`ensure_escaped_unknown`. Every consequence follows from that one miss: no
object, so no stack-slot certificate, so no name, no size, no declaration, and
the access renders as raw frame arithmetic.

The missing concept is small to state and not small to build. `StackAddressRoot`
is `{ base, offset }` and says an address is at an *exact* offset from a base.
An array element is at an unknown offset from a known object, and there is no
way to say that. Recording `base.offset` for `base + i` would be a lie -- it
would alias every element to the first -- so the fix is a third case in the
model, either a variable-offset root or an `ObjectKind::ArrayElement` carrying
the object and the index value.

That change starts in `r2ssa` and lands in the machine projection, the
certificates, the binding plan's declaration rule and the renderer, which is
why it is a session of its own rather than the tail of this one. The
declaration side is already prepared for it:
`rules::declaration_type_for_stack_object` asks the evidence and admits what
describes the storage, and would need `CTypeLike::Array` admitted beside the
scalars it admits today.

### The cleanest array shape to build the subscript rule against

`arr_sum(const uint32_t *a, uint64_t n)` at x86-64 -O0 is the fixture to work
from, because the machine writes the index and the stride out in the open:

```c
uint64_t tmp_4900_2 = (uint64_t)RCX_2 * (uint64_t)4;
uint32_t *tmp_4a00_2 = (uint32_t *)((uint64_t)RAX_3 + (uint64_t)tmp_4900_2);
uint32_t tmp_11f00_2 = *tmp_4a00_2;
```

Everything a subscript needs is present and typed: a base, an index multiplied
by a stride that equals the pointee width, and a dereference of the result. The
rule is that an address which is a pointer plus an index whose stride equals the
pointee width is that pointer subscripted by the index divided by the stride,
and `typed_subscript_access::index_in_elements` already performs that division
for the case it handles today.

Two things stand between the shape above and `a[i]`. The address value
`tmp_4a00_2` is bound rather than inlined, so `certified_memory_address_expr`
asks the plan for it and gets a name instead of the sum -- and the reason is not
`inlinable_values`, whose seven tests it passes; it is the `[use_site]` guard at
the top, which skips any value with a use count other than one. Counting those
uses for this exact value is the first thing to do, and the second is
`certified_pointer_base_expr`, which decides which operand is the base by
looking for a parameter role or a loop carrier and would not recognise `RAX_3`,
a copy of the parameter through its stack home, even though the sum is declared
`uint32_t *`.

Both are small. Neither was landed, because a subscript rule that fires nowhere
is worse than none, and the corpus has no case where the address folds -- its
byte loops carry a pointer round a phi, which is a use the fold must not
duplicate and which needs induction-variable recovery rather than a subscript.

## Assessment: where the expression engine stands, measured

Written after the question "what does the best mathematical engine need, and is
folding in the right shape". Everything here was measured on the tree at
`0e58632` with the uncommitted indexed-stack-root diff applied; the corpus
effect of that diff is recorded at the end of this section once the matrix
finishes.

**What the decompiler uses of SSA, symex and the VM module.** SSA is the whole
substrate: certificates, obligations, the machine expression arena and the
binding plan all read it. Symbolic execution (`r2sym`, about 62,000 lines, Z3
backed) is not on the certified C path at all. It is consulted for route policy
(summary, VM and structured-worker routes), for comment-only bodies, and for a
return-type hint; nothing it proves reaches an expression, a condition or a
declaration. The VM module recognises interpreter dispatch loops and renders a
statistics comment. The type evidence solver in `r2types` is wired to
declarations and is the one non-SSA engine that changes the emitted C.

**Folding is a single-use inliner, not an expression simplifier.** Over the
fifty-four corpus cells (5,271 statement lines) the residue is:

| noise class | count |
| --- | --- |
| same-type double casts `(uint64_t)(uint64_t)x` | 730 |
| triple-or-longer cast chains | 727 |
| flag locals declared (`CF`, `ZF`, `ZR`, `TMPZR`) | 192 |
| self-assignments `X = (T)X` | 141 |
| `goto` | 125 |
| constants bound to a temporary | 37 |
| `x & x` | 19 |
| `while` with a comma-packed header block | 17 of 60 |

Casts run at 1.5 to 2.5 times the statement count in every cell. The 64-bit
FNV offset basis renders as a five-operation `movz`/`movk` chain because the
only constant folder on the path handles `Add` and `Sub`. None of this is a
correctness defect -- all fifty-four cells agree with the oracle -- but it is
the machine rendered faithfully rather than the program.

**There are three rewriting layers, and the decision was one.**

1. `r2ssa/src/optimize.rs`, 3,690 lines: SCCP, an instruction combiner with
   about fifteen constant identities, copy propagation, CSE and DCE. Production
   runs SCCP alone (`from_blocks_raw_with_policy_and_control` builds its own
   config with everything else off); `DecompilePrepConfig` enables the
   combiner but is not what the plugin path calls. The rest is dead in
   production.
2. The binding plan's `rules::inlinable_values` with the materialiser in
   `fold/op_lower/lowering.rs`. This is the right layer. Its rules are narrow:
   exactly one use (so a constant temporary with two readers gets a local),
   same block and ordinal order, and only arithmetic, bitwise, boolean,
   compare, copy, negate, select and shift kinds. No extension, truncation or
   subpiece, no load, no merge, no flag arithmetic.
3. The C-tree passes: `normalize.rs` (3,114 lines), `fold/flags.rs` (a
   pattern matcher with four shapes), `fold_constant_arithmetic_in_function`,
   `simplify_identities_in_function`, three `normalize_*` passes and the five
   `cleanup_recurse` rewrites in `structure.rs`. The section "Where the
   rewriting layer belongs, decided by measurement" above already showed this
   layer computes wrong answers when asked to fold; it still runs.

Nothing in the live path is an algebraic engine. That is the gap the question
was about.

**What every rewrite has to pay.** The proof accounting is about 20,000 lines:
`observation_journal.rs` 4,849, `placement.rs` 4,276, `binding_plan/` about
5,000, `shadow_report/` about 1,700, `r2ssa/src/obligation.rs` 2,775, the two
ledgers about 900. It was built for "render every operation or refuse", and a
rewrite is neither. Single-use folding cost about fifteen build-measure cycles
through it and three multi-layer changes were reverted whole. Every further
rewrite kind -- algebraic identity, spill round trip, subscript, member -- pays
the same again unless the accounting rule is generalised once.

**Timing, end to end, one process per measurement.** `r2 -q -c "a:sla; aa"`
on the nine-function corpus binary costs 2.3 seconds before any analysis, which
is process start plus plugin load. Net decompile time for one function after
`aaa`:

| binary | function | obligations | `pdd` net |
| --- | --- | --- | --- |
| x86-64 -O2 | `xxhash32` | 381 | 0.52 s |
| x86-64 -O0 | `murmur3_32` | 376 | 0.69 s |
| arm64 -O0 | `xxhash32` | 573 | 0.99 s |
| `/bin/ls` | `main` | refused: unrepresentable operation | 4.27 s |
| `/bin/ls` | `sym.func.100001a78` | summary fallback | 0.45 s |
| `/bin/ls` | `sym.func.100003364` | refused: observation journal | 0.13 s |

So roughly two milliseconds per obligation on a function that renders, and four
seconds to refuse `main`. `a:sla; aaa` on `/bin/ls` takes 13 to 14 seconds and
prints `post-analysis budget exhausted during function sweep after 10050203
usec` at 79 of 136 functions: the plugin's own sweep is what the budget caps,
and it hits the cap on a 136-function binary. The engine records per-phase
timings (`R2SleighPhaseTimingV2`, `phase_timings` in the decompile JSON) and no
reachable command prints them -- `a:sla.decj` reports itself unavailable
outside the provider -- so where the two milliseconds go is not yet observable
from radare2.

Known cost shapes, from reading rather than profiling: `inlinable_values`
scans every instruction of the function for each candidate value (quadratic in
function size); `MachineBuilder::lower_op` filters every structured memory
access for each load (quadratic in access count); the machine projection is
built three times per function, once each in the rule, construction and the
seal; `placement.rs` deep-copies the whole `CFunction` per binding per demotion
round.

**What to build, in order.**

1. A canonicaliser on `MachineExprArena`. The arena is already the boundary
   between prepared SSA and renderers: name-free, typed, one node per value,
   derived after the certificates so SSA instruction identities and their
   obligations are untouched by anything done to it. The rules are wrapping
   constant folding across every operation; the identities (`x & x`, `x ^ x`,
   `x | 0`, `x * 1`, `x >> 0`); cast-chain normalisation to the narrowest
   width crossed and then the destination; `!(!c)`, `!(a < b)` to `a >= b`,
   `(a - b) == 0` to `a == b`; and the flag-to-comparison rules that
   `flags.rs` currently matches on rendered text. Each rule is a small
   equivalence and is to be proven once by Z3 in a unit test. That is the
   right use of symbolic execution here: prove the rules when the tree is
   built, never run the solver while rendering -- the determinism rule and
   solver timeouts both forbid it.
2. One accounting rule for rewrites, which needs a decision. Inlining moves an
   occurrence with the expression (already decided). An algebraic deletion --
   `x & x` to `x` -- leaves no node for the occurrence to move onto. Option A:
   the arena records the rewrite as a certified equivalence on the surviving
   node (rule identity and operands) and the journal accepts an occurrence of
   the replacement as the occurrence of every original it stands for; one
   mechanism then serves inlining, algebra, the spill round trip, subscripts
   and members. Option B: a new elision reason, `AlgebraicIdentity`. B is
   cheaper and is a second accounting path, and the ledger then says
   "elided" for something that was rendered. A is the recommendation and is
   the option consistent with the "one rewriting layer" decision.
3. Widen the inlining rule once 2 is in: a constant, and a copy of a constant,
   duplicates for free and should inline whatever its use count; admit
   extension, truncation and subpiece; admit loads with the hazard stated as
   "no store to the same `ObjectId` between definition and use", which the
   object model already answers; admit compare and flag operations; elide a
   merge-edge identity copy when the plan has coalesced both sides into one
   binding. Loop headers then collapse to their condition, the comma-packed
   `while` disappears, and the flag locals with it.
4. Delete layer 3 and the dead four-fifths of layer 1.
5. Cast policy from declared types rather than from projections: one
   conversion at each type boundary. This depends on the `CTypeLike`
   unification already decided.
6. Induction-variable recovery, needed for `a[i]` and for a `for` with a real
   condition. `r2sym/src/loops.rs` already recognises `AffineConst`
   recurrences for the solver and the decompiler cannot see them; the
   recurrence fact belongs in `r2ssa` with both reading one owner.
7. The four cost shapes above, and a command that prints the phase timings,
   before the engine is pointed at coreutils.

Not needed now: symbolic execution on the render path, the VM route rendered
as C, or more of Z3.

Coverage on real binaries is a separate ledger from all of this and its causes
are already traced above: the composed return value (eighteen refusals, the
largest single cause), `CallOther` traps, pass-through call arguments and the
direct tail call.

**The matrix, run on the tree with the indexed-stack-root change.** That
change was committed as `aece1f6` by a concurrent session while this ran.
Fifty-four of fifty-four on raw, diagnostic, differential, effect obligations,
placement and render refusal. Snapshot reports `mismatch` on all fifty-four,
which is staleness rather than a regression: the baseline was last blessed at
`1e2af4e` on 2026-09-01 and thirty-one commits have changed output since,
folding and typed declarations among them. It needs re-blessing once the
current output is believed correct, so the column detects something again.
Binding audit reports `non_quality` on fifty-two cells, `pass` on two; whether
that predates this stretch was not established, because the previous results
were overwritten by this run. Per-function decompile time was measured only
end to end, above; the per-phase split is still unobservable from radare2.

## The expression engine work: how it is organised, and what day zero measured

The plan this follows was approved with every open decision settled by the
user: rewrites are accounted for as certified equivalences rather than as a new
elision reason; the rule table lives in a new `r2rewrite` crate and every rule
carries a Z3-checked bit-vector proof at 8, 16, 32 and 64 bits; the C-tree
expression passes and the production-dead parts of `r2ssa/optimize.rs` are
deleted once rules replace them; the perf bar is per function rather than
whole-binary; and the finish line is exact predicate columns on the corpus plus
a DecBench sample-set run.

Three worktrees branch from `ec8d589`. `arch/expression-engine` integrates;
`arch/expr-accounting` holds step 1, the accounting rule; `arch/expr-rewrite`
holds the `r2rewrite` crate. All three install the plugin to one shared path,
so every measurement that involves `make install` takes
`/tmp/r2sleigh-plugin-install.lock` for the whole run and not merely for the
install. The dumps are captured against whatever is installed at that moment,
and this project has already voided four conclusions to that exact class of
error.

`tests/corpus/locked_matrix.sh` is that protocol written down. It builds the
plugin first and takes the lock only for the install and the capture, because
`run_matrix.sh` begins with `make install`, which builds before it installs --
so taking the lock and then calling it holds the lock through a cold release
build, minutes in which nobody measures and nobody else can start. The lock is
released from a trap, so an interrupted run does not strand the queue.

**The machine detail is now a measured column.** `machine_noise` counts seven
exact predicates on the extracted raw function of every cell, and `--gate
noise` requires all of them to be zero. Exact rather than a threshold, because
each one either appears or does not, and none can be produced by a source
construct. On the fifty-four cells at `ec8d589`:

    same_type_casts             792
    cast_chains                 752
    self_assignments            296
    literal_only_declarations   292
    flag_carriers               192
    gotos                       125
    comma_conditions             17

Zero of fifty-four cells pass. Two of the predicates had to be narrower than
they first looked, and each was caught by its own test rather than by the
corpus. A literal initialiser is only machine detail on a name this renderer
minted -- a lowered temporary or an SSA-versioned register -- because
`uint64_t total = 0;` is ordinary C and a named frame slot is a real local. And
a run of exactly two casts can be legitimate, since a pointer narrowed to a
smaller integer has to pass through the pointer's own width; only three is
counted. `goto` is required to be zero only at `-O0`, where structured control
is claimed.

**The verifier's own unit tests had rotted, and nothing ran them.** Two of the
forty were failing at `ec8d589`: `map_image_data` reads segments as well as
sections and owed its mock a third result, and a diagnostic-repair assertion
still expected a recovered pointer parameter to be retyped to `long`, which is
component 3 working rather than the repair failing. Both are fixed, and the
quality gate now runs `tests/corpus/test_verify_rendering.py`, which costs
0.04 seconds and is the file that decides whether any other corpus phase means
anything.

**Where a decompile's time actually goes, measured in process.** The engine's
phase inventory starts after the SSA artifact exists, so the provider path
reported `ssa=0us` and the capture that builds the artifact was attributed to
nothing. Split, with two other worktrees compiling throughout (load average 9
to 19, so the ratios are the claim and the milliseconds are an upper bound):

    case                        capture  decode  callee_lift  callees  root_lift  engine  rendering
    xxhash32   x64   -O2         112ms    13us       0us          0      112ms    379ms      97%
    murmur3_32 x64   -O0         129ms    13us      50ms          1       79ms    160ms      95%
    /bin/ls main, refused        524ms   107us     200ms          4      324ms     71ms   refused
    /bin/ls func.100003364       274ms    33us     174ms          4      100ms     19ms   refused

Rendering is almost all of the engine's time on a cell that renders, which is
where the rewriting layer lands. Lifting callees is repeated work nothing
caches: four callees cost about 45 milliseconds each and every `pdd` pays
again, which is the case for the per-binary program cache. Decoding the wire
buffer is microseconds, so the ingress that replaced the callback ABI is not
worth optimising.

One earlier claim in this document is withdrawn. Refusing `main` was reported
at 4.3 seconds; it costs about 0.6 seconds. That figure came from subtracting
one `aaa` run from another, and `aaa` on /bin/ls varies by seconds. Measure the
thing rather than deriving it from a difference of two large numbers, which is
the same rule this project already applies to coverage.

**The binding audit was reporting a disagreement that did not exist.** It
passed on 2 of 54 cells before the accounting work and passes on 54 of 54
after, and nothing about the emitted program moved. The candidate side mapped
every inline disposition to `InlineConstant` while the oracle distinguishes a
constant from an expression, so every function that folds anything reported a
mismatch. The column had been measuring its own classification.

**Caching a lifted callee needs an identity radare2 does not currently give
it.** The measurement above says four callees cost about 45 milliseconds each
and every `pdd` pays again, so a per-binary cache is worth real time on any
sweep. The obstacle is the key, and it is exact rather than vague.

`OwnedFunctionSnapshot::source_revision_identity` looks like the right key and
is documented in radare2 as the "stable diagnostic/cache identity of the owned
payload". For the root it is `function_snapshot_hash(snapshot)`, a content
hash, which is what a cache wants. For a callee it is not:
`libr/anal/function.c:6403` assigns `callee_snapshot->revision_identity =
snapshot->revision_identity`, so every callee inherits the *caller's* identity.
The same callee reached from two callers therefore carries two identities,
which is the one case a callee cache exists to serve. Keying on it is safe but
never hits.

Two ways out, and neither is a small change to be slipped into other work. A
callee's identity could be its own content hash, computed the same way the root
is, which is an upstream radare2 change and belongs in its own pull request
under the rule this project already follows. Or the plugin can derive a key
itself from the callee's address together with a hash of everything the lift
and the preparation actually consume -- the image bytes, the architecture
triple, the recovered interface, the stack slots and the type graph -- which is
sound only if the hash covers every input, and a hash that misses one renders
the wrong body. Whichever is taken, the identity has to be proven complete
before the cache is switched on, because a stale hit here is not a slow answer
but a wrong one.

**Most of the cast noise is spelled by the renderer, not present in the arena,
and that decides what the rewriting layer can and cannot fix.** Measured by
running canonicalisation over the corpus functions and counting rewrites by
rule identity, against the `machine_noise` column's counts of the emitted C:

    over the 54 cells                                  count
    rendered casts                                     10346
    same-type casts                                      731
    arena Cast and Extract nodes                        2338
    casts spelled with no arena node behind them        8008   (77%)
    cast terms the rules actually remove                 379
    share of rendered casts the rules can reach                (3.7%)

A representative site is `R10D_1 = (uint64_t)(uint32_t)(uint64_t)(uint32_t)R10D_1;`,
which is a copy. No arena cast node exists anywhere in it: all four casts come
from operand projection alternating between the carrier's width and the value's
width. So the cast work is a renderer policy change -- one conversion at each
type boundary -- and not a rule, and the ninety proven rules will not move the
`same_type_casts` or `cast_chains` columns on their own. Zero of the 731
same-type casts are two arena nodes, because an arena cast always changes width
except for a same-width reinterpretation, and that rule fired zero times across
all sixty renders.

**The flag carriers are a binding decision, not flag arithmetic.** Group E, the
eight flag-to-comparison rules, removes none of the 192 carriers, and the
reason is worth keeping: the carriers already hold comparisons. `x64_O0_djb2`
renders `CF_2 = (uint8_t)((uint64_t)RAX_2 < (uint64_t)tmp_3f800_2)`, because the
lifter emits the comparison directly rather than emitting flag arithmetic for
the renderer to reconstruct. The rule group fired seven times across the corpus
against forty for the boolean group. What keeps `CF_2` on the page is that the
value is bound, which is the binding plan's decision, so the carriers fall to
widened inlining rather than to any rule.

Two consequences for the order of the remaining work. The cast policy moves
ahead of the deletion pass, because it is the only thing that reaches 8008 of
the counted casts. And widened inlining is what clears the flag carriers, the
self-assignments and the literal-only temporaries, so it and the cast policy
are the two changes the noise columns are actually waiting on.

Cost of canonicalisation itself, for the record: about one projection build,
636 microseconds mean per function against 595 to build the projection, worst
case 3.4 milliseconds against 2.7 on `xxhash32` at x86-64 -O2, with no budget
failures anywhere. Against a fold stage that is one per cent of a render, the
rewriter is not a cost worth designing around.

**Coalescing a merge edge that is not a certified carrier needs the value half
too, and that is the whole of what blocks it.** The journal elides the uses of
a materialised phi-edge copy only when the edge belongs to a
`SemanticId::LoopCarrier`, and its own comment gives a reason that is not about
carriers at all: once both sides resolve to one binding the copy says `x = x`,
and the statement that computed the update has already said it. Dropping the
carrier restriction and keeping the binding-identity test -- which is the real
condition -- was tried.

It renders 53 of 54. `xxhash32` at x86-64 -O2 refuses with
`rendered_value_required` on `ValueId(920)`: the edge copy is suppressed, so
the value it defined has no rendered write, and no elision reason covers a
value whose merge is not a certified carrier. The carrier case works because
`coalesced_carrier_phi_writes` elides the phi write as `CoalescedCarrierPhi`
alongside the edge uses, and that set is gated on
`render.loop_carrier_for_value`.

So the change is symmetric or it is nothing: widening the edge-use elision
requires widening the value-and-write elision with it, and that needs its own
argument for why a non-carrier merge whose every edge is an identity owes no
rendered write. `ElisionReason::CoalescedImmutablePhi` already states something
close for immutable merges and is the place to look first. The elision reason
would also want renaming away from `CoalescedCarrierEdge`, since it would no
longer be about carriers and that name is read by a human in the proof line.

Reverted rather than left in the tree. The measurement is worth keeping: with
the edges coalesced, self-assignments fall from 296 to 206 and flag carriers
from 192 to 178 across the corpus, so this is roughly a third of the
self-assignment column and is worth finishing properly.

## Where the cast noise is actually spelled, measured three ways

Step 5 was taken on the evidence that 77 per cent of rendered casts have no
arena node behind them. That number is right and the conclusion drawn from it
was too coarse: "not the arena" is not the same as "the projection". Three
measured attempts, each a full matrix run, locate it.

**The read projection is not the source.** `project_machine_use_of` was made
type-aware: it takes the type the base is already spelled at, from the plan's
declaration for the value, and states the type each step needs instead of
casting unconditionally. On the twenty-nine cells that still rendered, that
removed 36 of 417 same-type casts and 30 of 363 cast chains, about eight per
cent of each. The change is semantically sound -- the rendered
`x64_O2 crc32_bitwise` body was compiled against the differential harness
beside the old one and agreed on all forty cases -- but it is not the lever.

**It broke twenty-five cells, and both causes are worth keeping.**

1. *The journal classifies a bound value's read by its node shape.*
   `classify_value_node` returns early on an `Inline` disposition with the
   comment that shape is not evidence, then falls through for `Bound` and
   reads the shape anyway: a bare `Var` is classified `Bound`, and a `Cast`
   over that same `Var` is classified `InlineNonLiteral`. Dropping the last
   redundant cast turns some reads of one value into bare names and leaves
   others cast, so one value collects two classifications and the seal
   refuses with `ConflictingValue`. Twenty-five cells refused this way. The
   fix is to classify a `Bound` value by its disposition, exactly as `Inline`
   already is; it needs the binding's symbol inside the classifier, which is
   why it was not taken here.
2. *Removing a redundant cast turns a hidden self-assignment into a hard
   error.* Seventy-five `-Wself-assign` errors appeared, because
   `x = (uint64_t)x;` compiles and `x = x;` does not. The 296 self-assignments
   the noise column already counts were being hidden from the compiler by the
   very cast the policy removes. The cast policy and the self-assignment
   elimination are therefore one piece of work, not two: whoever removes the
   cast has to remove the statement.

Also observed: the diagnostic column reported `x64_O2 crc32_bitwise` as wrong
while the raw rendering was provably equivalent. The diagnostic C is the
verifier's own rewrite of the rendering -- 139 `local_retype` rewrites on that
cell -- and it stopped surviving that rewrite once the casts went. The corpus
verifier rewrites the C it checks, so a diagnostic failure is evidence about
the verifier as much as about the renderer.

**What did land.** `cast_unless_already` in `projection.rs`: every projection
step says its conversion once. Same-type casts fall from 792 to 616 over the
fifty-four cells, a fifth, with every gate green. Cast chains are unchanged at
751.

**Where the remaining 616 are.** By type: 301 `(uint64_t)(uint64_t)`, 267
`(uint32_t)(uint32_t)`, 47 `(uint8_t)(uint8_t)`. By shape they are assignment
and operand boundaries in `implementation.rs`, not projections: `stack_m16 =
(uint64_t)(uint64_t)RDI_0` on a store, `uint64_t tmp_7100_3 =
(uint64_t)(uint64_t)tmp_5a00_2` on a declaration initialiser, and
`(uint32_t)(uint32_t)0x9dc5` on a literal operand. There are 26 direct
`CExpr::cast` calls in that file; `cast_expr_to` and `cast_expr_if_needed`
already refuse to double a cast, so the doubling comes from the sites that
call `CExpr::cast` directly -- the store path in particular, which does not
go through `assignment_rhs_with_type_policy` at all. That is the next thing to
measure, and it is a smaller and better-aimed change than retyping the
projection.

**Ordering that follows.** The journal classification fix comes first, because
it is what makes any further cast removal safe; self-assignment elimination
comes with it, because the two are the same piece of work; and only then does
dropping the outermost redundant cast become landable.

**Running several worktrees at once: what it costs and the two rules that make
it work.** Four efforts ran in parallel on this branch and the throughput was
real, but two operational facts are worth inheriting rather than rediscovering.

Every worktree installs the plugin to one shared path and `run_matrix.sh`
captures its dumps against whatever is installed at that moment, so two
overlapping runs measure each other's build.
`tests/corpus/locked_matrix.sh` is the answer: it builds first without the
lock, because `make install` builds before it installs and taking the lock
first holds it through a cold release build, then holds
`/tmp/r2sleigh-plugin-install.lock` for the install and the capture only, and
releases from a trap so an interrupted run does not strand the queue. Use it
rather than calling `run_matrix.sh` directly. One conclusion in this session
was drawn from a trace taken against another worktree's installed plugin and
had to be thrown away; that is the fourth or fifth time this class of error has
cost this project a measurement.

The second rule is that a worktree has exactly one live agent. Two were pointed
at one tree here, and although nothing was lost -- the first effort's work was
already committed and merged -- the second found six modified files it did not
write and correctly stopped rather than committing them.

Disk is the other constraint, and it has two halves. Three active build trees
reach about eleven to thirteen gigabytes each. The incremental caches are the
half that regrows: they return to several gigabytes per tree within about forty
minutes of active building, and deleting `target/*/incremental` reclaims them
in a second at the cost of a slower next build. The other half is
`target/debug/deps`, which reaches eleven gigabytes on its own because cargo
never removes the test binaries of earlier builds; clearing it costs one full
debug rebuild and is worth doing in a tree that is between runs rather than
mid-build. ENOSPC killed every tool in this session once before either was
understood, and a monitor that reclaims rather than warns is what kept it from
happening again.

**Where the machine-detail columns stand, and what each remaining one is
waiting on.** All 54 cells pass raw, diagnostic, differential, binding audit,
effect obligations, placement and render refusal throughout.

    predicate                    start    now    what it waits on
    same_type_casts               792       0    done
    cast_chains                   752      27    four pointer round trips whose middle step is
                                                 emitted by a site not yet calling
                                                 `pointer_width_cast`
    self_assignments              296     225    the rest are not merge edges; unmeasured which
    literal_only_declarations     292     292    duplicable constants inlined at every reader,
                                                 which needs the multiplicity rule
    flag_carriers                 192     192    the carriers hold comparisons and are bound;
                                                 widened inlining, not a rule
    gotos (-O0)                   125     125    structuring, untouched this stretch
    comma_conditions               17      17    loop-header collapse, which follows the
                                                 inlining above

Three facts worth carrying, each of which cost a measurement to learn.

The cast noise was never in the arena. Ninety proven rewrite rules reach 3.7
per cent of rendered casts, because 8008 of 10346 have no arena node behind
them. They are spelled at the assignment and operand boundaries, and the fix
was two rules in `CExpr::cast` -- one refusing to nest a cast inside an
identical one, one collapsing adjacent conversions -- plus recording the
address-width step as a `CastRole` at the four sites that spell it
deliberately. A pointer converted to `uint64_t` and a `uint32_t` widened to
`uint64_t` are indistinguishable afterwards, so the emitting site is the only
honest source.

The flag carriers are not flag arithmetic. The lifter emits the comparison
directly, so `CF_2` holds `RAX_2 < tmp_3f800_2` and the eight flag-to-
comparison rules fired seven times across the whole corpus. What keeps the
carrier on the page is that the value is bound.

`ElisionReason::CoalescedImmutablePhi` fires zero times in production, against
65 for the carrier path, measured across all 54 cells. It is live only in its
own unit test, so it is not a precedent for anything.

**Whole-binary coverage, checked after the expression-engine work: unchanged at
243 of 313.** The two functions below the blessed baseline of 245 are
`branchy_arm64_O2::sym._inverted_goto` and `hashes_x64_O1::sym._siphash24`,
which are the same two this document already recorded as open before any of
this session's work, with `siphash24`'s two lost markers diagnosed as far as
the address rebuild. Nothing regressed and nothing newly rendered, across the
canonical terms, the shared projection, the identity merges, the classifier and
both cast rules.

The baseline stays at 245 rather than being accepted down to 243. Blessing it
would record two known refusals as the expected state and remove the only thing
that keeps them visible.

Fifteen refusals did change their stated cause, from
`ExactUseRequiresRenderedOccurrence` to `RenderedValueRequired`. They are the
arm64 import thunks and three `branchy` functions, all of which refused before
and refuse now, so this is not a coverage change. It is worth knowing which
work moved them, because a cause is the thing a later session searches on: the
thunks are the `braa x16, x17` tail-call shape whose refusal has always been
that nothing in the renderer has a form for a branch through a value, and the
new cause says the value now reaches the seal without a cell rather than
without a rendered occurrence. That is consistent with the identity-merge
accounting, which fills cells for values whose merges no longer render a
statement, and it means the thunk work described earlier now starts from a
different symptom than the one recorded against it.

**Widening inlining to duplicable values: the accounting cannot come second.**
The plan sequenced the literal admission first and the multiplicity rule after
it, and that order does not exist. Admitting literal-only values on their own
renders 53 of 54: the ledger counts one rendered occurrence per obligation, a
literal spelled at three readers produces three, and nine cells refuse with
`DuplicateRenderedOccurrence` immediately. The two land together or not at all.
`duplicates_are_a_repeated_literal` now sits beside `duplicates_are_exclusive`
as the second way several occurrences are one execution.

`literal_only_declarations` falls from 292 to 103 with 54 of 54 on every
column. Two restrictions hold it back from the rest, each with a reason rather
than to pass a gate: the value's own storage must be a lowering temporary,
because a register or memory cell holding a literal is a machine object the
program writes and a reader spelling the constant does not perform that write;
and no reader may sit in a certificate-elided instruction, because the
accounting for a partly-elided duplicable value is not established.

**The plan's question and the rewriter's are not the same question.** The first
attempt asked `term_is_duplicable`, which is "does rendering this twice observe
anything twice", and inlined any expression over never-redefined entry values,
dissolving parameter bindings across twenty-one tests. The plan's question is
whether a value is cheap enough to spell instead of name, and only a literal
is. Two neighbouring questions with one obvious-looking answer, which is the
shape this branch has now hit three times.

**The flag carriers were never a flag problem, and admitting flag operations
cannot fix them.** `Compare` is already an inlinable kind and the carriers hold
comparisons, so there is nothing for `ArithmeticFlag` to convert; admitting it
anyway fails, because the materialiser has no flag arm and the plan then
promises an inline the renderer cannot produce. Why a comparison-holding
carrier stays bound is a separate question that needs instrumentation, and it
is the open one for the 192.

**Seventeen fixtures were corrected, for the second time and for the same
reason.** They were chains of constants, so every value in them now inlines and
a test about a bound value had no subject; they read a register instead. The
first time was when single-use folding landed and each fixture gained a second
reader. A fixture built from the simplest possible values is a fixture that
stops having a subject every time the renderer gets better, and the comments
now name both reasons.

**The flag carriers are not the comma-condition problem, and the guess that
they were is worth recording because it was wrong.** `djb2` at x86-64 -O0 shows
`CF_2` declared above its loop and assigned inside a comma-packed header, which
reads as one problem with two symptoms. Counting across the corpus says
otherwise: 23 of the 192 carriers are named inside a comma condition and 169
are not. The two columns move independently.

What the 192 actually are, counted by shape over the rendered cells:

    uint8_t ZR_N   = (uint8_t)TMPZR_N;                              33
    uint8_t ZF_N   = (uint8_t)(tmp_Nf180_N == 0);                   26
    uint8_t CY_N   = (uint8_t)TMPCY_N;                              14
    uint8_t TMPZR_N = (uint8_t)(X1_N == 0);                         13

So arm64 writes a flag twice: the specification computes into a temporary flag
and then copies it to the architectural one, and both survive as carriers. The
copy is `ZR = (uint8_t)TMPZR`, a single-use copy of exactly the kind the
inlining rule admits, and it stays bound anyway. That is the question to
answer, and it is one value's disposition rather than a survey: take one such
carrier and read why the plan bound it.

Two things about the probe, the second correcting the first. The audit does
come out of a bare `pdd`: `R2SLEIGH_BINDING_AUDIT=1` writes one JSON line to
**stderr** prefixed `R2SLEIGH_BINDING_AUDIT__`, from
`r2plugin/r_anal_sleigh.c:939`, and the first attempt saw nothing only because
it sent stderr to `/dev/null`. But capturing it does not answer the question
either: the audit reports aggregate counts per domain -- for `fnv1a64` at arm64
-O1, 97 values of which 41 rendered and 56 were justified elisions -- and
carries no per-value disposition.

So answering "why did the plan bind this carrier" needs a probe inside
`binding_plan::rules::inlinable_values` printing which of its tests rejected a
named value, in the shape of the `R2DEC_TRACE_REFUSAL` probes that already pay
for themselves elsewhere in this document. That is a few lines in a file no
current effort holds, and it is the next step on the 192.

**`/bin/ls` renders 11 of 136 and has for longer than anyone noticed.** An
agent raised it as a regression from this session's work, which was the right
alarm and the wrong cause. Measured on the integration branch and on `ec8d589`,
the commit this session started from, the two are identical, cause for cause:

    rendered                                                        11
    refused: observation journal RenderedValueRequired (the thunks) 87
    refused: effect obligations, one to seven each                  18
    refused: unrepresentable control flow                            6
    refused: unobserved_binding_write                                4

This document records 22 of 48 real functions rendering, against 136 total with
88 thunks, which is 22 of 136 by the same arithmetic. So the count halved
somewhere earlier in this branch, and nothing caught it.

Nothing caught it because the coverage harness sweeps only `branchy` and
`hashes`, the two binaries this project compiles for itself. It reported 243 of
313 throughout and is structurally incapable of seeing a real system binary
halve. That is the same failure as trusting the rendering corpus as a
specification, moved from correctness to coverage: a gate over input we
generate cannot tell us how we do on input we did not.

Two things follow. The 22 is not a number to plan against until it is
remeasured, and several notes above rest on it. And the harness wants a real
binary in it, with the binary's own hash recorded beside the baseline so a
different machine reports a different subject rather than silently comparing
against one it does not have.

Confirmed again after the composed return value landed: still 11, which is
right, because the eighteen that change were all in `branchy`.

**And measure it with `tests/corpus/locked_probe.sh`, not with a bare `r2`.**
The shared-plugin hazard has now cost five conclusions, four before it was
written down here and one after, and every one of them looked like a real
finding until somebody repeated it. Writing it down does not work, because the
failure is silent: nothing about a stale plugin's output says it is stale. The
script builds this tree without the lock, then holds the lock across the
install and the command together, which is the only window in which the answer
is about this tree. Releasing between the two is what makes a stale answer
possible.

## The plan after the first benchmark run and the architecture survey

Two things happened on the same day and between them they reorder the work.

### The engine ran on the benchmark's own platform for the first time

The plugin now builds and runs on Linux x86-64 against the radare2 fork, and
DecBench is installed there with joern. The first head-to-head, on
`bzip2recover` compiled by GCC at `-O0`, thirteen functions scored by graph edit
distance against the source control-flow graph:

| decompiler | decompiled | perfect | mean GED |
| --- | --- | --- | --- |
| angr 9.3.3 | 13 of 14 | 4 | 5.54 |
| r2sleigh | 8 of 14 | 4 | 5.43 |

The reading is unambiguous and it is not the reading this branch has been
working from. **Accuracy is already competitive.** Where r2sleigh renders, it
matches the source structure slightly better than angr does, on the same
functions, with the same number of exact matches. **Coverage is the entire
gap.** Every point of the difference is a function that refused.

The six it missed refused for three causes, none of which is a tail call:
`unobserved_binding_write` from placement, `missing_definition` from placement,
and `RenderedValueRequired` from the observation journal, the last twice. Those
are accounting failures in the binding plan and the journal, and the survey
below independently traced two of them to duplicated predicates that have
diverged. So the noise work and the accounting work are the same work as the
coverage work on real code, which is not how this branch had them ordered.

### The eager sweep was making analysis seventeen times slower

Measured by moving the plugin's directory aside and back, on the same binary:
radare2 analyses `bzip2recover` in 0.68 seconds alone, and 11.98 seconds with
r2sleigh installed. The plugin's post-analysis reported spending 10.16 of those
seconds and then refusing the rest of the program against its own budget.

The cause was `sleigh_function_may_prove`, whose comment says it looks for a
transfer radare2 could not resolve and whose test was that a block has no
successor -- which is also true of every `ret`. Every function was admitted.
Asking the block's last instruction instead takes `bzip2recover` to 6.94 seconds
with sixteen of thirty-eight functions skipped and the same two unreachable
blocks proven. What remains is the per-function cost, about 286 ms per proved
function and about 1.05 s for one `pdd`, against an agreed bar of 100 ms for a
500-obligation function. That is the per-binary program cache, and it is now the
performance item rather than the sweep.

### What the survey found that the plan did not have

A seventy-agent read of the tree, with every finding put to independent
refutation, left fifty standing. The ones that change the ordering:

- **A transfer through a value has no renderer form at all**, at
  `crates/r2dec/src/fold/op_lower/implementation.rs:3233`. It costs **105 of the
  449 matrix cells and 84 of the 136 `/bin/ls` entries**, which makes it the
  largest single coverage item in the tree, far larger than the direct tail
  call it was grouped with. It is one machine shape with two SSA shapes: on x64
  the operand is a `Bound` value with no definition whose canonical storage is a
  RAM address, and on arm64 it is an `Inline` value defined by a copy from a
  register. A fix keyed to either alone gets half the cells.
- **The direct tail call is smaller than reported.** Ten of the forty-one
  refusing real `/bin/ls` functions are on the exact path, sixteen counting the
  short forwarders. The earlier figure of twenty-two was co-occurrence. The six
  functions mislabelled "unrepresentable control flow" are the same forwarders,
  so the counts do not add.
- **The exiting branch must not be rewritten into a call in `CFG::from_blocks`.**
  That was written, measured and reverted: `/bin/ls` went from 123 to 125
  refusals and from one to eighty-one refused obligations. The capability
  belongs in the source-facts layer, as a callsite interface offered for a
  branch whose target lies outside the function's bounds.
- **`same_type_casts` was measuring the rarer of two shapes.** It compared only
  directly adjacent casts, so a lone cast to a value's own declared type was
  never examined. The corrected predicate counts 3,395 across the fifty-four
  cells where the column had read zero. Every noise fix before this landed was
  scored against a blind gate.
- **The identity-merge predicate is stated twice and the copies have diverged**,
  and the divergence is a whole-function refusal rather than a style problem:
  the phi output's value cell stays empty and the journal refuses with
  `RenderedValueRequired`. The obvious repair is backwards; the term has to move
  to the rule, not be copied into the journal.
- **The parameter-slot conflict rule and the width rule are each written four
  times**, and the certified-entities pair has diverged into a whole-function
  refusal with `UnexpectedParameterDisposition`. The root cause is that the two
  candidate enums differ.
- **Fifteen register-alias tables, and the name-keyed ones give wrong answers
  today**: `rdx` and `dh` are reported as the same family, so an external type
  assumption for `dh` is applied to the `rdx` parameter; `ah` and `al` get the
  same key, so an alias pair is emitted between disjoint storages and
  pointer-ness propagates across it; and the AArch64 frame pointer is spelled
  two ways that can never meet, so those slots are structurally un-rebasable.
- **Thirty-two-bit x86 is given the SysV-64 argument registers**, because the
  prepared arch name is re-spelled from a substring match rather than passed as
  the typed family.
- **Import evidence never crosses into r2sym**, so an eighteen-model libc seed
  table, a role source and a name hint are all permanently inert, and the
  twenty-one summaries the registry builds are discarded per function.

### Decisions the owner settled

| question | answer |
| --- | --- |
| a value with one rendered and one elided reader | inline it; the guard counts only rendered readers |
| the unreachable r2sym subsystems | delete, keeping what they proved as tests |
| interprocedural helper inlining | delete; out of scope, and a working owner already computes those summaries |
| import thunks in the coverage denominator | render them and keep them; report against 136 |
| a type spelling the parser cannot place | refuse, rather than inventing a typedef |
| radare2 type ingestion | the trusted snapshot is canonical, not the JSON schema |
| what CI sweeps | a pinned binary the repository ships gates; the runner's own binary is reported |

### The ordering now

1. The accounting refusals, because they are what the benchmark measures:
   the identity-merge predicate, the parameter-slot rules, and the two
   placement refusals behind `unobserved_binding_write` and
   `missing_definition`.
2. The transfer through a value, at 105 matrix cells and 84 `/bin/ls` entries.
3. The per-binary program cache, for the 286 ms per function.
4. Cast policy, now that 3,395 redundant casts are visible to the gate.
5. The direct tail call and the empty-body mislabel, together.
6. Array indexing, stack buffers and `for`, which is the largest information
   recovery win and is unblocked.
7. The register-identity collapse, which removes four live wrong-answer paths.
8. The deletions.

## What is actually blocking us, measured

The GED-only reading in the previous section was too kind, and this section
corrects it. DecBench now runs all three of its metrics on `bzip2recover`,
built by GCC at `-O0`, sixteen functions:

| metric | what it measures | angr | r2sleigh |
| --- | --- | --- | --- |
| ged | control-flow graph edit distance from source | 5.54 mean, 4 of 13 perfect | 5.43 mean, 4 of 13 perfect |
| byte_match | assembly of the recompiled output against the original | 0.60 mean, 0.75 median | 0.11 mean, 0.12 median |
| type_match | recovered types against DWARF | 0.59 mean, 3 of 11 perfect | 0.10 mean, 0 of 11 perfect |

**Control-flow shape is competitive and nothing else is.** `byte_match` is the
closest thing to a semantic correctness score this project has ever had, and it
is not refusals dragging the mean: on the functions r2sleigh renders it scores
0.00 to 0.21 where angr scores 0.35 to 0.93 on the same functions.

### Why, in one function

`readError` in `bzip2recover` is four source statements. Its rendered
control-flow graph is a perfect match, GED 0.0. Its `byte_match` is 0.21
against angr's 0.91, and the rendering shows every reason:

```c
FILE* RAX_1 = (FILE*)*(uint64_t*)&stderr;
uint64_t RDX_2 = (uint64_t)&progName;
char* RSI_1 = (char*)(uint64_t)"%s: I/O error reading `%s'...\n";
FILE* RDI_1 = (FILE*)RAX_1;
uint64_t RAX_3 = sym_imp_fprintf(RDI_1, RSI_1, RDX_2);
```

Fourteen statements for four. Six of them stage arguments into register-named
locals that are read once. Every value carries a cast it does not need.
`stderr` is declared `extern char stderr[]` and read through a pointer cast,
because a global has no recovered type. So the noise columns are not measuring
cosmetics: they are measuring the score.

**And the call is wrong.** The source passes four arguments; r2sleigh renders
three, dropping `&inFileName`, which the machine plainly loads into `rcx`. In
`tooManyBlocks` the same declaration serves three `fprintf` callsites of five,
three and three source arguments, and all three render as three. The argument
count is being decided once per callee rather than once per callsite, which for
a variadic callee is wrong by construction. The proof line above the function
says `0 refused`. This is a wrong answer rendered confidently, which is the one
outcome this project treats as worse than refusing, and no existing gate can
see it: the corpus is nine hash functions with no variadic calls, the coverage
sweep only asks whether a function rendered, and graph edit distance never
looks at an argument list.

### The refusal population, split properly

The headline coverage numbers are dominated by import thunks. Across the 449
functions in the coverage baseline:

| population | rendered |
| --- | --- |
| import thunks | 0 of 105 |
| real functions | 272 of 344 |

Every one of the 105 thunks refuses with `RenderedValueRequired`, and they are
the transfer-through-a-value item. Of the 117 `RenderedValueRequired` refusals
in total, 105 are thunks and 12 are real functions, so the duplicated
identity-merge predicate is worth twelve functions rather than a hundred.

The 72 real refusals, by cause:

| count | cause |
| --- | --- |
| 20 | effect obligations refused |
| 12 | observation journal: RenderedValueRequired |
| 6 | placement: missing_definition |
| 6 | placement: unobserved_binding_write |
| 6 | unrepresentable control flow |
| 4 | placement: preserved_carrier_read_before_assignment |
| 4 | projection authorization, memory renderer |
| 4 | observation journal: ConflictingUse |
| 3 | placement: unobserved_binding_read |
| 7 | singletons |

**Fifty-six of the seventy-two are the accounting machinery refusing its own
output**: twenty from the effect ledger, twenty from placement, sixteen from
the journal. Control flow accounts for seven and type recovery for none. The
proof accounting is the coverage blocker on real code, not the decompiler's
understanding of the program.

### Performance, profiled rather than guessed

Nothing is cached. Decompiling one function three times in one radare2 session
costs the same every time, and the same three callees are lifted from scratch
on each call. `crates/r2engine/src/lib.rs` holds no cache, and
`crates/r2ssa/src/fingerprint.rs` exists but is not used as a cache key.

| function | capture | decode | callee lift | root lift |
| --- | --- | --- | --- | --- |
| readError | 513 ms | 0.06 ms | 382 ms, 3 callees | 131 ms |
| bsGetBit | 618 ms | 0.05 ms | 450 ms, 3 callees | 168 ms |
| main | 1725 ms | 0.11 ms | 1139 ms, 4 callees | 586 ms |

Instruction decoding is nothing. Callee lifting is about eighty per cent of
capture, and it is repeated per caller. The r2dec side is small except in the
structurer, which is superlinear: `main` spends 2.27 seconds there and then
refuses, against a total of 2.77 seconds for every other r2dec stage combined.
That is the BDD safety budget, computed as blocks times 128 and consumed in
whatever order the proofs happen to run.

Whole-binary, after the eligibility-filter fix, with the plugin's directory
moved aside and back:

| binary | plugin absent | plugin present |
| --- | --- | --- |
| bzip2recover, 38 functions | 1.12 s | 7.50 s |
| bzip2, 154 functions | 18.38 s | 29.93 s |

### What we cannot see, which is the deepest problem

Every defect above was invisible to the gates until the benchmark ran.

- The **differential column** is the only semantic check, and it covers nine
  hash functions of one shape, a loop over bytes accumulating an integer, with
  eighteen to twenty-three fixed inputs each. No struct, no array of structs,
  no float, no recursion, no varargs, no signed division, no union, no
  multi-word return, no pointer to pointer.
- The **coverage sweep** asks only whether a function rendered.
- **GED** measures graph shape and is blind to the body.
- **byte_match** and **type_match** had never been run before today.

So the project's correctness evidence covers one program shape, and its two
quality metrics were unmeasured. Making `byte_match` a gate, and widening the
differential corpus past hash functions, is the work that lets every other item
be judged.
## Where a function's cost actually went: a Sleigh load, not the program

The per-function cost was the task, and the shape of the answer was agreed
before the work: an engine-owned per-binary cache of prepared bodies, because
the snapshot walk pulls in callee bodies and a callee is lifted again for every
caller that mentions it. That cache is built and it works. It is not what was
making a function expensive.

**Every measurement below was taken on the Linux VM against the DecBench GCC
-O0 builds, with each column's plugin installed under its own `HOME` so that
neither column can be overwritten while it is being measured.** That precaution
was not optional: the first two attempts at this measurement were void. The
shared install lock in `tests/locked_run.sh` was held for the whole of the
second run and another tree on the same host still installed over the plugin
between two sections of it, so half of that run was measuring somebody else's
build. radare2 reads its user plugins from `$HOME`, so a private `HOME` per
column is an isolation nothing outside the script can defeat, and it needs no
cooperation from the other agent. That is the sixth measurement this class of
error has cost the project and the first one it cannot cost again.

    bzip2recover, 38 functions        absent    before     after
      aaa                              0.76s     6.30s     3.29s
      aa                               0.19s     2.70s     2.29s
      aaa minus aa                     0.57s     3.60s     1.00s
      proof sweep, plugin's share         --     3.03s     0.43s
      per proved function (22)            --      138ms      20ms
      pdd capture, first                  --      599ms    58.8ms
      pdd capture, repeated               --      586ms     114us
      pdd wall clock over aaa             --   in noise    0.073s

    bzip2, 154 functions              absent    before     after
      aaa                             10.84s    23.90s    22.00s
      aa                               3.00s     5.99s     5.66s
      functions the sweep reached         --        35        97
      of those, proved                    --        35        42
      budget exhausted at                 --    10.35s    10.02s
      pdd capture, first                  --     1065ms     204ms
      pdd capture, repeated               --      880ms     135us

Medians of three on bzip2recover and two on bzip2; the machine is shared and
noisy, so the ratios are the claim and the milliseconds are approximate.

### The cache works completely, and the sweep gets nothing from it

Repeated work vanishes. A second `pdd` of one function costs 114 microseconds
of capture against 586 milliseconds, five thousand times less, with
`cached_callees=3 cached_root=1` on the line saying why.

And the analysis sweep reported `cache_hits=0` across the whole of `aaa`, with
26 entries for the 22 functions bzip2recover proves. The reason is worth
keeping, because it invalidates the premise the cache was designed from: **the
functions an analysis sweep proves are import thunks, and a thunk has no
callees to share.** The sweep produced 22 entries, exactly its 22 roots, and
not one callee entry. So the sweep's cost was never repeated work between
functions. It was the first-time cost of one function, and no cache removes
that.

### What the first time was spent on

`Disassembler::from_trusted_profile` parses the whole compiled `.sla` and
rebuilds the register and address-space tables from it, and `lift_owned_function`
called it once for the function asked for and once for every callee captured
beside it.

    x86-64 Sleigh profile load      58000-91000us
    one three-byte block lift             21-83us

Three orders of magnitude, and the load was on the per-function path. A request
with three callees spent about a quarter of a second building four identical
copies of one specification. A twelve-byte import thunk cost a profile load and
almost nothing else, which is the whole explanation for twenty-two tiny
functions taking three seconds to prove.

`shared_trusted_profile` loads each embedded profile on first ask and hands the
same one out afterwards -- 52588us, then 0us, then 1us. Reuse across functions
is the reuse that already happens across blocks: `lift_genuine_block` takes
`&self`, every block of a function already goes through one instance at
arbitrary addresses in arbitrary order, and nothing is reset between them now
or before. It is thread-local rather than global because the instance owns a
C++ Sleigh object that declares neither `Send` nor `Sync`, so the bound is one
per embedded profile per lifting thread: at most eleven, in practice one.

Both changes were needed and neither substitutes for the other. The profile
load is what makes a *first* look at a function cheap; the program cache is what
makes every look after the first nearly free. Together the per-proved-function
cost falls from 138ms to 20ms and a repeated decompile from 586ms to 114us.

### Keying a cache when a stale hit is a wrong answer

The key is the whole serialized snapshot, byte for byte, not a hash of it. A
miss costs time and a wrong hit renders a body that is not the function's, with
nothing downstream to say so. A hash small enough to store makes two claims at
once -- that it covers every input, and that no two inputs collide -- and
neither can be checked at the point of use, while the snapshot *is* the whole
input to a lift by construction of the V2 boundary. Comparing it costs one
`memcmp` and a few kilobytes per function against hundreds of milliseconds.

`stable_ssa_semantic_fingerprint` is recorded beside each entry rather than used
as the key, which is the only honest place for it: it is computed from the
prepared artifact, so it cannot be known until the work the lookup exists to
avoid has been done.

Two things the design had to get right, both of which would have silently
produced a cache that never hits:

*A root and a callee body are two different artifacts for one address.* The
function a request asks about is prepared knowing the recovered interfaces of
everything it calls; a body captured as a callee is prepared alone. Under one
address key each would be the other's eviction and neither would ever hit, so
`PreparedRole` is part of the key.

*A callee carries its caller's capture tag.* radare2 gives every callee the
root's `revision_identity`, deliberately, so a consumer can tell the bodies were
read together -- which means the same body under two callers serializes two
ways and a byte-exact key never matches in the one case a callee cache exists
for. `encode_snapshot_cache_key` writes the body's own `content_identity` in
the tag's place. Every other field is still written and still compared, so two
different bodies are still told apart by the bytes describing them, and the
substituted field is a hash of those same bytes rather than a new claim. On a
radare2 predating `content_identity` the two are equal and this degrades to a
key that misses rather than one that is wrong.

The entry bound is one per address per preparation, replaced when that address's
input changes, so the count is the program's own function count at most twice
over. Nothing is evicted while a session runs: an eviction policy would have to
guess which function a later request wants, and a sweep asks about all of them.

### The machine arena was lowered twice per render

`BindingPlan::build_shadow` builds a `MachineProjection` and keeps it;
`build_upstream_shadow_oracle` built a second from the same source. The oracle's
comment explains that it takes no plan as input so a wrong plan disposition is
observable rather than self-validating, and that argument is about the plan's
*decisions*. A projection is not one: it is derived from the source alone, and
`validate_source`, which `derive_report` already calls first, has proven the
plan's copy is what this exact source produces. The oracle now borrows it, and
the module documentation says which independence is load-bearing and which was
only cost, because the next reader of the first sentence would otherwise put
the second build back.

### Two open items, and one decision that is not ours

**The dominant cost is now the `aa` path, and nobody has measured it.** On
bzip2recover the plugin adds 2.10 seconds to `aa` after this work against 0.43
seconds to the proof sweep -- five times as much, over 38 functions, or about
55ms each. That is `sleigh_analyze_fcn`'s semantic comments,
`sleigh_get_data_refs`, and `sleigh_op` per instruction, none of which this
work touched and none of which has ever been split. It is the next measurement
to take, and it is a bigger number than the one this task was given.

**The two smaller hot shapes were deliberately not taken.** `inlinable_values`
scanning `graph.insts` per candidate sits in `binding_plan/rules.rs`, which
another effort is editing for the inlining guard, and the load-lowering access
filter is in `MachineProjection::from_artifact`. Both are inside the
`binding_plan` stage, which is 10ms of a 21ms render on `bsGetBit` and 275ms
against the structurer's 2274ms on `main`. Halving either moves nothing that
matters while the structurer is superlinear, so the structurer comes first.

**Whether the `aaa` sweep should become lazy is still open, and it is the
owner's call rather than ours.** The measurement says the question is live:
bzip2 still exhausts the ten-second budget, now reaching 97 of 154 functions
instead of 35 and proving 42 instead of 35. So the sweep is 2.8 times further
through the program and still does not finish it. Deferring proofs to first
`pdd` would finish `aaa` in the lift alone -- but the indirect-call xrefs and
unreachable-block comments radare2 consumes are produced by those proofs, so
`axt` immediately after `aaa` would no longer show them. Trading a fact radare2
can currently see for analysis time is a decision about what the plugin
promises, not an optimisation, and it is recorded here unmade.

The ten-second budget itself deserves the same scrutiny the project gives every
other bound. It is a constant per analysis mode in `r2engine`, not derived from
anything the sweep has to clear, and on bzip2 it is the only thing deciding how
much of the program gets proved. Whatever replaces it should be derived from
the work in front of it -- the function count and the measured per-function
cost, both of which the sweep now knows -- rather than from a number that
happens to feel like a long time.
The tail transfer: what the source now carries, and the two forks that remain
-----------------------------------------------------------------------------

**The brief's numbers were wrong in both directions, and the corrected ones
reorder the work.** The direct tail call was described as 22 of the 41 refusing
real `/bin/ls` functions and as the project's largest coverage lever. Measured
against the coverage baseline, the direct tail call is ten functions, sixteen
counting the short forwarders, and the largest lever by a wide margin is its
sibling: the transfer *through a value*, which is every import thunk, at
**0 of 105 rendered** across the whole sweep -- 84 in `/bin/ls` and 21 across
the corpus binaries. Every one of the 105 refuses identically, with
`observation journal: RenderedValueRequired`. Of the 72 refusing real
functions, only twelve are `RenderedValueRequired`, and those are a different
cause.

**Measured, on this tree, before and after.** 271 of 449 both before and after
the two commits below: 261 of 313 on the corpus binaries, 10 of 136 on
`/bin/ls`, 0 of 105 on thunks. The commits are plumbing and an honesty fix, so
coverage is unchanged by design; what moved is which cause each refusal
reports. The one `REGRESSION` line the harness prints against its blessed
baseline, `sym.func.10000306c`, predates this work: it comes from the
integration branch's new linear-body refusal, and was measured identically
before anything here was written.

**What radare2 now carries.** The function map is what knows that a jump's
target is where another function starts, and the relocation table is what
knows which import a loaded slot names, so the detection sits in the fork at
`libr/anal/function.c` rather than being guessed from addresses in Rust.
`fcn_context_collect_callees` kept only the `CALL` references leaving the
image; it now also offers a *tail jump* -- a direct successor outside the image
that is exactly a function entry, so a jump into the middle of another function
stays what it was -- and a *tail slot*, a block with no successor whose last
instruction decodes as a jump through a value. Each callee, each call site
interface and the interface hash carry an `RAnalCallTransfer`, the snapshot
exposes it through `r_anal_function_snapshot_call_site_transfer`, and the wire
format is version 7: one byte after the target name, read as `Call` from any
older buffer. `RBinBind` gained a relocation-at-address lookup, and
`function_get_signature` split so a prototype can be built for a bare name that
is no function of this binary, which is what an imported callee is.

**An empty body was being reported as unrepresentable control flow.** A
function whose body renders no statement had its `FunctionBody` marker
collapsed by the structurer cleanup along with the body it wrapped; sealing
then failed for want of a marker at the root, and that became
`unrepresentable control flow`. Six `/bin/ls` forwarders reported a structural
refusal for a fact about their contents. With the marker kept, that column goes
from six to zero and all six report the cause they actually have --
`effect obligations refused`, the refused `ControlTransfer` for the tail branch,
which is the real subject. Worth stating plainly because it was the risk in
the fix: they did **not** become empty-bodied renders. An empty body would have
counted as rendered by the harness and claimed the function does nothing, which
is the wrong-answer class; the effect ledger refuses first and no cell was
bought with a lie.

**Fork one, and it is the whole of the 105: what a thunk is allowed to claim.**
The refusal is exact and the machine side is easier than expected. On x86-64 a
thunk is one instruction and its whole SSA is
`BranchInd { target: ram:0x100002010 }` -- the GOT slot *is* the target value,
with no definition, which is why the journal has nothing to account. On arm64
the slot is `adrp` plus a displacement and the branch reads a register loaded
from it. So the machine can prove the exact slot, and radare2's relocation
names it. Note in passing that radare2's own `ICOD` reference for these blocks
is the `adrp` page base, not the slot: at `0x1000042a4` it points at
`0x100008000`, whose relocation says `humanize_number`, while the `add #0x28`
makes the true slot `0x100008028`, which the relocation table names
`__assert_rtn` -- matching the thunk. Keying on that reference would have named
every thunk in a page after the first relocation in it. The source must
therefore describe slots and let the machine pick, never pick for it.

What is *not* settled is what may then be rendered, and the arithmetic decides
nothing on its own. A thunk forwards the arguments its caller left in
registers; it reads none of them and writes none of them. So the standing rule
that an unknown call takes its arity from the convention's argument registers
provably written and live into the transfer yields **zero arguments** here, and
would render `acl_get_entry()` for a function of three arguments -- silently
dropping them, which is exactly the class of wrong answer the variadic
callsite-arity defect was just raised for. Counting `/bin/ls`'s 84 thunks by
what radare2 knows about the callee:

    complete non-variadic prototype, forwardable as a call        54
    no recovered prototype, so arity unknown                      22
    variadic                                                       8

The eight variadic ones are not a gap in the recovery: C cannot forward `...`,
so no call expression exists for them at any level of knowledge. The options,
with the trade-off that separates them:

1. *Render the 54, refuse the 30.* Truthful, and refusing per-callee where the
   evidence is absent is what this project already does per-value. Buys 54 of
   105 cells and leaves the metric honest about the rest.
2. *Render all 105 as a call through the named slot.* Requires asserting an
   arity radare2 never recovered for 22 of them, which drops arguments
   silently, and has no expression at all for the 8 variadic.
3. *Render none.* The status quo, and the position the earlier survey took when
   it recorded the value of rendering thunks as low.

Option 1 is the one consistent with the rest of the system, but it decides that
a thunk may claim a direct call to the symbol its slot's relocation names, on
radare2's authority and marked as such, and that is a claim about what the
decompiler asserts rather than an implementation detail. It is put here rather
than taken.

Two smaller things fall out of it either way. The thunk's parameters have to
exist for a forwarding call to name them, and radare2 already supplies them --
it gives the thunk function the callee's own signature -- so this does not need
the pass-through parameter work that four other `/bin/ls` functions do. And the
marking has no home yet: nothing in the renderer says which facts came from
radare2, so "the callee at this site is named by the relocation at slot S"
needs a line the proof can carry.

**Fork two: what IL shape a direct tail call takes.** Independent of the above
and needed for the ten-to-sixteen real functions. The source now offers the
callsite; what is unsettled is the representation.

*Option A -- rewrite at the lift into a call followed by the machine's own
return sequence.* `lift_owned_function` has the external exits, the advisory
sites and the architecture, so it can replace a terminal `Branch f` licensed by
a `TailJump` site with `Call f` and then the ops the architecture's return
performs. Downstream nothing changes: the block is an ordinary call-then-return
and every certificate already applies. The costs are real: the synthesized ops
are the *callee's* epilogue attributed to the caller's `jmp`, so the
per-instruction ledger states a load and a stack adjust that instruction does
not perform; the genuine lift stops being a function of bytes and Sleigh alone;
and on AArch64 the synthesized `return [x30]` reads x30 after the call, whose
`CallDefine` clobbers it, so either a tail call gets no `CallDefine` for the
return-address carrier or the return-address fact learns to look through one.

*Option C -- a terminal call with no fallthrough as a first-class tail return
boundary.* The op becomes `Call f`, the terminator `Call { fallthrough: None }`,
and `collect_source_boundary_facts` records a return boundary at the call whose
machine state is the stack-pointer and return-address carriers reaching it
entry-preserved -- which is the true requirement of a tail transfer, rather
than a load of a return slot that never happens. The renderer emits
`return f(args);`. The cost is breadth: every place that keys a return on
`SSAOp::Return` needs a tail arm -- the boundary collector, the return-control
and return-value certificates, the render plan, placement, the observation
journal, and both terminators -- which is the five-places shape this document
already records being reverted whole when attempted late in a session.

*Option B, keeping the `Branch` op and giving it a form,* is dominated by C: it
needs the result register defined at the branch, which is what calling it a
call provides.

**One caution for whoever takes either fork.** Do not build anything that
assumes a callee has one arity. A separate confirmed defect decides argument
count once per callee rather than per callsite, so three `fprintf` calls of
five, three and three arguments all render as three; the thunk work touches the
same call-boundary machinery and must not deepen that assumption.
## Self-assignments, literal-only declarations, and the staging locals

Three columns were the brief; a fourth thing turned out to matter more, and two
of the three brief items ended as questions rather than answers. Everything
below is measured on the fifty-four cells with `locked_matrix.sh`, and every
number that moved is stated with the state it moved from.

    predicate                    before   after   what happened
    self_assignments               225      50    merge-copy coalescing widened, and the
                                                  carrier zero-extend now discharges
    literal_only_declarations      103      80    call arguments now spell their literal
                                                  where it is read; the rest are open
    flag_carriers                  192     192    untouched, and still the open question
    cast_chains                      8       8    untouched
    comma_conditions                17      17    untouched
    gotos                          125     125    untouched
    same_type_casts                  0       0    still zero

54 of 54 on generation, raw, diagnostic, differential, binding audit, effect
obligations, placement and render refusal. Whole-binary coverage 272 of 449,
no regressions. Seventeen cells differ from the blessed snapshot and want a
fresh blessing.

**The staging locals were never a single-use question, and that is the finding
worth carrying.** DecBench scores `byte_match` by recompiling the rendering and
comparing assembly, and on `bzip2recover` at -O0 r2sleigh sat at 0.11 against
angr's 0.60. `readError` is four lines of source and rendered as fourteen
statements, six of which existed only to stage call arguments. The obvious
reading is that the inlining guard counts elided readers, and it is wrong.
`SSAOp::Call` takes only the callee as an operand: a value staged in `rdi` is
consumed by the call boundary and has **no `UseSite` in the graph at all**. The
SSA dump says so directly -- `RDI_1 ... uses=[]`. `inlinable_values` turned
those values away at its first gate, "no readers", before any question about
single use could be asked. The callsite certificate is the source's record that
the read happens, the renderer already consults it and already accepts an
argument the plan inlines; only the plan did not know the reader existed. It
counts them now. `readError` renders as eight statements, and the literal-only
column falls by 23.

`RDI_1 = (FILE*)RAX_1` still survives, because a register-to-register copy
roots at `Source` and `Source` is not among the shapes that render inline.
Whether it belongs there is the next thing to try on this path, and it is
cheap to test.

Measured on the benchmark, `bzip2recover` at -O0, `byte_match`, the eight
functions r2sleigh renders, before and after this one change:

    function          before    after
    readError         0.2143   0.4000
    writeError        0.2143   0.4000
    mallocFail        0.1607   0.3095
    tooManyBlocks     0.1558   0.3158
    endsInBz2         0.0878   0.0887
    bsPutBit          0.0529   0.0534
    bsClose           0.0000   0.0000
    entry.fini0       0.0000   0.0000
    mean              0.1107   0.1959

Nothing regressed and nothing stopped rendering. angr scores 0.6017 over the
fifteen it decompiles, so the gap is far from closed, but the four functions
that are mostly calls roughly doubled, which is what a staging local costs when
it is spelled as a statement instead of an argument. `bsClose` at 0.0000 and
`bsPutBit` at 0.05 are not call-shaped and are where the next look belongs.

### Three things that were tried, measured, and reverted

Each looked right, each is recorded with the evidence, and none should be
retried without reading the reason.

**Counting only rendered readers is unsound as `inlinable_values` stands.**
Discounting a reader whose instruction a certificate elides is what the brief
asked for and it is what the staging locals appeared to need. It widens what
may be folded without widening the window the interference test looks at: that
test spans the definition and the one reader the guard then believes in.
`fnv1a64` at x86-64 -O2 renders `R8_1 = byte3;` and then
`R8_1 = (R8_1 ^ (... ^ R8_1) * k) * k`, reading the accumulator after the byte
load overwrote it -- a wrong hash under a proof line reading `0 refused`. Three
cells compute wrong answers and five more refuse. If this is wanted, the
interference test has to cover every reader's window, not the surviving one's.

**Discharging an absorbed carrier extension on the write that absorbed it
refuses ten cells.** This was the plan for the 149 self-assignments of the form
`EAX_2 = (uint64_t)(uint32_t)EAX_2`, and the machine half of it landed:
`MachineProjection::absorbed_extensions` and `absorbing_write` now report which
extensions a `ZeroExtend` projection consumed, with tests, including the nested
case where a byte is widened twice. The accounting half is where it stops, and
the cause was bisected to one cell rather than guessed: the extension reads the
very binding the fused statement defines, so recording that operand as a
rendered use puts a *read* of the object on the statement that first assigns
it, and placement refuses with `read_before_assignment`. Dropping just the
operand targets changes the refusal to `ExactUseRequiresRenderedOccurrence`,
which is the proof that the operand cell is the one at fault.

That looked like a question about accounting and it was not. **The answer is
below, under "the conflation was in placement's ordering model"; what follows
is the reasoning that turned out to be aimed at the wrong layer, kept because
the options are the ones anybody will reach for next.** What is
the honest cell for an operand read that a write projection absorbed?

- *Elide it*, with a reason of its own. Truthful -- the read does not appear in
  the text -- and it is the mechanism the codebase already uses for the
  analogous case, `account_materialized_phi_occurrences`. It contradicts the
  brief's expectation that no new elision reason would be needed.
- *Keep it exact and teach placement that a discharged operand read at the
  statement that defines it is not an occurrence.* Preserves the "rendered by
  equivalence" story and splits the journal's notion of an occurrence from
  placement's, which is exactly the two-answerers-that-drift shape this
  codebase keeps warning about.
- *Narrow the discharge* to extensions whose operand is not in the absorbing
  write's binding. This disables the feature: same-binding is its precondition.

None of the three is needed.

### The conflation was in placement's ordering model, one level below

Asked to trace it further rather than choose among ways of living with it, the
answer came out clean and it is now landed.

A statement contributes **two** ordered occurrence groups, not one:
`record_completion_observations` partitions its markers into reads and writes
and records the reads at order N and the writes at order N+1, because a
statement reads its operands before it assigns its destination. That is right
for `x = x + 1`, where the read names the value the statement replaces. It is
wrong when the read names the value the statement *produces*, and nothing in
the model could tell those two apart: the only thing relating a statement's two
groups was that their orders happened to be consecutive, so a read could never
sort after a write of its own statement however it was ranked. The first
attempt at a fix ranked self-reads after writes and changed nothing, because
the rank only breaks ties *within* one order and these are two orders. The
trace that showed it is worth keeping in mind:

    binding=BindingId(3) order=24 self_defined=true  Read(Use(inst 20, input 0))
                         order=25 self_defined=false Write { inst: 19 }
                         order=25 self_defined=false Write { inst: 20 }

So the two groups now carry the statement they came from, occurrences sort on
that statement rather than on the group order, and a read of a value that a
write in the same statement defines is ranked after the writes. The read stays
an occurrence, stays exact, stays the binding's, and proves the object live; it
is placed where it happens. `FinalBindingRead` gained the value it names and
`FinalBindingWrite` the value it defines, which is what lets them be matched,
and `FinalObservationScope::Exact` gained the statement.

No new elision reason, no split between what the journal calls an occurrence
and what placement does. The accounting rule the owner settled -- a rendered
term discharges the replaced instructions' cells as exact, by equivalence --
holds exactly as written; it was the *order* that was wrong, not the cell.

Self-assignments fall from 205 to **50** across the fifty-four cells, with
`pearson`, `crc32_bitwise` and `fnv1a64` rendering at every x86-64 level where
they had refused. What is left is not the carrier zero-extend.

**Coalescing the program's own copies, merge edges whose source is version 0,
and literals held in registers all delete an object's only definition.** A
copy normalization made for a merge is safe to drop when both sides are one
binding, because nothing can have touched the object between an edge's two
ends. A program copy has a position, and the object can be written between its
source's definition and it -- a save and restore around a clobber is that
shape. A live-in register that is not a parameter has no declaration to be
rendered by. And `RAX_1 = 0xcbf29ce484222325` initialises an accumulator it
shares a binding with, so spelling the constant at each reader deletes the
definition and the loop header reads it unassigned.

The literal case is the one with a clean statement of what would be correct,
and it is blocked on ordering rather than on evidence: the honest test is
whether the value is coalesced with anything, and that cannot be asked where
inlining is decided, because the partition is computed *from* the inlining
answer. Admitting register literals needs a two-pass partition -- provisional
components first, inlining decided against them, then the real partition -- and
that is a structural change, not a predicate change. Until then the
lowering-temporary restriction stands, and the comment beside it now says so
with the reason rather than the storage class.

What did survive from that direction: a copy relocated ahead of a certified
carrier's entry edges is coalesced like any other merge copy, which is most of
the 20 self-assignments that went.

### Two defects found on the way, both fixed

`expression_renders_inline` is the list of shapes the materialiser can build,
and `Constant` was missing from it. Every literal the duplicable rule admitted
was then asked whether a constant renders inline and told no, which is why that
column had not moved in a previous session either. A computation *over*
constants is still not a constant: `machine_expr_is_literal` is true of
`popcount(0xf0f0)` because it asks only whether every leaf is constant, and the
materialiser has no form for a population count. Two pipeline tests were
quietly asserting exactly that distinction and caught the first attempt.

The parameter-slot candidate rules were written twice, in `construction` and in
`seal`, and they disagreed about a slot claimed three times: one overwrote the
refusal reason, the other kept it, so the seal would reject a plan that was
right. They are one statement in `rules` now.

### Probes added

`R2SLEIGH_TRACE_INLINE=<display name>` or `=all` prints, for each value,
which gate in `inlinable_values` turned it away and why. This is what turned
"the guard counts elided readers" into "a call argument has no `UseSite`", and
it is the probe the previous session asked for when it recorded the flag
carriers as needing one. `R2SLEIGH_DUMP_SSA=1` prints the prepared and
normalized functions, every value with its storage, definition and use sites,
and every instruction; between them the two answer most "why is this value
bound" questions without a rebuild.

### A hazard that cost two measurements here

Syncing a worktree to the benchmark host with `rsync` carried macOS `.o` files
into `r2plugin/`, the host linker rejected them, `make install` aborted *before*
copying the library, and DecBench then scored the previously installed plugin.
The run looked completely normal and the numbers were identical to the
baseline, which is exactly what a real "no effect" result looks like. On a
second run the Makefile copied a library that was not the one just built. Both
are the shared-plugin hazard wearing a different coat, and the answer is the
same one this document already gives for the corpus: verify the artifact you
measured is the artifact you built. `run-placement.sh` on the host now copies
the freshly built library itself and prints whether a string only this tree
contains is present in the installed one.

## The effect-ledger refusals, split by layer

The effect ledger is the largest single cause of refusal among real functions,
26 of them across the coverage baseline, and until now the cause line said only
"N refused, N unaccounted, N conflicts". `R2SLEIGH_DEBUG_UNOWNED=1` writes a
per-function ledger line to `/tmp/r2sleigh_unowned.log` naming the layer, the
reason and the obligation ids, and it splits them cleanly. Swept over 78
functions in three binaries, four had a refused obligation:

| count | layer and reason | obligation kind |
| --- | --- | --- |
| 22 | `ssa/unsupported-effect` | `volatile-or-unknown` |
| 5 | `codegen/block-not-rendered` | `live-value-producer` |

The two are different problems and only one of them is about the decompiler's
ability to read a program.

**`ssa/unsupported-effect`** was written up here as a scope question about
compiler stubs. That was wrong, and tracing it took twenty minutes. It is one
unimplemented rule, and the same rule accounts for three other symptoms this
branch is chasing separately.

The obligations refuse at `crates/r2dec/src/effect_ledger.rs:78`, which turns
`VolatileOrUnknownEffect` into a refusal unconditionally. That is the report,
not the cause. The kind is minted at `crates/r2ssa/src/obligation.rs:519`,
whenever a call boundary is not `complete`. And a boundary becomes complete in
exactly one place, `crates/r2ssa/src/semantic.rs:3144`, reached only when
`machine_context.call_site_interface` returns an interface for the site. The
field's own comment says so: "Only an exact source-owned callsite interface may
change this state to complete."

So a call radare2 could not resolve to a callee has no interface, never
completes, and every obligation it carries is refused. The refusing stub is
precisely that shape. `sym._init` in the pinned GCC binary disassembles to
`endbr64; sub rsp,8; mov rax,[rip+0x2fd1]; test rax,rax; je +2; call rax;
add rsp,8; ret` — the `ff d0` at `0x401014` is an indirect call through a
register, the standard `__gmon_start__` guard. Nothing about it is a compiler
oddity worth excusing.

The owner settled the second path years of this branch have needed: a call
whose signature nothing knows takes its arity from the convention's argument
registers that are provably written before the call and live into it. That rule
would complete such a boundary. It is not implemented, and its absence is the
single cause behind four things counted separately until now: these 22 refused
obligations, the call that renders `f()` with an empty argument list under a
proof line saying nothing was refused, the import thunks that transfer through
a value, and the direct tail call. They are one defect seen from four sides.

**`codegen/block-not-rendered`** is the real one. A block exists in the SSA,
produces live values, and never reached the output, so the obligations of the
values it produces have nowhere to be discharged. `siphash24` at x64-O1 is the
clearest case: 435 obligations, 393 rendered, 40 elided, and exactly two
refused, both `live-value-producer` on the same block. Anything that drops a
block after the plan is fixed produces this, so the trace runs from the
structurer's region handling and the linearizer through placement's statement
removal.

Note that the elision profile of that same function is healthy and worth
keeping as a reference for what a well-accounted function looks like:
21 coalesced identity phis, 6 coalesced copies, 3 dead stack bases,
3 materialized phi edges, 3 stack frame, 2 return control, 1 direct control
target and 1 with no native semantics.
## A second semantic gate, and the first map of what breaks outside hash functions

The differential column was the project's strongest correctness evidence and it
covered nine hash functions of one shape, a loop over bytes accumulating an
integer. Three defects found by the external benchmark were invisible to it,
not because the gate was lenient but because none of them can occur in that
shape. A gate that cannot see a defect is the deeper problem, so there is now a
second corpus.

`tests/corpus/shapes.c` holds thirteen scored functions, each
`uint64_t shape_*(uint64_t, uint64_t)` so the harness hands it two integers and
compares one back. The shape under test lives in the body and in the noinline
helpers it calls, not in the interface, which is why the harness needs to know
nothing about structs or frames to score them: a variadic libc callee reached
with one, two, three and five variable arguments; a variadic callee of our own;
calls in sequence with address-taken locals read after each; a struct of four
field widths passed by pointer and by value; an array of structs indexed by a
loop counter; a stack buffer written and read back out of order; direct and
mutual recursion; signed division and remainder at two widths with negative
operands; a struct returned by value across two registers; a pointer to a
pointer; and a call through a function pointer held in a variable. Every result
is a pure function of the two arguments, so no address reaches the value
compared, and all six target configurations produce identical values.

`tests/corpus/shapes_oracle.c` includes `shapes.c` the way `oracle.c` includes
`hashes.c`: the expected value comes from the original source, built by the
same compiler for the same target. It is never adjusted to match a rendering.

### How the harness grew

`FunctionSpec` could describe one thing -- a byte buffer, a length, and
optionally a seed -- so nothing outside that shape was expressible. `ScalarSpec`
is the second description: N unsigned 64-bit arguments in, one unsigned integer
out, with the argument vectors named per spec so the division shape gets a
negative dividend and `INT64_MIN` over minus one. `cases_for`, `runner_source`
and `oracle_case` dispatch on which description a function has;
`verify_rendering.py --corpus shapes` selects the table, and the artifact
paths, baseline manifest and result files are namespaced so the two corpora
cannot overwrite each other's evidence.

Two things had to change for the shapes to be reachable at all.
`callee_definitions` now closes transitively over the definitions it pulls in
and excludes the scored function itself: a helper that calls a second helper
needs that one too, and mutual recursion needs both, so direct callees alone
left the translation unit short of a definition for reasons that had nothing to
do with the rendering. And the scored-function list now lives in one place --
`corpus_names.py` reads it out of `verify_rendering.py` for both the sweep and
the run script -- because three copies drift and the failure that produces is
misleading: a function added to the specs but not to the sweep measures as
`missing` for a reason that is not about the decompiler.

`tests/corpus/run_shapes.sh` is a separate gate with its own names, run through
`tests/corpus/locked_shapes.sh`. The 54 hash cells keep gating merges unchanged.
Its gates are `shapes-measurement` (every cell produced a record -- the one that
can be required today), `shapes-snapshot`, `shapes-raw` and
`shapes-differential`; a shape is promoted by adding it to
`REQUIRED_DIFFERENTIAL` once its six cells pass, and when all thirteen are
listed there the per-shape list goes and `shapes-differential` becomes the gate.
Snapshot is deliberately *not* implied by the correctness gates: sixty-four of
these cells are refusal comments today, and pinning their text as the expected
rendering would make every improvement read as a regression.

### The tally, measured under the install lock

Seventy-eight cells, thirteen shapes across the six configurations.

| column | result |
| --- | --- |
| generation | 14 present, 64 refused |
| raw | 6 pass, 5 compile failures, 3 signature mismatches, 64 blocked |
| differential | 8 pass, 1 failed, 2 blocked on compile, 3 blocked on signature, 64 blocked |

Six cells are green on every correctness column with `basis=raw`:
`shape_recurse_direct` at x64_O1, x64_O2, arm64_O1 and arm64_O2, and
`shape_struct_array` at x64_O2 and arm64_O2. Two more agree with the oracle only
on the diagnostic basis (`shape_struct_value` at arm64_O1 and arm64_O2), which
is not proof about emitted C. Direct recursion and an array of structs indexed
by a loop counter therefore both work at higher optimization levels, which is
more than the hash corpus could have told us.

### The named cause for every red cell

The decompiler almost always declines rather than answering wrongly, and it
names the rule that declined. That is the honest result and it is what makes
this list actionable.

**`shape_variadic` -- all six configurations, `declaration placement refused:
missing_definition`.** Four `snprintf` callsites with one, two, three and five
variadic arguments. This is the defect another agent owns: the variadic call.
Here it refuses at placement rather than dropping arguments, so the corpus sees
it as a refusal, not as a wrong answer.

**`shape_variadic_local` -- the one confidently wrong rendering in the set.** At
x64 O0/O1/O2 it refuses with `missing machine projection authorization:
OpLowering(calls.rs:144)`, which is the arm that refuses when two callsites of
one name need different declarations -- exactly what four `vfold` calls of
differing arity produce, and the right answer. At arm64_O1 and arm64_O2 it
refuses on effect obligations (2 refused). At **arm64_O0 it renders**, and the
rendering is wrong: every callsite becomes `sym__vfold((uint64_t)1)`,
`sym__vfold((uint64_t)2)`, `sym__vfold((uint64_t)3)`, `sym__vfold((uint64_t)5)`
-- the fixed argument only, with one, two, three and five variadic arguments
silently gone, the callee declared `uint64_t sym__vfold(uint64_t)` and not
marked variadic, under a proof line reading `0 refused`. On Darwin arm64 the
variadic arguments go on the stack, so the argument-area stores are not
recognised as arguments at all. All 16 differential cases fail. `raw` also fails
to compile, for a second reason worth its own line.

**`vfold`'s own rendering declares the stack pointer as an uninitialized
local.** `uint64_t SP_0; SP_0 = (uint64_t)SP_0 - (uint64_t)48;` and then
`(int64_t *)((uint64_t)SP_0 + 48)` for the `va_arg` area. `-Wuninitialized`
rejects it, and the diagnostic executable segfaults (exit -11) rather than
printing a wrong number. The same `SP_0` shape appears in
`arm64_O1/shape_struct_array`. This is adjacent to the stack-pointer defect
another agent owns -- `call` lowering never returning the eight bytes -- but it
is a distinct failure: SP has no definition at all here, so it becomes a local
with no initializer rather than a frame base off by eight.

**`shape_call_chain` -- calls in sequence with locals read after each.**
`unobserved_binding_write` at x64_O0 and arm64_O0, `missing_definition` at
x64_O1, x64_O2 and arm64_O2. At **arm64_O1 it renders
`uint64_t sym__shape_call_chain(void)`** -- arity 0 for a function of two
arguments, which the harness reports as `signature_mismatch`. That is the third
benchmark defect's shape: a call boundary the decompiler could not establish
producing an argument-free signature, here caught because the corpus knows the
function takes two arguments and has values to pass.

**`shape_recurse_mutual`** refuses at placement on four configurations
(`unobserved_binding_write` at O0, `missing_definition` at x64_O1/O2) and at
arm64_O1 and arm64_O2 renders arity 1 for a function of two -- the same
argument-recovery gap as `shape_call_chain`.

**`shape_struct_pointer` -- a struct read and written through a pointer.**
`missing program-variable authorization` at both O0 levels;
`missing machine projection authorization: OpLowering(memory_renderer.rs:81)` at
the four higher levels. That site is the certified-memory-fact lookup: no fact
matches the block, op, space, address, value, direction and width of the access,
so the field access has no projection. Field accesses of four different widths
off one base are the shape it cannot certify.

**`shape_struct_value` -- a 16-byte struct passed in two registers.**
`unobserved_binding_write` at O0, `missing_definition` at x64_O1/O2. At arm64_O1
and arm64_O2 it renders and *agrees with the oracle*, but `raw` fails to compile
on `stack_m48` and `stack_m40` set but never used and `X22_0` uninitialized, so
the agreement rests on the diagnostic build and is not evidence about emitted C.

**`shape_struct_array` -- the best-behaved aggregate shape.** Green at x64_O2
and arm64_O2. `RenderedValueRequired` at x64_O0, `missing_definition` at x64_O1,
effect obligations (2 refused) at arm64_O0, and at arm64_O1 a raw compile
failure with three distinct causes: a `uint32_t` to `int32_t` implicit signedness
change, a non-void path with no return, and `SP_0` uninitialized again.

**`shape_stack_buffer` -- a 64-byte frame array written and read back.** Effect
obligations refused everywhere on arm64 (5, 5 and 3 refused at O0/O1/O2) and at
x64_O0 (1 refused); `RenderedValueRequired` at x64_O2. At x64_O1 it renders but
`raw` will not compile: a non-void function with a path that returns nothing.
This is the frame-object array recovery that was already recorded as producing
nothing; the gate now measures it.

**`shape_recurse_direct`** is green at the four higher levels and refuses at O0
only: `read_before_assignment` at x64_O0, `missing_definition` at arm64_O0.

**`shape_signed_divmod` -- refuses on all six.** `observation journal:
ConflictingUse` on every x64 level, and `missing machine projection
authorization: OpLowering(lowering.rs:30)` on every arm64 level, which is the
catch-all arm that turns any other journal error into a projection refusal. A
value used as both a signed dividend at 64 bits and at 32 bits is a conflicting
use, and the per-value refusal rule then declines the whole function rather than
that value. Nothing here is a wrong answer, which is the important part: signed
division was the shape where a wrong answer would have been silent.

**`shape_multiword_return` -- refuses on all six.**
`unobserved_binding_write` at both O0 levels, and
`OpLowering(calls.rs:308)` at the other four -- the argument-projection
collector, which refuses when any one argument of a certified call has no
expression the plan can spell.

**`shape_pointer_to_pointer` -- refuses on all six.**
`unobserved_binding_write` at three levels, `calls.rs:308` at x64_O2 and
arm64_O2, effect obligations (6 refused) at arm64_O1.

**`shape_function_pointer` -- refuses on all six.** `missing_definition` on
every x64 level; on arm64, `memory_renderer.rs:81` at O0 and
`RenderedValueRequired` at O1 and O2. An indirect call through a table entry is
the one shape here whose callees are not declared, so even a rendering would
have had no definitions to link against.

### What the map says, taken together

Five causes account for sixty-four of the seventy-eight cells:
`declaration placement refused: unobserved_binding_write` and
`missing_definition` (30 cells between them),
`missing machine projection authorization` at three sites --
`calls.rs:308`, `memory_renderer.rs:81`, `calls.rs:144` (16),
`effect obligations refused` (7), and the observation journal's
`ConflictingUse` and `RenderedValueRequired` (8). Placement is the largest
single blocker outside hash functions, and it is not shape-specific: it refuses
on the call chain, on mutual recursion, on both struct shapes and on the
function-pointer table alike.

Only one cell in seventy-eight produced a confidently wrong rendering, and it is
the variadic one. That is the decompiler behaving as designed, and it is also
why the hash corpus could pass 54 of 54 while the benchmark found three wrong
answers: the shapes that break here mostly refuse, and a refusal is invisible to
a corpus that never asks the question.

### What was verified alongside it

`cargo test --workspace` is green: 2198 tests, no failures.

`tests/corpus/locked_matrix.sh --gate differential` still measures the 54 hash
cells at `generation: 54 present`, `raw: 54 pass`, `differential: 54 pass` with
`basis=raw` in every cell. Nothing in this work touches Rust; the diff from the
branch point is `tests/corpus/` and this document only.

Two things in that run are worth writing down so the next reader does not chase
them:

- The gate exits non-zero on `snapshot: 37 match, 17 mismatch`. Those seventeen
  section hashes are byte-for-byte the ones `arch/expression-engine` has since
  re-accepted into `raw-baseline-sha256.json`; the branch point this work was
  cut from carries the older manifest. Checked key by key: the mismatch set and
  the re-accepted set are the same seventeen, and this run's hashes equal the
  newer manifest's. It is base drift, not a rendering change.
- One cell reports `diagnostic: infrastructure_error` -- `x64_O2/fnv1a32`. The
  *oracle* timed out at three seconds under six agents building at once. Its
  differential passed, because the differential re-runs the oracle per case. A
  measurement taken on a loaded machine can produce this on any cell.

The shape run was executed twice under the lock and produced identical column
totals both times, so the fourteen renderings and the eight differential passes
are reproducible rather than a scheduling artifact.

## Array indexing: the cell becomes a term, and what that measured

Array indexing appeared in zero per cent of rendered functions, and the cause
was not the renderer being timid. Nothing on the certified path could *say*
"this cell is an element". The two pieces that came closest --
`typed_subscript_access`, which divided a rendered index by the pointee width,
and `certified_pointer_base_expr`, which decided which operand of a C address
expression was the base -- worked on emitted text with no proof behind either
decision, which is the second rewriting layer this branch exists to remove.

The decision now lives in `r2rewrite`. Three term kinds carry it: `Load`, which
is also the cell a store writes, because the cell a store writes is the one a
load at that address would read; `Subscript`, the read at
`base + index * (width / 8)`; and `ObjectAddress`, what a placed object's name
decays to. Three rules turn the first into the second, each proven at 8, 16, 32
and 64 bits like every other rule in the table. `constant_stride` needs no
certificate for its *equivalence* -- `Mem[p + i*k]` is that cell whichever
operand is called the base -- so the certificate only chooses the spelling.
`stack_element[stack_slot]` and `pointer_walk[induction]` do rest on
certificates and say so in their ids.

**A pointer is proven by a dereference, not by being a parameter.** The first
version asked whether a value had parameter address provenance, and every
parameter has it: `arr_sum(const uint32_t *a, size_t n)` gives `n` a parameter
expression exactly as it gives one to `a`. With both called pointers a sum has
two candidate bases at unit coefficients and the rule refuses. Object existence
is no better -- an object is made for every parameter appearing in any address
expression, `n` included. What is evidence is a certified access whose address
carries that parameter's provenance: memory was read or written through it. A
value is a base when its provenance is that parameter with *no terms added*;
with terms it is the whole address, and an address that is its own base leaves
no index behind.

**The shape that makes this work is the `-O0` parameter home.** A parameter is
stored to the stack, reloaded, and the reload is indexed. The reload is a
legitimate base only because the address provenance pass carries the parameter
base through the spill -- a fact a reader of the emitted C cannot recover,
which is why the earlier renderer-side attempts could not see it and were
correctly recorded here as inert.

**One case refuses and is worth naming.** Where both operands of an address sum
are parameters -- `s[i]` with `i` itself a parameter -- the provenance pass
gives the sum no expression at all, because two parameter bases combined have
no single base. The access then has no proven pointer and the rule declines
rather than picking an operand. The corpus's own shape indexes by a local
initialised to a constant, which the pass does resolve, so this is a real
limitation with no corpus cost yet measured.

### Measured: zero subscripts to twenty-one, and two accounting defects

On the fifty-four hash cells, counted exactly before and after:

    subscript expressions        0 -> 21   (in 11 of 54 cells)
    array declarations           0 ->  0
    for loops                    0 ->  0
    while headers               17 -> 17
    do-while                    43 -> 43

All fifty-four cells pass generation, raw, diagnostic, differential, binding
audit, effect obligations, placement audit and render refusal. The snapshot
column reports exactly eleven mismatches, and they are the same eleven cells
that gained a subscript, which is the corroboration worth having: the output
that changed is precisely the output that was meant to.

What it looks like. `xxhash32` reads its lanes as
`((uint32_t *)RDI_0)[1]` where it used to spell `*(uint32_t *)(p + 4)`, and
`pearson` indexes its table as `((uint8_t *)RCX_2)[RDX_2]` with a variable
index. Both are `constant_stride`; the `-O2` cells index because the compiler
unrolled the byte loop into `p + i + k` forms, which is the shape the rule was
written for.

Array declarations and `for` loops are still zero. Stack buffers and
region-level `for` construction were not reached, and nothing here should be
read as evidence about either.

**Two accounting defects, both found by the gates and neither by reading.**
They are worth keeping because both are the same mistake in different clothes:
the subscript path does not go through the code that used to answer for a
cell, so it has to answer for that cell itself, and twice it did not.

The first refused six `x64_O2` cells with `RenderedValueRequired`. The
dereference path marks the address value inside
`certified_memory_address_expr`; the subscript path bypasses that function, and
marked the address only when the canonical term had absorbed a producer. That
made the accounting depend on which rule fired rather than on what was
rendered -- `constant_stride` absorbs the add and the multiply so the cell was
filled by luck, `pointer_walk` absorbs nothing so it was not filled at all.

Marking the address unconditionally did *not* clear those six cells, and the
failure to clear was the useful part: it proved the address was never the
missing thing. `R2DEC_TRACE_REFUSAL` then named the value outright --
`ValueId(378)`, `Inline`, one use, **no defining instruction**, constant
storage, read by the `IntAdd` that formed the address.
`observe_discharged_expr` marks each consumed instruction's write, its output
value and its operands' *uses*; a constant is nobody's output, so it never
appears in a discharged set, and its only occurrence was inside the expression
the subscript replaced.

An earlier attempt at that same cell searched the term's leaves and found
nothing, because import turns a constant into `TermKind::Literal` and `leaves`
collects only `Leaf` and `Opaque`. Asking the graph for each consumed
instruction's operands does not depend on how a constant happens to be
represented in a term, which was the right question from the start. The marks
are deduplicated: one literal can be an operand of two consumed instructions,
and two marks would count one execution twice.

The second defect refused every store to a proven element.
`expr_is_store_target_candidate` saw through `Paren` but not `Observed`, and
had never needed to, because the dereference path hands it an unmarked
`CExpr::Deref` while the subscript path marks the address it renders. It now
asks `unobserved()`, the idiom the rest of the tree already uses.

The lesson for whoever adds the next rendering path: the cells a path must
fill are not the cells its author thinks about, they are the cells the path it
replaced used to fill. Diff the two.

### Declared member and proven stride are one owner, not a ranking

These look like two authorities over one access and cannot both answer.
`certified_member_fact_for_memory` returns a fact only when it matches the
access's object, access id *and* width, and only when exactly one such fact
exists. So either it describes this very access or it is absent, and the states
are disjoint: a matching member owns the access and the subscript declines; a
width disagreement or a duplicate means no member fact is returned and the
proven stride answers; neither present means the rewriter answers if it proved
anything. There is deliberately no tie-break code, because a tie cannot occur,
and a resolver for an impossible tie would be a second answerer for a settled
question. This is stated again in the module documentation so nobody adds one.

The one decided rather than derived case: a member fact matches but the member
renderer cannot build an expression, because the C address carries no base
identity to split around. That access renders as a dereference, not a
subscript. Asserting an array shape a declared type contradicts is worse than
declining to name the shape, which is the same rule under which a conflicting
type refuses per value instead of guessing. **Revisit it only on a measurement
showing those accesses are common enough to cost `type_match`.**

### The benchmark witness never reached the binary, and the guard always fired

`tests/decbench/run_decbench.sh` exists so that a `make install` aborting on
stale objects cannot be mistaken for a change with no effect. As written it
appended `pub const DECBENCH_WITNESS: &str = "..."` to `r2engine` and searched
the installed library for the string. A `const` is inlined at its use sites and
this one has none, so no storage is emitted and nothing reaches the binary: the
check failed on every tree it was ever pointed at. The install had succeeded --
a fresh 22MB library, minutes old -- and the run aborted claiming the library
was stale. Two of the integration branch's own runs were read as hangs because
of it.

A guard that always fires is exactly as useless as one that never does, and
worse than either, because it sends a reader hunting a build problem that does
not exist and invites the next reader to disable it. `#[used]` with an exported
symbol is emitted whether or not anything reads it, which is the property
wanted, and it was verified against a real built `cdylib` -- symbol exported,
string in the image -- rather than reasoned about. The search is `grep -a` now
too, since BSD grep reports no match on a binary whose bytes do match, which
would have made the check wrong again the first time anyone ran it against a
locally built library instead of over ssh.

### Two operational hazards this stretch hit

A corpus run started while the tree is being edited measures neither the commit
before nor the commit after. `locked_matrix.sh` builds, then queues for the
shared install lock, and `run_matrix.sh` rebuilds once it has it -- so an edit
made during the queue wait silently reaches the captured plugin. With four
worktrees queued the wait is long enough that this is easy to do by accident.
Cancel and re-run rather than editing through a queued measurement.

The benchmark host is shared, and a run's remote directory can be removed by
another agent's cleanup while it is still building. One run here died that way
with its own install log already deleted underneath it. A run that vanishes
mid-build is not a build failure and should not be read as one.
## The `aa` path measured directly, and the figure it replaces

The last section named the `aa` path as the dominant remaining cost, at about
55 milliseconds per function across `sleigh_analyze_fcn`, `sleigh_get_data_refs`
and `sleigh_op`. **That figure was wrong and the method that produced it was
wrong.** It came from `(aaa - aa)` differencing, on the assumption that the
proof sweep is what `aaa` adds to `aa`. radare2 runs the plugin's
`post_analysis` hook during `aa` as well, so the subtraction cancelled most of
the sweep instead of isolating it, and what was left over got attributed to
callbacks that turn out to cost almost nothing.

Each callback now counts and times itself, printed under `R2SLEIGH_TIMING`.
bzip2recover, `aaa`, on a quiet VM:

    site                calls    total      mean
    analyze_fcn            32     2.6ms    81us
    get_data_refs          38    14.9ms   392us
    op                      0        --      --
    eligible               72     320ms   4.4ms
      context.create        1     302ms   302ms
      context.regprofile   73     0.5ms   6.5us
    post_analysis           1    1494ms
      snapshot.walk        39     448ms  11.5ms
      snapshot.reuse       43       9us   209ns
      proof.engine         22     387ms  17.6ms

Three things fall out that no amount of differencing would have given.

**The three callbacks named in the brief cost 17.5 milliseconds between them,
and `sleigh_op` is never called at all.** radare2 decodes this binary through
another arch plugin, so the per-instruction path that looked like the obvious
suspect does not run. Every per-instruction worry about `get_context` --
the multi-kilobyte register-profile `strcmp`, the two FFI calls per instruction
-- was about a function that is not on the path. `context.regprofile` is 73
calls and half a millisecond in total.

**What `eligible` costs is one Sleigh context creation.** radare2 asks the
plugin's `eligible` hook per function, 72 times here, and 302 of the 320
milliseconds is a single `sleigh_v2_context_create` -- the same compiled `.sla`
parse the previous section moved off the lift path, on the other of the two
paths that load one. The Rust side now shares a loaded profile through
`shared_trusted_profile`; the C `R2ILContext` does not share with it, so a
session that both analyses and decompiles parses the specification twice. That
is one call and 0.3 seconds, and it is the cheapest item left.

**Everything else is the sweep**, at 1.49 seconds, and the largest thing in it
was the same function's snapshot being collected three times.

### One walk per function instead of three

`r_core_function_snapshot_at` collects the function, its blocks, its bytes, its
type graph and the bodies of everything it calls. Three places asked for one
per function and each kept a different part: `sleigh_artifact_plan_init` walked
it all to read a single 64-bit revision, once for the proof plan and again for
the taint plan, and `sleigh_proven_facts_json` walked it a third time for the
wire buffer. 82 walks per `aaa` on a 38-function binary.

One held capture keyed by the address and both dirty epochs brings that to 39
walks and 43 reuses at 209 nanoseconds. One entry rather than a per-program
cache, because the three readers are consecutive for one function, so a second
entry buys no hit while holding whole snapshots for a program would hold the
program twice over. The wire buffer is always built, because the walk is the
cost -- 44.5ms with the buffer against 50.6ms without is the same number twice
-- so making it conditional would only add a way for the entry to miss.

**What that is worth, and a measurement that had to be thrown away.** Run as
two blocks, before then after, the same two builds read 13.20s against 3.12s
for `aaa` and 8.67s against 1.49s for post-analysis: a four- to sixfold win.
It is not real. The before block ran while the machine was busy and the after
block did not. Interleaved, three rounds, alternating:

    round   before aaa   after aaa   before post   after post
      1        2.79s       2.92s        1518ms       1249ms
      2        2.87s       3.11s        1596ms       1245ms
      3        3.26s       2.44s        1545ms       1378ms
    bzip2     22.51s      21.30s

So `aaa` is unchanged within noise and post-analysis falls about nineteen per
cent, from 1.55s to 1.25s. That is 43 walks removed at the 11.5ms they actually
cost on a quiet machine, not the 34 to 50ms the loaded runs reported. The
proofs are identical either way: 22 functions, 16 skipped, the same two
unreachable blocks.

This is the seventh measurement this project has had to correct for measuring
the wrong thing, and the second in two days. The rule that keeps working is to
interleave the columns rather than run them in blocks, because a machine's load
drifts over minutes and a block is minutes long. Private `HOME` per column
stops another agent overwriting the plugin; interleaving stops the machine
overwriting the answer.

### The budget is now the program's size, not a number

The sweep was governed by three whole-program constants -- two, ten and thirty
seconds by analysis mode -- derived from nothing. Ten seconds is not a fact
about a program. bzip2recover, 38 functions, finishes in 1.5 seconds and never
touches it; bzip2, 154 functions, was stopped by it after a third of the
program on every run. One number cannot be right for both, because the work
scales with the function count and the number did not.

The budget is now the function count times the project's own per-function
performance bar, the one already agreed: under 100 milliseconds net per
function. That is not a fresh judgement about how long is too long, it is the
bar the sweep is already held to multiplied by the work in front of it. A
function that exceeds it is a defect to fix rather than a budget to widen. The
analysis mode is deliberately no longer a factor: a mode decides how much work
each function gets, not how long a wall clock may run, and stating the same
policy in two places is what let the two disagree.

    bzip2               before              after
      budget            10.0s               15.4s (154 x 100ms)
      exhausted         yes, every run      no
      functions reached 35 to 42 of 154     all 154
      proved            35 to 42            46
      skipped           0                   104
      unreachable found 0                   2
      aaa               21.3s               25.4s

Finishing the program costs about four seconds more than being cut off two
thirds of the way through, and buys 46 proved functions instead of 42 plus two
unreachable blocks the sweep had never reached. bzip2recover is unchanged at
2.88 seconds with the budget never binding.

### What is left, in the order the measurement puts it

**About 0.66 seconds of bzip2recover's 1.49-second sweep is still
unattributed** -- post-analysis minus the snapshot walks and the proof engine.
That is artifact submission, the taint plan path, and the budget checks, none
of which is separated yet. It is now the largest unmeasured thing the plugin
does and the next site to split.

**The proof engine is 17.6 milliseconds per function** across 22 functions.
That is the engine doing real work on a real snapshot and it is within the
project's bar, so it is a target only after the unattributed remainder.

**The C `R2ILContext` and the Rust trusted profile load the same specification
separately**, 0.3 seconds once per session. Sharing one loaded Sleigh between
`r2il_arch_init` and `shared_trusted_profile` removes it. Small, contained, and
the last of the three places this project has found the same parse.

**The structurer was not reached.** `main` in bzip2recover spends 2.27 seconds
there and then refuses, against 2.77 for every other r2dec stage combined. The
suspected cause is unchanged: the BDD safety budget at blocks times 128,
consumed in whatever order the proofs run, so a late block gets what earlier
ones left; `varying_predicates` in `structure.rs` already narrows the set the
bound should come from, and the refusal at `consume_safety_budget` compares a
counter against a limit fixed at construction to that same counter, so it can
never fire.

## Two performance figures in this document were wrong, and the method was worse

**The attribution was wrong.** This document said roughly 55 milliseconds per
function went into `sleigh_analyze_fcn`, `sleigh_get_data_refs` and
`sleigh_op`. That number came from subtracting an `aa` timing from an `aaa`
timing, which does not isolate what it appears to: radare2 runs the plugin's
post-analysis during `aa` as well, so the subtraction cancelled the sweep rather
than removing it. Measured directly with per-site counters on a quiet host, the
three callbacks cost **17.5 milliseconds between them across a whole binary**,
and `sleigh_op` is **never called at all**, because radare2 decodes this binary
through a different architecture plugin. Every suspicion recorded here about
per-instruction cost in `get_context` was about a function that is not on the
path.

**The speedups were inflated by measurement order.** Sequential before-and-after
runs on the shared Linux host read 13.20 seconds against 3.12 for one change.
Interleaved A/B over three alternating rounds put the same change at about
**19 per cent**. The before block had simply run while the machine was busy with
other agents. That makes seven measurements this project has had to correct, and
it generalises: a private `HOME` stops another agent overwriting the plugin, and
only interleaving stops the *machine* overwriting the answer. **Treat any
before-and-after on that host that was not interleaved as unproven**, including
the earlier figures in this document for the Sleigh profile load, which were
taken the same way.

What is solid, because it was measured directly rather than by subtraction:

| site | calls | total | mean |
| --- | --- | --- | --- |
| post_analysis | 1 | 1494 ms | |
| snapshot walk | 39 | 448 ms | 11.5 ms |
| snapshot reuse | 43 | 9 µs | 209 ns |
| proof engine | 22 | 387 ms | 17.6 ms |
| context create, one `.sla` parse | 1 | 302 ms | 302 ms |
| get_data_refs | 38 | 14.9 ms | 392 µs |
| analyze_fcn | 32 | 2.6 ms | 81 µs |
| sleigh_op | 0 | never called | |

Two things follow that are worth more than another round of tuning. About 0.66
of the sweep's 1.49 seconds is still unattributed, which makes it the largest
unmeasured thing the plugin does. And the C context and the Rust trusted profile
parse the same `.sla` file separately, at 302 milliseconds, which is the **third**
place this project has found the same parse happening twice.

## Working rules for parallel worktrees, learned the expensive way

Several worktrees building and measuring at once produced four distinct
failures in one session, three of them destructive, and none of them visible in
the output of the thing that failed. They are recorded here because each one
looked like a defect in the work rather than in the surroundings.

**Reclaim a build directory, never a worktree.** A `target/` costs a rebuild to
delete. A worktree can hold uncommitted work and can still be the workspace of
an agent that is between steps, so removing one because its branch merged
destroys work and orphans whoever was using it. That happened here, and only a
commit-early habit saved the contents.

**Never delete by glob on a shared host.** A sweep of stale directories matched
a live run's source tree and deleted it underneath the compiler, twice, which
reads as a build that failed before writing its log. The fix that holds is
structural rather than careful: runs live under their own root that a sweep of
the old namespace cannot match, they write a marker while live, and the
collector spares anything marked, anything younger than a day whose state is
unknown, and reports rather than removes unless forced.

**Interleave every before-and-after.** Sequential blocks on a shared host
measured the machine's load, not the change: one change read as four-fold
sequentially and about nineteen per cent interleaved. A private plugin
directory stops another worktree overwriting the binary; only interleaving
stops the machine overwriting the answer.

**A build outside a lock is a different tree from the one measured inside it.**
The lock wrapper builds before it queues so a cold build does not block others,
and the command it runs builds again once it holds the lock. Anything edited
during the wait is what gets measured, silently. It now fingerprints the tree on
both sides and refuses rather than report one tree's numbers under another
tree's name.

**Put a build setting in the manifest, not in the instructions.** Every worktree
was told to build with line tables rather than full debug info. One did not, and
grew a twelve gigabyte debug directory against three or four for the others.
The setting is now in `Cargo.toml`.

## The first integration measurement, and what it caught

The benchmark harness ran end to end for the first time against the merged
tree, with the witness present in the installed library and the run compared
per function against the record. It found five gains, one function lost, and a
score below what one of the merged branches had measured on its own.

| function | recorded | merged tree |
| --- | --- | --- |
| readError | 0.214 | 0.255 |
| writeError | 0.214 | 0.255 |
| mallocFail | 0.161 | 0.182 |
| endsInBz2 | 0.088 | 0.089 |
| tooManyBlocks | 0.156 | **0.148** |
| bsClose | 0.000 | **refuses** |

`byte_match` 0.140 over 7 functions against a recorded 0.111 over 8, and
`type_match` 0.125 over 4 against 0.100 over 5. Both means rose partly because
the function that stopped rendering had scored zero, which is exactly why the
record is per function and carries `decompiled` beside each score: a mean that
improves because a bad case disappeared is not an improvement.

**The merged tree scored below one of its own branches, and the cause was not
the merge.** Measured alone, the inlining branch put `readError` at 0.400 and
`tooManyBlocks` at 0.316; through the integration harness they are 0.255 and
0.148. Two trees, one before and one after the performance merge, were measured
and render byte-identically, and the branch's own files are unchanged by the
merge. The variable is the radare2 fork. The integration harness syncs it, so
those runs carry the ellipsis predicate fix and the branch measurements did not.

The fix is doing exactly what it should and the result is still worse, which is
worth seeing rendered:

```c
uint64_t sym_imp_fprintf(uint64_t, uint64_t, ...);
RAX_3 = sym_imp_fprintf(RDI_1, "%s: I/O error reading `%s'...\n", &progName, RCX_1);
RAX_8 = sym_imp_fprintf(RDI_5, (char*)RCX_4, &progName, RCX_4);
```

The declaration is correctly variadic and the first call is right for the first
time: four arguments, matching the source. The second call, whose source passes
three, has a spurious fourth from gcc's use of `rcx` as scratch at `-O0`, and its
format argument is a register rather than the literal, with that same register
also handed over as the fourth argument. Correct on one call, worse on the
other, worse in total.

The discriminator for this was reported as not existing, on the grounds that
counting format conversions would be a name test. It is not. Keying on a callee
being *called* `printf` is forbidden because identity here is structural, but
reading the bytes of a literal argument the program carries is data, in the same
category as the string literals already recovered and rendered. Which parameter
holds the format comes from radare2's prototype, which is load-bearing when
marked. So: a variadic callee whose format argument resolves to a literal takes
its count from that literal's conversion specifiers, and one whose format does
not resolve refuses, which is what the second call above should be doing today
instead of inventing a fourth argument.

Both deltas in that run are now accounted for, and the record has been re-taken
against the merged tree so the next change is measured against reality rather
than against a state nobody will return to.

`tooManyBlocks` falling from 0.156 to 0.148 is the second `fprintf` above,
gaining an argument it should refuse over.

`bsClose` going from rendered to refusing is **not a loss**, and it is worth
being exact about why, because the count of decompiled functions fell from eight
to seven and that reads badly. It refuses with `unrepresentable operation`, from
the linearizer, which is the guard this branch added for a transfer that leaves
the function. Before the guard it rendered a `goto` to a label the function
never defines, which does not compile, and it scored 0.000. It scores nothing
now. No information was lost: a wrong answer was replaced by an honest refusal,
and the guard already carries a comment naming the commit that must delete it,
which is the one that gives such a transfer a callsite and renders it as a
terminal call. When that lands, `bsClose` should return, and this time with a
score.

This is the case the per-function record was built for, and it is worth saying
what would have happened without it. The aggregate went up. A run that reported
only `byte_match 0.111 → 0.140` would have read as progress, and both the lost
function and the halved gain would have travelled forward invisibly.

Note also that `byte_match` and `type_match` are deterministic, unlike the
timing figures corrected earlier in this document, so a single run of each tree
settles a comparison between them. Only the timings need interleaving.

## An unowned refusal that hides which argument failed

`missing machine projection authorization` accounts for six of the seventy-two
real-function refusals in the coverage baseline and sixteen of the seventy-eight
shape cells. Three sites raise it, and they are not one problem.

`memory_renderer.rs:81` was a store to a proven array element being rejected
because the store-target predicate looked through `Paren` but not through an
observation marker; that is fixed on the array branch.

`calls.rs:144` is two callsites of one callee that would need different
declarations, which refuses correctly and is the right answer.

`calls.rs:308` is the one worth taking, and its defect is as much about
diagnosis as about rendering. The site collects every call argument through
`collect::<Option<Vec<_>>>()`, so a single argument that cannot be spelled
becomes a refusal of the whole function, and the refusal says only that a
projection authorization was missing. Which argument, and why, is discarded at
exactly the point where it is known. Every other refusal on this branch has been
made to name its subject -- placement now names the binding and its occurrences,
the ledger names the layer and the obligation ids -- and this one has not, which
is why it has stayed unowned while smaller causes were traced. Name the argument
index and the value first, then the cause will be a short read rather than a
hunt.

### The argument was already known, and the missing projection was not the cause

The collector is a loop now. On its first `None` it writes one line on the
existing refusal-evidence channel before constructing the same typed refusal:

    refusal evidence call-argument-spelling ...:
      callsite=(0x10000173c, 3) argument_index=1 value=ValueId(185)

The callsite, index and `ValueId` are structural. No spelling or symbol name is
used as identity. With tracing off the line is not evaluated; with it on the
reader gets the operands at the predicate that discarded them. The traversal is
still one bounded pass over the certified argument list and still stops at the
first failure.

The locked whole-binary trace has ten `calls.rs` projection refusals. Nine are
the argument collector and one is the declaration-conflict site. The nine
arguments split into two causes:

| functions | first predicate that fails | what the other owners say |
| --- | --- | --- |
| 8 | `CertifiedRenderPlan::call_arg_admission` sees the argument's `ExpressionRenderFact` as `renderable: false` | all eight have an exact binding-plan disposition: seven `Bound`, one `Inline`; all eight prepared call views and `CallsiteRenderFact.proof_values` agree on the indexed `ValueId` |
| 1 | the expression fact is renderable, but the prepared call view has only the one-argument prefix `[ValueId(571)]` while the render fact proves `[ValueId(571), ValueId(580)]` | argument 1, `ValueId(580)`, has an exact binding-plan `Inline` disposition |

The first row is `branchy` `main` at all three x64 levels, `hashes` `main` at
all three x64 levels, pinned GCC `combined`, and
`/bin/ls` `fcn_1000016d4`. The second is `hashes` `main` at arm64 O0. Six of
the first row's values are zero-extended return-register values, the `ls` value
is a copied return-register value, and the pinned value is a copied saved
argument. That variety is useful: this is not a register-name rule and must not
be fixed as one.

So none of the nine traces establishes a genuinely unspellable argument. Eight
are stopped by a general expression-renderability gate before the binding plan
is asked for its exact answer. The ninth is stopped by
`PreparedSemanticView`'s separate call-argument expression reconstruction even
though the later binding plan has the answer. `CallsiteRenderFact` owns which
structural values the call passes and the binding plan owns how those values are
spelled; the two earlier gates are parallel answers that can drift from them.

This change does **not** fix those nine refusals and does not reduce the refusal
count. It fixes the diagnostic defect that erased their subjects. Fixing the
underlying refusals reaches a design fork:

1. Make the binding plan the sole spelling authority. Keep the callsite and
   render facts as the ordered value proof, remove expression renderability and
   the prepared view's reconstructed argument prefix from call-argument
   admission, and let `planned_value_expr` either spell or refuse each value.
2. Strengthen an upstream typed call-argument renderability contract, including
   return-derived values and a complete ordered argument projection, then make
   both the prepared view and binding plan consume that one answer instead of
   reconstructing it independently.

The first is the smaller and cleaner owner shape, but no behavior change was
made here: each option needs a pipeline test that proves all nine exact values
render and that the observation/effect ledgers still close. Guessing a missing
argument, or dropping it, is not an option.

Refusing the whole function remains right when an argument is *actually*
unspellable. A call with one positional argument omitted is executable C with
different behavior, not a partial answer, and emitting it would turn absence of
evidence into a confident wrong result. The current native route has no
executable-C spelling for an unresolved call effect that would preserve the
rest of the function honestly, so the function must refuse until such a
contract exists.

The two contextual sites were measured too. `/bin/ls` `fcn_100003698` is the
one `calls.rs:144` refusal: two callsites need incompatible declarations for one
callee identity, so it correctly remains refused. `memory_renderer.rs:81`
contributes zero in the current trace. Its store-target predicate still calls
`unobserved()` and therefore sees through the observation marker; the four
memory-renderer entries in the older baseline have moved to their next causes.
There is also one `lowering.rs` projection refusal in the coverage report; it is
outside these three sites and was not changed.

## Candidate: the install lock is held about four times longer than it needs to be

`locked_run.sh` wraps a whole command, so `run_matrix.sh` holds the lock across
install, six sweeps, six compiles, six oracle builds and six verifications.
Only the install and the six sweeps touch the installed plugin.

The verification half was checked rather than assumed. `verify_rendering.py`
invokes radare2 three times, for `iSj`, `iSSj` and `p8j`: a section list, a
section-header list and raw bytes. None disassembles, none decompiles, and none
depends on which plugin is installed. The compiles and the oracle runs touch
nothing of ours at all.

So the held window could shrink to install plus sweeps, which at six agents and
a queue five deep is the difference between a wait measured in hours and one
measured in minutes.

It is not a small edit. The lock is owned by the wrapper, and moving it to the
script that installs changes the contract of five callers -- the matrix, probe,
coverage, shapes and values wrappers -- every one of which is being executed by
a running agent. Bash reads a script by byte offset as it runs, so an in-place
edit of a file mid-execution corrupts the instance reading it; an atomic replace
avoids that, since the running shell keeps its descriptor on the old inode.

Do it when the queue drains, not before, and use atomic replacement for every
script edit from then on. Note also that whoever does it should keep the one-
owner property that made the wrapper worth building: the lock belongs with the
thing that needs exclusivity, so the honest end state is the installing script
taking it directly rather than a wrapper guessing when to let go.
## Two subsystems deleted, and the register tables collapsed onto geometry

Three things landed on `arch/expr-accounting`, and one design fork is left
open at the end because it is a decision rather than a bug.

**The symbolic query island: nine modules, 17,446 lines.** The brief named
`kernel.rs`, `telemetry.rs`, `r2api.rs`, the native worker's libc table and
the `EngineSession` entry points. Checking each first, as the brief required,
moved the boundary twice. `telemetry.rs` was already gone. The "libc table" is
`function_semantic_summary_seed_for_name`, which returns `None`
unconditionally and is *pinned* there by a dylint forbidding name-derived
seeds -- it is a refusal the lint depends on, not a table, and deleting it
would remove an assertion rather than dead code. And the island is larger than
five names: `query`, `verification`, `symbol`, `spec`, `tactics`,
`constraints`, `kernel`, `replay` and `r2api` reach each other and nothing
else.

What decides it is a single seam. Every export of those nine enters the rest
of the tree only through `EngineSession::{symbolic_summary, symbolic_paths,
symbolic_target_explore, symbolic_target_solve}` and their
`_with_execution_control` variants, and those have no caller outside
r2engine's own tests. Checked against radare2 rather than only against Rust,
because that is how this survey has been wrong before: the C plugin sends
three request kinds, seventeen analysis kinds, four query kinds and three
planner kinds through `r2sleigh_api_v2`, and not one reaches a symbolic entry
point. `r2api.rs` sits behind an `r2` cargo feature nothing enables.

Four facts were asserted only inside the island and were kept. Three moved to
`path.rs`, where `explore` runs the same worklist the deleted
`summarize_function` wrapped, and they ask `ExploreStats` directly instead of
through a `QueryCompletion` that was only the wrapper's spelling: a
pre-cancelled exploration is a cooperative stop and not budget exhaustion, an
expired deadline is not an exploration timeout, and the `max_states` budget
stays distinct from execution control. The fourth stayed in `backward.rs`
under a truer name -- it was checking that a load through a parameter pointer
survives as a symbolic memory term, which belongs to the reverse-path compiler
and not to the paired-branch entry it happened to call.

Two traps in that deletion, both real. `replay.rs` cannot go without
`compiled_semantic_info_with_replay_seed`, and with it go the `seed_mode` and
`replay_seed_fingerprint` fields nothing else could populate. And
`FactPrecision` is the one `kernel.rs` export with a user outside its module,
`verification.rs`, which was going too -- so it escapes to nothing.

**The register tables were producing wrong answers, and that turned out to
matter more than the deletions.** Three tables in `r2types` answered
register-identity questions by matching spellings. `register_family_matches`
mapped `rdx` and `dh` to the same key "dx" and said they were the same
parameter, so an externally supplied type assumption for `dh` was applied to
the `rdx` parameter, counted toward the applied-parameter slots that grant
signature-certificate authority, and named a stack slot after a parameter it
does not carry.

`dh` really is a byte of `rdx`, which is what makes the wrong answer tempting.
The distinction a name cannot make is *where a register starts*: a parameter
in `rdx` is read back as `rdx`, `edx`, `dx` or `dl`, all beginning where the
register begins, and never as `dh`, which begins one byte in. So the predicate
is not "same family" -- `dh` passes that -- but "same space at the same
offset", which is exactly `CanonicalStorageId`.

The owner already knew this and was not being asked. `RegisterFamilyInfo::
from_arch` derives families by union-find over register byte ranges, so
overlap decides membership and no name is consulted. Sitting on top of it was
`seed_x86_low_register_aliases`, sixteen rows of GPR alias names behind an
`arch.name.eq_ignore_ascii_case("x86-64")` gate. That seed is a no-op in
production -- the real `ArchSpec` comes from `sleigh.register_name_map()`,
which declares `AL`, `AH`, `AX`, `EAX` and `RAX` as separate varnodes -- and
was load-bearing only for hand-built test `ArchSpec`s that name `RAX` and
`EAX` and then use `AL`, a shape sleigh never emits. Three such tests now
declare the register they use. The gate was wrong in the direction that
matters too: keyed on the architecture's *name*, it silently supplied nothing
for every architecture but two, making aliasing an x86 privilege rather than a
property of storage.

`RegisterFamilyInfo`, `RegisterFamilySlot` and `family_slot_contains` are now
public, `from_arch` delegates to a `from_register_storages` that any holder of
names-and-geometry can call, and `r2types::RegisterIdentity` builds one from
the prepared function's machine context. `same_parameter_storage` replaces
`register_family_matches` with no x86 branch and no arm64 branch: `w0` is the
low half of `x0` for the same reason `edi` is the low half of `rdi`.

**Where it stops, and the fork.** Two of the three tables are still there, and
the second one needs a decision rather than more work.

`scalar_register_family_key` (`prepare.rs:342`) gives `ah` and `al` one key,
so `collect_register_live_in_aliases` emits an alias pair between disjoint
storages and pointer-ness propagates across it; it also maps `rsp`, `esp` and
`spl` to an x86 key while the reachable two-byte `SP` falls through to the
AArch64 arm and becomes `aarch64:sp`. Its callers are internal helpers under
`recover_vars_from_ssa(ssa_blocks, arch_name, ...)`, which has no machine
context -- but `recover_vars_from_prepared_ssa(source, ptr_bits)` does. The
work is to route the family key through `RegisterIdentity` on the prepared
path; the legacy entry point is pinned by a dylint
(`plugin_variable_recovery_ownership_expr`) and would need to keep answering
something.

`stack_base_from_var` (`writeback.rs:8781`) is the fork, and deleting it as
briefed would be a regression rather than a fix. It builds the *raw* key that
the rebase in `canonicalize_external_stack_slots_with_prep_facts` looks up in
the externally supplied slot map, and the canonical key comes from
`stack_address_root_of`; the rebase exists precisely because the two differ.
Delete the raw side and no rebase can be attempted at all, on x86 either.

The deeper problem is that the external key is minted where the machine is not
known. `parse_external_stack_base` (`context.rs:1226`) runs over radare2 JSON
inside `parse_external_vars`, before any prepared artifact exists, and maps a
base register name to `FramePointer`, `StackPointer` or `Named(raw)` with a
table knowing only `bp/ebp/rbp/fp` and `sp/esp/rsp`. So on AArch64 both halves
fail differently and never meet: parsing yields `Named("x29")` while
`stack_base_from_var` yields `None`. That is why AArch64 frame-pointer slots
are structurally un-rebasable, and adding an `x29` case to either table would
be extending the bug.

Three defensible answers, and this is the decision to make:

  (a) *Canonicalise at parse.* Thread a machine context into
      `parse_external_vars` so `x29` becomes `FramePointer` at the source and
      both sides agree by construction. Costs an ordering change to the
      context pipeline, which today runs before a prepared artifact exists,
      and touches every caller of the parser.

  (b) *Record the raw name, resolve in writeback.* `parse_external_stack_base`
      keeps `Named(raw)` whenever it is not certain, and the rebase resolves
      `Named(n)` through `RegisterIdentity` and the machine context's
      `frame_pointer_storage()` / `stack_pointer_carrier()`. Smallest change
      and resolves where the knowledge is, but `ExternalStackBase` keeps a
      variant meaning "unresolved", and every consumer must know that
      `Named("x29")` and `FramePointer` may be the same slot.

  (c) *Make the canonical key the only key.* Drop the name-derived variants
      and key every external stack slot by `StackAddressRoot`, treating a slot
      prep cannot root as unplaceable. Cleanest invariant, and it will lose
      slots that work today wherever prep facts are absent or cannot root the
      base.

(b) looks right from here -- it fixes at the cause, which is that the parse
layer genuinely does not know the machine -- but it decides what
`ExternalStackBase` means for every consumer, so it is being asked rather than
picked.

The related `prepared_arch_name` defect (`prepare.rs:184`) is untouched: it
re-spells the typed architecture family into a string that
`recover_vars_arch_profile` then substring-matches, so `"x86"` matches the
`contains("x86")` arm and 32-bit x86 is handed the SysV-64 argument
registers. The fix is to pass `MachineArchitectureFamily` and read
`machine_context().abi_model().argument_registers()`, and note the second
feeder at `r2plugin/src/lib.rs:3268` passes radare2's own `"x86"` for both
widths, so fixing one site leaves the other ambiguous.

## The benchmark cannot see the array work, and that is a fact about the workload

Array indexing landed and is measurably working: subscripts went from zero in
all fifty-four corpus cells to twenty-one across eleven of them, with the
snapshot column reporting mismatches on exactly those eleven and no others.

`type_match` on DecBench did not move, and the reason is not the feature.
Rendering every function of `bzip2recover` and counting gives **one** subscript
in the whole binary, a store, against twenty-one on the hash corpus. The seven
functions r2sleigh renders there are small input and output helpers with almost
no indexed access at all.

So the benchmark's *rendered subset* contains almost none of the construct, and
a metric computed over it measures nothing about that construct. The apparent
`type_match` rise, 0.100 to 0.125, is an artefact of a different kind and was
caught by the per-function record: every function that scores is unchanged, and
the mean moved only because a function scoring zero stopped being decompiled and
left the denominator. Zero perfect functions, unchanged, against angr's three.

Two consequences for how this project measures itself.

A metric is only evidence about a feature if the population it is computed over
exercises that feature. Before reporting that a change did or did not move a
benchmark number, count how often the construct appears in what was actually
rendered. That count is cheap and it is the difference between a result and a
coincidence.

And the way to make `type_match` mean something here is coverage, not more
rules. The functions in that binary which do index arrays are among the ones
r2sleigh still refuses, so the array work will remain unmeasurable there until
the refusals fall. A second benchmark project with indexed access in its
rendered subset would also serve, and is cheaper than waiting.
## One conversion per type boundary: the types are stated once now

**What was wrong.** Seven sites in the renderer each decided locally whether a
cast was needed, and five of them decided it by looking at the text they had
just produced -- whether a name `looks_like_pointer`, what type an
`expr_type_hint` reads off an expression. Reading a type off the rendering is
a defect rather than a style, because the rendering is the thing being
decided: the answer changes with the spelling. It is also the mechanism behind
the 3,395 same-type casts the new predicate found -- the read projection
converted, then the assignment policy converted what the projection had
spelled, then the next operand projection converted that.

**What replaced it.** `r2rewrite::typed_boundaries` states, for every node of
the machine arena, two things: what the expression that node renders *has*,
and what the node *requires* of each operand. The operand rule is the
operator's own -- the signedness a comparison, a shift or a division states,
the unsigned width every other integer operator works in, the pointee for an
address, the promoted `int` C computes narrow operands in. Signedness comes
from the `interpretation` at a `Compare` and the `kind` at a `Shift`, never
from the C operator about to be spelled. A leaf reads at the type the plan
declared its object with, or at the type of the expression an inlined value
stands for, so a value's declaration and its uses cannot disagree.

`FoldingContext::convert` is the only emitter. It spells nothing where the two
types are one, spells at most two casts -- the address-width step and the
target -- and respells a constant in the type that reads it rather than
casting it, because C types a constant by its value.
`looks_like_pointer`, `expr_type_hint`, `cast_needed`, `cast_expr_to`,
`cast_expr_if_needed`, both assignment policies and `RecordedType` are gone.

**Measured, all fifty-four cells, against the new `same_type_casts`
predicate.**

    predicate                    before    after
    same_type_casts               3395      185
    cast_chains                      8        1
    self_assignments               225      174
    flag_carriers                  192      192
    literal_only_declarations      103      103
    comma_conditions                17       17
    gotos                          125      125

By configuration, the remaining 185 are `arm64_O0` 67, `x64_O0` 52,
`arm64_O1` 38, `arm64_O2` 28, and **zero** at `x64_O1` and `x64_O2`. The one
surviving cast chain is at `x64_O0`.

Binding audit, effect obligations, placement audit and render refusal are
54 of 54. The workspace suite is 2,203 tests green, up from 2,186, and every
`r2rewrite` rule is still proven.

**Two rules and a rule-side test.** `cast.extend_identity` -- an extension to
the width its input already has -- is what lets `zext(zext(x))` collapse to
one, proven at 8/16/32/64 like every other rule. The C sandwich
`(uint64_t)(uint32_t)(uint64_t)x` needed no new rule: the driver
canonicalises children first and the existing
`cast.extract_of_extend_whole` removes the inner truncation, which
`an_extension_sandwiched_in_its_own_truncation_is_one_extension` now records
end to end.

**A value's identity is the plan's answer, not the rendering's.** The journal
classified a value by the shape of the C it was rendered as. A value the plan
*inlines* was already exempt, with the reason written beside it -- the shape
is not evidence. The same is true of a value the plan *binds*, and it was not
exempt: one value is read at several places and the renderer spells each read
as that place requires, so recovering the identity from each spelling makes it
a function of the C. Two spellings then give one value two identities and the
seal refuses with `ConflictingValue`. That refused **26 of 54 cells** the
moment the redundant conversions went. `x` and `(uint64_t)x` were already
handled by looking through casts, which is the same fix applied one shape at a
time; `!x` inside a condition the structurer negated was the shape left over.
A bound value is now classified by the symbol the plan gave it, provided the
occurrence mentions that name -- which keeps a rendering that spells a bound
value as a *constant* a conflict, because that one really does contradict the
plan.

**A late substitution changes a type, and the conversions above it have to be
restated.** Two passes put an address where a number was: the string table and
the object table. Everything above them was decided while the expression was a
`uint64_t` constant, so `(char *)(uint64_t)"a string"` survived, and
`uint64_t RDX_2 = &progName;` -- a pointer assigned to an integer with no
conversion at all, because for a `uint64_t` constant into a `uint64_t` object
the right answer had been *nothing*. The chain is now restated end to end
through the one emitter, from what the address is to what the place required,
and the place is asked even when it spells no cast. The corpus's own
`-Wint-conversion` is what found the second shape.

**Where the remaining twenty-three raw-compile failures are, and why one of
them is a fork.**

    error                                   count   status
    -Wself-assign  (`x = x;`)                  18   design fork, below
    -Wsign-conversion  int -> uint64_t          3   open, cause known
    -Wint-conversion  uint64_t -> uint8_t *     2   open, cause known
    -Wsign-compare  uint64_t vs int             1   open

The three sign-conversion and one sign-compare failures are the same cause as
the mask literal already fixed -- a constant that reaches the reader with no
type of its own -- at sites the restatement walk does not reach yet. The two
`-Wint-conversion` failures are a call result assigned to a pointer-declared
object at a site where neither the callee's recorded signature nor the
certificate names the value, so nothing states what the call produced.

**The fork: what elision reason covers a copy whose two sides are one
binding.** `x = x;` compiles only while a redundant cast hides it, which is
why removing the casts turned 18 hidden self-assignments into hard errors. The
statement performs nothing *because the plan bound both values to one object*,
and the plan is the authority on that. `ElisionReason::CoalescedEdgeCopy`
already says so in its own documentation -- "This was once restricted to a
certified loop carrier, which is where the case was found rather than the
reason it holds: what makes the copy say nothing is that both sides are one
binding" -- and this stretch already widened it from certified carriers to any
materialised merge edge, and from non-entry sources to entry ones, which took
self-assignments from 225 to 174 and rendered `X1_0 = X1_0;` unnecessary in
the merge cases. What is left is the copies that are not merge edges at all:
real `Copy` instructions the plan coalesced.

  * *Reuse `CoalescedEdgeCopy`.* Follows the reason the codebase already wrote
    down, needs no schema change -- and misnames the case, because a plain
    copy is not an edge, so the audits would report an edge elision where
    there is no edge.
  * *Add a reason, `CoalescedCopy`.* Names the case honestly and keeps the two
    findings distinguishable in the ledger; costs an `ElisionReason` variant,
    which appears in audit output and in blessed baselines.
  * *Do not elide, and stop the plan coalescing across a real copy.* Keeps
    every machine instruction answerable by a statement, at the cost of the
    coalescing that removes the noise elsewhere -- and it is a bigger change
    to the plan than to the ledger.
  * *Do not elide, and keep a cast so `x = (uint64_t)x;` compiles.* Rejected
    here rather than offered: it is a compensating workaround at the symptom,
    and it is the thing this whole stretch removed.

The first three are all defensible and the choice is long-lived, so it is put
here rather than taken. This is the same fork this document has recorded once
before, under the widening of merge-edge coalescing; it is now load-bearing,
because it is the only thing between the corpus and a green raw column.

**The benchmark says the casts were not what `byte_match` was measuring.**
DecBench on `bzip2recover` at `-O0`, per function, r2sleigh before and after
the typed-boundary work:

    function        byte_match before -> after
    endsInBz2            0.088 -> 0.085
    mallocFail           0.161 -> 0.161
    readError            0.214 -> 0.214
    tooManyBlocks        0.156 -> 0.156
    writeError           0.214 -> 0.214

Unmoved. What the rendered C shows is why: the casts were never the bulk. For
`readError`, four source statements become fourteen, and the fourteen are
*bindings* -- a register-named local for every argument before the call --
not conversions:

    FILE* RAX_1 = (FILE*)*(uint64_t*)&stderr;
    uint64_t RDX_2 = &progName;
    char* RSI_1 = (char*)"%s: I/O error reading `%s' ...";
    FILE* RDI_1 = RAX_1;
    uint64_t RAX_3 = (uint64_t)sym_imp_fprintf(RDI_1, RSI_1, RDX_2);

against `fprintf(stderr, "...", progName, inFileName)`. So the lever on
`byte_match` is the inlining question -- why the plan binds a value with one
reader instead of spelling it at that reader -- which is the `flag_carriers`
and `literal_only_declarations` work, not this one. That is a correction to
the premise this task was given, and it is worth carrying: removing 3,210
redundant casts moved the semantic-correctness score by nothing.

**The second fork: what type a global object is declared with.** `ast.rs`
states the present decision beside the field and states it as a deliberate
one -- "The type is deliberately not claimed: the body only ever takes the
object's address, so an incomplete array of bytes declares exactly what is
known". Every global therefore renders as `extern char name[]` and every read
of one goes through the access width by hand, as `*(uint64_t *)&stderr` above.
It is a fork rather than a bug because the standing decision that a type may
be asserted from use evidence was made about *values*, whose scope is one
function, while a global's scope is the program.

  * *Keep the abstention.* Never asserts a type it cannot prove; costs a cast
    and a dereference at every global read.
  * *Declare the global at the width the evidence shows*, as
    `declaration_type_for_stack_object` already does for stack slots, refusing
    on disagreement. Reads become `stderr`. But r2sleigh renders one function
    at a time, so two functions reading one global at two widths emit two
    contradictory declarations of one name and nothing in a per-function
    rendering can see the conflict; and the asserted type is knowingly not the
    real one, since `stderr` is a `FILE *`.
  * *Assert per rendering rather than per program* -- declare the width only
    where this function reads the object as a scalar at one width. That is the
    only scope a per-function decompiler has, and it makes two renderings of
    one program disagree about a global, which is a new kind of statement for
    this project.

Worth knowing before choosing: the read compiles to the same load under all
three, so `byte_match` should not move, and `type_match` is wrong under the
first two alike because neither says `FILE *`.

**An operational note that cost a measurement.** A corpus run was started
while the tree was mid-edit; `locked_matrix.sh` built a half-edited tree, the
build failed, and the matrix on disk was the *previous* run's, which read as
"no change" rather than as an error. Delete `tests/corpus/artifacts/results/
matrix.json` before a run, and do not edit the tree between starting
`locked_matrix.sh` and its completion -- `run_matrix.sh` builds again under the
lock, so an edit in that window is measured. That is the sixth reading this
class of hazard has cost.


## Both forks answered, and what the answers cost to carry out

The two forks the typed-boundary work left are resolved, and the resolutions
are implemented. What follows is what each turned out to require, because in
both cases the answer was cheap to state and the accounting behind it was not.

**Fork one, the elision reason for a copy whose two sides are one binding.**
The rename had already landed on the integration branch -- `CoalescedEdgeCopy`
became `CoalescedCopy`, one reason widened rather than a sibling added,
following `CoalescedCarrierEdge` before it -- and its documentation already
named the program's own copies as the case it covers. The journal did not:
it declined every `Original` copy, because dropping them on the strength of
the coalescing alone made three corpus cells compute the wrong answer.

That decline was right and its reason is worth keeping. A copy normalization
makes for a merge sits at an edge, where nothing can have touched the object
between the edge's two ends. A copy the program made has a *position*, and a
save and restore around a clobber is the same shape -- there the object is
written in between and the restore is the only thing that puts the value
back. So the question is now asked at the copy rather than of the coalescing:
*nothing wrote this object between the value being produced and the copy of
it*. That is local, exact, and independent of the interference test having
been right. A source defined in another block declines, because reaching it
crosses a control edge and what wrote the object on the way is a liveness
question this does not ask.

Eliding the statement then took three more answers, one per layer, and each
was a separate refusal until it was given:

  * the *value* the copy defined is rendered by its binding -- the same answer
    the symmetric merge case gives, where a merge coalesced to one binding is
    rendered by that binding rather than by a write of its own;
  * the *write* is elided with the statement, because the object was already
    written by whatever produced the value copied;
  * the *`LiveValueProducer` obligation* is answered by that same statement,
    which is the rule the coalesced merge already had, asked of a copy.

Separately, a parameter's entry copy is now elided too. The version-0
exclusion was wider than the reason recorded beside it: that reason is about a
live-in register nothing declares, and a parameter is the case it excepts,
since the signature declares it and the binding is written before the body
starts. Excluding it left `X0_0 = X0_0;` on the first two lines of every arm64
function that takes arguments.

**Fork two, the type a global object is declared with: answered, not
implemented, and the reason is a missing fact rather than a missing
decision.** The answer -- radare2's type where it has one, marked as radare2's
fact, and the evidenced access width where it does not, with the per-binary
engine cache as the program scope that makes refuse-on-conflict possible --
needs radare2's type for a data object to *reach* the renderer, and it does
not. `DisplayNames` carries three maps and all three are spellings:
`functions`, `symbols`, `strings`. The plugin's wire writes a data symbol as
an address and a name and nothing else (`snapshot_walk.c`, the
`num_data_symbols` loop). So the work is a vertical slice -- the C snapshot
walk, the wire, `r2source`, `r2types`, then the renderer and the cache -- and
none of it is the decision. It is left whole rather than started, because a
half-plumbed type fact is worse than none.

**The measurement, all fifty-four cells, after both.**

    predicate                    start    now
    same_type_casts               3395     185
    cast_chains                      8       1
    self_assignments               225     155
    literal_only_declarations      103      80
    flag_carriers                  192     192
    comma_conditions                17      17
    gotos                          125     125

    column               result
    binding_audit        54 / 54
    effect_obligations   54 / 54
    placement_audit      54 / 54
    render_refusal       54 / 54
    differential         52 pass, 1 fail, 1 blocked
    raw                  52 pass, 2 fail

The workspace suite is 2,216 green. The raw column went 23 failures to 2 over
this stretch, and the two left are named rather than counted:

  * `x64_O2 xxhash32:411`, `tmp_3ea80_2 < -0x4` -- a mask compared against a
    `uint64_t`. The restatement gives a compared literal the type of what it
    is compared with, and this site is not reached by it; every other mask
    shape in the corpus is.
  * `arm64_O0 xxhash32:332`, `uint8_t *X0_9 = sym__rotl32(...)` -- a call
    result assigned to a pointer-declared object. Neither the callee's
    recorded signature nor the call-result certificate names the value behind
    the object at that site, so nothing states what the call produced.

**The one that cost the most to find, and would again.** A render marker is
metadata, and the restatement walk matched on the expression *directly*, so a
marked right-hand side fell through with the requirement dropped. In
production nearly every right-hand side carries an occurrence marker, so the
pass silently did nothing on most statements while working perfectly in its
own unit tests. What made it visible was two adjacent lines in one rendered
function, the same shape, one converted and one not -- the converted one had
been converted at lowering, not by this pass. A pass that walks the rendered
tree has to look through `Observed` and `Paren` at every branch, not only in
the descent.

## The lock split works, measured in the field

`released the install lock; verification does not need it` now appears in a
real gate run. A corpus run holds the shared install lock for its install and
its six sweeps and hands it back before the six compiles, six oracle builds and
six verifications, which need no plugin. That was written when six worktrees
were queued behind a whole-binary coverage sweep.

Both files were replaced atomically rather than written in place, because bash
reads a script by byte offset as it executes and five wrappers were running at
the time. Running instances kept their descriptor on the old inode and the next
invocation picked up the split, which is the technique to use for every edit to
a script this project runs concurrently.

## The gate this session has been using cannot fail on a wrong answer

`run_matrix.sh --gate measurement` checks that every column was *measured*. Its
only failures are `not_run`: a column that produced no record. It does not
require the raw compile to pass, the differential to agree with the oracle, or
the snapshot to match. It exits zero with a cell rendering the wrong value.

That is what the name says, and it is a useful thing to have. The error was
mine: I briefed every agent in this session to treat it as *the* merge gate, and
reported branches as green on the strength of it. A run on the integration
branch exited zero while one differential cell failed and eight diagnostic cells
computed wrong values, and nothing in the exit status said so.

**The correctness gate is `--gate differential`.** It subsumes the others: raw
must compile and pass, the differential must agree with the source-built oracle
*on the raw basis* rather than on the repaired one, and the snapshot must match
or have been accepted. Use it before merging anything, and read `measurement`
for what it is, a check that the harness still measures.

One consequence for reading the diagnostic column. It exists to repair raw
output that does not compile, and raw now passes on all fifty-four cells, so
every diagnostic cell is a repair of something that needed none. The eight that
compute wrong values are the repair heuristics mis-firing on output whose shape
improved, not the decompiler getting an answer wrong: the same eight cells pass
the differential on the raw basis. A column that only reports on a fallback
nobody takes is measuring itself.
## `arm64_O0 pearson`: the harness read a cast as a fact, and the naming gap behind it

The differential scored this cell a wrong answer on every non-empty input,
with `rendered_exit -11`. The decompiler was right and the harness was wrong,
and the two are worth separating because the second half is still open.

**The wrong answer was the harness.** `verify_rendering.py` maps an image
address into a blob so the recompiled C reads the real table, and
`certified_image_literals` recognised the binding of such an address to a
name by matching `name = (uint64_t)0x100001000` -- with the conversion
required, because every rendering used to spell one. This branch states a
type only where the type changes, so the statement became
`name = 0x100001000`, the test stopped recognising it, the address was left
absolute and the program segfaulted. The conversion is now optional; the
evidence it rests on is unchanged. All eighteen cases now return the right
hash. This is the second time this one test has had to stop reading a
spelling as the fact it carries, and the comment above it records the first.

**The register-family hypothesis is disproven by the output.** The rendered C
computes `0x100001000 + 0xe6c + index` and returns the correct Pearson hash on
all eighteen inputs, so the `adrp` result and the `add` operand *are* agreed
to be the same storage. If the pairing were broken the arithmetic would be
wrong, not merely unnamed.

**What is still open is naming, and it is not a lookup question.** Measured
across the three architectures:

    x64_O0     `0x1000019a0` arrives as one literal -> looked up ->
               `&_pearson_tab`, with `extern char _pearson_tab[];` emitted
    arm64_O1   neither the name nor the page base appears; the table is
               reached by another path
    arm64_O0   `X8_5 = 0x100001000;` then `X8_5 + 0xe6c` -- two statements

The object table is not missing an entry and is not being asked about an
interior address. `sym._pearson_tab` sits at `0x100001e6c`, which is exactly
`0x100001000 + 0xe6c`, and radare2 has a flag there. The lookup would hit the
way x64's does. It never runs, because the fold that performs it needs the
address as one literal expression and the page base is *bound to a local*.

So this is the `literal_only_declarations` column, not a new question: eighty
literal-only bindings remain, and this is one of them. Inlining it would make
the addition fold and the name appear. Doing that in the late fold would put
a second answerer beside the binding plan for "does this value render
inline", which is the duplication this project keeps removing, so it belongs
to the inlining work and not here.

## A test that reads a spelling as the fact, for the third time

The one differential failure left on the integration branch, `arm64_O0 pearson`,
was the harness. `verify_rendering.py` maps an image address into a blob so the
recompiled C reads the real table, and `certified_image_literals` recognised the
binding of such an address by matching `name = (uint64_t)0x100001000`, with the
conversion required, because every rendering used to spell one. The cast work
states a type only where the type changes, so the statement became
`name = 0x100001000`, the pattern stopped matching, the address stayed absolute
and the program segfaulted on eighteen of eighteen cases.

The comment directly above that code records the previous time the same test had
to stop reading a spelling as the fact, when recognising `*(uint8_t *)p` but not
`*p` made a better rendering look unmapped. It is now three, counting the pass
that matched an expression directly and so did nothing on any statement carrying
a render marker.

Two hypotheses were wrong and the output disproved both without a bisect. It was
not the register families rekeyed on geometry: the rendered C computes
`0x100001000 + 0xe6c + index` and returns the correct hash on all eighteen
inputs, so the `adrp` result and the `add` operand are agreed to be the same
storage. Had the pairing broken, the arithmetic would be wrong rather than
merely unnamed. And it was not an object lookup missing an interior address:
`sym._pearson_tab` is at `0x100001e6c`, exactly the base plus the offset, so the
lookup would hit as it does on x64.

**The lookup never runs.** It needs the address as one literal expression, and
on this cell the page base is bound to a local rather than inlined, so the fold
that would recombine them never sees a literal. x64 names the table because the
address arrives as a single literal. That makes this one of the eighty remaining
`literal_only_declarations`, and inlining it would make the fold happen and the
name appear. It was deliberately not fixed in the fold: constant propagation
there would stand a second answerer beside the binding plan for whether a value
renders inline. It belongs to the inlining work.

Note this is a different fact from the `adrp` page base found in the thunk work,
where radare2's own reference points at the page rather than the slot. Here the
page base is correct and simply un-recombined.

## A lock nobody could clear, and a corpus cell nobody can render

Two things came out of the first attempt to measure the value-hazard corpus, and
neither was the measurement.

**The install lock had no recovery from a dead holder.** A run killed with a
signal its trap cannot catch left the directory behind, and every later run
waited on it forever. That is a guard that can never clear, the same defect
class as one that can never fire, and this session has now found one of each
kind three times over. The holder now records its process id in the lock and a
waiter reclaims the lock when that process is gone. Reclaiming is safe because
the directory *is* the lock: whoever recreates it is the new holder, and a live
holder is never displaced. Both paths were exercised, a dead holder reclaimed
and a live one waited on.

**A value-hazard function does not finish.** The run held the lock for forty
minutes and never got past the first of six configurations, sweeping thirteen
leaf functions with no calls, no loops over memory and no aggregates. Whatever is
slow is slow on straight-line integer arithmetic, which makes it a much smaller
reproduction than `main` in `bzip2recover`, the function that spends 2.27
seconds in the structurer against 2.77 for every other stage combined.

That is worth more than the measurement it prevented. A pathological case in
thirteen short functions can be bisected to one function and one hazard in
minutes, and it should be handed to whoever holds the structurer's safety
budget, since a budget of block count times 128 consumed in proof order is the
standing suspect. Run one config with a timeout and per-function timing to find
which of the thirteen it is before running the whole matrix again.

## The structurer pathology, reduced to one function

The value-hazard corpus held the install lock for forty minutes without
finishing one of six configurations. Timing its thirteen leaf functions
individually, with the plugin already installed and no lock involved, says why.
Eleven finish in under eight seconds. Three do not:

| function | time |
| --- | --- |
| `value_overflow_flags` | exceeds 60 s, did not finish |
| `value_signed_compare` | exceeds 60 s, did not finish |
| `value_width_conflict` | 21 s, finishes |

These are leaf functions with no calls, no loops over memory and no aggregates,
so whatever is superlinear is superlinear on straight-line flag arithmetic and
signed comparison, which is where the reaching-path predicates multiply. They
also have very few blocks, and still exhaust whatever budget they are given,
which is direct evidence that a budget of block count times 128 is the wrong
shape rather than merely an unprincipled constant.

`value_overflow_flags` is therefore a one-function reproduction that iterates in
a minute, against the 2.27 seconds inside `main` in `bzip2recover` that the
work was originally scoped against. Time those three before and after any change
to the safety budget; it costs seconds and needs no plugin install and no lock.

Method worth reusing: install once, then run the decompiler per function with a
timeout, outside the lock. Identifying which function is pathological does not
need an exclusive plugin, and taking the lock for a hang is how a forty-minute
hold happened in the first place.

## The flag carriers are dead values, not un-inlined ones

The 192 flag locals have been described here as an inlining problem for as long
as the noise gate has existed, and an architecture survey reinforced it by
reading `inlinable_values` and concluding that by its own text the
temporary-to-architectural flag copy passes every gate. Running the probe rather
than reading the function says something else, and it is not close.

Counting why every flag-named value stays bound, across whole binaries at two
configurations:

| reason it stays bound | x64 -O0 | arm64 -O0 |
| --- | --- | --- |
| **no readers** | **14,323** | **10,852** |
| expression kind does not render inline | 2,487 | 4,500 |
| the one reader is a merge | 1,780 | 2,560 |
| a location it reads is written before the reader | 1,270 | 260 |

The dominant answer by a factor of three is that **nothing reads them at all**.
`CF_1` and `OF_1` in `xxhash32` are the clean specimens: no readers, and bound
and declared anyway.

So the question was never which inlining gate rejects them. A value nothing
reads should not acquire a binding or a declaration, and the machinery for that
already exists in `DeadUnusedTemporary` and `DeadUnreadBinding`, which the
journal closes from a reported set when placement drops a statement. Either that
path does not cover a value that was dead before placement ran, or the binding
is created before anything asks whether it has a reader. That is where to look,
and it is a different file from the one everyone has been reading.

The site is exact, so nobody need re-find it. `inlinable_values` in
`crates/r2dec/src/binding_plan/rules.rs` counts readers at around line 570 and,
where the count is zero, rejects the value for inlining and continues, which
leaves it bound. Rejecting a dead value *for inlining* is the right answer to
the question being asked and the wrong thing to do with it: a value nothing
reads should be eliminated, not named.

Note the near-miss directly above that gate, because it shows the same code has
already been corrected once for a related reason. A call's arguments are readers
the graph does not record, since a call takes only its callee as an operand, so
a value staged in an argument register has no use site at all and was turned
away at this very gate. That was fixed by consulting the callsite certificate,
and it is what took one function from fourteen rendered statements to eight. So
the zero-reader count is now trustworthy in a way it was not before, which is
precisely why the remaining zero-reader values can be treated as genuinely dead.

Two lessons, both of which this session has now paid for more than once. A survey
that reads a function will tell you what the function says, and what it says can
be true while being about a different value than the one you are holding. And
the probe that answers this took one command against a binary that was already
built, against months of the same wrong framing.
## The page-base literal: what the probe says, and why the fix is still a fork

`R2SLEIGH_TRACE_INLINE=all` on `arm64_O0 pearson` names the gate exactly, and
it is not the one the reading predicted:

    INLINE X8_5 ValueId(128) stays bound: 3 readers (0 of them call
    arguments), of which 0 sit in a certificate-elided instruction; root Copy

Three readers, not one. So the single-reader path never applies, and the only
way in is the duplicable-literal path -- which is gated on storage class:

    let literal_only = ...machine_expr_is_literal(...)
        && value.canonical_storage.is_none_or(|storage| {
            matches!(storage.space, CanonicalStorageSpace::Unique)
        });

`X8_5` lives in a register, so it is turned away. The comment beside that gate
already says the storage class is a proxy and names the honest test -- whether
the value is coalesced with anything -- and says it cannot be asked there
because the partition is computed from this answer.

**The two rendered shapes confirm the proxy is discriminating the right
thing.** In `pearson` the `x8` versions render as `X8_2, X8_4, X8_5, X8_6,
X8_8, X8_9, X8_10` -- seven distinct names, so seven distinct bindings, so
`X8_5` is alone in its object and inlining it orphans nothing. In `fnv1a64` at
x86-64 -O2 the accumulator renders `R8_1 = 0xcbf29ce484222325U;` and is read
later as `RAX_15 = R8_1;` -- one object, and the literal is its only write, so
inlining it leaves the object read before it is assigned. That is the
ten-cell breakage the proxy was installed to stop. "Alone in its binding" is
exactly the discriminator, and it is exactly what the plan cannot ask yet.

**The obvious way to break the circularity does not work, and this is new.**
The natural two-pass is: compute a maximal partition with every value
eligible, admit a literal that is alone in it, then compute the real
partition. That relies on components only shrinking as values leave
eligibility, and they do not. `merge_would_interfere` collects its members
from the values that actually joined, so a value excluded from eligibility is
not a member and cannot contribute an interference; removing it can therefore
*remove* the interference that was blocking a merge, and the component grows.
A value alone in the maximal partition can be coalesced in the real one, so
the test is unsound in the direction that matters.

Nor is there a partition-free sufficient condition available for this case.
"Sole value in its storage span" would be sound -- nothing could merge with
it -- but `X8_5` shares the `x8` span with six other versions and is separated
from them only by the interference test, which is the partition again.

So admitting the page-base literal requires the interference-resolved
partition before the inlining answer that the partition is computed from, and
the fix is the two-pass restructuring rather than a wider gate. That is the
design question this file has recorded once before, now with the probe output
that names the gate, the two renderings that show what the proxy is
protecting, and one way of breaking the circularity ruled out.


## The fixed point, built: what it buys and the one refusal it costs

The two-pass construction is in. The partition is built once from the
conservative answer that admits no bound literal -- exactly what
`inlinable_values` returned before -- and a literal that is a **one-member
component** there is admitted on a second pass. Nothing coalesces with a
one-member component by definition, so removing that value removes its own
object and no other object loses a writer; `fnv1a64`'s accumulator shares an
object, is not a singleton, and stays bound, so the ten-cell breakage the
storage-class proxy prevented is still prevented -- now by the property the
proxy stood in for.

Termination is by construction. Pass one does not depend on pass two, so
there is no iteration, no bound to choose, and nothing to observe converging.
The second pass is deliberately conservative rather than maximal: a candidate
that would become a singleton only after other candidates are inlined is
declined. That is the safe direction and it is why the relaxed-eligibility
estimate is not needed -- which matters, because that estimate is unsound, as
recorded above.

It stays one answerer. `inlinable_values` keeps its signature and is still the
only place inlining is decided; `component_eligible_with` and
`binding_components_with` take that decision as an argument so the partition
is *read against* it rather than guessing at it.

**The payoff is confirmed on the cell that motivated it.**

    #define _pearson_tab__r2sleigh_addr 0x100001e6cULL
    extern char _pearson_tab[];
    uint64_t tmp_11f80_2 = (uint64_t)&_pearson_tab;

The page base inlines, the fold recombines it with its `0xe6c`, the object
lookup runs, and `arm64_O0 pearson` names its table instead of dereferencing a
bare page base. Across the corpus, `literal_only_declarations` falls 103 -> 70
and `self_assignments` 225 -> 133.

**And it costs two cells, which is where this stops.** `murmur3_32` at x86-64
-O1 and -O2 refuse: one obligation of 145, `LiveValueProducer`, with
`Refused { layer: Codegen, reason: BlockNotRendered }`. The inline trace says
exactly one value is newly admitted in that function -- `R9_1`, a register
literal, alone in its binding, four readers -- so the admission and the
refusal are one-to-one.

Three hypotheses were tried against it and all three were wrong, which is
worth recording so the next attempt does not repeat them:

  * *The block empties because its only statement was inlined.* Requiring a
    reader in the defining block did not fix it.
  * *That reader is itself inlined, so the block empties anyway.* Requiring an
    instruction in the block whose output is bound under the conservative
    answer and is not itself a candidate did not fix it either.
  * *It is the storage class after all.* It is not; the same admission on
    `pearson` renders and seals.

So `BlockNotRendered` here is not obviously about the defining block being
empty, and the next step is to establish which instruction the refused
obligation names -- the id is `CanonicalInstructionId { block_addr:
0x10000085c, site: Op(34) }`, in source coordinates, while the trace reports
the definition in graph coordinates as `BlockId(3), ordinal 110`. Those were
never reconciled, and every hypothesis above assumed they were the same
instruction without checking. That is the first thing to check and it needs a
probe, not a reading.

Until then the branch is red on two of fifty-four on `--gate differential`,
with no wrong answers -- both cells refuse rather than miscompute. Reverting
`6f0cd8d..be06880` returns the corpus to 54 of 54 and gives up the naming and
the thirty-three literal declarations.


## The fixed point, green: the refusal was placement, not the admission

The two cells the bound-literal admission cost are green, and the cause was
none of the five things read into it. It was found by printing the mapping
the coordinator asked for and then one more trace, and both should be kept.

**The coordinate mapping.** The refusal is reported in source coordinates and
every other view of the instruction in graph coordinates, and nothing
reconciled them, so five hypotheses were argued about an instruction nobody
had confirmed was the right one. The refusal evidence now prints both, and
the answer was that the assumption had been correct all along:

    kind=LiveValueProducer component=Op(34) block=0x10000085c
    source_inst=Some(InstId(329)) graph_block=Some((BlockId(3), 110))
    output=Some((ValueId(417), "R9_1"))

`(BlockId(3), 110)` and `ValueId(417)` are exactly the admitted value's
definition. The instruction was right; every proposed cause was wrong.

**What it actually was.** Placement removes a binding nothing reads and
reports the observations that went with it. The journal fills the value, use
and write cells of those observations with `DeadUnreadBinding`; for an effect
it did nothing, with a comment saying an effect answers to the effect ledger.
That is right, and nothing was telling the ledger. The obligation was left
with zero occurrences, no rule claimed it, and the default refusal fired.
The two traces name the same obligation to the instruction, kind and
component:

    PLACEMENT_ELIDED_EFFECT  LiveValueProducer  0x10000085c Op(34)
    zero-occurrence-outcome  LiveValueProducer  0x10000085c Op(34)

So the obligation is dead with the statement, for the same fact the three
cells beside it already record, and it is elided with the same reason. The
rule can only fire on an obligation with no occurrences at all, so it cannot
hide a live effect.

The admission exposed this rather than caused it: inlining a literal moves its
occurrence onto a reader's statement, and if placement later finds that
statement's object unread, the occurrence goes with it. Any change that moves
an occurrence onto another statement can reach the same hole.

**Ruled out by experiment, not by reading.** The program-copy elision is not
involved -- disabling it left the refusal unchanged. The defining block
emptying is not the mechanism -- requiring a reader in that block, and then an
instruction in it that provably still renders, both left the refusal in place,
and both filters were removed again. Filtering on the `LiveValueProducer`
obligation *kind* turned away every candidate including the page base, because
that kind is seeded by a transitive closure over inputs and not only at
boundaries; the filter that remains names the values a return boundary spells
through its own path, which is the set `seed_value_definition` is called on
there.

**Where it lands.**

    predicate                    start    now
    same_type_casts               3395     185
    cast_chains                      8       1
    self_assignments               225     155
    literal_only_declarations      103      75

    column               result
    binding_audit        54 / 54
    effect_obligations   54 / 54
    placement_audit      54 / 54
    render_refusal       54 / 54
    raw                  54 / 54
    differential         54 / 54

`--gate differential` exits zero. The workspace suite is 2,119 green. And
`arm64_O0 pearson` names its table:

    #define _pearson_tab__r2sleigh_addr 0x100001e6cULL
    extern char _pearson_tab[];
    uint64_t tmp_11f80_2 = (uint64_t)&_pearson_tab;

The raw baseline is re-blessed, because the rendering changed on purpose.

**One thing left on the table.** The return-boundary filter was added while
chasing the wrong cause and kept because it is defensible on its own terms --
a value the boundary spells through its own path should not be inlined -- but
it was never shown to be *necessary* once the placement hole was closed.
Removing it may admit more literals. That is one corpus run to find out.

## The call-restore work is reverted from integration, and why

Three independent measurements agreed that the integration branch had regressed,
and all three point at the same change.

| measurement | before | after |
| --- | --- | --- |
| corpus correctness gate | 54 of 54 | 52 of 54 |
| whole-binary coverage, real functions | 321 of 409 | 312 of 409 |
| benchmark functions decompiled | 7 of 14 | 1 of 14 |

The two corpus cells are `murmur3_32` and `xxhash32` at x64_O0, the only two
corpus functions that call anything, refusing with `UnownedBindingSymbol`. The
six benchmark functions are all call-heavy. The branch was known to be at 52 of
54 when it was merged, and merging it anyway was the mistake: five other workers
branch from integration, so a regression there is inherited by every measurement
taken against it, and their numbers stop meaning anything.

Reverting also removed `crates/r2dec/src/lib.rs.bak`, a 10,654-line stray backup
committed on that branch and merged without anyone looking at the file list.
Whoever re-lands the work must drop it; the real change is about 800 lines
across the SSA and r2dec layers.

**None of the work is lost and it should come back.** `arch/expr-callstack`
holds all eight commits, and what they fix is real: an x86-64 `call` is lowered
as `RSP = RSP - 8` plus the return-address store and nothing refunds it, so a
caller's stack pointer is wrong from its first call and by a further eight bytes
at each one after. `SSAOp::CallRestore` states the refund at the boundary from
the convention's own preserved-carrier fact, with no per-architecture constant
anywhere, and the owner chose to license the coalescing by that proof rather
than by an exception for one operation kind.

The condition for re-landing is that the two cells render, measured on the
branch, before the merge rather than after it.

The rule this cost us: **a branch merges when its own gate is green, not when
its work is good.** A red cell carried into integration is not one team's
problem, it is everybody's, and it invalidates every measurement taken until it
is fixed.

## The array functions stopped rendering because one producer was rendered twice

Eight whole-binary cells regressed when array indexing landed --
`elem_at`, `elem_before`, `bounded_fetch` and `half_stride`, at x86-64 -O1 and
-O2, exactly the corpus's indexed shapes -- all refusing at declaration
placement with `ambiguous_observation_execution_order`. The fifty-four-cell
matrix stayed green throughout, which is why it was the coverage sweep that
found them: these four functions are in `branchy.c` and no cell scores them.

### What the trace said

`ambiguous_observation_execution_order` reports an observation id and nothing
else, so the first thing added was a trace. For `elem_at` it says:

    ambiguous group [22, 21, ... 7, 5, 6] recorded at placement.rs:970
    ambiguous observation 9 target Some(Write { inst: InstId(4), ... })
      write of InstId(4) output ValueId(7) disposition Bound { binding: 1 }

`placement.rs:970` is `record_ambiguous_expr_group` reached from the
assignment arm, and the statement is
`tmp_11f00_1 = ((uint32_t*)RDI_0)[(int64_t)(int32_t)ESI_0]`. Two lines above
it, the same function renders `RAX_1 = (uint64_t)(int32_t)ESI_0`. `InstId(4)`
is that sign extension, and its write is marked twice: once as observation 3,
on the statement that assigns `RAX_1`, and once as observation 9, inside the
subscript. Placement is right to refuse -- C states no order between a write
in an operand and the reads beside it -- and the refusal is the symptom of the
duplication rather than the defect.

### The cause, which predates the subscript rule by a day

`BindingPlan` supplies the rewriter's expansion policy, and it read

    inlinable_for_expansion.contains(&query.value)
        || r2rewrite::term_is_duplicable(..)

The comment above it already said the intent: "may this producer be expanded
into its reader" and "may this value be rendered without a local" are one
question with one answer. The second disjunct answers a different one.
Duplicability says re-evaluating a term observes nothing twice; it does not say
the producer stops being rendered, and only the plan's disposition does that.
`ExpansionPolicy`'s own documentation says as much -- a duplicable term
expanded at every reader "would need `Multiplicity::Any` there" -- and the plan
has no multiplicity rule.

So a duplicable term whose value the plan bound is rendered twice: once as
`name = ...`, and again inside every term that absorbed it. `discharged_from`
then reports that producer as discharged, correctly by its own definition --
the canonical term no longer reads the value as a leaf -- and
`observe_discharged_expr` marks the vanished instruction's write on the
expression standing in for it. Two answerers for one write.

`sext(esi)` hits it exactly. The plan binds the value because
`expression_renders_inline` excludes `Cast`, and the term is duplicable because
`esi` is an entry value the function never writes. The divergence was inert
while nothing rendered from the canonical terms; the subscript renderer is the
first thing that does.

The policy is one function in `binding_plan::rules` now, `term_absorbs_producer`,
called by construction and by the seal so they cannot drift.

### Measured

Whole-binary sweep, 517 functions over twelve compiled configurations, two
pinned GCC binaries and `/bin/ls`, run from the worktree with the plugin loaded
by `L` rather than installed, so the shared install lock was not involved:

    rendered            316 -> 324      (the blessed baseline is 321; the
                                         difference either way is the eight)
    regressions vs baseline   8 -> 0

Exactly eight functions render different text. The other 509 are
byte-identical, so no subscript was lost anywhere and the corpus's twenty-one
are untouched. Six of the eight index:
`((uint32_t*)RDI_0)[RAX_1]`, with the index spelled as the name the plan gave
it rather than re-derived.

### Two things this leaves on the table

**`bounded_fetch` renders address arithmetic instead of a subscript.** Its
lifter temporaries `tmp:4900_1` and `tmp:4a00_1` have two readers each -- the
second is a merge of the Sleigh temporary across the branch, which the source
program does not have -- so the plan binds them, so the term cannot absorb them
and the address is spelled out. The subscript is recoverable by making those
temporaries single-reader, which is a question about lifting Sleigh scratch
across blocks rather than about the rewriter. Nothing here decided against it.

**A width change has no inline form, and the subscript renderer has one.**
`expression_renders_inline` is the list of shapes `materialize_machine_expr`
can build and it excludes `Cast`, which is why `sext(esi)` is bound at all,
which is why the index is `RAX_1` and not `ESI_0`. `render_subscript_term`
does have a `TermKind::Cast` arm. Two renderers with different capabilities is
tolerable; the plan's gate being written against the weaker one is what costs
the source-shaped `v[i]`. Widening it is one measurement, and it is the change
that would make these renderings read like the source.

**Not the fix, and worth saying so.** A guard refusing a second exact write
occurrence for one instruction looks like the way to catch this class at its
source. It is wrong: normalization materializes one phi definition as a copy on
each incoming edge, so several write occurrences for one instruction are
legitimate and `PlacementObservationTarget::Write` carries a per-occurrence
block precisely to distinguish them.
### Adding an SSA operation: there are three tables, not two

`SSAOp` has a catch-all in most of the matches that key on it, so a new variant
compiles with every one of them missed. Three of those decide whether the
operation reaches the renderer at all, and all three are needed:

* `machine.rs`, the expression lowering itself, or the operation falls through
  to `UnsupportedOperation`;
* `machine.rs`, `machine_kind_matches_op`, which pairs the operation with the
  expression kind it may produce;
* `machine.rs`, `machine_type_matches_op`, which says what type that expression
  has.

Missing the third is the one that reads oddly. The shape check fails, no entity
is built for the operation's output, and validation reports `EntityMismatch`
naming an *instruction*, which sends a reader to look at the instruction rather
than at a type table that has never heard of the operation. `CallRestore` cost
two corpus cells that way -- `murmur3_32` and `xxhash32` at `x64_O0`, the only
two corpus functions that call anything -- and the reading took a locked run
while the fix was one line.

Beside them, two more decide whether it renders correctly rather than at all:
the statement lowering in `r2dec/fold/op_lower/implementation.rs`, and the
accounting -- an operation that renders no statement must still say what
happened to the values it read and wrote, or the seal refuses the function for
an unaccounted use and then for a write with no rendered occurrence.

The transferable part is that none of this needs the plugin. A regression in
any of the five reproduces in a unit test that builds the blocks and asks for
the machine projection, or for a rendering through
`source_owned_decompiler_input`, with no radare2 and no install lock -- seconds
rather than a ten-minute locked run. Both assertions now exist:
`a_call_leaves_the_stack_pointer_where_the_convention_says_it_found_it` in
`r2ssa::function` and `a_restored_stack_pointer_renders` in `r2dec`.

## A noise improvement that was two cells going missing

Earlier in this session the call-restore work appeared to reduce the noise
columns substantially, and reverting it appeared to put them back:

| column | "with" | "without" |
| --- | --- | --- |
| same-type casts | 136 | 185 |
| gotos | 39 | 55 |
| self-assignments | 148 | 155 |
| flag carriers | 183 | 192 |

That reading was wrong and the mechanism is worth naming, because it is the
third time this session the same trap has caught someone. The "with" column was
measured while `murmur3_32` and `xxhash32` at x64_O0 were **refusing**. A cell
that renders nothing contributes no noise, so removing two of the largest cells
from the corpus lowered every count. With the sealing order fixed, both cells
render again and the honest figures are the higher ones.

The same shape has now appeared three ways. A benchmark mean rose because a
function scoring zero stopped being decompiled and left the denominator. An
inlining attempt turned away every candidate and produced a green gate that had
done nothing. And here, a noise column fell because two cells vanished.

**A count over a population is only comparable when the population is.** Before
reading any improvement in a per-corpus total, check that the same cells are
present on both sides. The coverage report already records `decompiled` beside
each score for exactly this reason; the noise columns do not, and a
`cells_rendered` denominator printed beside them would make this class of
mistake impossible rather than merely detectable.

### Measured again after the call-restore work came back

The fix above was measured against the tree with the call-restore work
reverted. Integration reapplied it while this was in flight, so everything was
run again on the merged tree:

    cargo test --workspace                    2,066 passed, 0 failed
    locked_matrix.sh --gate differential      differential 54/54, raw 54/54,
                                              binding audit, effect obligations,
                                              placement audit and render refusal
                                              54/54 each
    locked_coverage.sh                        328 of 517 rendered

No cell refuses with `ambiguous_observation_execution_order` anywhere in the
sweep. Two things still make those two scripts exit non-zero and neither is
this work, both established by a controlled comparison rather than by
inference:

- **`x64_O0/murmur3_32` and `x64_O0/xxhash32` snapshot mismatches.** Rendering
  both cells with and without this change, on the merged tree, gives
  byte-identical output. `raw-baseline-sha256.json` was last blessed by
  `bc5a76e`, which is an ancestor of the reapply, so the recorded hashes
  describe the pre-reapply rendering. Whoever re-landed the call-restore work
  owes that re-bless.
- **`pinned_branchy_gcc_x64_O0::sym.pure_zero_guard` and `sym.slot_eq_guard`
  refusing with `ExactUseRequiresRenderedOccurrence`.** Both render in the
  whole-binary sweep taken from this worktree before the merge, with and
  without this change, so they arrived with the reapply. They are the second of
  the three regression families the coverage sweep found.

## The flag carriers are declared by their component, not by their value

Removing dead values from the binding plan left the flag-carrier count exactly
where it was, at 192, and the null result is more informative than the change.

The reasoning ran: 14,323 flag-named values on x86-64 at -O0 stay bound because
nothing reads them, so eliminating a value nothing reads should remove the
declaration. Dead values are now excluded from plan membership and their cells
closed, and the count did not move, because **a storage component that contains
a dead flag value usually also contains a live one**. The component survives,
and the declaration is minted from the component rather than from the value. So
the name on the page belongs to a binding that is genuinely needed; what is dead
is one member of it.

That is the third correction to this one framing. It was called an inlining
problem for as long as the noise gate existed; a probe showed the values were
unread rather than un-inlined; and now the declaration turns out not to be
per-value at all. Each correction came from measuring rather than reading, and
each was one level below the last.

The remaining work is therefore at component granularity: whether a component
whose live members are all architectural flags needs a name in the rendered C at
all, which is a different question from whether any of its values is dead.

Worth keeping from the same work: the reader audit found three more channels the
graph does not record, alongside the call arguments found earlier. Semantic
returns, switch selectors, and identity call-result carriers consumed by
derived-width results are all real readers with no use site, and they now share
one canonical path. Every one of them was a value that would have looked dead
and was not, so the zero-reader count is only safe to act on because they are
counted.

## The gates had Linux ELF coverage and it was the wrong ELF coverage

A merge candidate passed the fifty-four-cell corpus at 54 of 54, with the
differential agreeing against a source-built oracle, and rendered **zero of
fifteen functions** on the benchmark binary. Only the external benchmark caught
it, and only because it was run before merging rather than after.

The two pinned ELF programs did not catch it. They are compiled from the hash
and branch corpora, whose functions barely call anything, and the defect is at
the call boundary, so fifty-two of their sixty-eight functions kept rendering
while the platform was broken end to end. Two of them did regress, and those two
were judged minor against three hundred and twenty-eight rendering elsewhere.
They were the only call-boundary ELF cells in the tree and they were telling the
truth.

`shapes.c` compiled for ELF is now the third pinned program, and it is the gate
that has the sensitivity the others lack:

| population | rendered |
| --- | --- |
| macOS corpus binaries | 281 of 449 |
| pinned ELF, call-light | 52 of 68 |
| **pinned ELF, call-heavy** | **13 of 39** |

What it refuses on is the whole remaining defect list at once, which is why it is
the right canary: four projection authorisations from op lowering, four
`ExactUseRequiresRenderedOccurrence`, three `RenderedValueRequired`, three
`missing_definition`, three `unobserved_binding_write`, two
`unprovable_execution_order`, and two more projection authorisations from the
memory renderer and the call lowering.

Every one of those families has an owner already, and each was found on macOS.
The value of this cell is that it reproduces them **locally, without the VM**,
on the platform the project is scored against.

Two rules follow.

**Coverage of a platform is not coverage of a shape.** Three ELF programs is not
three times the confidence if all three are compiled from sources with the same
control-flow vocabulary. Ask what a corpus *exercises*, not what it targets.

**A change reverted for failing one measurement re-lands on that measurement.**
The call-restore work was reverted because the benchmark fell from seven
functions to one. A real defect in it was then found and fixed, the macOS corpus
went green, and it was reapplied on that evidence alone. The benchmark was never
re-run, and the regression it had been reverted for was still there.

## The Sleigh instance cannot be shared, and the commit that shared it was wrong

The per-function cost was traced to `Disassembler::from_trusted_profile`
re-parsing the whole compiled `.sla` on every lift, and the fix was to load each
embedded profile once. **That fix is withdrawn. It returned wrong instructions.**

A `GhidraSleigh` instance caches decoded instructions by address. Sharing one
across lifts therefore returns the *first* decode whenever a later lift asks
about the same address with different bytes:

    one instance,   0x1000, 88 d8  (mov al, bl)  ->  AL
    one instance,   0x1000, 88 dc  (mov ah, bl)  ->  AL     wrong
    fresh instance, 0x2000, 88 dc  (mov ah, bl)  ->  AH

Two of this crate's own tests state exactly this and both failed the moment the
sharing moved into the constructor they exercise.
`x86_byte_register_writes_do_not_invent_full_carrier_zero_extensions` builds a
disassembler per loop iteration and lifts both instructions at 0x1000;
`genuine_lift_binds_full_bytes_to_one_opaque_session` asserts two loads do not
share a session. The original sharing commit passed every gate because it cached
in a *separate function* that only `lift_owned_function` called, leaving the
constructor the tests exercise parsing its own copy. **A cache one layer below
the guard is a cache the guard cannot see**, and that is the transferable
lesson: put a cache where the existing tests already look, or the tests are
measuring the uncached path.

It is reachable in production wherever one process sees one address twice with
different bytes: a second binary opened in the same radare2 session, two
position-independent executables both based at zero, or bytes patched and
re-analysed. Single-binary analysis never repeats an address, which is why the
corpus and coverage gates could not have caught it -- each cell is its own
process and its own binary. The gates are not a substitute for the unit tests
here, and this is the second time in two days that a defect was invisible to
them.

**The decision this leaves.** The parse is where the time is:

    x86-64, per load        parse   register table   architecture extraction
                          84-295ms       1.4-67ms                    3-9ms

So sharing only the immutable derived tables saves almost nothing, and the speed
can only come back by flushing the decode cache rather than duplicating the
instance. `ghidra::Sleigh::clearCache` does precisely that; the `libsla-sys`
bridge this project pins does not expose it. Three ways forward, and the choice
is the owner's because two of them change a dependency this project forks:

1. *Expose `clearCache` in the `libsla-sys` fork and call it per lift.* Correct
   and fast, one small commit to `0verflowme/libsla-sys`. The clear is cheap
   next to a parse. This is the fix at the cause.
2. *Track, per shared specification, the address ranges already decoded, and
   reload the instance when one is asked for again with different bytes.*
   In-tree and sound -- it never returns a stale decode -- but it is machinery
   in this repository to work around a missing upstream call, and the memory is
   one entry per decoded block.
3. *Leave it unshared,* which is where the tree is now: correct, and paying the
   parse per lift.

Until one is taken, the per-function cost the previous section attributed to the
profile load is back. What is *not* withdrawn is the structural half:
`LoadedSpecification` separates what a specification derives from what a caller
derives, so `create_disassembler_for_arch` now gets its architecture and its
disassembler from one load rather than two hand-written parses of the same
bytes, and the lift authority is minted from that one load. Immutable derived
data can be shared; the decoder cannot.

**Every uninterleaved before-and-after on the shared host is unproven**, this
document's profile-load figures included. They were taken as two blocks minutes
apart and the machine's load drifts over minutes; the one interleaved comparison
run here turned an apparent fourfold win into nineteen per cent. A private
`HOME` per column stops another agent overwriting the plugin, and only
interleaving stops the machine overwriting the answer.
