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
     | narrow carrier member read after a loop (`eax_5`, `eax_8`, `eax_12`/`ecx_9`, `rcx_6`) | 4 | x64 -O1/-O2 |
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

     Two of these look cheap and are not. `uint128_t` comes from `CType::UInt(128)`
     printing `uint{bits}_t` in `ast.rs:129`, but the reason a 128-bit type is
     there at all is that a 32-bit table is being read 128 bits wide:
     `((uint128_t*)0x100000000U)[245]`. Spelling it `__uint128_t` would move the
     verdict from `nocompile` to `wrong`, not to `CORRECT`, so it belongs to the
     width layer and not to naming. Likewise `sym__rotl32` compiles once declared
     but cannot link, because the harness builds one function per file.

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

     Note that this is the *third* place the same rule is needed, which is an
     argument for putting it somewhere shared: `carrier_member_views` in
     `normalize.rs` applies it to header phis, `exit_merges_for_carrier` was
     widened to apply it to exit merges and measured inert because those values
     are not phis either, and carrier growth needs it for writes. All three ask
     the same question -- is this value the carrier's place at another width --
     and all three answer it separately.

     Also still recorded: using the selector value instead of
     `prepared_canonical_value_root` of it changes nothing, because there was no
     selector to root.

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