Questions this tree answers more than once
==========================================

Every defect found in the sessions that produced this document had the same
shape: two components each held half of one fact, and nothing reconciled them.
That is not an argument against asking a question twice. The binding plan
derives its components twice on purpose, and the duplication is the proof. It
is an argument against *stating a rule* twice, because two independently
written statements of one rule are two answerers, and answerers drift.

The arrangement that works is already in the tree:
`crates/r2dec/src/binding_plan/rules.rs` holds the rules, and the construction
and seal passes keep their own traversals while calling them. This document is
the inventory of everywhere else the same question is asked, what was done
about it, and what is still open.

Collapsed
---------

**What reaches a function's return register.** Asked by
`liveout::FunctionLiveOut::collect_reaching`, to recover the interface before
any machine context exists, and again by
`semantic::reaching_abi_return_register_in_block` at the return boundary with
one. Two different questions about different inputs, which is legitimate; two
different rules, which was not. The liveout walk read only each operation's
destination and passed straight through a call, naming whatever had been put in
the register before it -- for a function whose last act is `warnx(fmt, ...)`,
the format string, recovered as the value the function returns. Nothing rendered
it only because the stricter walk refused the boundary afterwards. That is luck,
not design.

The rule now lives in `crates/r2ssa/src/reaching_rules.rs` and both walks call
it. Sharing it surfaced two further divergences immediately, both of which had
to be decided rather than preserved. `Return` was a stop in the strict walk
only; it is a boundary rather than a writer, each walk already knows where its
own boundary is, and treating it as a stop made the liveout walk halt on its own
starting point. `CallDefine` was a stop in the strict walk only; it is the
operation that names a call's result, so stopping on it refuses to see the value
a function returning `f(x)` hands back.

**Whether a name is one radare2 generated for an unnamed parameter.**
`is_generic_arg_name` existed byte-identically in `r2types` and in `r2dec`,
which already depends on it. `r2dec` now re-exports it.

**Whether a signature type says nothing.** `is_generic_signature_type` existed
three times in `r2types`: the answer in `facts.rs`, a delegating alias in
`writeback.rs`, and a private copy of the body in `context.rs` -- in a module
whose neighbouring `signature_param_count_is_authoritative` already delegated to
`facts`. The copy now delegates too.

Deliberately duplicated, with the rule shared
---------------------------------------------

**Which values belong to one binding.** `binding_plan::construction` unions as
it walks the certificates; `binding_plan::seal` recomputes the components by a
sorted traversal that cannot see the first pass's representatives, schedule or
accumulator. Both call `binding_plan::rules`. This is the pattern the rest of
this document is measured against.

Open
----

**Whether a call argument obligation can be discharged.**
`r2ssa::obligation` seeds a `CallArgument` obligation for a
`SourceCallArgumentValue::PreservedEntry` argument with an empty input list, and
says why: the function never defines the carrier, so no SSA value names it, but
the call reads it either way. `r2dec::fold::context` requires
`!obligation.inputs.is_empty()` and that every input appear in the rendered
call's proof values. The two are not two answerers to one question -- they are
the two halves of a contract that do not meet, and no rendering can satisfy the
obligation as seeded. Four functions on `/bin/ls` refuse for it. The refusal now
says so outright under `R2DEC_TRACE_REFUSAL`; closing it needs the parameter to
exist and to be passed, which reaches `recover_interface` and the value-keyed
call-argument rendering.

**Whether two rendered occurrences can both happen.** Asked by placement, as
"are these regions nested"; by `first_read_before_assignment`, as a
must-assignment dataflow over blocks; and by the effect ledger, as "is more than
one occurrence a duplicate". The third now asks the region tree through
`SealedStructuredRegionArtifact::regions_are_exclusive`, and the first was
relaxed to exempt a region that assigns before it reads. They still reason over
different domains -- regions, blocks, occurrences -- and whether that is three
questions or one stated three ways has not been settled.

**Which register is the stack pointer.** `disasm::is_stack_register` matches a
hand-written list per architecture family. The ROADMAP carries this as debt
against the compiler specification, which states it; it is listed here because
a hand-written list is an answerer, and when the specification-derived answer
lands there will be two.
