r2sleigh Certifying Decompiler
==============================

Purpose
-------

The decompiler must render high-level C only when canonical checked facts justify
the construct. If the proof is missing, ambiguous, or owned by the wrong layer,
the output must be a residual, summary comment, or refusal.

This is not a full formal verification system. It is a local proof kernel for
the decompiler pipeline:

```
canonical facts + evidence -> checked claim -> render permission
```

Owners
------

- `../radare2`: typed function/type/import/debug context and dirty epochs.
- `r2ssa`: CFG, def-use, memory, stack, callsite, return, and control
  certificates.
- `r2sym`: semantic evidence, semantic claims, proof vocabulary, summary
  applicability, ambiguity, and refusal policy.
- `r2types`: type/layout/signature projection from typed context and semantic
  evidence.
- `r2engine`: request-local route selection by proof coverage, budgets, and
  refusal.
- `r2dec`: rendering only from render permissions, certificates, and residuals.
- `r2plugin`: typed context collection, FFI, command dispatch, and apply/render
  glue only.

Output Authority
----------------

- Executable C requires an opaque `CertifiedTypedOutputSeal` backed by checked
  canonical facts, a closed ledger, and exact typed owners.
- `SummaryComment`: output is intentionally summary-driven and visibly marked.
- `Residual`: facts are insufficient for structured C, but partial information
  can be rendered honestly.
- `Refuse`: analysis crossed a proof, cost, or evidence boundary.

Required Certificates
---------------------

- `LoopCertificate`: header, latches, body, exits, and optional condition.
- `SwitchCertificate`: selector, cases, targets, and optional default.
- `IfRegionCertificate`: predicate and true/false targets.
- `ExpressionCertificate`: value and defining instruction provenance.
- `MemoryAccessCertificate`: object, address, value, width, and write/read flag.
- `StackSlotCertificate`: canonical stack object, base, and offset.
- `CallsiteCertificate`: instruction, target, direct target, and fallthrough.
- `ReturnValueCertificate`: return instruction and returned value.

Rules
-----

1. Do not render `while`, `for`, `do`, or `switch` without the matching
   certificate.
2. Do not invent case values, locals, stack slots, call arguments, signatures, or
   struct fields.
3. Name hints are weak evidence only. They cannot grant executable C authority.
4. Cache hits and budget caps never justify semantics.
5. Any downstream cleanup that hides missing upstream facts is a correctness bug.
6. Closure gates must fail on incomplete status, timeouts, executable semantic
   oracle failures, fake semantics, undefined identifiers, and raw temp/stack
   leaks. Source-shape text comparisons remain advisory.

Current Implementation State
----------------------------

The first tranche adds:

- proof vocabulary in `r2sym`
- structural certificate carriers in `r2ssa::PreparedFunctionFacts`
- proof coverage in `r2types::FunctionFacts`
- engine route diagnostics carrying proof coverage
- an initial `r2dec` gate that residualizes standard loop/switch output when
  prepared control certificates are missing
- closure-gate checks for incomplete reports and fake-output counters

The remaining rewrite work is to make expression, memory/layout, callsite, and
signature rendering consume certificates directly instead of legacy local repair
paths.
