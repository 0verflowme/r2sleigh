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
canonical facts + evidence -> closed typed ledger -> opaque typed-output seal
```

Owners
------

- `../radare2`: typed function/type/import/debug context and dirty epochs.
- `r2ssa`: CFG, def-use, memory, stack, callsite, return, and control
  certificates.
- `r2sym`: source-bound semantic evidence, semantic claims, summary
  applicability, ambiguity, and refusal policy.
- `r2types`: type/layout/signature projection from typed context and semantic
  evidence.
- `r2engine`: request-local typed-route selection by exact owners, budgets, and
  refusal.
- `r2dec`: rendering only from typed-output seals, certificates, and residuals.
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

The current source-owned spine provides:

- structural certificate carriers in `r2ssa::PreparedFunctionFacts`
- an advisory report DTO in `r2types::FunctionFacts`
- runtime authority in `r2types::SourceOwnedFunctionFacts`, which retains the
  exact `Arc<r2ssa::SsaArtifact>` used to derive the report
- typed engine route diagnostics with no detached counter or legacy permission
  compatibility layer
- `r2dec` gates that render semantic-kernel C only from exact typed-region seals
  and otherwise emit summary comments, residuals, or refusals
- closure-gate checks for incomplete reports and fake-output counters

The remaining rewrite work is to make expression, memory/layout, callsite, and
signature rendering consume certificates directly instead of legacy local repair
paths.
