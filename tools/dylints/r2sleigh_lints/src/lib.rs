#![feature(rustc_private)]
#![warn(unused_extern_crates)]

extern crate rustc_ast;
extern crate rustc_hir;
extern crate rustc_lint;
extern crate rustc_session;
extern crate rustc_span;

use clippy_utils::diagnostics::span_lint;
use rustc_ast::LitKind;
use rustc_hir::{Expr, ExprKind, ImplItem, Item, QPath};
use rustc_lint::{LateContext, LateLintPass, LintContext};

dylint_linting::dylint_library!();

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when semantic storage/address classification is encoded as
    /// `starts_with` checks against string prefixes such as `tmp:`, `const:`,
    /// `ram:`, `sym.`, or `obj.`.
    ///
    /// ### Why is this bad?
    ///
    /// In r2sleigh those prefixes identify canonical IL/storage/address facts.
    /// Repeating prefix checks across crates creates parallel ownership and lets
    /// render/type/plugin code infer semantics that should arrive through typed
    /// contracts.
    ///
    /// ### Example
    ///
    /// ```rust
    /// if name.starts_with("tmp:") {
    ///     // stringly semantic classification
    /// }
    /// ```
    ///
    /// Use instead:
    ///
    /// ```rust
    /// match storage_kind {
    ///     StorageKind::Temporary => {}
    ///     _ => {}
    /// }
    /// ```
    pub STRING_PREFIX_SEMANTIC_CLASSIFICATION,
    Warn,
    "semantic classification should use typed contracts, not string prefixes"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when internal Rust code embeds radare2 JSON command strings that
    /// are banned as plugin data sources, such as `afcfj`, `afvj`, or `tsj`.
    ///
    /// ### Why is this bad?
    ///
    /// The plugin may expose user-visible commands, but internal analysis must
    /// use typed collector APIs. Re-parsing radare2 command JSON creates a
    /// second source of truth and hides missing typed fields.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let facts = r2.cmd_str("afcfj");
    /// ```
    ///
    /// Use instead a typed collector payload owned by the radare2 seam.
    pub R2_JSON_COMMAND_INTERNAL_SEAM,
    Warn,
    "internal radare2 data seams should use typed collectors, not command JSON"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` indexes `known_function_signatures` directly.
    ///
    /// ### Why is this bad?
    ///
    /// Signature lookup depends on the same alias, direct-address, import, and
    /// evidence rules as callee identity. Letting the renderer index the raw
    /// signature map recreates type policy downstream and can confuse type
    /// evidence with import evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// inputs.known_function_signatures.get(name);
    /// ```
    ///
    /// Use instead `r2types::CalleeIdentity` query methods, such as
    /// `known_signature()` or `non_variadic_known_arity()`.
    pub R2DEC_DIRECT_KNOWN_SIGNATURE_LOOKUP,
    Warn,
    "r2dec should query signatures through typed callee identity, not the raw signature map"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` analysis code reconstructs imported-callee or
    /// imported-like call-argument policy instead of consuming typed
    /// `CalleeResolutionFacts` target resolution.
    ///
    /// ### Why is this bad?
    ///
    /// Import/model classification depends on the same callsite, direct-address,
    /// summary, callee-fact, and typed-signature evidence as callee identity.
    /// Rebuilding it in analysis from raw names or partial identity lookups
    /// creates a second owner and lets raw hints override typed facts.
    ///
    /// ### Example
    ///
    /// ```rust
    /// r2types::callee_name_is_import_like(name);
    /// facts.identity_for_callsite(site).is_some_and(|id| id.is_import_policy_authorized());
    /// ```
    ///
    /// Use instead `CalleeResolutionFacts::resolve_target_identity(...)` or
    /// `CalleeResolutionFacts::resolve_target_policy(...)`.
    pub R2DEC_RAW_CALLEE_IMPORT_POLICY,
    Warn,
    "r2dec analysis should use typed callee resolution for import policy"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` op-lowering code parses call-target addresses through
    /// a local helper or direct `ram:` / `const:` prefix handling.
    ///
    /// ### Why is this bad?
    ///
    /// Call-target address interpretation is part of typed callee resolution and
    /// the shared decompiler address parser. Recreating it in lowering creates a
    /// second owner for call identity and lets rendering bypass
    /// `CalleeResolutionFacts`.
    ///
    /// ### Example
    ///
    /// ```rust
    /// extract_call_address(name);
    /// self.prepared_constish_target_addr(target);
    /// name.strip_prefix("ram:");
    /// ```
    ///
    /// Use instead `crate::address::parse_address_from_var_name()` or a
    /// `CalleeResolutionFacts` lookup.
    pub R2DEC_RAW_CALL_TARGET_ADDRESS_PARSER,
    Warn,
    "r2dec op-lowering should use typed callee resolution or the shared address parser"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` op-lowering code reconstructs call-target policy from
    /// imported-name authorization, raw callsite identity lookups,
    /// summary-helper lookups, or local modeled target helpers.
    ///
    /// ### Why is this bad?
    ///
    /// Imported/modeled call behavior is a typed callee-contract decision. If
    /// the renderer recomputes it from aliases, helper summaries, or callee
    /// facts, raw rendered names can override callsite evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// identity.is_import_policy_authorized();
    /// facts.identity_for_callsite(callsite);
    /// self.summary_helper_view_for_name(alias);
    /// self.is_modeled_callee_identity(identity);
    /// direct_target_context: Some(&ctx);
    /// ```
    ///
    /// Use instead `CalleeResolutionFacts::resolve_target_policy()` through the
    /// renderer's typed callee target resolver.
    pub R2DEC_CALL_TARGET_POLICY_OWNERSHIP,
    Warn,
    "r2dec op-lowering should consume typed callee target policy instead of recomputing it"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` builds or reconstructs callee resolution
    /// internally from raw context.
    ///
    /// ### Why is this bad?
    ///
    /// Callee resolution is an engine/type-system contract. If the decompiler
    /// reconstructs it from prepared callsites, raw maps, or direct context
    /// identity helpers, rendering becomes a second owner for call identity and
    /// can silently turn missing engine facts into confident callee policy.
    ///
    /// ### Example
    ///
    /// ```rust
    /// CalleeResolutionFacts::from_direct_call_targets(targets, &ctx);
    /// CalleeResolutionFacts::identity_for_direct_target_in_context(None, addr, &ctx);
    /// CalleeResolutionFacts::identity_for_name_in_context(name, &ctx);
    /// ```
    ///
    /// Pass the engine-owned `CalleeResolutionFacts` through
    /// `FunctionFacts::with_callee_resolution()` instead.
    pub R2DEC_CALLEE_RESOLUTION_FALLBACK_OWNERSHIP,
    Warn,
    "r2dec must not synthesize CalleeResolutionFacts; r2engine owns callee resolution"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` call-argument rendering policy authorizes a nested
    /// call argument by asking whether its rendered callee is imported or
    /// modeled.
    ///
    /// ### Why is this bad?
    ///
    /// A rendered callee name is not proof that a nested call argument is safe
    /// to emit as executable C. Public call arguments may contain a call only
    /// when a certified render proof authorizes that callsite and argument
    /// value. Otherwise the renderer must emit an explicit unresolved argument
    /// or residual/refusal.
    ///
    /// ### Example
    ///
    /// ```rust
    /// if self.is_imported_call_target(func) {
    ///     return false; // source-less nested call accepted
    /// }
    /// ```
    ///
    /// Use instead the certified public call-argument gate, such as
    /// `proven_source_for_public_call_arg_call(...)`, and fail closed.
    pub R2DEC_UNCERTIFIED_CALL_ARG_CALL_POLICY,
    Warn,
    "r2dec call arguments must not authorize nested calls from rendered callee policy"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` call-argument render authorization treats
    /// `CallArgBinding::source_var_name` as standalone proof.
    ///
    /// ### Why is this bad?
    ///
    /// A source variable name is a rendered hint, not evidence that the call
    /// argument is safe to emit as executable C. Call arguments may render from
    /// exact value/call provenance, or from a source name only after it resolves
    /// through prepared semantic evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// binding.source_var_name.is_some()
    /// ```
    ///
    /// Use instead a helper that ties the name back to prepared SSA/semantic
    /// ownership before accepting it.
    pub R2DEC_CALL_ARG_SOURCE_NAME_AUTHORITY,
    Warn,
    "r2dec call-argument rendering must not treat source_var_name as standalone authority"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` call-argument render authorization treats
    /// `CallArgBinding::source_call` as standalone proof.
    ///
    /// ### Why is this bad?
    ///
    /// A source call proves where a value came from; it does not prove that the
    /// call argument is safe to emit as executable C. Argument rendering must
    /// be backed by a certified value ID or prepared semantic authority.
    ///
    /// ### Example
    ///
    /// ```rust
    /// binding.source_call.is_some()
    /// ```
    ///
    /// Use instead the certified callsite argument contract carried through
    /// `FunctionFacts`, or fail closed with a residual.
    pub R2DEC_CALL_ARG_SOURCE_CALL_AUTHORITY,
    Warn,
    "r2dec call-argument rendering must not treat source_call as standalone authority"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` call-argument rendering can fall through
    /// to local raw `CallArgBinding` inference without a prepared
    /// `FunctionFacts` callsite contract.
    ///
    /// ### Why is this bad?
    ///
    /// Matching a raw argument binding to an SSA value ID is still local
    /// renderer repair unless the argument list was projected through
    /// `FunctionFacts`. Certified executable calls must consume prepared
    /// callsite facts or residualize.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let args = self.render_call_args_for_site_with_direct_target(..., raw_args);
    /// self.call_arg_binding_has_render_authority(binding);
    /// ```
    ///
    /// Match raw argument source values against
    /// `CallsiteArgumentFacts::canonical_argument_values()` before rendering.
    pub R2DEC_CERTIFIED_RAW_CALL_ARG_FALLBACK,
    Warn,
    "certified r2dec call arguments must come from FunctionFacts, not local raw arg fallback"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified call proof validation compares rendered argument
    /// values against only a prefix of `FunctionCallsiteFacts.argument_values`.
    ///
    /// ### Why is this bad?
    ///
    /// A prefix match lets a renderer emit fewer call arguments than the
    /// canonical callsite contract proves. Certified executable calls must
    /// match the full typed callsite argument vector or residualize.
    ///
    /// ### Example
    ///
    /// ```rust
    /// cert.argument_values.iter().take(proof.values.len())
    /// ```
    ///
    /// Compare proof values against every `FunctionCallsiteFacts` argument
    /// value.
    pub R2DEC_CERTIFIED_CALL_ARG_PREFIX_PROOF,
    Warn,
    "certified r2dec call argument proofs must match the full FunctionFacts callsite vector"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when generic `r2dec` SSA-op statement lowering emits a direct
    /// zero-argument call fallback for `SSAOp::Call` or `SSAOp::CallInd`.
    ///
    /// ### Why is this bad?
    ///
    /// Certified executable calls require callsite target and argument evidence
    /// from `FunctionFacts`. The generic lowering path has no callsite frame,
    /// so rendering `foo()` locally fabricates an executable call when the
    /// typed callsite contract is missing or bypassed.
    ///
    /// ### Example
    ///
    /// ```rust
    /// SSAOp::Call { .. } => Some(CStmt::Expr(CExpr::call(func_expr, vec![])))
    /// ```
    ///
    /// Return a residual comment in certified rendering and use
    /// `op_to_stmt_with_args` for call-aware lowering.
    pub R2DEC_DIRECT_ZERO_ARG_CALL_FALLBACK,
    Warn,
    "r2dec direct call lowering must residualize instead of emitting zero-arg fallback calls"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` call-result replay can use cached
    /// `call_result_exprs` or alias definitions before trying the certified
    /// synthesized call expression.
    ///
    /// ### Why is this bad?
    ///
    /// Cached rendered calls and alias definitions are local renderer state.
    /// In certified mode, replaying a call result as executable C must use the
    /// certified callsite/argument proof carried through the prepared
    /// `FunctionFacts` path.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.call_result_exprs_map().get(&source_call)
    ///     .or_else(|| self.synthesized_call_expr_for_source_call(source_call))
    /// ```
    ///
    /// Use the synthesized certified call first in certified mode and only keep
    /// cached/alias fallback for legacy non-certified rendering.
    pub R2DEC_CERTIFIED_CALL_RESULT_REPLAY_FALLBACK,
    Warn,
    "certified r2dec call-result replay must use certified synthesized calls before cached fallback"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` accepts prepared rendered call-argument
    /// expressions as executable call arguments.
    ///
    /// ### Why is this bad?
    ///
    /// Prepared `CExpr` argument text is a renderer convenience view, not the
    /// decompile evidence contract. Certified calls must render arguments from
    /// `FunctionCallsiteFacts` argument values plus render evidence, otherwise
    /// prepared aliases, owner names, or cached definitions can become fake
    /// executable C.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.prepared_call_args_for_site_with_direct_target(...)
    /// ```
    ///
    /// In certified mode, build call arguments from the FunctionFacts value
    /// vector; keep prepared argument rendering for non-certified display only.
pub R2DEC_CERTIFIED_PREPARED_CALL_ARG_EXPR_PROOF,
    Warn,
    "certified r2dec call arguments must not use prepared argument expression text as authority"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified executable lowering repairs post-call values from
    /// local renderer state.
    ///
    /// ### Why is this bad?
    ///
    /// Local post-call repair, cached call-result expressions, and raw
    /// definitions are compatibility paths. Certified executable C must flow
    /// from FunctionFacts render/call-result proof, otherwise the renderer can
    /// recover plausible call results without canonical evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.local_post_call_source_for_ssa_name(...)
    /// self.recovered_owned_call_result_definition_rhs(...)
    /// ```
    ///
    /// In certified mode, emit a residual unless FunctionFacts authorizes the
    /// value and rendered expression.
    pub R2DEC_CERTIFIED_EXECUTABLE_POST_CALL_REPAIR,
    Warn,
    "certified r2dec executable lowering must not repair post-call values from local renderer state"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified rendered-call proof collection discovers source
    /// calls by comparing local cached call expressions.
    ///
    /// ### Why is this bad?
    ///
    /// Equality against `call_result_exprs` or raw source-owner definitions is
    /// local renderer state, not a canonical callsite proof. Certified rendered
    /// calls must be tied to the current source call and FunctionFacts
    /// call-render disposition.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.source_matches_for_call_expr(call)
    /// self.call_result_exprs_map()
    /// ```
    ///
    /// Use current-source-call proof and FunctionCallRenderFacts instead.
    pub R2DEC_CERTIFIED_CALL_RENDER_PROOF_LOCAL_EQUALITY,
    Warn,
    "certified rendered-call proof must not be recovered from local cached call-expression equality"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` return rendering can choose local semantic
    /// or visible definitions before deriving the returned expression from a
    /// prepared `ReturnValueCertificate` / `ExpressionCertificate`.
    ///
    /// ### Why is this bad?
    ///
    /// A certified return proof identifies the returned SSA value, but local
    /// renderer definitions can still be poisoned or source-shaped. Executable
    /// return C must be rendered from prepared evidence or residualize.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.best_visible_definition(&target.display_name())
    /// ```
    ///
    /// Use `certified_return_expr_for_op` first in certified mode and keep local
    /// expression ranking only for legacy non-certified rendering.
    pub R2DEC_CERTIFIED_RETURN_LOCAL_EXPR_FALLBACK,
    Warn,
    "certified r2dec returns must render from prepared return evidence before local expression fallback"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` return-call rendering treats a prepared
    /// SSA call-result certificate as enough proof without requiring the
    /// canonical `FunctionCallResultFacts` result fact.
    ///
    /// ### Why is this bad?
    ///
    /// Prepared SSA certificates are construction evidence. The decompile
    /// render gate must consume the typed `FunctionFacts` contract; otherwise
    /// a return value can become executable `return callee(...)` without the
    /// canonical call-result fact carried through `r2engine`.
    ///
    /// ### Example
    ///
    /// ```rust
    /// prepared.call_result_certificate_for_value(value)
    /// ```
    ///
    /// Use `certified_call_result_fact_for_value(value)` before synthesizing
    /// the returned call expression.
    pub R2DEC_CERTIFIED_RETURN_CALL_RESULT_FACT,
    Warn,
    "certified r2dec return-call rendering must require FunctionFacts call-result evidence"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` local post-call source recovery can scan
    /// local SSA adjacency for a source call.
    ///
    /// ### Why is this bad?
    ///
    /// A nearby `CallDefine`, copy chain, or stack reload is useful discovery
    /// evidence, but it is not the typed decompile contract. Certified
    /// rendering must use FunctionFacts/prepared call-result provenance
    /// directly instead of rediscovering it in `r2dec`.
    ///
    /// ### Example
    ///
    /// ```rust
    /// local_post_call_source_for_ssa_name_in_block(...)
    /// ```
    ///
    /// Return `None` immediately in certified mode and use the canonical
    /// call-result source lookup instead.
    pub R2DEC_CERTIFIED_LOCAL_POST_CALL_SOURCE_FACT,
    Warn,
    "certified r2dec local post-call source recovery must not scan local SSA adjacency"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` analysis defines helpers that infer
    /// authoritative call arguments locally.
    ///
    /// ### Why is this bad?
    ///
    /// Call arguments are executable C only after upstream SSA evidence has
    /// been carried through `r2types::FunctionFacts`. A decompiler-local
    /// `infer_call_authoritative_arg*` helper recreates callsite ownership
    /// downstream and can render plausible arguments without the canonical
    /// contract.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn infer_call_authoritative_args(...) { ... }
    /// ```
    ///
    /// Use instead `FunctionFacts` callsite argument facts populated by
    /// `r2engine` from `r2ssa` certificates.
    pub R2DEC_LOCAL_AUTHORITATIVE_CALL_ARG_INFERENCE,
    Warn,
    "r2dec must not infer authoritative call arguments outside FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when summary-only `r2dec` rendering paths emit executable-looking
    /// C constructs such as `switch`, `case`, `break`, or `return`.
    ///
    /// ### Why is this bad?
    ///
    /// Summary evidence is not native CFG/control/dataflow proof. Summary
    /// routes may render facts, comments, residuals, or refusals, but they must
    /// not present executable C as if control flow had been reconstructed.
    ///
    /// ### Example
    ///
    /// ```rust
    /// writeln!(out, "    switch ({selector}) {{");
    /// ```
    ///
    /// Use instead comment/fact rendering such as:
    ///
    /// ```rust
    /// writeln!(out, "    /* selector: {selector} */");
    /// ```
    pub R2DEC_SUMMARY_ROUTE_EXECUTABLE_C,
    Warn,
    "summary routes must render comments/facts, not executable C"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when summary-only `r2dec` renderer files construct executable
    /// `CStmt` nodes such as returns, branches, loops, switches, or expression
    /// statements without an explicit CertifiedC permission gate.
    ///
    /// ### Why is this bad?
    ///
    /// Summary routes may emit comments/facts/residuals only. Building
    /// executable AST nodes in summary renderers creates a path where
    /// summary-only evidence can become native-looking C without going through
    /// the certified `FunctionFacts` render contract.
    ///
    /// ### Example
    ///
    /// ```rust
    /// vec![CStmt::Return(Some(expr))]
    /// ```
    ///
    /// Use `CStmt::comment(...)` or residualize unless the enclosing function
    /// has explicitly checked `RenderPermissionKind::CertifiedC`.
    pub R2DEC_SUMMARY_RENDER_EXECUTABLE_CSTMT,
    Warn,
    "summary/VM renderers must not construct executable CStmt bodies without CertifiedC permission"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` code owns semantic route selection,
    /// fallback selection, CFG guard policy, or detached semantic route planning.
    ///
    /// ### Why is this bad?
    ///
    /// `r2dec` is a renderer. Route/refusal policy belongs in `r2engine`, where
    /// it can account for cache state, prepared facts, semantic evidence,
    /// budgets, and request kind consistently. If `r2dec` grows route helpers
    /// again, consumers can bypass engine refusal policy and make summary/fake C
    /// look like native reconstruction.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn semantic_route_plan(...) -> SemanticRoutePlan {
    ///     // renderer-owned routing policy
    /// }
    /// ```
    ///
    /// Use `r2types::DecompileRouteFacts` on `FunctionFacts` as the render
    /// boundary. `r2dec` must not define a local route enum or route adapter.
    pub R2DEC_ROUTE_POLICY_OWNERSHIP,
    Warn,
    "r2dec must consume engine route decisions, not own route/refusal policy"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` treats a missing `FunctionFacts::decompile_route` as
    /// any locally synthesized route.
    ///
    /// ### Why is this bad?
    ///
    /// Missing route facts mean the engine did not certify a render route.
    /// Defaulting that case to any renderer-minted route bypasses the typed
    /// spine and can turn missing engine policy into renderer policy.
    ///
    /// ### Example
    ///
    /// ```rust
    /// DecompileRouteFacts { kind: DecompileRouteKind::FallbackComment, ... }
    /// ```
    ///
    /// Residualize or refuse instead.
    pub R2DEC_MISSING_DECOMPILE_ROUTE_DEFAULT_STANDARD,
    Warn,
    "r2dec must residualize missing FunctionFacts::decompile_route without synthesizing a route"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec::Decompiler` exposes the removed raw
    /// `build_function(&SSAFunction)` API, or when the prepared AST builder can
    /// construct an executable `CFunction` without first checking
    /// `FunctionFacts::decompile_route`.
    ///
    /// ### Why is this bad?
    ///
    /// `SSAFunction` alone has no prepared SSA artifact or canonical
    /// `FunctionFacts` evidence. Keeping the raw AST builder as a compatibility
    /// entrypoint lets downstream callers bypass the engine-owned render
    /// contract.
    ///
    /// ### Example
    ///
    /// ```rust
    /// pub fn build_function(&self, func: &SSAFunction) -> CFunction {
    ///     ...
    /// }
    /// ```
    ///
    /// Use only `build_function_from_input(&DecompilerInput)` and require route
    /// facts before executable AST rendering.
    pub R2DEC_BUILD_FUNCTION_REQUIRES_ROUTE_FACTS,
    Warn,
    "r2dec must not expose raw SSAFunction build_function; prepared input must require FunctionFacts::decompile_route"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when public `r2dec` semantic-summary render entrypoints accept a
    /// caller-supplied `SemanticRoutePlan`, or render VM summaries without
    /// checking `FunctionFacts::decompile_route`.
    ///
    /// ### Why is this bad?
    ///
    /// The decompile route is part of the canonical `FunctionFacts` contract.
    /// A separate route argument lets r2engine or direct callers render summary
    /// output under a policy that differs from the facts payload and cache key.
    ///
    /// ### Example
    ///
    /// ```rust
    /// pub fn render_semantic_worker_summary(..., route: &SemanticRoutePlan, ...)
    /// pub fn render_vm_semantic_summary(..., type_facts: &FunctionTypeFacts, ...)
    /// ```
    ///
    /// Read `FunctionFacts::decompile_route()` and require the matching summary
    /// render permission before emitting summary output.
    pub R2DEC_SUMMARY_RENDER_ROUTE_SIDE_CHANNEL,
    Warn,
    "r2dec summary rendering must derive route permission from FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` expands or repairs a certified external/header
    /// signature with locally recovered parameters or return types.
    ///
    /// ### Why is this bad?
    ///
    /// Function header arity is a typed contract owned by `FunctionFacts`.
    /// Letting local variable recovery append extra ABI-looking params or
    /// letting runtime type inference fill a return type makes the renderer a
    /// second signature owner.
    ///
    /// ### Example
    ///
    /// ```rust
    /// recovered_params.len().max(signature.params.len())
    /// ```
    ///
    /// Use the render-authorized signature for executable headers.
    pub R2DEC_LOCAL_HEADER_ARITY_REPAIR,
    Warn,
    "r2dec must not repair certified headers from local recovery or inference"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2engine` applies decompile route, render permission, or
    /// callsite/callee evidence by filling request/context side-channel fields.
    ///
    /// ### Why is this bad?
    ///
    /// The decompile spine is `FunctionFacts`. Engine-owned route, refusal,
    /// proof coverage, render permission, and callee resolution must travel through
    /// `FunctionFacts`; otherwise plugin/decompiler callers
    /// can observe different policy depending on which side channel was set.
    ///
    /// ### Example
    ///
    /// ```rust
    /// context.with_semantic_route(Some(route));
    /// context.with_render_permission(Some(permission));
    /// EngineDecompileRequest { callee_resolution: Some(facts), ..request }
    /// ```
    ///
    /// Use instead `FunctionFacts::set_decompile_route(...)` and
    /// `FunctionFacts::set_callee_resolution(...)`.
    pub R2ENGINE_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
    Warn,
    "r2engine must carry decompile route decisions through FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2engine` passes, converts, or exposes renderer-local route
    /// plans beside `FunctionFacts`.
    ///
    /// ### Why is this bad?
    ///
    /// `r2engine` owns route selection, but the render boundary must carry that
    /// decision through `FunctionFacts::decompile_route`. Passing a route as a
    /// sibling argument recreates the removed r2engine/r2dec side channel and
    /// can diverge from cache identity and facts-owned refusal state.
    ///
    /// ### Example
    ///
    /// ```rust
    /// r2dec::render_semantic_worker_summary(name, facts, &route.to_decompiler_route(), config)
    /// ```
    ///
    /// Stamp route facts onto `FunctionFacts` before render and call r2dec APIs
    /// with only the facts-owned route authority.
    pub R2ENGINE_R2DEC_SUMMARY_RENDER_ROUTE_SIDE_CHANNEL,
    Warn,
    "r2engine must not pass decompile routes beside FunctionFacts into r2dec summary rendering"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2engine` code directly attaches callee,
    /// callsite, call-result, or control facts to `FunctionFacts` outside the
    /// canonical decompile-facts assembly helper.
    ///
    /// ### Why is this bad?
    ///
    /// Decompile rendering needs one completed typed evidence contract. Letting
    /// separate call sites attach subsets of the contract creates divergent
    /// cache keys, route decisions, and renderer permissions.
    ///
    /// ### Example
    ///
    /// ```rust
    /// function_facts.set_callsites(...);
    /// function_facts.set_control(...);
    /// ```
    ///
    /// Use instead `attach_prepared_decompile_evidence(...)` or
    /// `function_facts_for_decompile(...)`.
    pub R2ENGINE_DECOMPILE_FACTS_SPINE_OWNERSHIP,
    Warn,
    "r2engine must assemble decompile FunctionFacts through the canonical spine helper"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when summary decompile route/refusal state is carried beside
    /// `FunctionFacts` in `EngineSummaryDecompileRequest` or render falls back
    /// to a request-local comment.
    ///
    /// ### Why is this bad?
    ///
    /// Summary decompile is still part of the decompile product path. If guard
    /// state or fallback comments live on the request, cache keys and render
    /// decisions can diverge from the canonical `FunctionFacts::decompile_route`
    /// contract.
    ///
    /// ### Example
    ///
    /// ```rust
    /// struct EngineSummaryDecompileRequest {
    ///     named_worker_guarded: bool,
    ///     fallback_comment: Option<String>,
    /// }
    /// ```
    ///
    /// Stamp `DecompileRouteFacts` onto `FunctionFacts` before render and read
    /// summary output only from that facts-owned route.
    pub R2ENGINE_SUMMARY_DECOMPILE_ROUTE_SIDE_CHANNEL,
    Warn,
    "r2engine summary decompile route/refusal state must live in FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `crates/r2engine/src/lib.rs` exposes or calls the
    /// summary-only decompile API names `EngineSummaryDecompileRequest`,
    /// `decompile_summary`, or `decompile_summary_preprobe`.
    ///
    /// ### Why is this bad?
    ///
    /// Summary-only decompile must not be a decompile product path without the
    /// prepared SSA / `FunctionFacts` spine. Keeping a public request type or
    /// session method for summary decompile lets callers bypass prepared SSA,
    /// route/cache identity, and certified render evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// session.decompile_summary(EngineSummaryDecompileRequest { ... });
    /// ```
    ///
    /// Use the prepared `EngineSession::decompile_function(...)` path and make
    /// summary evidence feed `FunctionFacts` before rendering or refusal.
    pub R2ENGINE_SUMMARY_ONLY_DECOMPILE_API,
    Warn,
    "r2engine must not expose/use summary-only decompile APIs as production decompile paths"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `crates/r2engine/src/lib.rs` exposes the
    /// lower-level `EngineDecompileRequest` API as public surface, either as a
    /// public request type or a public `decompile` method accepting that type.
    ///
    /// ### Why is this bad?
    ///
    /// Plugin and user-facing decompile paths must enter through
    /// `EngineFunctionDecompileRequest` so route policy, cache identity,
    /// prepared SSA evidence, and `FunctionFacts` render contracts stay on the
    /// engine-owned function decompile spine. Public lower-level decompile
    /// entrypoints let callers bypass that policy.
    ///
    /// ### Example
    ///
    /// ```rust
    /// pub struct EngineDecompileRequest { ... }
    ///
    /// pub fn decompile(&self, request: EngineDecompileRequest) { ... }
    /// ```
    ///
    /// Keep `EngineDecompileRequest` internal and expose
    /// `EngineFunctionDecompileRequest` / `decompile_function(...)` instead.
    pub R2ENGINE_LOWER_LEVEL_DECOMPILE_API_BYPASS,
    Warn,
    "r2engine must not expose lower-level EngineDecompileRequest decompile APIs publicly"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2engine` mutates `FunctionFacts` semantics during render
    /// to hide an unrenderable summary artifact.
    ///
    /// ### Why is this bad?
    ///
    /// Render receives the canonical evidence contract. Clearing semantics
    /// while building `r2dec::DecompilerContext` makes the renderer see a
    /// different contract than route planning and cache keys saw. The route or
    /// refusal must be expressed in `FunctionFacts::decompile_route` before
    /// render starts.
    ///
    /// ### Example
    ///
    /// ```rust
    /// function_facts.set_semantics(None);
    /// ```
    ///
    /// Choose a facts-owned fallback route for unrenderable summaries instead.
    pub R2ENGINE_RENDER_TIME_SEMANTICS_SUPPRESSION,
    Warn,
    "r2engine must not clear FunctionFacts semantics during decompile rendering"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when the production `r2engine` decompile path writes
    /// `FunctionFacts.types.merged_signature` or `signature_certificate`
    /// directly while applying a decompile type override.
    ///
    /// ### Why is this bad?
    ///
    /// The type override decision is engine orchestration, but the mutation
    /// that makes a signature render-authorized belongs to the typed
    /// `FunctionFacts` contract. Direct field writes create a second signature
    /// authority and let decompile rendering observe hand-patched facts that
    /// were not applied through the canonical type evidence API.
    ///
    /// ### Example
    ///
    /// ```rust
    /// artifact.function_facts.types.merged_signature = Some(signature);
    /// artifact.function_facts.types.signature_certificate = certificate;
    /// ```
    ///
    /// Use `FunctionFacts::apply_decompile_type_override(...)` instead.
    pub R2ENGINE_DECOMPILE_TYPE_OVERRIDE_SIDE_CHANNEL,
    Warn,
    "r2engine decompile type overrides must be applied through FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when the production `r2engine` decompile render request carries a
    /// fallback/refusal comment outside `FunctionFacts`.
    ///
    /// ### Why is this bad?
    ///
    /// Decompile refusal and fallback output are route decisions. A request
    /// field such as `fallback_comment` can disagree with
    /// `FunctionFacts::decompile_route`, letting render output be controlled by
    /// a side channel that cache keys and downstream consumers do not own.
    ///
    /// ### Example
    ///
    /// ```rust
    /// struct EngineDecompileRequest {
    ///     fallback_comment: Option<String>,
    /// }
    /// request.fallback_comment.clone()
    /// ```
    ///
    /// Use `FunctionFacts::decompile_fallback_comment()` instead.
    pub R2ENGINE_DECOMPILE_FALLBACK_COMMENT_SIDE_CHANNEL,
    Warn,
    "r2engine decompile fallback comments must be carried by FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2engine::decompile_function` computes a decompile render
    /// cache key before stamping the route/refusal decision into
    /// `FunctionFacts`.
    ///
    /// ### Why is this bad?
    ///
    /// The render cache key hashes the canonical facts contract. If the key is
    /// built before `FunctionFacts::decompile_route` is attached, cache identity
    /// can ignore the route/refusal state that the renderer consumes, allowing
    /// standard and fallback renders to share a stale key shape.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let render_cache_key = decompile_render_cache_key(...);
    /// function_facts.set_decompile_route(...);
    /// ```
    ///
    /// Attach `FunctionFacts::decompile_route` before calling
    /// `decompile_render_cache_key(...)`.
    pub R2ENGINE_DECOMPILE_RENDER_CACHE_PRE_ROUTE_FACTS,
    Warn,
    "r2engine must hash decompile render cache keys after route facts are attached"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2engine` exposes direct artifact-cache mutation
    /// APIs outside the normal request path.
    ///
    /// ### Why is this bad?
    ///
    /// Analysis/decompile cache reuse is session policy. Public cache-key or
    /// alias invalidation APIs let plugin glue decide engine cache ownership
    /// and can bypass the typed request/FunctionFacts identity.
    ///
    /// ### Example
    ///
    /// ```rust
    /// session.clear_analysis_artifacts_for_function(&key, hash);
    /// ```
    ///
    /// Let `EngineSession::{analyze,decompile_function}` own reuse.
    pub R2ENGINE_CACHE_POLICY_OWNERSHIP,
    Warn,
    "r2engine cache mutation policy must stay inside engine request handling"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2engine::EngineArtifacts` carries decompile route or
    /// semantic-artifact fields beside `FunctionFacts`.
    ///
    /// ### Why is this bad?
    ///
    /// `FunctionFacts` is the canonical evidence spine. A generic cache artifact
    /// bag with `route` or `semantic_artifact` fields creates a second owner for
    /// render/refusal policy or semantic evidence and can drift from the facts
    /// handed to `r2dec`.
    ///
    /// ### Example
    ///
    /// ```rust
    /// struct EngineArtifacts {
    ///     semantic_artifact: Option<SemanticArtifact>,
    ///     route: Option<DecompileRouteFacts>,
    /// }
    /// ```
    ///
    /// Store semantics and route/refusal decisions inside `FunctionFacts`.
    pub R2ENGINE_ARTIFACTS_FACTS_SIDE_CHANNEL,
    Warn,
    "r2engine EngineArtifacts must not duplicate FunctionFacts semantic or route evidence"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when decompile route planning in `r2engine` accepts
    /// `FunctionTypeFacts` or a `type_facts` parameter beside
    /// `FunctionFacts`.
    ///
    /// ### Why is this bad?
    ///
    /// `FunctionFacts` is the decompile evidence spine. Passing type facts as a
    /// sibling argument lets a caller plan route/refusal decisions from type
    /// evidence that does not match the facts contract later handed to `r2dec`.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn decompile_route_decision(..., function_facts: &FunctionFacts, type_facts: &FunctionTypeFacts, ...)
    /// ```
    ///
    /// Read type evidence through `function_facts.types`.
    pub R2ENGINE_DECOMPILE_ROUTE_TYPE_FACTS_SIDE_CHANNEL,
    Warn,
    "r2engine decompile route planning must read type evidence through FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `decompiler_input_from_prepared_facts` replans or restamps
    /// the decompile route after `function_facts_for_decompile` has already
    /// attached route facts.
    ///
    /// ### Why is this bad?
    ///
    /// `FunctionFacts::decompile_route` is the single render contract. Recomputing
    /// an `EngineRouteDecision` while building `r2dec::DecompilerInput` creates a
    /// second route authority and can diverge from the facts payload used for
    /// cache identity and downstream rendering.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let route_decision = decompile_route_decision(...);
    /// let context = decompiler_context_with_route_decision(context, &route_decision);
    /// ```
    ///
    /// Build the context directly from the already stamped `FunctionFacts`.
    pub R2ENGINE_DECOMPILER_INPUT_ROUTE_REPLAN_SIDE_CHANNEL,
    Warn,
    "r2engine decompiler input assembly must not replan routes outside FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2engine::decompiler_input_from_prepared_facts` is exposed
    /// outside tests.
    ///
    /// ### Why is this bad?
    ///
    /// Normal decompile requests must enter through `EngineSession` so cache,
    /// route diagnostics, refusal policy, and render permission stay owned by
    /// `r2engine`. A production-visible raw `DecompilerInput` constructor gives
    /// callers a side door into `r2dec`.
    ///
    /// ### Example
    ///
    /// ```rust
    /// pub fn decompiler_input_from_prepared_facts(...) -> r2dec::DecompilerInput
    /// ```
    ///
    /// Gate this helper with `#[cfg(test)]`.
    pub R2ENGINE_DECOMPILER_INPUT_HELPER_TEST_SUPPORT_ONLY,
    Warn,
    "r2engine raw decompiler input assembly must be test-support only"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2engine` directly assembles prepared decompile
    /// evidence maps or mutates individual `FunctionFacts` prepared-evidence
    /// fields.
    ///
    /// ### Why is this bad?
    ///
    /// Prepared SSA callsite, call-result, control, and render certificates are
    /// part of the single typed `FunctionFacts` contract. If `r2engine` builds
    /// or attaches those maps piecemeal, future callers can create partial
    /// evidence payloads whose route/cache identity says "decompile" while the
    /// renderer sees missing proof.
    ///
    /// ### Example
    ///
    /// ```rust
    /// function_facts.set_callsites(decompile_callsite_argument_facts(prepared));
    /// function_facts.set_render(decompile_render_facts(prepared));
    /// ```
    ///
    /// Use `FunctionFacts::attach_prepared_decompile_evidence(...)`.
    pub R2ENGINE_PREPARED_DECOMPILE_EVIDENCE_SIDE_CHANNEL,
    Warn,
    "r2engine must attach prepared decompile evidence through FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec::DecompilerContext` defines decompile route,
    /// render permission, or render-policy side-channel fields/mutators outside
    /// `FunctionFacts`.
    ///
    /// ### Why is this bad?
    ///
    /// `FunctionFacts::decompile_route` is the canonical render contract. A
    /// parallel context field lets direct callers bypass or contradict the
    /// engine-owned route/refusal decision, so executable C may be rendered under
    /// a different proof policy than the one carried by the typed facts.
    ///
    /// ### Example
    ///
    /// ```rust
    /// struct DecompilerContext {
    ///     semantic_route: Option<SemanticRoutePlan>,
    ///     render_permission: Option<RenderPermission>,
    /// }
    /// ```
    ///
    /// Use `FunctionFacts::with_decompile_route(...)` instead.
    pub R2DEC_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
    Warn,
    "r2dec must carry decompile route decisions through FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec::DecompilerContext` defines a callee
    /// resolution side-channel field or mutator outside `FunctionFacts`.
    ///
    /// ### Why is this bad?
    ///
    /// Callee identity is canonical `FunctionFacts` evidence. A parallel
    /// renderer context field lets direct callers bypass the engine-owned
    /// callsite identity contract and can make raw target/name maps look
    /// authoritative.
    ///
    /// ### Example
    ///
    /// ```rust
    /// struct DecompilerContext {
    ///     callee_resolution: Option<CalleeResolutionFacts>,
    /// }
    /// ```
    ///
    /// Use `FunctionFacts::with_callee_resolution(...)` instead.
    pub R2DEC_DECOMPILER_CONTEXT_CALLEE_RESOLUTION_SIDE_CHANNEL,
    Warn,
    "r2dec must carry callee resolution through FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` exposes APIs that mutate decompiler type
    /// evidence outside `FunctionFacts`.
    ///
    /// ### Why is this bad?
    ///
    /// Type/layout/signature facts are part of the `FunctionFacts` render
    /// contract. Public setters such as `set_type_facts`, `with_type_facts`, or
    /// mutable type-fact accessors let callers alter render evidence without
    /// carrying the matching route/refusal/cache contract.
    ///
    /// ### Example
    ///
    /// ```rust
    /// decompiler.set_type_facts(type_facts);
    /// context.with_type_facts(type_facts);
    /// ```
    ///
    /// Use `DecompilerContext::from_function_facts(...)` or
    /// `Decompiler::set_function_facts(...)`.
    pub R2DEC_DIRECT_TYPE_FACTS_MUTATOR,
    Warn,
    "r2dec production code must carry type evidence through FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` enriches known function signatures from
    /// name/symbol maps while constructing render context.
    ///
    /// ### Why is this bad?
    ///
    /// Known callee signatures are typed evidence. If the renderer derives them
    /// from display names, `r2dec` becomes a second type-policy owner and can
    /// render calls with confidence that was not present in `FunctionFacts`.
    /// The engine/facts assembly path must attach this evidence before render.
    ///
    /// ### Example
    ///
    /// ```rust
    /// r2types::enrich_known_function_signatures_from_names(
    ///     &mut function_facts.types,
    ///     &function_names,
    ///     ptr_bits,
    /// );
    /// ```
    ///
    /// Use `FunctionFacts::attach_prepared_decompile_evidence(...)` before
    /// constructing the `r2dec` context.
    pub R2DEC_LOCAL_SIGNATURE_ENRICHMENT,
    Warn,
    "r2dec must consume known callee signatures from FunctionFacts, not enrich them from names locally"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` code mutates switch case labels from
    /// nearby arithmetic or helper-derived display bias.
    ///
    /// ### Why is this bad?
    ///
    /// Switch case values are canonical CFG/SSA facts. If the renderer adjusts
    /// them from local `IntSub` patterns or dense-case guesses, unrelated
    /// arithmetic can turn authoritative switch metadata into plausible but
    /// fake source-shaped C.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let label = case_value.saturating_add_signed(case_display_bias);
    /// ```
    ///
    /// Render the exact case value supplied by the canonical switch fact owner.
    pub R2DEC_SWITCH_CASE_VALUE_OWNERSHIP,
    Warn,
    "r2dec must render canonical switch case values without downstream display bias"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified switch selector rendering falls back to local
    /// `switch_selector_roots` instead of requiring `FunctionFacts` control
    /// evidence.
    ///
    /// ### Why is this bad?
    ///
    /// A local selector root is a renderer/use-info heuristic, not proof of a
    /// switch selector. Certified C must render switches only from canonical
    /// control facts; missing selector proof should become a residual.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let value = self.switch_selector_roots_map().get(&block_addr)?;
    /// ```
    ///
    /// In certified rendering, return `None` before using local selector roots.
    pub R2DEC_UNCERTIFIED_SWITCH_SELECTOR_ROOT_FALLBACK,
    Warn,
    "r2dec certified switch rendering must require FunctionFacts control evidence"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified switch selector rendering accepts
    /// `PreparedSemanticView::switch_selector_expr_for_block` before requiring
    /// canonical `FunctionControlFacts`.
    ///
    /// ### Why is this bad?
    ///
    /// Prepared selector text is a renderer convenience view. It is not the
    /// typed control contract. Certified executable switch C must be authorized
    /// by `FunctionFacts::control`; otherwise summary/prepared text can
    /// materialize a switch selector without a block-scoped proof.
    ///
    /// ### Example
    ///
    /// ```rust
    /// view.switch_selector_expr_for_block(block_addr)
    /// ```
    ///
    /// In certified rendering, return `None` after the control-fact lookup and
    /// before reading prepared selector expressions.
    pub R2DEC_CERTIFIED_PREPARED_SWITCH_SELECTOR_PROOF,
    Warn,
    "certified r2dec switch selectors must require FunctionFacts control proof before prepared selector text"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` treats "there is exactly one switch selector fact"
    /// as proof for whatever block is currently being rendered.
    ///
    /// ### Why is this bad?
    ///
    /// Switch selector evidence is block-scoped. Reusing the only selector in
    /// the function for a different block fabricates control proof and can
    /// render executable switch C for the wrong CFG node.
    ///
    /// ### Example
    ///
    /// ```rust
    /// facts.switches.len() == 1
    /// view.switch_selector_expr_by_block.len() == 1
    /// ```
    ///
    /// Use exact `FunctionControlFacts::switch_for_block(block_addr)` style
    /// lookup and residualize when the block has no selector proof.
    pub R2DEC_SWITCH_SELECTOR_SINGLE_FACT_FALLBACK,
    Warn,
    "r2dec switch selector rendering must require a block-matching FunctionFacts control fact"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` reconstructs a prepared direct call target from
    /// prepared SSA variables, canonical value roots, or raw prepared callsite
    /// fields instead of consuming `FunctionFacts` callsite evidence.
    ///
    /// ### Why is this bad?
    ///
    /// Direct call targets are a canonical callsite fact produced upstream from
    /// SSA certificates and projected through `r2types::FunctionCallsiteFacts`.
    /// If `r2dec` reparses SSA variable names or reads prepared callsite target
    /// fields directly, missing FunctionFacts evidence becomes confident callee
    /// identity again.
    ///
    /// ### Example
    ///
    /// ```rust
    /// call_site.direct_target
    /// self.prepared_canonical_value_root(target)
    /// parse_address_from_var_name(&target.name)
    /// ```
    ///
    /// Use `FunctionCallsiteFacts::arguments_for_site(...).direct_target`.
    pub R2DEC_PREPARED_DIRECT_TARGET_REPARSE,
    Warn,
    "r2dec must consume FunctionFacts direct-target evidence instead of reparsing prepared SSA"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` op-lowering reads prepared
    /// `CallsiteCertificate` data directly while synthesizing or recording
    /// executable calls.
    ///
    /// ### Why is this bad?
    ///
    /// Callsite target and argument evidence is already projected through
    /// `r2types::FunctionCallsiteFacts`. Reading prepared callsite
    /// certificates in the renderer creates a second call-proof owner and lets
    /// prepared SSA alone authorize executable calls without the `FunctionFacts`
    /// spine.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.prepared_call_site_for_op(block, op)
    /// self.prepared.callsite_certificate_for_op(block, op)
    /// fn certified_callsite_argument_values(cert: &r2types::CallsiteArgumentFacts)
    /// ```
    ///
    /// Use `FunctionCallsiteFacts::arguments_for_site(...)`.
    pub R2DEC_DIRECT_PREPARED_CALLSITE_CERTIFICATES,
    Warn,
    "certified r2dec call rendering must consume FunctionFacts callsite evidence"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` output validation reads raw prepared
    /// expression, memory, return, or stack-slot certificates instead of the
    /// canonical `FunctionFacts` render evidence.
    ///
    /// ### Why is this bad?
    ///
    /// Renderability is an upstream fact. If `r2dec` validates executable C
    /// directly from prepared certificates, it creates a second render-proof
    /// owner and can bypass missing `FunctionFacts` evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let certificates = prepared.certificates();
    /// prepared.memory_certificate_for_op_site(block, op, is_write);
    /// prepared.return_certificate_for_op(block, op);
    /// certificates.expressions.get(&value);
    /// ```
    ///
    /// Use `FunctionRenderFacts` carried by `FunctionFacts`.
    pub R2DEC_DIRECT_PREPARED_RENDER_CERTIFICATES,
    Warn,
    "certified r2dec render validation must consume FunctionFacts render evidence"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` call-result ownership logic derives a
    /// stable result owner from stack-local fallback helpers.
    ///
    /// ### Why is this bad?
    ///
    /// A post-call stack store is not by itself proof that the renderer may
    /// name the call result as that local. Stack-backed call-result ownership
    /// must arrive as prepared SSA/semantic ownership evidence; otherwise the
    /// renderer can turn missing provenance into confident source-shaped C.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fallback_owned_call_result_stack_local_name_for_source(source);
    /// ```
    ///
    /// Use instead prepared semantic ownership, such as
    /// `PreparedCallView::result_owner`, or render the call result without
    /// inventing a stack-local owner.
    pub R2DEC_CALL_RESULT_STACK_OWNER_FALLBACK,
    Warn,
    "r2dec must not derive call-result owners from stack-local fallback logic"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` call-result ownership logic derives a
    /// stable owner from rendered call-expression matching.
    ///
    /// ### Why is this bad?
    ///
    /// Two rendered calls that look equivalent are not proof that one register
    /// owns the other callsite result. Call-result ownership must come from
    /// prepared SSA/semantic evidence, explicit aliases, or an exact
    /// unambiguous source proof; otherwise the decompiler can turn replayed or
    /// guessed call text into confident source-shaped C.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fallback_owned_call_result_register_name_from_matching_definition(source);
    /// ```
    ///
    /// Use instead prepared semantic ownership, such as
    /// `PreparedCallView::result_owner`, or render a residual when ownership is
    /// not proven.
    pub R2DEC_CALL_RESULT_SOURCE_EXPR_OWNER_FALLBACK,
    Warn,
    "r2dec must not derive call-result owners from matching rendered call expressions"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` return-register call-result fallback can
    /// run before certified rendering has failed closed.
    ///
    /// ### Why is this bad?
    ///
    /// A direct return-register alias such as `rax` is ABI storage, not proof of
    /// stable result ownership. In certified rendering, call-result ownership
    /// must arrive through `FunctionFacts`; otherwise the renderer can turn
    /// missing ownership evidence into confident source-shaped C.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fallback_owned_call_result_return_name_for_source(source_call);
    /// ```
    ///
    /// Use instead a certified guard before any return-register fallback logic,
    /// or consume an owner carried by `FunctionFacts`.
    pub R2DEC_CERTIFIED_CALL_RESULT_RETURN_REGISTER_FALLBACK,
    Warn,
    "certified r2dec rendering must not derive call-result owners from return-register fallback"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` call-result alias fallback can derive a
    /// stable owner before certified rendering has failed closed.
    ///
    /// ### Why is this bad?
    ///
    /// Alias maps and direct register aliases are local renderer observations,
    /// not proof that a call result has a stable source-level owner. Certified
    /// rendering must consume owners projected from `FunctionFacts`; otherwise
    /// a post-call register or temporary can become confident C without typed
    /// ownership evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// derive_stable_owned_call_result_name_for_source(aliases);
    /// ```
    ///
    /// Use instead a certified guard before local alias fallback, or consume
    /// `PreparedCallView::result_owner` projected from `FunctionFacts`.
    pub R2DEC_CERTIFIED_CALL_RESULT_ALIAS_OWNER_FALLBACK,
    Warn,
    "certified r2dec rendering must not derive call-result owners from local alias fallback"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` call-result ownership consults
    /// renderer-local `SemanticOwnershipFacts` before checking the prepared
    /// `FunctionFacts` owner path.
    ///
    /// ### Why is this bad?
    ///
    /// Local ownership maps are renderer recovery state. In certified
    /// rendering, stable call-result owners must come from prepared
    /// FunctionFacts/call-result evidence; otherwise a locally inferred owner
    /// can make an unproven call result look like source-level C.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.ownership().ownership_for_source(...)
    /// self.ownership().source_for_visible_owner_name(...)
    /// ```
    ///
    /// Guard these paths out of certified rendering and use the prepared
    /// result-owner view instead.
    pub R2DEC_CERTIFIED_LOCAL_CALL_OWNERSHIP_FALLBACK,
    Warn,
    "certified r2dec call-result ownership must not trust renderer-local ownership maps"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` call-result preservation treats the
    /// renderer-local visible-owner cache as proof that a name should survive.
    ///
    /// ### Why is this bad?
    ///
    /// Preservation affects executable output even when it does not directly
    /// recover a call expression. In certified rendering, a visible call-result
    /// name must be preserved only if it can be traced back to stable
    /// FunctionFacts call-result ownership.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.ownership().has_visible_owner_name(name)
    /// ```
    ///
    /// In certified rendering, resolve the source call and require
    /// `stable_owned_call_result_name_for_source(source)` to match the visible
    /// name.
    pub R2DEC_CERTIFIED_CALL_RESULT_PRESERVATION_FALLBACK,
    Warn,
    "certified r2dec call-result preservation must not trust renderer-local ownership maps"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` duplicate-call pruning uses rendered-call
    /// source matching instead of certified FunctionFacts callsite proof.
    ///
    /// ### Why is this bad?
    ///
    /// Pruning is still a rendering decision: deleting a call because it looks
    /// like another rendered call can hide missing proof and change executable
    /// output. Certified rendering may prune duplicate calls only after the
    /// call source is proven through FunctionFacts callsite evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.collect_rendered_call_sources_for_expr(expr, &mut sources);
    /// ```
    ///
    /// In certified rendering, use
    /// `collect_certified_rendered_call_sources_for_expr` and keep the
    /// statement when the proof is missing.
    pub R2DEC_CERTIFIED_DUPLICATE_CALL_PRUNING_FALLBACK,
    Warn,
    "certified r2dec duplicate-call pruning must require FunctionFacts callsite proof"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified visible-owner lookup returns a prepared source
    /// call without confirming the name is the stable FunctionFacts result
    /// owner for that call.
    ///
    /// ### Why is this bad?
    ///
    /// Prepared views may contain low-signal carriers such as return registers.
    /// A raw name match must not authorize executable call replay unless it
    /// also passes the same stable owner filter used by call-result ownership.
    ///
    /// ### Example
    ///
    /// ```rust
    /// return self.prepared_source_call_for_visible_owner_name(visible_name);
    /// ```
    ///
    /// Require `stable_owned_call_result_name_for_source(source)` to match the
    /// visible name before returning a source call.
    pub R2DEC_CERTIFIED_VISIBLE_OWNER_SOURCE_LOOKUP,
    Warn,
    "certified r2dec visible owner lookup must require stable FunctionFacts result ownership"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` call-result ownership accepts arbitrary
    /// prepared owner expressions instead of the stable FunctionFacts owner
    /// name path.
    ///
    /// ### Why is this bad?
    ///
    /// A call-result owner is identity evidence. If certified rendering treats
    /// `PreparedCallView::result_owner` as a general `CExpr`, a prepared side
    /// channel can smuggle executable expressions into output without proving
    /// a stable source-level owner name.
    ///
    /// ### Example
    ///
    /// ```rust
    /// view.result_owner.clone()
    /// ```
    ///
    /// Use `prepared_result_owner_name_for_source(...)` for certified
    /// rendering, then materialize `CExpr::Var(owner_name)`.
    pub R2DEC_CERTIFIED_PREPARED_RESULT_OWNER_EXPR,
    Warn,
    "certified r2dec call-result ownership must accept only stable prepared owner names"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` accepts a prepared call-result owner name
    /// without also requiring canonical `FunctionCallResultFacts` owner
    /// evidence for the source call.
    ///
    /// ### Why is this bad?
    ///
    /// `PreparedSemanticView` is a render preparation view. Certified owner
    /// authority must come from `FunctionFacts::call_results`; otherwise a
    /// manually seeded prepared name can authorize executable call-result C.
    ///
    /// ### Example
    ///
    /// ```rust
    /// prepared_result_owner_name_for_source(source_call).map(CExpr::Var)
    /// ```
    ///
    /// Require `has_certified_call_result_owner_fact_for_source(source_call)`
    /// before accepting the prepared owner name in certified mode.
    pub R2DEC_CERTIFIED_PREPARED_RESULT_OWNER_FACT,
    Warn,
    "certified r2dec call-result owners must be backed by FunctionFacts call-result owner facts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` appended stack-return recovery reads
    /// renderer-local `return_stack_slots` without also requiring canonical
    /// render facts.
    ///
    /// ### Why is this bad?
    ///
    /// A locally detected stack return slot is not proof that executable C may
    /// return a friendly stack-local name. Certified rendering must require
    /// `FunctionFacts::render` return evidence and a structurally renderable
    /// return value before appending a return statement.
    pub R2DEC_CERTIFIED_STACK_RETURN_RENDER_FACTS,
    Warn,
    "certified r2dec stack-return recovery must require FunctionFacts render evidence"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` local declaration validation or retention
    /// treats a stack offset certificate as enough proof for a rendered local
    /// name.
    ///
    /// ### Why is this bad?
    ///
    /// A certified stack offset only proves an object exists at that offset. It
    /// does not prove that a renderer-local friendly name or type is the
    /// canonical source-level local. Certified locals must require exact typed
    /// stack identity from `FunctionFacts`.
    pub R2DEC_CERTIFIED_STACK_LOCAL_IDENTITY,
    Warn,
    "certified r2dec local declarations must require exact typed stack identity"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` stack owner authorization calls
    /// `FunctionRenderFacts::has_stack_slot_offset` and then locally
    /// recomposes proof from visible binding or type checks, or when certified
    /// call-result owner rendering reads stack alias/provenance helpers
    /// directly.
    ///
    /// ### Why is this bad?
    ///
    /// A render-fact stack offset or stack alias/provenance lookup only proves
    /// local renderer recovery. It does not authorize the renderer-local owner
    /// name or type. Certified stack owner helpers must call a
    /// `FunctionFacts`-owned predicate that checks the complete stack identity
    /// contract.
    pub R2DEC_CERTIFIED_STACK_OWNER_PROOF_RECOMPOSITION,
    Warn,
    "certified r2dec stack owner authorization must use a FunctionFacts-owned predicate"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` local declaration types can still come
    /// from renderer recovery, runtime inference, or runtime type hints.
    ///
    /// ### Why is this bad?
    ///
    /// Certified stack-local types must come from `FunctionTypeFacts`
    /// stack-slot/visible-binding evidence. Runtime type repair in `r2dec`
    /// creates a second type owner and can make unproven locals look typed.
    pub R2DEC_CERTIFIED_STACK_LOCAL_TYPE_OWNERSHIP,
    Warn,
    "certified r2dec stack local types must come from FunctionTypeFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` fold setup passes renderer-local type
    /// hints or a local type oracle into expression lowering.
    ///
    /// ### Why is this bad?
    ///
    /// CertifiedC output may use fold type hints to choose casts, pointer
    /// element types, and memory access shape. Those hints come from local
    /// runtime inference or variable recovery, not from the canonical
    /// `FunctionFacts` render contract.
    pub R2DEC_CERTIFIED_LOCAL_TYPE_HINTS,
    Warn,
    "certified r2dec fold inputs must not consume local type hints or local type oracle"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` reads local stable stack/local-store
    /// recovery directly on paths that can feed certified rendering.
    ///
    /// ### Why is this bad?
    ///
    /// `stable_stack_values` and `local_store_owner_expr_for_offset` are local
    /// recovery conveniences, not certified `FunctionFacts` evidence. Certified
    /// rendering must pass through a certified-aware accessor or an explicit
    /// non-certified/prepared-only guard before consuming them.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.use_info().stable_stack_values.get(&offset);
    /// local_store_owner_expr_for_offset(view, prepared, block, idx, offset);
    /// ```
    ///
    /// Use `stable_stack_value_for_offset(...)` or guard the prepared-only
    /// fallback out of certified rendering first.
    pub R2DEC_CERTIFIED_LOCAL_STACK_RECOVERY_BYPASS,
    Warn,
    "certified r2dec must not consume local stable stack/local-store recovery directly"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` analysis reads prepared SSA call-result
    /// certificate maps directly.
    ///
    /// ### Why is this bad?
    ///
    /// Call-result ownership used by executable rendering must travel through
    /// `r2types::FunctionFacts`. Reading `prepared.certificates().call_results`
    /// in the renderer recreates a side channel and bypasses the engine-owned
    /// evidence projection.
    ///
    /// ### Example
    ///
    /// ```rust
    /// prepared.certificates().call_results.get(&value);
    /// prepared.certificates().call_results_by_callsite.get(&site);
    /// ```
    ///
    /// Use instead `FunctionCallResultFacts` from `FunctionFacts`.
    pub R2DEC_DIRECT_PREPARED_CALL_RESULT_CERTIFICATES,
    Warn,
    "r2dec analysis must consume FunctionFacts call-result facts instead of prepared certificate maps"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` reads prepared SSA predicate or switch
    /// maps directly, carries them through a side channel, or infers switch
    /// selectors from prepared SSA instead of the canonical control contract.
    ///
    /// ### Why is this bad?
    ///
    /// Branch predicate, loop structure, and switch selector rendering must be
    /// authorized by `r2types::FunctionFacts`. Reading
    /// `prepared.predicates().predicates`, `prepared.certificates().loops`,
    /// carrying `prepared_predicates`, or calling `infer_switch_selector_var`
    /// in the renderer recreates a side channel and bypasses the engine-owned
    /// control evidence projection.
    ///
    /// ### Example
    ///
    /// ```rust
    /// prepared.predicates().predicates.values();
    /// prepared.predicates().switches.get(&block);
    /// prepared.certificates().loops.values();
    /// inputs.prepared_predicates;
    /// prepared.function().infer_switch_selector_var(block);
    /// ```
    ///
    /// Use instead `FunctionControlFacts` from `FunctionFacts`.
    pub R2DEC_DIRECT_PREPARED_CONTROL_FACTS,
    Warn,
    "r2dec analysis must consume FunctionFacts control facts instead of prepared predicate maps"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code directly reconstructs type
    /// signature writeback authority or constructs type writeback apply policy
    /// instead of consuming an engine-owned orchestration decision.
    ///
    /// ### Why is this bad?
    ///
    /// Signature certificates, source authority, stale-certificate refusal,
    /// and apply-policy thresholds are type-system policy. Keeping that logic
    /// in plugin glue creates a second owner and lets FFI code decide which
    /// type facts are authoritative.
    ///
    /// ### Example
    ///
    /// ```rust
    /// certificate.authorizes_signature_writeback();
    /// r2types::type_writeback_authority_report_with_policy(...);
    /// r2engine::type_writeback_authority_report_for_policy(...);
    /// r2engine::type_writeback_plan_report_for_policy(...);
    /// r2engine::bounded_cfg_type_writeback_plan(...);
    /// r2engine::bounded_cfg_type_writeback_plan_report(...);
    /// r2engine::type_writeback_external_struct_names(...);
    /// r2engine::semantic_fallback_type_writeback_plan_report(...);
    /// r2engine::type_writeback_field_access_certificate_names(...);
    /// r2types::type_writeback_var_type_apply_decision(...);
    /// r2types::signature_register_arg_rename_decision(...);
    /// r2types::TypeWritebackApplyPolicy::balanced();
    /// "signature mutation refused: ...";
    /// ```
    ///
    /// Use instead `r2engine::type_writeback_apply_policy_for_mode(...)` and
    /// an engine-owned `EngineTypeWritebackPayload`.
    pub R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
    Warn,
    "r2plugin must not decide type writeback authority or construct apply policy directly"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code matches or maps
    /// `r2types::TypeWritebackMutationKind` variants directly.
    ///
    /// ### Why is this bad?
    ///
    /// Mutation taxonomy is part of the engine/type-writeback contract. Plugin
    /// glue may pack engine-owned mutation IDs into C ABI structs, but must not
    /// become a second owner for the variant-to-public-ID mapping.
    ///
    /// ### Example
    ///
    /// ```rust
    /// r2types::TypeWritebackMutationKind::Signature => 0
    /// ```
    ///
    /// Use instead `r2engine::type_writeback_mutation_kind_id(...)`.
    pub R2PLUGIN_TYPE_WRITEBACK_MUTATION_KIND_OWNERSHIP,
    Warn,
    "r2plugin must not map TypeWritebackMutationKind variants directly"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code reads `CallSiteFact::direct_target`
    /// directly.
    ///
    /// ### Why is this bad?
    ///
    /// Direct call targets can be recovered through canonical SSA root
    /// resolution even when the raw callsite fact lacks an immediate
    /// `direct_target`. Plugin glue must consume the canonical
    /// `SsaArtifact::resolved_call_target` owner instead of exporting a partial
    /// raw field view.
    ///
    /// ### Example
    ///
    /// ```rust
    /// call.direct_target;
    /// ```
    ///
    /// Use instead `analysis.ssa_func.resolved_call_target(call)`.
    pub R2PLUGIN_RAW_DIRECT_CALL_TARGET,
    Warn,
    "r2plugin must use r2ssa::SsaArtifact::resolved_call_target instead of CallSiteFact::direct_target"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code builds type-writeback analysis or
    /// local struct/type artifacts directly.
    ///
    /// ### Why is this bad?
    ///
    /// Building `FunctionFacts` for decompile is an engine-owned orchestration
    /// path. If plugin glue calls `r2types` type-writeback assembly APIs or
    /// constructs `FunctionFacts` directly, it creates a second FunctionFacts
    /// producer that can drift from route/refusal/cache policy.
    ///
    /// ### Example
    ///
    /// ```rust
    /// r2types::build_type_writeback_analysis(input);
    /// r2types::infer_local_struct_artifacts_from_ssa(...);
    /// r2types::FunctionFacts::new(...);
    /// ```
    ///
    /// Use `r2engine::EngineSession::analyze(...)` or an engine-owned request.
    pub R2PLUGIN_DIRECT_TYPE_WRITEBACK_ANALYSIS_OWNERSHIP,
    Warn,
    "r2plugin must not build type-writeback analysis directly"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code reads or recomputes type writeback
    /// apply-threshold fields.
    ///
    /// ### Why is this bad?
    ///
    /// Apply thresholds are type-system policy. The plugin may select a
    /// writeback mode and execute already-authorized mutations, but it must not
    /// become a second owner for per-kind confidence thresholds.
    ///
    /// ### Example
    ///
    /// ```rust
    /// policy.mutation_min_confidence(kind);
    /// policy.type_min_confidence;
    /// ```
    ///
    /// Use instead a `r2types::TypeWritebackMutationPlan` built with the desired
    /// `TypeWritebackApplyPolicy`.
    pub R2PLUGIN_TYPE_WRITEBACK_APPLY_THRESHOLD_OWNERSHIP,
    Warn,
    "r2plugin must not compute or inspect type writeback apply thresholds"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code reads `FunctionFacts.types`
    /// directly.
    ///
    /// ### Why is this bad?
    ///
    /// `FunctionFacts` is the cross-crate evidence contract, but plugin glue
    /// must not inspect its type internals or decide which type projections are
    /// public. Engine-owned request/response helpers should expose the stable
    /// projection needed by FFI or JSON.
    ///
    /// ### Example
    ///
    /// ```rust
    /// function_facts.types.external_type_db.structs.values();
    /// ```
    ///
    /// Use instead an `r2engine` projection helper or typed engine response.
    pub R2PLUGIN_FUNCTION_FACTS_TYPES_OWNERSHIP,
    Warn,
    "r2plugin must not read FunctionFacts.types directly"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code mines `FunctionFacts` report
    /// fields directly.
    ///
    /// ### Why is this bad?
    ///
    /// Session report fields such as route facts, plans, assumptions, semantic
    /// artifact presence, and summary diagnostics are engine-owned projections.
    /// Plugin glue should serialize an engine response, not reconstruct report
    /// policy from the canonical evidence contract.
    ///
    /// ### Example
    ///
    /// ```rust
    /// function_facts.plans.clone();
    /// function_facts.decompile_route();
    /// function_facts.summary_view.diagnostics();
    /// ```
    ///
    /// Use instead an engine-owned report payload such as
    /// `EngineFunctionAnalysisReportPayload`.
    pub R2PLUGIN_FUNCTION_FACTS_REPORT_OWNERSHIP,
    Warn,
    "r2plugin must not mine FunctionFacts report fields directly"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code manually projects
    /// `EngineTypeWritebackPayload` fields into JSON.
    ///
    /// ### Why is this bad?
    ///
    /// Type-writeback display fields encode source/evidence names, confidence
    /// policy output, diagnostics, and public JSON spellings. That projection
    /// belongs to `r2engine`; plugin glue should only wrap engine-owned output
    /// with ABI/session-only fields.
    ///
    /// ### Example
    ///
    /// ```rust
    /// payload.signature.signature;
    /// payload.var_type_candidates.into_iter().map(...);
    /// payload.diagnostics.warnings;
    /// ```
    ///
    /// Use instead `r2engine::type_writeback_json_core(payload)`.
    pub R2PLUGIN_TYPE_WRITEBACK_JSON_PROJECTION_OWNERSHIP,
    Warn,
    "r2plugin must not manually project EngineTypeWritebackPayload into JSON"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code manually projects
    /// `EngineFunctionAnalysisReportPayload` fields into session report JSON.
    ///
    /// ### Why is this bad?
    ///
    /// Function identity, CFG risk summaries, route JSON spelling, plans,
    /// assumptions, summary diagnostics, and bounded-plan decisions are
    /// engine-owned report projections. Plugin glue may wrap engine output
    /// with ABI-local fields, but must not become a second owner for the
    /// public report schema.
    ///
    /// ### Example
    ///
    /// ```rust
    /// report_payload.cfg_summary;
    /// report_payload.semantic_route.as_ref().map(...);
    /// report_payload.prefer_bounded_type_plan;
    /// ```
    ///
    /// Use instead `r2engine::function_analysis_report_json_core(...)`.
    pub R2PLUGIN_FUNCTION_ANALYSIS_REPORT_JSON_PROJECTION_OWNERSHIP,
    Warn,
    "r2plugin must not manually project EngineFunctionAnalysisReportPayload into JSON"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` defines the public type-writeback or
    /// function-analysis report JSON schema locally.
    ///
    /// ### Why is this bad?
    ///
    /// Report schema fields encode engine/type/semantic evidence contracts.
    /// Plugin glue may serialize engine-owned report DTOs and pack C ABI
    /// pointers, but local schema structs make the plugin a second report
    /// owner.
    ///
    /// ### Example
    ///
    /// ```rust
    /// struct InferredTypeWritebackJson { ... }
    /// struct FunctionAnalysisSessionReportJson { ... }
    /// ```
    ///
    /// Use instead `r2engine::EngineInferredTypeWritebackJson` and
    /// `r2engine::EngineFunctionAnalysisSessionReportJson`.
    pub R2PLUGIN_REPORT_JSON_SCHEMA_OWNERSHIP,
    Warn,
    "r2plugin must not define engine-owned report JSON schema structs"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` defines type-writeback report
    /// assembly helpers around engine-owned report payloads.
    ///
    /// ### Why is this bad?
    ///
    /// Converting `EngineFunctionAnalysisReportPayload` into public
    /// type-writeback JSON decides which semantics, compiled semantic report,
    /// interproc summary, and scope evidence are attached. That is engine
    /// orchestration/report policy, not FFI glue.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn type_writeback_payload_from_engine_report(...) { ... }
    /// fn bounded_cfg_type_payload(...) { ... }
    /// fn semantic_type_fallback_payload(...) { ... }
    /// struct WritebackPayloadJsonInput { ... }
    /// fn writeback_payload_json(...) { ... }
    /// ```
    ///
    /// Use instead `r2engine::type_writeback_report_json_from_function_analysis(...)`.
    pub R2PLUGIN_TYPE_WRITEBACK_REPORT_ASSEMBLY_OWNERSHIP,
    Warn,
    "r2plugin must not assemble engine type-writeback report JSON locally"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` defines symbolic-scope/interproc
    /// report projection helpers.
    ///
    /// ### Why is this bad?
    ///
    /// Symbolic scope report fields are derived from typed
    /// `PreparedFunctionScope` evidence and are part of the engine-owned
    /// function-analysis report DTO. Plugin glue may pass scope facts through
    /// to `r2engine`, but must not shape `payloads`, `seeds`, or report merge
    /// policy locally.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn symbolic_scope_view_json(...) { ... }
    /// fn merged_interproc_scope_report(...) { ... }
    /// ```
    ///
    /// Use instead `r2engine::interproc_summary_json(...)`.
    pub R2PLUGIN_INTERPROC_SCOPE_REPORT_OWNERSHIP,
    Warn,
    "r2plugin must not shape symbolic-scope/interproc report JSON locally"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` defines semantic artifact report
    /// projection types or helpers.
    ///
    /// ### Why is this bad?
    ///
    /// Semantic artifact report fields are derived entirely from
    /// `r2sym::SemanticArtifact`, plans, native summaries, VM summaries, and
    /// semantic diagnostics. That schema belongs to `r2sym`; plugin glue may
    /// serialize the r2sym-owned projection, but must not define a parallel
    /// report owner.
    ///
    /// ### Example
    ///
    /// ```rust
    /// struct CompiledSemanticInfo { ... }
    /// fn compiled_semantic_info(artifact: &r2sym::SemanticArtifact) { ... }
    /// ```
    ///
    /// Use instead `r2sym::compiled_semantic_info(...)` inside semantic-owner
    /// crates, or `r2engine::compiled_semantic_info(...)` from the plugin
    /// decompile/session path.
    pub R2PLUGIN_SEMANTIC_REPORT_PROJECTION_OWNERSHIP,
    Warn,
    "r2plugin must not define semantic artifact report projections"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` constructs typed external context JSON
    /// schema objects or calls raw `r2types` external context parsers.
    ///
    /// ### Why is this bad?
    ///
    /// Typed radare2 context fallback merging, numeric role/linkage mapping,
    /// and schema defaults are engine/type-contract policy. Plugin glue may
    /// copy C ABI fields into an engine-owned input DTO, but must not become a
    /// second owner for the canonical external context schema.
    ///
    /// ### Example
    ///
    /// ```rust
    /// r2types::ExternalContextJson { ... }
    /// r2types::parse_external_context_json(raw, ptr_bits)
    /// r2types::parse_external_context(raw, ptr_bits)
    /// ```
    ///
    /// Use instead `r2engine::parse_typed_external_context(...)`.
    pub R2PLUGIN_TYPED_EXTERNAL_CONTEXT_OWNERSHIP,
    Warn,
    "r2plugin must not construct typed external context schema directly"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2plugin` defines an external type parser that returns
    /// `r2dec::CType`.
    ///
    /// ### Why is this bad?
    ///
    /// External radare2 type strings are type-system input. Parsing and
    /// normalization belong to `r2types`, and the parser contract should be
    /// `CTypeLike`. Using renderer `CType` as the parser oracle keeps type
    /// policy coupled to the decompiler crate.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn parse_external_type(raw: &str, ptr_bits: u32) -> Option<r2dec::CType> { ... }
    /// ```
    ///
    /// Use instead `r2types::parse_external_type_like_spec(...)`.
    pub R2PLUGIN_EXTERNAL_TYPE_PARSER_RENDERER_TYPE_OWNERSHIP,
    Warn,
    "r2plugin external type parsing must return r2types::CTypeLike, not r2dec::CType"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2plugin` defines signature-confidence candidate wrappers
    /// or helpers that route through `r2dec::CType`.
    ///
    /// ### Why is this bad?
    ///
    /// Signature confidence is type-system policy. Tests should assert the
    /// canonical `r2types::SignatureParamCandidate` and `CTypeLike` contract
    /// directly instead of treating renderer `CType` as the evidence model.
    ///
    /// ### Example
    ///
    /// ```rust
    /// struct InferredParam { ty: r2dec::CType, ... }
    /// fn compute_signature_confidence(params: &[InferredParam], ret: &r2dec::CType, ...) { ... }
    /// ```
    ///
    /// Use instead `r2types::SignatureParamCandidate` and
    /// `r2types::compute_signature_confidence(...)`.
    pub R2PLUGIN_SIGNATURE_CONFIDENCE_RENDERER_TYPE_OWNERSHIP,
    Warn,
    "r2plugin signature confidence tests must use r2types candidates, not r2dec::CType wrappers"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2plugin` signature fixtures build
    /// `FunctionSignatureSpec` through renderer `r2dec::CType`.
    ///
    /// ### Why is this bad?
    ///
    /// Signature fixtures are type-system inputs. They should exercise the
    /// canonical `r2types::CTypeLike` contract directly instead of teaching
    /// plugin tests that renderer types are acceptable evidence carriers.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn signature_spec(ret: Option<r2dec::CType>, ...) -> FunctionSignatureSpec { ... }
    /// ```
    ///
    /// Use instead `r2types::CTypeLike` in the fixture contract.
    pub R2PLUGIN_SIGNATURE_SPEC_RENDERER_TYPE_OWNERSHIP,
    Warn,
    "r2plugin signature fixtures must construct FunctionSignatureSpec with r2types::CTypeLike"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2plugin` defines helper functions that translate between
    /// canonical `r2types::CTypeLike` values and renderer-owned
    /// `r2dec::CType`.
    ///
    /// ### Why is this bad?
    ///
    /// Type policy belongs to `r2types`. Plugin tests and fixtures must assert
    /// the canonical type contract directly, not route through decompiler
    /// rendering types just to materialize strings or expected values.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn type_like_to_ctype(ty: &r2types::CTypeLike) -> r2dec::CType { ... }
    /// fn ctype_to_type_like(ty: &r2dec::CType) -> r2types::CTypeLike { ... }
    /// fn materialize_signature_ctype(ty: r2dec::CType, ptr_bits: u32) -> r2dec::CType { ... }
    /// ```
    ///
    /// Use instead `r2types::CTypeLike` and `r2types::render_c_type_like(...)`
    /// at the assertion boundary.
    pub R2PLUGIN_CTYPE_BRIDGE_OWNERSHIP,
    Warn,
    "r2plugin must not bridge r2types::CTypeLike through renderer-owned r2dec::CType"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code calls
    /// `r2dec::DecompilerConfig::for_arch(...)`.
    ///
    /// ### Why is this bad?
    ///
    /// Architecture name and pointer-width normalization are engine
    /// orchestration facts. Letting plugin glue ask the renderer to derive
    /// those facts makes `r2plugin` depend on renderer policy and creates a
    /// second owner for request/session target metadata.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let cfg = r2dec::DecompilerConfig::for_arch(ctx.arch);
    /// ```
    ///
    /// Use instead `r2engine::engine_arch_target(...)` or
    /// `r2engine::EngineRenderTarget`, then build renderer config only at the
    /// render boundary.
    pub R2PLUGIN_RENDERER_CONFIG_ARCH_TARGET_OWNERSHIP,
    Warn,
    "r2plugin must derive arch targets through r2engine, not r2dec::DecompilerConfig::for_arch"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code recovers variables directly
    /// through renderer/type-system internals.
    ///
    /// ### Why is this bad?
    ///
    /// Variable recovery feeds signature, callconv, and type writeback facts.
    /// Those are engine/type-system contracts, not plugin glue policy. If the
    /// plugin constructs the renderer's variable recovery or calls the
    /// type-system recovery routine directly, it becomes a second owner for
    /// recovered signature evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let mut vars = r2dec::VariableRecovery::new("rsp", "rbp", 8);
    /// ```
    ///
    /// Use instead an `r2engine` request/response API that owns recovered
    /// signature evidence.
    pub R2PLUGIN_VARIABLE_RECOVERY_OWNERSHIP,
    Warn,
    "r2plugin must not recover variables through r2dec/r2types directly; r2engine owns recovered signature evidence orchestration"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2plugin/src/types.rs` interprets r2il metadata into
    /// `TypeHint` policy directly.
    ///
    /// ### Why is this bad?
    ///
    /// Metadata-to-type interpretation is a type-system and engine
    /// orchestration contract. The plugin may resolve radare2 register names,
    /// but it must not decide that a `ScalarKind` or `PointerHint` becomes a C
    /// type. Keeping that policy in plugin glue creates a second owner for
    /// signature evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn scalar_kind_to_type(kind: r2il::ScalarKind, size: u32) -> Option<TypeHint> {
    ///     // plugin-owned type policy
    /// }
    /// ```
    ///
    /// Use instead `r2engine::collect_register_type_hints_with_names()` backed
    /// by `r2types` metadata type mapping.
    pub R2PLUGIN_METADATA_TYPE_HINT_OWNERSHIP,
    Warn,
    "r2plugin must not interpret r2il metadata into TypeHint policy"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code owns engine/session policy such as
    /// caches, bounded-route preferences, semantic mode selection, or summary
    /// fallback assembly.
    ///
    /// ### Why is this bad?
    ///
    /// `r2plugin` is FFI and command glue. Session cache ownership, route
    /// selection, budget/depth policy, and fallback/refusal construction belong
    /// in `r2engine` so every command sees one canonical policy.
    ///
    /// ### Example
    ///
    /// ```rust
    /// EngineTypeAnalysisRequest {
    ///     caller_prefers_bounded_type_plan: true,
    ///     // plugin-owned route policy
    /// }
    /// engine_session().type_function(...);
    /// r2engine::function_analysis_report_payload_from_type_response(...);
    /// r2engine::EngineAnalyzeRequest::full_semantics(...);
    /// ```
    ///
    /// Use instead an engine-owned request builder or policy decision.
    pub R2PLUGIN_ENGINE_POLICY_OWNERSHIP,
    Warn,
    "r2plugin must not own engine route/cache/session/fallback policy"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` code parses decompile metadata
    /// payloads or resolves renderer display identity locally.
    ///
    /// ### Why is this bad?
    ///
    /// Decompile metadata affects callee identity, render cache keys, and the
    /// public function name passed through `FunctionFacts`/`r2engine`. If the
    /// plugin parses aliases or picks display names, the radare2 command path
    /// can drift from engine-owned route and cache policy.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn parse_addr_name_map(...) { ... }
    /// helpers::resolve_decompiler_display_name(...)
    /// ```
    ///
    /// Use `EngineFunctionDecompileRequest` payload fields and let `r2engine`
    /// parse metadata and select display identity.
    pub R2PLUGIN_DECOMPILE_METADATA_POLICY_OWNERSHIP,
    Warn,
    "r2plugin must not parse decompile metadata or select display identity"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2plugin` tests render an analysis artifact through
    /// `Decompiler::decompile(&artifact.ssa_func)`.
    ///
    /// ### Why is this bad?
    ///
    /// `SSAFunction` alone does not carry route decisions, callee resolution,
    /// render permission, or prepared SSA certificates. Tests that assert
    /// source-shaped ownership through this path bless uncertified renderer
    /// reconstruction instead of the engine-owned prepared contract.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let output = decompiler.decompile(&artifact.ssa_func);
    /// ```
    ///
    /// Use instead `EngineFunctionDecompileRequest` through the engine-backed
    /// plugin helper.
    pub R2PLUGIN_UNPREPARED_DECOMPILE_ORACLE,
    Warn,
    "r2plugin artifact render tests must use the engine decompile path, not raw SSAFunction decompile"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when an `r2plugin` test asserts executable C body text from
    /// `decompiler_input_from_artifact(...)` rendered directly through
    /// `Decompiler::decompile_input(...)`.
    ///
    /// ### Why is this bad?
    ///
    /// Positive executable-C plugin tests should exercise the same
    /// `EngineSession::decompile_function` path as `pdd` / `a:sla.dec`.
    /// Direct prepared-input renderer tests normalize a bypass around engine
    /// cache, route diagnostics, and request construction.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let input = decompiler_input_from_artifact(artifact, ...);
    /// let output = decompiler.decompile_input(&input);
    /// assert!(output.contains("return 1;"));
    /// ```
    ///
    /// Use an `EngineFunctionDecompileRequest` and assert the returned engine
    /// output, or keep direct prepared-input tests limited to residual/refusal
    /// checks.
    pub R2PLUGIN_DECOMPILER_INPUT_EXECUTABLE_C_ORACLE,
    Warn,
    "r2plugin executable-C tests must use the engine decompile path"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when an `r2plugin` test constructs a decompiler input from a
    /// detached artifact and renders it directly through `r2dec`.
    ///
    /// ### Why is this bad?
    ///
    /// Plugin tests are integration contracts for the public command path. A
    /// direct `DecompilerInput` bridge bypasses `r2engine` request construction,
    /// route selection, cache identity, and refusal policy even when the test
    /// only asserts residual text.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let input = decompiler_input_from_artifact(artifact, ...);
    /// let output = decompiler.decompile_input(&input);
    /// ```
    ///
    /// Use `EngineFunctionDecompileRequest` / `EngineSession::decompile_function`
    /// or the plugin's engine-backed detached decompile helper.
    pub R2PLUGIN_DECOMPILER_INPUT_TEST_BYPASS,
    Warn,
    "r2plugin tests must not bypass r2engine with direct DecompilerInput rendering"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` calls
    /// `r2dec::lower_ssa_ops_to_stmts` directly.
    ///
    /// ### Why is this bad?
    ///
    /// Direct SSA-op lowering bypasses `r2engine` route selection and the
    /// `FunctionFacts` render contract. A plugin-facing AST/debug surface must
    /// residualize or route through the engine instead of emitting executable
    /// C-shaped statements from uncertified local SSA.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let stmts = r2dec::lower_ssa_ops_to_stmts(64, &ssa_block.ops);
    /// ```
    ///
    /// Use an engine-owned `DecompilerInput`/`FunctionFacts` route or return an
    /// explicit residual comment.
    pub R2PLUGIN_DIRECT_R2DEC_OP_LOWERING,
    Warn,
    "r2plugin must not lower SSA ops directly through r2dec without FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` asks the instruction exporter for
    /// C-like decompile output directly.
    ///
    /// ### Why is this bad?
    ///
    /// C-like decompile output is executable-looking renderer output. A block
    /// exporter has no function route, no certified control/call/type facts,
    /// and no `FunctionFacts` render permission. Plugin-facing block surfaces
    /// must residualize or route through `r2engine`.
    ///
    /// ### Example
    ///
    /// ```rust
    /// export_instruction(&input, InstructionAction::Dec, ExportFormat::CLike)
    /// ```
    ///
    /// Return an explicit residual unless the output is produced by an
    /// engine-owned function decompile route.
    pub R2PLUGIN_DIRECT_CLIKE_BLOCK_DECOMPILE_EXPORT,
    Warn,
    "r2plugin must not export C-like block decompile output without FunctionFacts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` constructs `r2dec` AST nodes directly.
    ///
    /// ### Why is this bad?
    ///
    /// `r2dec` AST nodes are renderer-owned output. Plugin block surfaces do
    /// not have certified `FunctionFacts`, so they must route through
    /// engine-owned residual payloads instead of constructing even comment-only
    /// renderer AST locally.
    ///
    /// ### Example
    ///
    /// ```rust
    /// r2dec::CStmt::Comment("residual".to_string())
    /// ```
    ///
    /// Use an engine-owned residual JSON helper or a full engine decompile
    /// request.
    pub R2PLUGIN_DIRECT_R2DEC_AST_OWNERSHIP,
    Warn,
    "r2plugin must not construct r2dec AST nodes directly"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2plugin` calls `r2dec` fallback-comment
    /// renderers directly.
    ///
    /// ### Why is this bad?
    ///
    /// Fallback/refusal text is part of engine route policy. The plugin may
    /// expose an FFI command, but it must ask `r2engine` for the chosen
    /// fallback/refusal output instead of assembling renderer comments itself.
    ///
    /// ### Example
    ///
    /// ```rust
    /// r2dec::artifact_guard_fallback_comment(name, reason)
    /// ```
    ///
    /// Use an engine-owned fallback helper or request/response route.
    pub R2PLUGIN_DIRECT_R2DEC_FALLBACK_COMMENT,
    Warn,
    "r2plugin must not call r2dec fallback-comment renderers directly"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2plugin` directly constructs an
    /// `r2dec::Decompiler` / `r2dec::DecompilerInput`, or directly calls
    /// `Decompiler::decompile` / `Decompiler::decompile_input`.
    ///
    /// ### Why is this bad?
    ///
    /// Plugin glue must not own route selection, fallback policy, render cache
    /// identity, or the final `FunctionFacts` contract. Direct renderer use lets
    /// the plugin bypass `r2engine::EngineFunctionDecompileRequest`, so missing
    /// evidence can become executable C again.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let decompiler = r2dec::Decompiler::new(config);
    /// decompiler.decompile(&func);
    /// ```
    ///
    /// Use `r2engine::EngineFunctionDecompileRequest` and
    /// `EngineSession::decompile_function(...)`.
    pub R2PLUGIN_DIRECT_R2DEC_DECOMPILER_OWNERSHIP,
    Warn,
    "r2plugin production decompile must route through r2engine, not direct r2dec"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when the production `r2plugin` one-function decompile path
    /// directly constructs or calls `r2dec` decompiler/lowering APIs.
    ///
    /// ### Why is this bad?
    ///
    /// Decompile-one-function is an engine request. If plugin glue constructs
    /// renderer inputs, renderer instances, AST builders, or direct lowering
    /// calls, it bypasses `r2engine` route selection, cache identity, fallback
    /// policy, and the final `FunctionFacts` render contract.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn decompile_one_function(...) {
    ///     r2dec::DecompilerInput::new(ssa, context);
    ///     r2dec::lower_function_to_c(&input);
    /// }
    /// ```
    ///
    /// Use `r2engine::EngineFunctionDecompileRequest` and
    /// `EngineSession::decompile_function(...)`.
    pub R2PLUGIN_DECOMPILE_ONE_FUNCTION_DIRECT_R2DEC,
    Warn,
    "r2plugin decompile-one-function must call r2engine, not r2dec decompiler/lowering APIs"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` tests assert source-shaped C snippets such as
    /// `return 1;` or `if (...)` from raw `Decompiler::decompile(&func)`
    /// output.
    ///
    /// ### Why is this bad?
    ///
    /// Raw `SSAFunction` decompile output does not prove that the rendered C is
    /// backed by canonical CFG/dataflow/type facts. Tests should assert the
    /// fold/AST/certificate invariant first, then use final text only for
    /// narrow stability or residual/refusal coverage.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let output = decompiler.decompile(&func);
    /// assert!(output.contains("return 1;"));
    /// ```
    ///
    /// Use instead a folded `CStmt::Return`, built AST, or render certificate
    /// invariant.
    pub R2DEC_SOURCE_SHAPED_DECOMPILE_ORACLE,
    Warn,
    "r2dec tests must not bless source-shaped C from raw SSAFunction decompile output"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` falls back from a missing extracted branch condition
    /// to `CExpr::IntLit(1)`.
    ///
    /// ### Why is this bad?
    ///
    /// A missing branch predicate is not proof of a true condition. Rendering
    /// `if (1)` makes unresolved control flow look executable and confident.
    /// The renderer must emit an explicit residual/refusal comment unless the
    /// condition is backed by SSA/control evidence.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fold_ctx.extract_condition_from_block(block).unwrap_or(CExpr::IntLit(1));
    /// ```
    ///
    /// Use instead an explicit unresolved-branch residual.
    pub R2DEC_DEFAULT_TRUE_BRANCH_CONDITION,
    Warn,
    "r2dec must not default missing branch predicates to true"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` branch condition extraction can fall back
    /// to local/symbolic predicate recovery without first requiring
    /// `FunctionFacts` branch predicate evidence.
    ///
    /// ### Why is this bad?
    ///
    /// A rendered branch condition is executable control flow. Local flag,
    /// symbolic, or prepared-view recovery can be useful in legacy rendering,
    /// but certified rendering must only structure an `if`/loop condition when
    /// the condition expression is derived from canonical FunctionFacts control
    /// facts.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.fold_ctx.extract_condition(op)
    /// self.local_branch_condition_expr(block, idx, cond, 0)
    /// ```
    ///
    /// In certified rendering, return `None` before those fallbacks unless
    /// `FunctionControlFacts::branch_for_block` supplies the predicate and
    /// comparison proof.
    pub R2DEC_CERTIFIED_BRANCH_CONDITION_FALLBACK,
    Warn,
    "certified r2dec branch conditions must come from FunctionFacts control facts"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` switch structuring emits `switch` syntax
    /// from selector/region shape without proving selector, case targets, and
    /// default target against `FunctionFacts` switch facts.
    ///
    /// ### Why is this bad?
    ///
    /// A switch is executable control flow. Selector proof alone does not prove
    /// case values or targets; rendering cases without the canonical
    /// `FunctionControlFacts::switches` payload can invent control structure.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.record_switch_render_proof(block, selector, cases, default);
    /// CStmt::Switch { ... }
    /// ```
    ///
    /// In certified rendering, require an exact `FunctionControlFacts::switches`
    /// match before emitting switch syntax; otherwise render a residual.
    pub R2DEC_CERTIFIED_SWITCH_STRUCTURE_FALLBACK,
    Warn,
    "certified r2dec switch rendering must require FunctionFacts switch structure proof"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` loop structuring emits `while`/`do while`
    /// from region shape without proving the loop against
    /// `FunctionFacts` loop structure facts.
    ///
    /// ### Why is this bad?
    ///
    /// A loop is executable control flow and includes more than a condition:
    /// body membership, latches, and exits must agree with the canonical loop
    /// certificate. Branch predicate proof alone is not enough to render a
    /// certified loop.
    ///
    /// ### Example
    ///
    /// ```rust
    /// self.record_loop_render_proof(header, predicate, value, body);
    /// CStmt::while_loop(cond, body_stmt)
    /// ```
    ///
    /// In certified rendering, require an exact `FunctionControlFacts::loops`
    /// match before emitting the loop; otherwise render an explicit residual.
    pub R2DEC_CERTIFIED_LOOP_STRUCTURE_FALLBACK,
    Warn,
    "certified r2dec loop rendering must require FunctionFacts loop structure proof"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2dec` structures `Region::IfThenElse` into executable
    /// `CStmt::if_stmt` output without recording a branch render proof.
    ///
    /// ### Why is this bad?
    ///
    /// A rendered `if` is executable control flow. In certified mode it must
    /// be tied to the canonical `FunctionFacts` branch predicate for the
    /// condition block. Otherwise fake branch structure can survive validation
    /// as source-shaped C.
    ///
    /// ### Example
    ///
    /// ```rust
    /// Region::IfThenElse { .. } => CStmt::if_stmt(cond, then_stmt, else_stmt)
    /// ```
    ///
    /// Record `record_branch_render_proof(cond_block, predicate, value)` before
    /// emitting the `if` node, then validate it against `FunctionControlFacts`.
    pub R2DEC_CERTIFIED_BRANCH_RENDER_PROOF,
    Warn,
    "r2dec certified branch rendering must record FunctionFacts branch proof identity"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` uses broad local analysis presence, such
    /// as `has_definitions()` or `has_stack_slots()`, as proof that a synthetic
    /// stack local may be rendered.
    ///
    /// ### Why is this bad?
    ///
    /// Seeing a stack-shaped expression or any local definitions is not proof
    /// that an offset is a real local, stack argument, saved slot, or typed
    /// field. Executable stack locals must be backed by typed stack-slot facts
    /// in `FunctionFacts`; otherwise the renderer should leave a residual/raw
    /// expression.
    ///
    /// ### Example
    ///
    /// ```rust
    /// if offset < 0 && (self.has_stack_slots() || self.has_definitions()) {
    ///     return Some(Self::stack_synthetic_name(offset));
    /// }
    /// ```
    ///
    /// Use instead a typed stack-slot match from `FunctionFacts`.
    pub R2DEC_UNCERTIFIED_STACK_LOCAL_SYNTHESIS,
    Warn,
    "r2dec must not synthesize stack locals from broad local analysis presence"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2dec` defines fallback helpers that manufacture
    /// aggregate field names such as `f_<offset>` from a bare type name.
    ///
    /// ### Why is this bad?
    ///
    /// A `struct` or typedef-looking name is not proof that an offset is a real
    /// field. Member syntax must come from an explicit external layout,
    /// certified field access fact, or typed oracle evidence. Otherwise the
    /// renderer should keep pointer arithmetic/residual shape instead of
    /// inventing source-like fields.
    ///
    /// ### Example
    ///
    /// ```rust
    /// fn fallback_aggregate_field_name(type_name: &str, offset: u64) -> Option<String> {
    ///     Some(format!("f_{offset:x}"))
    /// }
    /// ```
    ///
    /// Use external layout facts carried through `FunctionFacts` instead.
    pub R2DEC_UNCERTIFIED_FIELD_PLACEHOLDER,
    Warn,
    "r2dec must not manufacture aggregate field placeholders without layout proof"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when certified `r2dec` memory lowering can construct member
    /// syntax from local type hints or type-oracle names without checking
    /// `FunctionTypeFacts::field_access_certificates`.
    ///
    /// ### Why is this bad?
    ///
    /// A type-looking base and external layout are not proof that a specific
    /// load/store is a real field access. Certified executable member syntax
    /// must be backed by explicit field-access evidence.
    pub R2DEC_CERTIFIED_MEMBER_FIELD_CERTIFICATE,
    Warn,
    "certified r2dec structured memory rendering must require direction-exact FunctionRenderFacts evidence"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2engine` constructs `r2dec::VariableRecovery` to infer
    /// signature parameters.
    ///
    /// ### Why is this bad?
    ///
    /// `r2engine` owns orchestration, while `r2types` owns type/signature
    /// inference and `r2dec` owns rendering. Pulling renderer variable recovery
    /// into the engine makes type inference depend on decompiler-local naming
    /// heuristics and reintroduces a second signature owner.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let mut vars = r2dec::VariableRecovery::new("rsp", "rbp", 64);
    /// vars.recover(&ssa);
    /// ```
    ///
    /// Use `r2types::recover_signature_params_from_ssa` instead.
    pub R2ENGINE_R2DEC_VARIABLE_RECOVERY_OWNERSHIP,
    Warn,
    "r2engine must not use r2dec VariableRecovery for signature inference"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2engine` calls `r2dec` fallback-comment helpers.
    ///
    /// ### Why is this bad?
    ///
    /// Fallback/refusal text is route policy. `r2engine` owns the route,
    /// refusal, and cache decision, so it must construct engine-owned
    /// fallback comments from typed `FunctionFacts` instead of importing
    /// renderer helper policy.
    ///
    /// ### Example
    ///
    /// ```rust
    /// r2dec::semantic_fallback_comment(name, facts.semantics.as_ref())
    /// ```
    ///
    /// Use `r2engine::semantic_fallback_comment_for_facts(...)` or another
    /// engine-owned fallback helper.
    pub R2ENGINE_R2DEC_FALLBACK_COMMENT_OWNERSHIP,
    Warn,
    "r2engine must own fallback/refusal comments instead of calling r2dec fallback helpers"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2types` code outside `role_registry` calls the
    /// raw role-name signature lookup APIs directly.
    ///
    /// ### Why is this bad?
    ///
    /// Role names are weak hints. Signature/type projection must flow through
    /// `NativeWorkerRoleIdentity` and semantic evidence gates so name-only
    /// summaries cannot become authoritative type facts.
    ///
    /// ### Example
    ///
    /// ```rust
    /// role_registry::signature_hint_for_name_candidates([name], 0);
    /// ```
    ///
    /// Use instead `signature_hint_for_role_identity(...)` after r2sym has
    /// produced non-name semantic evidence.
    pub R2TYPES_ROLE_NAME_SIGNATURE_HINT_OWNERSHIP,
    Warn,
    "r2types consumers must not project signatures directly from role names"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when production `r2engine` or `r2dec` assigns directly to canonical
    /// `FunctionFacts` owner fields such as `types`, `summary_view`,
    /// `assumption_usage`, `proof`, `render`, or `control`.
    ///
    /// ### Why is this bad?
    ///
    /// `FunctionFacts` is the typed combined contract. Direct field writes in
    /// consumers create silent side channels where type, semantic, proof, or
    /// render evidence can be replaced without the canonical invariant methods
    /// that refresh plans and normalize certificates.
    ///
    /// ### Example
    ///
    /// ```rust
    /// function_facts.types = type_facts;
    /// ```
    ///
    /// Use instead `FunctionFacts` mutation methods such as
    /// `replace_type_facts(...)`, `set_summary_set(...)`, or
    /// `merge_proof_coverage(...)`.
    pub R2TYPES_FUNCTION_FACTS_FIELD_OWNERSHIP,
    Warn,
    "FunctionFacts owner fields must be mutated through r2types methods"
);

rustc_session::declare_lint_pass!(R2sleighLintPass => [
    STRING_PREFIX_SEMANTIC_CLASSIFICATION,
    R2_JSON_COMMAND_INTERNAL_SEAM,
    R2DEC_DIRECT_KNOWN_SIGNATURE_LOOKUP,
    R2DEC_RAW_CALLEE_IMPORT_POLICY,
    R2DEC_RAW_CALL_TARGET_ADDRESS_PARSER,
    R2DEC_CALL_TARGET_POLICY_OWNERSHIP,
    R2DEC_CALLEE_RESOLUTION_FALLBACK_OWNERSHIP,
    R2DEC_UNCERTIFIED_CALL_ARG_CALL_POLICY,
    R2DEC_CALL_ARG_SOURCE_NAME_AUTHORITY,
    R2DEC_CALL_ARG_SOURCE_CALL_AUTHORITY,
    R2DEC_CERTIFIED_RAW_CALL_ARG_FALLBACK,
    R2DEC_CERTIFIED_CALL_ARG_PREFIX_PROOF,
    R2DEC_DIRECT_ZERO_ARG_CALL_FALLBACK,
    R2DEC_CERTIFIED_CALL_RESULT_REPLAY_FALLBACK,
    R2DEC_CERTIFIED_PREPARED_CALL_ARG_EXPR_PROOF,
    R2DEC_CERTIFIED_EXECUTABLE_POST_CALL_REPAIR,
    R2DEC_CERTIFIED_CALL_RENDER_PROOF_LOCAL_EQUALITY,
    R2DEC_CERTIFIED_RETURN_LOCAL_EXPR_FALLBACK,
    R2DEC_CERTIFIED_RETURN_CALL_RESULT_FACT,
    R2DEC_CERTIFIED_LOCAL_POST_CALL_SOURCE_FACT,
    R2DEC_LOCAL_AUTHORITATIVE_CALL_ARG_INFERENCE,
    R2DEC_SUMMARY_ROUTE_EXECUTABLE_C,
    R2DEC_SUMMARY_RENDER_EXECUTABLE_CSTMT,
    R2DEC_ROUTE_POLICY_OWNERSHIP,
    R2DEC_MISSING_DECOMPILE_ROUTE_DEFAULT_STANDARD,
    R2DEC_BUILD_FUNCTION_REQUIRES_ROUTE_FACTS,
    R2DEC_SUMMARY_RENDER_ROUTE_SIDE_CHANNEL,
    R2DEC_LOCAL_HEADER_ARITY_REPAIR,
    R2ENGINE_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
    R2ENGINE_R2DEC_SUMMARY_RENDER_ROUTE_SIDE_CHANNEL,
    R2ENGINE_DECOMPILE_FACTS_SPINE_OWNERSHIP,
    R2ENGINE_SUMMARY_DECOMPILE_ROUTE_SIDE_CHANNEL,
    R2ENGINE_SUMMARY_ONLY_DECOMPILE_API,
    R2ENGINE_LOWER_LEVEL_DECOMPILE_API_BYPASS,
    R2ENGINE_RENDER_TIME_SEMANTICS_SUPPRESSION,
    R2ENGINE_DECOMPILE_TYPE_OVERRIDE_SIDE_CHANNEL,
    R2ENGINE_DECOMPILE_FALLBACK_COMMENT_SIDE_CHANNEL,
    R2ENGINE_DECOMPILE_RENDER_CACHE_PRE_ROUTE_FACTS,
    R2ENGINE_ARTIFACTS_FACTS_SIDE_CHANNEL,
    R2ENGINE_DECOMPILE_ROUTE_TYPE_FACTS_SIDE_CHANNEL,
    R2ENGINE_DECOMPILER_INPUT_ROUTE_REPLAN_SIDE_CHANNEL,
    R2ENGINE_DECOMPILER_INPUT_HELPER_TEST_SUPPORT_ONLY,
    R2ENGINE_PREPARED_DECOMPILE_EVIDENCE_SIDE_CHANNEL,
    R2DEC_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
    R2DEC_DECOMPILER_CONTEXT_CALLEE_RESOLUTION_SIDE_CHANNEL,
    R2DEC_DIRECT_TYPE_FACTS_MUTATOR,
    R2DEC_LOCAL_SIGNATURE_ENRICHMENT,
    R2DEC_SWITCH_CASE_VALUE_OWNERSHIP,
    R2DEC_UNCERTIFIED_SWITCH_SELECTOR_ROOT_FALLBACK,
    R2DEC_CERTIFIED_PREPARED_SWITCH_SELECTOR_PROOF,
    R2DEC_SWITCH_SELECTOR_SINGLE_FACT_FALLBACK,
    R2DEC_PREPARED_DIRECT_TARGET_REPARSE,
    R2DEC_DIRECT_PREPARED_CALLSITE_CERTIFICATES,
    R2DEC_DIRECT_PREPARED_RENDER_CERTIFICATES,
    R2DEC_CALL_RESULT_STACK_OWNER_FALLBACK,
    R2DEC_CALL_RESULT_SOURCE_EXPR_OWNER_FALLBACK,
    R2DEC_CERTIFIED_CALL_RESULT_RETURN_REGISTER_FALLBACK,
    R2DEC_CERTIFIED_CALL_RESULT_ALIAS_OWNER_FALLBACK,
    R2DEC_CERTIFIED_LOCAL_CALL_OWNERSHIP_FALLBACK,
    R2DEC_CERTIFIED_CALL_RESULT_PRESERVATION_FALLBACK,
    R2DEC_CERTIFIED_DUPLICATE_CALL_PRUNING_FALLBACK,
    R2DEC_CERTIFIED_VISIBLE_OWNER_SOURCE_LOOKUP,
    R2DEC_CERTIFIED_PREPARED_RESULT_OWNER_EXPR,
    R2DEC_CERTIFIED_PREPARED_RESULT_OWNER_FACT,
    R2DEC_CERTIFIED_STACK_RETURN_RENDER_FACTS,
    R2DEC_CERTIFIED_STACK_LOCAL_IDENTITY,
    R2DEC_CERTIFIED_STACK_OWNER_PROOF_RECOMPOSITION,
    R2DEC_CERTIFIED_STACK_LOCAL_TYPE_OWNERSHIP,
    R2DEC_CERTIFIED_LOCAL_TYPE_HINTS,
    R2DEC_CERTIFIED_LOCAL_STACK_RECOVERY_BYPASS,
    R2DEC_DIRECT_PREPARED_CALL_RESULT_CERTIFICATES,
    R2DEC_DIRECT_PREPARED_CONTROL_FACTS,
    R2PLUGIN_RAW_DIRECT_CALL_TARGET,
    R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
    R2PLUGIN_TYPE_WRITEBACK_MUTATION_KIND_OWNERSHIP,
    R2PLUGIN_DIRECT_TYPE_WRITEBACK_ANALYSIS_OWNERSHIP,
    R2PLUGIN_TYPE_WRITEBACK_APPLY_THRESHOLD_OWNERSHIP,
    R2PLUGIN_FUNCTION_FACTS_TYPES_OWNERSHIP,
    R2PLUGIN_FUNCTION_FACTS_REPORT_OWNERSHIP,
    R2PLUGIN_TYPE_WRITEBACK_JSON_PROJECTION_OWNERSHIP,
    R2PLUGIN_FUNCTION_ANALYSIS_REPORT_JSON_PROJECTION_OWNERSHIP,
    R2PLUGIN_REPORT_JSON_SCHEMA_OWNERSHIP,
    R2PLUGIN_TYPE_WRITEBACK_REPORT_ASSEMBLY_OWNERSHIP,
    R2PLUGIN_INTERPROC_SCOPE_REPORT_OWNERSHIP,
    R2PLUGIN_SEMANTIC_REPORT_PROJECTION_OWNERSHIP,
    R2PLUGIN_TYPED_EXTERNAL_CONTEXT_OWNERSHIP,
    R2PLUGIN_EXTERNAL_TYPE_PARSER_RENDERER_TYPE_OWNERSHIP,
    R2PLUGIN_SIGNATURE_CONFIDENCE_RENDERER_TYPE_OWNERSHIP,
    R2PLUGIN_SIGNATURE_SPEC_RENDERER_TYPE_OWNERSHIP,
    R2PLUGIN_CTYPE_BRIDGE_OWNERSHIP,
    R2PLUGIN_RENDERER_CONFIG_ARCH_TARGET_OWNERSHIP,
    R2PLUGIN_VARIABLE_RECOVERY_OWNERSHIP,
    R2PLUGIN_METADATA_TYPE_HINT_OWNERSHIP,
    R2PLUGIN_ENGINE_POLICY_OWNERSHIP,
    R2PLUGIN_DECOMPILE_METADATA_POLICY_OWNERSHIP,
    R2PLUGIN_UNPREPARED_DECOMPILE_ORACLE,
    R2PLUGIN_DECOMPILER_INPUT_EXECUTABLE_C_ORACLE,
    R2PLUGIN_DECOMPILER_INPUT_TEST_BYPASS,
    R2PLUGIN_DIRECT_R2DEC_OP_LOWERING,
    R2PLUGIN_DIRECT_CLIKE_BLOCK_DECOMPILE_EXPORT,
    R2PLUGIN_DIRECT_R2DEC_AST_OWNERSHIP,
    R2PLUGIN_DIRECT_R2DEC_FALLBACK_COMMENT,
    R2PLUGIN_DIRECT_R2DEC_DECOMPILER_OWNERSHIP,
    R2PLUGIN_DECOMPILE_ONE_FUNCTION_DIRECT_R2DEC,
    R2DEC_SOURCE_SHAPED_DECOMPILE_ORACLE,
    R2DEC_DEFAULT_TRUE_BRANCH_CONDITION,
    R2DEC_CERTIFIED_BRANCH_CONDITION_FALLBACK,
    R2DEC_CERTIFIED_SWITCH_STRUCTURE_FALLBACK,
    R2DEC_CERTIFIED_LOOP_STRUCTURE_FALLBACK,
    R2DEC_CERTIFIED_BRANCH_RENDER_PROOF,
    R2DEC_UNCERTIFIED_STACK_LOCAL_SYNTHESIS,
    R2DEC_UNCERTIFIED_FIELD_PLACEHOLDER,
    R2DEC_CERTIFIED_MEMBER_FIELD_CERTIFICATE,
    R2ENGINE_R2DEC_VARIABLE_RECOVERY_OWNERSHIP,
    R2ENGINE_R2DEC_FALLBACK_COMMENT_OWNERSHIP,
    R2TYPES_ROLE_NAME_SIGNATURE_HINT_OWNERSHIP,
    R2TYPES_FUNCTION_FACTS_FIELD_OWNERSHIP
]);

#[unsafe(no_mangle)]
pub fn register_lints(sess: &rustc_session::Session, lint_store: &mut rustc_lint::LintStore) {
    dylint_linting::init_config(sess);
    lint_store.register_lints(&[
        STRING_PREFIX_SEMANTIC_CLASSIFICATION,
        R2_JSON_COMMAND_INTERNAL_SEAM,
        R2DEC_DIRECT_KNOWN_SIGNATURE_LOOKUP,
        R2DEC_RAW_CALLEE_IMPORT_POLICY,
        R2DEC_RAW_CALL_TARGET_ADDRESS_PARSER,
        R2DEC_CALL_TARGET_POLICY_OWNERSHIP,
        R2DEC_CALLEE_RESOLUTION_FALLBACK_OWNERSHIP,
        R2DEC_UNCERTIFIED_CALL_ARG_CALL_POLICY,
        R2DEC_CALL_ARG_SOURCE_NAME_AUTHORITY,
        R2DEC_CALL_ARG_SOURCE_CALL_AUTHORITY,
        R2DEC_CERTIFIED_RAW_CALL_ARG_FALLBACK,
        R2DEC_CERTIFIED_CALL_ARG_PREFIX_PROOF,
        R2DEC_DIRECT_ZERO_ARG_CALL_FALLBACK,
        R2DEC_CERTIFIED_CALL_RESULT_REPLAY_FALLBACK,
        R2DEC_CERTIFIED_PREPARED_CALL_ARG_EXPR_PROOF,
        R2DEC_CERTIFIED_EXECUTABLE_POST_CALL_REPAIR,
        R2DEC_CERTIFIED_CALL_RENDER_PROOF_LOCAL_EQUALITY,
        R2DEC_CERTIFIED_RETURN_LOCAL_EXPR_FALLBACK,
        R2DEC_CERTIFIED_RETURN_CALL_RESULT_FACT,
        R2DEC_CERTIFIED_LOCAL_POST_CALL_SOURCE_FACT,
        R2DEC_LOCAL_AUTHORITATIVE_CALL_ARG_INFERENCE,
        R2DEC_SUMMARY_ROUTE_EXECUTABLE_C,
        R2DEC_SUMMARY_RENDER_EXECUTABLE_CSTMT,
        R2DEC_ROUTE_POLICY_OWNERSHIP,
        R2DEC_MISSING_DECOMPILE_ROUTE_DEFAULT_STANDARD,
        R2DEC_BUILD_FUNCTION_REQUIRES_ROUTE_FACTS,
        R2DEC_SUMMARY_RENDER_ROUTE_SIDE_CHANNEL,
        R2DEC_LOCAL_HEADER_ARITY_REPAIR,
        R2ENGINE_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
        R2ENGINE_R2DEC_SUMMARY_RENDER_ROUTE_SIDE_CHANNEL,
        R2ENGINE_DECOMPILE_FACTS_SPINE_OWNERSHIP,
        R2ENGINE_SUMMARY_DECOMPILE_ROUTE_SIDE_CHANNEL,
        R2ENGINE_SUMMARY_ONLY_DECOMPILE_API,
        R2ENGINE_LOWER_LEVEL_DECOMPILE_API_BYPASS,
        R2ENGINE_RENDER_TIME_SEMANTICS_SUPPRESSION,
        R2ENGINE_DECOMPILE_TYPE_OVERRIDE_SIDE_CHANNEL,
        R2ENGINE_DECOMPILE_FALLBACK_COMMENT_SIDE_CHANNEL,
        R2ENGINE_DECOMPILE_RENDER_CACHE_PRE_ROUTE_FACTS,
        R2ENGINE_CACHE_POLICY_OWNERSHIP,
        R2ENGINE_ARTIFACTS_FACTS_SIDE_CHANNEL,
        R2ENGINE_DECOMPILE_ROUTE_TYPE_FACTS_SIDE_CHANNEL,
        R2ENGINE_DECOMPILER_INPUT_ROUTE_REPLAN_SIDE_CHANNEL,
        R2ENGINE_DECOMPILER_INPUT_HELPER_TEST_SUPPORT_ONLY,
        R2ENGINE_PREPARED_DECOMPILE_EVIDENCE_SIDE_CHANNEL,
        R2DEC_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
        R2DEC_DECOMPILER_CONTEXT_CALLEE_RESOLUTION_SIDE_CHANNEL,
        R2DEC_DIRECT_TYPE_FACTS_MUTATOR,
        R2DEC_LOCAL_SIGNATURE_ENRICHMENT,
        R2DEC_SWITCH_CASE_VALUE_OWNERSHIP,
        R2DEC_UNCERTIFIED_SWITCH_SELECTOR_ROOT_FALLBACK,
        R2DEC_CERTIFIED_PREPARED_SWITCH_SELECTOR_PROOF,
        R2DEC_SWITCH_SELECTOR_SINGLE_FACT_FALLBACK,
        R2DEC_PREPARED_DIRECT_TARGET_REPARSE,
        R2DEC_DIRECT_PREPARED_CALLSITE_CERTIFICATES,
        R2DEC_DIRECT_PREPARED_RENDER_CERTIFICATES,
        R2DEC_CALL_RESULT_STACK_OWNER_FALLBACK,
        R2DEC_CALL_RESULT_SOURCE_EXPR_OWNER_FALLBACK,
        R2DEC_CERTIFIED_CALL_RESULT_RETURN_REGISTER_FALLBACK,
        R2DEC_CERTIFIED_CALL_RESULT_ALIAS_OWNER_FALLBACK,
        R2DEC_CERTIFIED_LOCAL_CALL_OWNERSHIP_FALLBACK,
        R2DEC_CERTIFIED_CALL_RESULT_PRESERVATION_FALLBACK,
        R2DEC_CERTIFIED_DUPLICATE_CALL_PRUNING_FALLBACK,
        R2DEC_CERTIFIED_VISIBLE_OWNER_SOURCE_LOOKUP,
        R2DEC_CERTIFIED_PREPARED_RESULT_OWNER_EXPR,
        R2DEC_CERTIFIED_PREPARED_RESULT_OWNER_FACT,
        R2DEC_CERTIFIED_STACK_RETURN_RENDER_FACTS,
        R2DEC_CERTIFIED_STACK_LOCAL_IDENTITY,
        R2DEC_CERTIFIED_STACK_OWNER_PROOF_RECOMPOSITION,
        R2DEC_CERTIFIED_STACK_LOCAL_TYPE_OWNERSHIP,
        R2DEC_CERTIFIED_LOCAL_TYPE_HINTS,
        R2DEC_CERTIFIED_LOCAL_STACK_RECOVERY_BYPASS,
        R2DEC_DIRECT_PREPARED_CALL_RESULT_CERTIFICATES,
        R2DEC_DIRECT_PREPARED_CONTROL_FACTS,
        R2PLUGIN_RAW_DIRECT_CALL_TARGET,
        R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
        R2PLUGIN_TYPE_WRITEBACK_MUTATION_KIND_OWNERSHIP,
        R2PLUGIN_DIRECT_TYPE_WRITEBACK_ANALYSIS_OWNERSHIP,
        R2PLUGIN_TYPE_WRITEBACK_APPLY_THRESHOLD_OWNERSHIP,
        R2PLUGIN_FUNCTION_FACTS_TYPES_OWNERSHIP,
        R2PLUGIN_FUNCTION_FACTS_REPORT_OWNERSHIP,
        R2PLUGIN_TYPE_WRITEBACK_JSON_PROJECTION_OWNERSHIP,
        R2PLUGIN_FUNCTION_ANALYSIS_REPORT_JSON_PROJECTION_OWNERSHIP,
        R2PLUGIN_REPORT_JSON_SCHEMA_OWNERSHIP,
        R2PLUGIN_TYPE_WRITEBACK_REPORT_ASSEMBLY_OWNERSHIP,
        R2PLUGIN_INTERPROC_SCOPE_REPORT_OWNERSHIP,
        R2PLUGIN_SEMANTIC_REPORT_PROJECTION_OWNERSHIP,
        R2PLUGIN_TYPED_EXTERNAL_CONTEXT_OWNERSHIP,
        R2PLUGIN_EXTERNAL_TYPE_PARSER_RENDERER_TYPE_OWNERSHIP,
        R2PLUGIN_SIGNATURE_CONFIDENCE_RENDERER_TYPE_OWNERSHIP,
        R2PLUGIN_SIGNATURE_SPEC_RENDERER_TYPE_OWNERSHIP,
        R2PLUGIN_CTYPE_BRIDGE_OWNERSHIP,
        R2PLUGIN_RENDERER_CONFIG_ARCH_TARGET_OWNERSHIP,
        R2PLUGIN_VARIABLE_RECOVERY_OWNERSHIP,
        R2PLUGIN_METADATA_TYPE_HINT_OWNERSHIP,
        R2PLUGIN_ENGINE_POLICY_OWNERSHIP,
        R2PLUGIN_DECOMPILE_METADATA_POLICY_OWNERSHIP,
        R2PLUGIN_UNPREPARED_DECOMPILE_ORACLE,
        R2PLUGIN_DECOMPILER_INPUT_EXECUTABLE_C_ORACLE,
        R2PLUGIN_DECOMPILER_INPUT_TEST_BYPASS,
        R2PLUGIN_DIRECT_R2DEC_OP_LOWERING,
        R2PLUGIN_DIRECT_CLIKE_BLOCK_DECOMPILE_EXPORT,
        R2PLUGIN_DIRECT_R2DEC_AST_OWNERSHIP,
        R2PLUGIN_DIRECT_R2DEC_FALLBACK_COMMENT,
        R2PLUGIN_DIRECT_R2DEC_DECOMPILER_OWNERSHIP,
        R2PLUGIN_DECOMPILE_ONE_FUNCTION_DIRECT_R2DEC,
        R2DEC_SOURCE_SHAPED_DECOMPILE_ORACLE,
        R2DEC_DEFAULT_TRUE_BRANCH_CONDITION,
        R2DEC_CERTIFIED_BRANCH_CONDITION_FALLBACK,
        R2DEC_CERTIFIED_SWITCH_STRUCTURE_FALLBACK,
        R2DEC_CERTIFIED_LOOP_STRUCTURE_FALLBACK,
        R2DEC_CERTIFIED_BRANCH_RENDER_PROOF,
        R2DEC_UNCERTIFIED_STACK_LOCAL_SYNTHESIS,
        R2DEC_UNCERTIFIED_FIELD_PLACEHOLDER,
        R2DEC_CERTIFIED_MEMBER_FIELD_CERTIFICATE,
        R2ENGINE_R2DEC_VARIABLE_RECOVERY_OWNERSHIP,
        R2ENGINE_R2DEC_FALLBACK_COMMENT_OWNERSHIP,
        R2TYPES_ROLE_NAME_SIGNATURE_HINT_OWNERSHIP,
        R2TYPES_FUNCTION_FACTS_FIELD_OWNERSHIP,
    ]);
    lint_store.register_late_pass(|_| Box::new(R2sleighLintPass));
}

impl<'tcx> LateLintPass<'tcx> for R2sleighLintPass {
    fn check_item(&mut self, cx: &LateContext<'tcx>, item: &'tcx Item<'tcx>) {
        if is_r2plugin_type_hint_policy_span(cx, item.span)
            && plugin_metadata_type_hint_policy_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_METADATA_TYPE_HINT_OWNERSHIP,
                item.span,
                "r2plugin must delegate metadata-derived type hints to r2engine/r2types",
            );
        }

        if is_r2plugin_span(cx, item.span) && plugin_engine_policy_ownership_item(cx, item) {
            span_lint(
                cx,
                R2PLUGIN_ENGINE_POLICY_OWNERSHIP,
                item.span,
                "r2plugin must delegate cache/session/route policy to r2engine",
            );
        }

        if is_r2plugin_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && plugin_typed_external_context_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_TYPED_EXTERNAL_CONTEXT_OWNERSHIP,
                item.span,
                "r2plugin must not return ParsedExternalContext from typed FFI context; build EngineExternalContextInput and call r2engine::parse_typed_external_context",
            );
        }

        if is_r2plugin_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && plugin_decompile_metadata_policy_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_DECOMPILE_METADATA_POLICY_OWNERSHIP,
                item.span,
                "r2plugin must pass decompile metadata payloads to r2engine instead of parsing aliases or selecting display names",
            );
        }

        if is_r2plugin_span(cx, item.span)
            && plugin_decompiler_input_executable_c_oracle_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_DECOMPILER_INPUT_EXECUTABLE_C_ORACLE,
                item.span,
                "r2plugin tests must not assert executable C body text through decompiler_input_from_artifact; use EngineSession::decompile_function",
            );
        }

        if is_r2plugin_span(cx, item.span) && plugin_decompiler_input_test_bypass_item(cx, item) {
            span_lint(
                cx,
                R2PLUGIN_DECOMPILER_INPUT_TEST_BYPASS,
                item.span,
                "r2plugin tests must route detached artifact rendering through r2engine, not direct DecompilerInput",
            );
        }

        if is_r2plugin_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && plugin_semantic_report_projection_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_SEMANTIC_REPORT_PROJECTION_OWNERSHIP,
                item.span,
                "r2plugin must consume r2sym-owned semantic report projections instead of defining local CompiledSemanticInfo helpers",
            );
        }

        if is_r2plugin_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && plugin_report_json_schema_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_REPORT_JSON_SCHEMA_OWNERSHIP,
                item.span,
                "r2plugin must consume r2engine-owned report JSON schema DTOs instead of defining local report structs",
            );
        }

        if is_r2plugin_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && plugin_interproc_scope_report_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_INTERPROC_SCOPE_REPORT_OWNERSHIP,
                item.span,
                "r2plugin must route symbolic-scope/interproc report projection through r2engine",
            );
        }

        if is_r2plugin_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && plugin_type_writeback_report_assembly_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_TYPE_WRITEBACK_REPORT_ASSEMBLY_OWNERSHIP,
                item.span,
                "r2plugin must route type-writeback report assembly through r2engine",
            );
        }

        if is_r2plugin_span(cx, item.span)
            && plugin_external_type_parser_renderer_type_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_EXTERNAL_TYPE_PARSER_RENDERER_TYPE_OWNERSHIP,
                item.span,
                "r2plugin external type parsers must return r2types::CTypeLike through r2types::parse_external_type_like_spec, not r2dec::CType",
            );
        }

        if is_r2plugin_span(cx, item.span)
            && plugin_signature_confidence_renderer_type_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_SIGNATURE_CONFIDENCE_RENDERER_TYPE_OWNERSHIP,
                item.span,
                "r2plugin signature confidence tests must construct r2types::SignatureParamCandidate directly instead of routing through r2dec::CType wrappers",
            );
        }

        if is_r2plugin_span(cx, item.span)
            && plugin_signature_spec_renderer_type_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2PLUGIN_SIGNATURE_SPEC_RENDERER_TYPE_OWNERSHIP,
                item.span,
                "r2plugin signature fixtures must construct FunctionSignatureSpec with r2types::CTypeLike, not r2dec::CType",
            );
        }

        if is_r2plugin_span(cx, item.span) && plugin_ctype_bridge_ownership_item(cx, item) {
            span_lint(
                cx,
                R2PLUGIN_CTYPE_BRIDGE_OWNERSHIP,
                item.span,
                "r2plugin must assert r2types::CTypeLike directly instead of bridging through r2dec::CType",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_route_policy_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_ROUTE_POLICY_OWNERSHIP,
                item.span,
                "r2dec must not define route/refusal policy helpers; r2engine owns route selection",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_missing_route_defaults_to_standard_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_MISSING_DECOMPILE_ROUTE_DEFAULT_STANDARD,
                item.span,
                "r2dec must residualize missing FunctionFacts::decompile_route instead of defaulting to Standard",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_build_function_requires_route_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_BUILD_FUNCTION_REQUIRES_ROUTE_FACTS,
                item.span,
                "r2dec build_function must residualize before executable AST rendering when FunctionFacts::decompile_route is missing",
            );
        }

        if is_r2dec_lib_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_summary_render_route_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_SUMMARY_RENDER_ROUTE_SIDE_CHANNEL,
                item.span,
                "r2dec summary render APIs must derive route permission from FunctionFacts::decompile_route",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_local_header_arity_repair_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_LOCAL_HEADER_ARITY_REPAIR,
                item.span,
                "r2dec must not repair certified headers from local recovery or inference",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_local_signature_enrichment_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_LOCAL_SIGNATURE_ENRICHMENT,
                item.span,
                "r2dec must not enrich known signatures from names while constructing render context",
            );
        }

        if is_r2dec_analysis_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_local_authoritative_call_arg_inference_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_LOCAL_AUTHORITATIVE_CALL_ARG_INFERENCE,
                item.span,
                "r2dec must consume FunctionFacts callsite arguments instead of inferring authoritative call args locally",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_decompiler_context_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
                item.span,
                "r2engine must carry decompile route/callee evidence through FunctionFacts, not request or context side channels",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_r2dec_route_conversion_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_R2DEC_SUMMARY_RENDER_ROUTE_SIDE_CHANNEL,
                item.span,
                "r2engine must not define route conversion helpers or depend on r2dec route types",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_decompile_facts_spine_ownership_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_DECOMPILE_FACTS_SPINE_OWNERSHIP,
                item.span,
                "r2engine must assemble decompile evidence through attach_prepared_decompile_evidence/function_facts_for_decompile",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && raw_attach_prepared_decompile_evidence_signature_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_PREPARED_DECOMPILE_EVIDENCE_SIDE_CHANNEL,
                item.span,
                "attach_prepared_decompile_evidence must not accept raw function_names/symbols side channels",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_summary_decompile_route_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_SUMMARY_DECOMPILE_ROUTE_SIDE_CHANNEL,
                item.span,
                "r2engine summary decompile route/refusal must be carried by FunctionFacts, not request fields",
            );
        }

        if is_r2engine_lib_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_summary_only_decompile_api_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_SUMMARY_ONLY_DECOMPILE_API,
                item.span,
                "r2engine production decompile must not expose summary-only request or decompile_summary entrypoints without prepared SSA",
            );
        }

        if is_r2engine_lib_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_lower_level_decompile_api_bypass_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_LOWER_LEVEL_DECOMPILE_API_BYPASS,
                item.span,
                "r2engine must keep EngineDecompileRequest internal; expose EngineFunctionDecompileRequest for plugin/user decompile paths",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_render_time_semantics_suppression_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_RENDER_TIME_SEMANTICS_SUPPRESSION,
                item.span,
                "r2engine must route/refuse unrenderable summaries before render instead of clearing FunctionFacts semantics",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_decompile_type_override_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_DECOMPILE_TYPE_OVERRIDE_SIDE_CHANNEL,
                item.span,
                "r2engine must apply decompile type overrides through FunctionFacts",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_decompile_fallback_comment_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_DECOMPILE_FALLBACK_COMMENT_SIDE_CHANNEL,
                item.span,
                "r2engine must carry decompile fallback comments through FunctionFacts",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_artifacts_facts_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_ARTIFACTS_FACTS_SIDE_CHANNEL,
                item.span,
                "r2engine EngineArtifacts must not duplicate FunctionFacts semantic or route evidence",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_decompile_route_type_facts_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_DECOMPILE_ROUTE_TYPE_FACTS_SIDE_CHANNEL,
                item.span,
                "r2engine decompile route planning must not accept type facts outside FunctionFacts",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_decompiler_input_route_replan_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_DECOMPILER_INPUT_ROUTE_REPLAN_SIDE_CHANNEL,
                item.span,
                "r2engine decompiler input assembly must use the FunctionFacts route already attached by function_facts_for_decompile",
            );
        }

        if is_r2engine_span(cx, item.span)
            && engine_decompiler_input_helper_not_test_support_only_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_DECOMPILER_INPUT_HELPER_TEST_SUPPORT_ONLY,
                item.span,
                "r2engine raw decompiler input helper must be hidden behind cfg(test) or the explicit test-support feature",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && engine_prepared_decompile_evidence_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_PREPARED_DECOMPILE_EVIDENCE_SIDE_CHANNEL,
                item.span,
                "r2engine must attach prepared decompile evidence through FunctionFacts, not individual proof-map builders or setters",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_decompiler_context_route_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
                item.span,
                "r2dec DecompilerContext must not store route/render policy outside FunctionFacts",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_decompiler_context_callee_resolution_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_DECOMPILER_CONTEXT_CALLEE_RESOLUTION_SIDE_CHANNEL,
                item.span,
                "r2dec DecompilerContext must not store callee resolution outside FunctionFacts",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_direct_type_facts_mutator_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_DIRECT_TYPE_FACTS_MUTATOR,
                item.span,
                "r2dec production APIs must not mutate type facts outside FunctionFacts",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_certified_call_arg_prefix_proof_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_CALL_ARG_PREFIX_PROOF,
                item.span,
                "certified call proof validation must compare the full FunctionFacts callsite argument vector",
            );
        }

        if is_r2dec_span(cx, item.span) && r2dec_source_shaped_decompile_oracle_item(cx, item) {
            span_lint(
                cx,
                R2DEC_SOURCE_SHAPED_DECOMPILE_ORACLE,
                item.span,
                "r2dec tests must prove fold/AST/certificate invariants instead of source-shaped raw decompile text",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_uncertified_switch_selector_root_fallback_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_UNCERTIFIED_SWITCH_SELECTOR_ROOT_FALLBACK,
                item.span,
                "certified switch rendering must residualize before local switch_selector_roots fallback",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_prepared_call_view_direct_target_side_channel_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_PREPARED_DIRECT_TARGET_REPARSE,
                item.span,
                "r2dec prepared semantic view must read direct targets from FunctionFacts, not prepared callsite fields",
            );
        }

        if is_r2dec_op_lower_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_direct_prepared_callsite_certificates_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_DIRECT_PREPARED_CALLSITE_CERTIFICATES,
                item.span,
                "certified r2dec call rendering must read callsite proof from FunctionFacts, not prepared CallsiteCertificate",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !item_is_test_only(cx, item)
            && r2dec_direct_prepared_render_certificates_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_DIRECT_PREPARED_RENDER_CERTIFICATES,
                item.span,
                "certified r2dec render validation must read render proof from FunctionFacts, not prepared certificates",
            );
        }

    }

    fn check_impl_item(&mut self, cx: &LateContext<'tcx>, item: &'tcx ImplItem<'tcx>) {
        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_direct_type_facts_mutator_impl_item(cx, item)
        {
            span_lint(
                cx,
                R2DEC_DIRECT_TYPE_FACTS_MUTATOR,
                item.span,
                "r2dec production methods must not mutate type facts outside FunctionFacts",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && engine_decompile_render_cache_pre_route_facts_impl_item(cx, item.span)
        {
            span_lint(
                cx,
                R2ENGINE_DECOMPILE_RENDER_CACHE_PRE_ROUTE_FACTS,
                item.span,
                "r2engine must attach FunctionFacts route facts before computing the decompile render cache key",
            );
        }

        if is_r2engine_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && item.ident.name.as_str() == "clear_analysis_artifacts_for_function"
        {
            span_lint(
                cx,
                R2ENGINE_CACHE_POLICY_OWNERSHIP,
                item.span,
                "r2engine must not expose direct artifact-cache invalidation outside engine requests",
            );
        }

        if is_r2engine_lib_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && engine_summary_only_decompile_api_impl_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_SUMMARY_ONLY_DECOMPILE_API,
                item.span,
                "r2engine production decompile must use prepared EngineFunctionDecompileRequest instead of summary-only decompile entrypoints",
            );
        }

        if is_r2engine_lib_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && engine_lower_level_decompile_api_bypass_impl_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_LOWER_LEVEL_DECOMPILE_API_BYPASS,
                item.span,
                "r2engine must not expose public decompile(&self, EngineDecompileRequest); use decompile_function with EngineFunctionDecompileRequest",
            );
        }

        if is_r2types_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && raw_attach_prepared_decompile_evidence_signature_impl_item(cx, item)
        {
            span_lint(
                cx,
                R2ENGINE_PREPARED_DECOMPILE_EVIDENCE_SIDE_CHANNEL,
                item.span,
                "FunctionFacts::attach_prepared_decompile_evidence must not accept raw function_names/symbols side channels",
            );
        }

        if is_r2dec_span(cx, item.span) && r2dec_switch_case_value_ownership_item(cx, item.span) {
            span_lint(
                cx,
                R2DEC_SWITCH_CASE_VALUE_OWNERSHIP,
                item.span,
                "r2dec must not define switch case display-bias helpers; canonical switch facts own case values",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_switch_selector_single_fact_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_SWITCH_SELECTOR_SINGLE_FACT_FALLBACK,
                item.span,
                "r2dec must not reuse a single switch selector fact for a non-matching block",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_prepared_switch_selector_proof_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_PREPARED_SWITCH_SELECTOR_PROOF,
                item.span,
                "certified switch rendering must residualize before prepared selector text fallback",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_prepared_direct_target_reparse_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_PREPARED_DIRECT_TARGET_REPARSE,
                item.span,
                "r2dec direct call target lookup must not reparse prepared SSA names or roots",
            );
        }

        if is_r2dec_op_lower_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_direct_prepared_callsite_certificates_impl_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_DIRECT_PREPARED_CALLSITE_CERTIFICATES,
                item.span,
                "certified r2dec call rendering must not authorize calls from prepared callsite certificates",
            );
        }

        if is_r2dec_span(cx, item.span)
            && r2dec_call_result_stack_owner_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CALL_RESULT_STACK_OWNER_FALLBACK,
                item.span,
                "r2dec must not derive call-result owners from stack-local fallback logic",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_call_result_source_expr_owner_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CALL_RESULT_SOURCE_EXPR_OWNER_FALLBACK,
                item.span,
                "r2dec must not derive call-result owners from matching rendered call expressions",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_call_result_return_register_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_CALL_RESULT_RETURN_REGISTER_FALLBACK,
                item.span,
                "certified r2dec rendering must reject return-register owner fallback before inference",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_call_result_alias_owner_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_CALL_RESULT_ALIAS_OWNER_FALLBACK,
                item.span,
                "certified r2dec rendering must reject local alias owner fallback before inference",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_local_call_ownership_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_LOCAL_CALL_OWNERSHIP_FALLBACK,
                item.span,
                "certified r2dec call-result ownership must not read local ownership maps before prepared FunctionFacts ownership",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_call_result_preservation_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_CALL_RESULT_PRESERVATION_FALLBACK,
                item.span,
                "certified call-result preservation must prove the visible name through FunctionFacts ownership before reading local owner caches",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_duplicate_call_pruning_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_DUPLICATE_CALL_PRUNING_FALLBACK,
                item.span,
                "certified duplicate-call pruning must use FunctionFacts callsite proof and keep calls when proof is missing",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_visible_owner_source_lookup_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_VISIBLE_OWNER_SOURCE_LOOKUP,
                item.span,
                "certified visible-owner lookup must cross-check the stable FunctionFacts result owner",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_prepared_result_owner_expr_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_PREPARED_RESULT_OWNER_EXPR,
                item.span,
                "certified call-result owner expressions must be reduced to stable prepared owner names",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_prepared_result_owner_fact_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_PREPARED_RESULT_OWNER_FACT,
                item.span,
                "certified call-result owner names must require FunctionFacts call-result owner facts",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_stack_return_render_facts_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_STACK_RETURN_RENDER_FACTS,
                item.span,
                "certified r2dec stack-return recovery must require FunctionFacts render evidence",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_stack_local_identity_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_STACK_LOCAL_IDENTITY,
                item.span,
                "certified r2dec local declarations must require exact typed stack identity",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_stack_local_type_ownership_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_STACK_LOCAL_TYPE_OWNERSHIP,
                item.span,
                "certified r2dec stack local types must come from FunctionTypeFacts",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_local_type_hints_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_LOCAL_TYPE_HINTS,
                item.span,
                "certified r2dec fold inputs must not consume local type hints or local type oracle",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_uncertified_field_placeholder_name(item.ident.name.as_str())
        {
            span_lint(
                cx,
                R2DEC_UNCERTIFIED_FIELD_PLACEHOLDER,
                item.span,
                "r2dec must not define fallback aggregate field-name helpers; use certified layout facts",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_member_field_certificate_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_MEMBER_FIELD_CERTIFICATE,
                item.span,
                "certified r2dec structured memory rendering must require direction-exact FunctionRenderFacts evidence",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_branch_condition_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_BRANCH_CONDITION_FALLBACK,
                item.span,
                "certified branch condition extraction must require FunctionFacts control proof before local predicate fallback",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_switch_structure_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_SWITCH_STRUCTURE_FALLBACK,
                item.span,
                "certified switch rendering must prove selector/cases/default through FunctionFacts before emitting switch syntax",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_loop_structure_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_LOOP_STRUCTURE_FALLBACK,
                item.span,
                "certified loop rendering must prove body/latch/exit structure through FunctionFacts before emitting loop syntax",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_branch_render_proof_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_BRANCH_RENDER_PROOF,
                item.span,
                "r2dec must record branch render proof before emitting certified if statements",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_raw_call_arg_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_RAW_CALL_ARG_FALLBACK,
                item.span,
                "certified r2dec call arguments must refuse local raw arg fallback without FunctionFacts callsite facts",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_prepared_call_arg_expr_proof_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_PREPARED_CALL_ARG_EXPR_PROOF,
                item.span,
                "certified prepared call arguments must prove rendered expressions match certified values",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_executable_post_call_repair_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_EXECUTABLE_POST_CALL_REPAIR,
                item.span,
                "certified executable lowering must not repair post-call values from local renderer state",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_call_render_proof_local_equality_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_CALL_RENDER_PROOF_LOCAL_EQUALITY,
                item.span,
                "certified rendered-call proof must not be recovered from local cached call-expression equality",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_direct_zero_arg_call_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_DIRECT_ZERO_ARG_CALL_FALLBACK,
                item.span,
                "r2dec direct SSA call lowering must not emit zero-arg executable fallback calls",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_call_result_replay_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_CALL_RESULT_REPLAY_FALLBACK,
                item.span,
                "certified r2dec call-result replay must try certified synthesized calls before cached fallback",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_return_local_expr_fallback_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_RETURN_LOCAL_EXPR_FALLBACK,
                item.span,
                "certified r2dec returns must derive expressions from prepared return proof before local expression fallback",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_return_call_result_fact_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_RETURN_CALL_RESULT_FACT,
                item.span,
                "certified return-call rendering must require FunctionFacts call-result evidence",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_certified_local_post_call_source_fact_item(cx, item.span)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_LOCAL_POST_CALL_SOURCE_FACT,
                item.span,
                "certified local post-call source recovery must require FunctionFacts call-result evidence",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && r2dec_decompiler_context_route_side_channel_method(item.ident.name.as_str())
        {
            span_lint(
                cx,
                R2DEC_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
                item.span,
                "r2dec DecompilerContext must not expose route/render policy side-channel mutators",
            );
        }

        if is_r2dec_span(cx, item.span)
            && !impl_item_is_test_only(cx, item)
            && item.ident.name.as_str() == "with_callee_resolution"
        {
            span_lint(
                cx,
                R2DEC_DECOMPILER_CONTEXT_CALLEE_RESOLUTION_SIDE_CHANNEL,
                item.span,
                "r2dec DecompilerContext must not expose callee-resolution side-channel mutators",
            );
        }
    }

    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        if is_canonical_ssa_var_classifier(cx, expr) {
            return;
        }

        if (is_r2dec_span(cx, expr.span) || is_r2engine_span(cx, expr.span))
            && !is_inside_test_item(cx, expr)
            && !is_inside_cfg_test_item_source(cx, expr)
            && function_facts_owner_field_assignment_expr(expr)
        {
            span_lint(
                cx,
                R2TYPES_FUNCTION_FACTS_FIELD_OWNERSHIP,
                expr.span,
                "r2engine/r2dec must mutate FunctionFacts through r2types owner methods, not direct field assignment",
            );
        }

        if let ExprKind::MethodCall(method, _receiver, [arg], _) = expr.kind
            && method.ident.as_str() == "starts_with"
            && semantic_prefix_literal(arg)
        {
            span_lint(
                cx,
                STRING_PREFIX_SEMANTIC_CLASSIFICATION,
                expr.span,
                "semantic storage/address classification by string prefix; use a typed classifier owned by the canonical fact producer",
            );
        }

        if let ExprKind::MethodCall(method, receiver, [_arg], _) = expr.kind
            && method.ident.as_str() == "get"
            && is_r2dec_path(cx, expr)
            && expr_references_known_function_signatures(receiver)
        {
            span_lint(
                cx,
                R2DEC_DIRECT_KNOWN_SIGNATURE_LOOKUP,
                expr.span,
                "r2dec must resolve function signatures through r2types::CalleeIdentity, not direct raw-map lookup",
            );
        }

        if is_r2dec_analysis_path(cx, expr) && raw_callee_import_policy_expr(expr) {
            span_lint(
                cx,
                R2DEC_RAW_CALLEE_IMPORT_POLICY,
                expr.span,
                "r2dec analysis must consume CalleeResolutionFacts target resolution/policy, not reconstruct callee import/model policy",
            );
        }

        if is_r2dec_op_lower_path(cx, expr) && raw_call_target_address_parser_expr(expr) {
            span_lint(
                cx,
                R2DEC_RAW_CALL_TARGET_ADDRESS_PARSER,
                expr.span,
                "r2dec op-lowering must use parse_address_from_var_name or CalleeResolutionFacts instead of local call-target address parsing",
            );
        }

        if is_r2dec_op_lower_path(cx, expr) && call_target_policy_ownership_expr(expr) {
            span_lint(
                cx,
                R2DEC_CALL_TARGET_POLICY_OWNERSHIP,
                expr.span,
                "r2dec op-lowering must consume the typed callee target policy contract instead of recomputing imported/modeled policy",
            );
        }

        if is_r2dec_lib_path(cx, expr) && callee_resolution_fallback_ownership_expr(expr) {
            span_lint(
                cx,
                R2DEC_CALLEE_RESOLUTION_FALLBACK_OWNERSHIP,
                expr.span,
                "r2dec must not synthesize CalleeResolutionFacts from raw call targets; pass the r2engine-owned resolution contract",
            );
        }

        if is_r2dec_op_lower_path(cx, expr) && uncertified_call_arg_call_policy_expr(cx, expr) {
            span_lint(
                cx,
                R2DEC_UNCERTIFIED_CALL_ARG_CALL_POLICY,
                expr.span,
                "r2dec call arguments must require certified nested-call proof instead of rendered imported/modeled callee policy",
            );
        }

        if is_r2dec_op_lower_path(cx, expr) && call_arg_source_name_authority_expr(cx, expr) {
            span_lint(
                cx,
                R2DEC_CALL_ARG_SOURCE_NAME_AUTHORITY,
                expr.span,
                "source_var_name is only a hint; call-argument rendering needs source_value_id or prepared semantic authority",
            );
        }

        if is_r2dec_op_lower_path(cx, expr) && call_arg_source_call_authority_expr(cx, expr) {
            span_lint(
                cx,
                R2DEC_CALL_ARG_SOURCE_CALL_AUTHORITY,
                expr.span,
                "source_call proves provenance only; call-argument rendering needs certified argument evidence",
            );
        }

        if is_r2dec_summary_render_path(cx, expr) && summary_route_executable_c_expr(cx, expr) {
            span_lint(
                cx,
                R2DEC_SUMMARY_ROUTE_EXECUTABLE_C,
                expr.span,
                "summary route rendering must stay comment/fact-only until native CFG/control/dataflow proof exists",
            );
        }

        if is_r2dec_summary_or_structured_consumer_path(cx, expr)
            && summary_render_executable_cstmt_expr(cx, expr)
        {
            span_lint(
                cx,
                R2DEC_SUMMARY_RENDER_EXECUTABLE_CSTMT,
                expr.span,
                "summary/VM renderers must not construct executable CStmt bodies without CertifiedC permission",
            );
        }

        if is_r2dec_route_render_path(cx, expr) && summary_route_structured_worker_expr(expr) {
            span_lint(
                cx,
                R2DEC_SUMMARY_ROUTE_EXECUTABLE_C,
                expr.span,
                "summary route rendering must not call semantic worker structuring without certified native render permission",
            );
        }

        if is_r2dec_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && r2dec_route_policy_ownership_expr(expr)
        {
            span_lint(
                cx,
                R2DEC_ROUTE_POLICY_OWNERSHIP,
                expr.span,
                "r2dec must receive route/refusal decisions from r2engine instead of selecting them locally",
            );
        }

        if is_r2engine_path(cx, expr) && engine_decompiler_context_side_channel_expr(expr) {
            span_lint(
                cx,
                R2ENGINE_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
                expr.span,
                "r2engine must write decompile route/refusal decisions into FunctionFacts, not legacy DecompilerContext policy fields",
            );
        }

        if is_r2engine_path(cx, expr)
            && engine_r2dec_summary_render_route_side_channel_expr(cx, expr)
        {
            span_lint(
                cx,
                R2ENGINE_R2DEC_SUMMARY_RENDER_ROUTE_SIDE_CHANNEL,
                expr.span,
                "r2engine must not pass EngineSemanticRoutePlan/SemanticRoutePlan as a r2dec summary render side channel",
            );
        }

        if is_r2engine_lib_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && engine_summary_only_decompile_api_expr(cx, expr)
        {
            span_lint(
                cx,
                R2ENGINE_SUMMARY_ONLY_DECOMPILE_API,
                expr.span,
                "summary-only decompile APIs must not be used as a production r2engine decompile path without prepared SSA",
            );
        }

        if is_r2dec_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && r2dec_switch_case_value_ownership_expr(cx, expr)
        {
            span_lint(
                cx,
                R2DEC_SWITCH_CASE_VALUE_OWNERSHIP,
                expr.span,
                "r2dec must not rewrite switch case values from display bias; render canonical case facts",
            );
        }

        if is_r2dec_op_lower_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && r2dec_call_result_stack_owner_fallback_expr(cx, expr)
        {
            span_lint(
                cx,
                R2DEC_CALL_RESULT_STACK_OWNER_FALLBACK,
                expr.span,
                "r2dec must consume prepared call-result ownership instead of deriving stack-local owners in op-lowering",
            );
        }

        if is_r2dec_op_lower_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && r2dec_call_result_source_expr_owner_fallback_expr(cx, expr)
        {
            span_lint(
                cx,
                R2DEC_CALL_RESULT_SOURCE_EXPR_OWNER_FALLBACK,
                expr.span,
                "r2dec must consume prepared call-result ownership instead of matching rendered call expressions",
            );
        }

        if is_r2dec_analysis_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && r2dec_direct_prepared_call_result_certificates_expr(cx, expr)
        {
            span_lint(
                cx,
                R2DEC_DIRECT_PREPARED_CALL_RESULT_CERTIFICATES,
                expr.span,
                "r2dec analysis must read call-result proof from FunctionFacts, not prepared SSA certificate maps",
            );
        }

        if is_r2dec_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && r2dec_direct_prepared_control_facts_expr(cx, expr)
        {
            span_lint(
                cx,
                R2DEC_DIRECT_PREPARED_CONTROL_FACTS,
                expr.span,
                "r2dec must read branch/switch proof from FunctionFacts, not prepared SSA predicate maps or local selector inference",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_type_writeback_policy_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
                expr.span,
                "r2plugin must not decide type writeback authority or construct apply policy directly; use r2engine/r2types owner APIs",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_type_writeback_mutation_kind_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_TYPE_WRITEBACK_MUTATION_KIND_OWNERSHIP,
                expr.span,
                "r2plugin must not map TypeWritebackMutationKind variants directly; use r2engine::type_writeback_mutation_kind_id",
            );
        }

        if is_r2plugin_path(cx, expr)
            && plugin_direct_type_writeback_analysis_expr(cx, expr)
            && !is_inside_test_item(cx, expr)
            && !is_inside_cfg_test_item_source(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_DIRECT_TYPE_WRITEBACK_ANALYSIS_OWNERSHIP,
                expr.span,
                "r2plugin must not assemble FunctionFacts/type-writeback analysis directly; route through r2engine",
            );
        }

        if is_r2plugin_path(cx, expr) && plugin_raw_direct_call_target_expr(expr) {
            span_lint(
                cx,
                R2PLUGIN_RAW_DIRECT_CALL_TARGET,
                expr.span,
                "r2plugin must use SsaArtifact::resolved_call_target so copied-constant call targets are exported",
            );
        }

        if is_r2plugin_path(cx, expr) && plugin_type_writeback_apply_threshold_expr(expr) {
            span_lint(
                cx,
                R2PLUGIN_TYPE_WRITEBACK_APPLY_THRESHOLD_OWNERSHIP,
                expr.span,
                "r2plugin must not compute or inspect type writeback apply thresholds; consume r2types mutation plans",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_function_facts_types_ownership_expr(expr)
        {
            span_lint(
                cx,
                R2PLUGIN_FUNCTION_FACTS_TYPES_OWNERSHIP,
                expr.span,
                "r2plugin must not inspect FunctionFacts.types; use an r2engine projection or response API",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_function_facts_report_ownership_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_FUNCTION_FACTS_REPORT_OWNERSHIP,
                expr.span,
                "r2plugin must not mine FunctionFacts report fields; consume an engine-owned report payload",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_type_writeback_json_projection_ownership_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_TYPE_WRITEBACK_JSON_PROJECTION_OWNERSHIP,
                expr.span,
                "r2plugin must not manually project EngineTypeWritebackPayload into JSON; use r2engine::type_writeback_json_core",
            );
        }

        if is_r2plugin_lib_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_semantic_report_projection_ownership_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_SEMANTIC_REPORT_PROJECTION_OWNERSHIP,
                expr.span,
                "r2plugin lib/session paths must request semantic report projections through r2engine",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_function_analysis_report_json_projection_ownership_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_FUNCTION_ANALYSIS_REPORT_JSON_PROJECTION_OWNERSHIP,
                expr.span,
                "r2plugin must not manually project EngineFunctionAnalysisReportPayload into JSON; use r2engine::function_analysis_report_json_core",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_typed_external_context_ownership_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_TYPED_EXTERNAL_CONTEXT_OWNERSHIP,
                expr.span,
                "r2plugin must pass typed FFI context through r2engine::parse_typed_external_context instead of constructing r2types external context schema",
            );
        }

        if is_r2plugin_path(cx, expr) && plugin_renderer_config_arch_target_expr(cx, expr) {
            span_lint(
                cx,
                R2PLUGIN_RENDERER_CONFIG_ARCH_TARGET_OWNERSHIP,
                expr.span,
                "r2plugin must derive canonical arch targets through r2engine, then construct renderer config at the render boundary",
            );
        }

        if is_r2plugin_path(cx, expr) && plugin_variable_recovery_ownership_expr(cx, expr) {
            span_lint(
                cx,
                R2PLUGIN_VARIABLE_RECOVERY_OWNERSHIP,
                expr.span,
                "r2plugin must request recovered signature evidence from r2engine instead of constructing r2dec::VariableRecovery",
            );
        }

        if is_r2plugin_type_hint_policy_span(cx, expr.span)
            && plugin_metadata_type_hint_policy_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_METADATA_TYPE_HINT_OWNERSHIP,
                expr.span,
                "r2plugin must not interpret r2il ScalarKind/PointerHint into TypeHint policy",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_engine_policy_ownership_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_ENGINE_POLICY_OWNERSHIP,
                expr.span,
                "r2plugin must delegate route/cache/session/fallback decisions to r2engine",
            );
        }

        if is_r2plugin_path(cx, expr) && plugin_unprepared_decompile_oracle_expr(cx, expr) {
            span_lint(
                cx,
                R2PLUGIN_UNPREPARED_DECOMPILE_ORACLE,
                expr.span,
                "r2plugin tests must route prepared artifacts through the engine decompile path",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_direct_r2dec_op_lowering_expr(expr)
        {
            span_lint(
                cx,
                R2PLUGIN_DIRECT_R2DEC_OP_LOWERING,
                expr.span,
                "r2plugin must not expose direct r2dec SSA-op lowering without engine FunctionFacts",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_direct_clike_block_decompile_export_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_DIRECT_CLIKE_BLOCK_DECOMPILE_EXPORT,
                expr.span,
                "r2plugin must not expose direct C-like block decompile output without engine FunctionFacts",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_direct_r2dec_ast_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_DIRECT_R2DEC_AST_OWNERSHIP,
                expr.span,
                "r2plugin must request residual AST payloads from r2engine instead of constructing r2dec AST nodes",
            );
        }

        if is_r2plugin_path(cx, expr) && plugin_direct_r2dec_fallback_comment_expr(cx, expr) {
            span_lint(
                cx,
                R2PLUGIN_DIRECT_R2DEC_FALLBACK_COMMENT,
                expr.span,
                "r2plugin must route fallback/refusal comment selection through r2engine",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_direct_r2dec_decompiler_ownership_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_DIRECT_R2DEC_DECOMPILER_OWNERSHIP,
                expr.span,
                "r2plugin production decompile must go through r2engine EngineSession, not direct r2dec",
            );
        }

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_decompile_one_function_direct_r2dec_expr(cx, expr)
        {
            span_lint(
                cx,
                R2PLUGIN_DECOMPILE_ONE_FUNCTION_DIRECT_R2DEC,
                expr.span,
                "r2plugin decompile-one-function paths must call r2engine instead of constructing or lowering through r2dec",
            );
        }

        if is_r2engine_path(cx, expr) && engine_r2dec_variable_recovery_ownership_expr(cx, expr) {
            span_lint(
                cx,
                R2ENGINE_R2DEC_VARIABLE_RECOVERY_OWNERSHIP,
                expr.span,
                "r2engine must use r2types-owned signature parameter recovery instead of r2dec::VariableRecovery",
            );
        }

        if is_r2engine_path(cx, expr) && engine_r2dec_fallback_comment_ownership_expr(cx, expr) {
            span_lint(
                cx,
                R2ENGINE_R2DEC_FALLBACK_COMMENT_OWNERSHIP,
                expr.span,
                "r2engine must construct fallback/refusal comments from engine-owned route policy, not r2dec helper functions",
            );
        }

        if is_r2dec_path(cx, expr) && r2dec_default_true_branch_condition_expr(cx, expr) {
            span_lint(
                cx,
                R2DEC_DEFAULT_TRUE_BRANCH_CONDITION,
                expr.span,
                "r2dec must residualize unresolved branch predicates instead of rendering if (1)",
            );
        }

        if is_r2dec_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && r2dec_uncertified_stack_local_synthesis_expr(expr)
        {
            span_lint(
                cx,
                R2DEC_UNCERTIFIED_STACK_LOCAL_SYNTHESIS,
                expr.span,
                "r2dec must require typed stack-slot proof before synthesizing stack locals",
            );
        }

        if is_r2dec_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && r2dec_certified_stack_owner_proof_recomposition_expr(cx, expr)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_STACK_OWNER_PROOF_RECOMPOSITION,
                expr.span,
                "certified r2dec stack owner helpers must call a FunctionFacts-owned predicate instead of recomposing proof from render facts or stack alias/provenance helpers",
            );
        }

        if is_r2dec_op_lower_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && r2dec_direct_stable_stack_values_get_expr(cx, expr)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_LOCAL_STACK_RECOVERY_BYPASS,
                expr.span,
                "r2dec op-lowering must read stable stack values through the certified-aware accessor",
            );
        }

        if is_r2dec_analysis_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && r2dec_unguarded_local_store_owner_expr(cx, expr)
        {
            span_lint(
                cx,
                R2DEC_CERTIFIED_LOCAL_STACK_RECOVERY_BYPASS,
                expr.span,
                "r2dec prepared local-store recovery must be guarded out of certified rendering",
            );
        }

        if is_r2types_non_role_registry_path(cx, expr) && r2types_role_name_signature_hint_expr(expr)
        {
            span_lint(
                cx,
                R2TYPES_ROLE_NAME_SIGNATURE_HINT_OWNERSHIP,
                expr.span,
                "r2types must project role signatures through evidence-backed role identity",
            );
        }

        if forbidden_r2_json_command_literal(expr) {
            span_lint(
                cx,
                R2_JSON_COMMAND_INTERNAL_SEAM,
                expr.span,
                "internal analysis must use typed radare2 collector APIs instead of JSON command strings",
            );
        }
    }
}

fn semantic_prefix_literal(expr: &Expr<'_>) -> bool {
    let ExprKind::Lit(lit) = expr.kind else {
        return false;
    };
    let LitKind::Str(symbol, _) = lit.node else {
        return false;
    };
    matches!(
        symbol.as_str(),
        "tmp:" | "const:" | "ram:" | "reg:" | "space" | "sym." | "obj." | "reloc."
    )
}

fn forbidden_r2_json_command_literal(expr: &Expr<'_>) -> bool {
    let ExprKind::Lit(lit) = expr.kind else {
        return false;
    };
    let LitKind::Str(symbol, _) = lit.node else {
        return false;
    };
    let text = symbol.as_str();
    let command = text.split_whitespace().next().unwrap_or(text.as_ref());
    matches!(command, "afcfj" | "afvj" | "tsj")
}

fn plugin_type_writeback_policy_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::MethodCall(method, _, _, _) => {
            matches!(
                method.ident.as_str(),
                "authorizes_signature_writeback" | "render_authorized_signature"
            )
        }
        ExprKind::Call(callee, _) => {
            if [
                "signature_writeback_decision",
                "type_writeback_mutation_plan",
                    "type_writeback_mutation_plan_with_policy",
                    "type_writeback_authority_report",
                    "type_writeback_authority_report_with_policy",
                    "type_writeback_authority_report_for_policy",
                    "type_writeback_plan_report_for_policy",
                    "bounded_cfg_type_writeback_plan",
                    "bounded_cfg_type_writeback_plan_report",
                    "semantic_fallback_type_writeback_plan",
                    "semantic_fallback_type_writeback_plan_report",
                    "type_writeback_external_struct_names",
                    "type_writeback_field_access_certificate_names",
                    "writeback_var_name_is_generated",
                    "type_writeback_var_type_apply_decision",
                    "type_writeback_global_type_link_apply_decision",
                    "type_writeback_var_rename_apply_decision",
                    "signature_writeback_arch_supported",
                    "callconv_writeback_arch_supported",
                    "signature_register_arg_var_score",
                    "signature_register_arg_rename_decision",
                    "signature_register_arg_type_apply_required",
                    "signature_register_arg_stack_conflict_delete_required",
                    "type_writeback_stack_arg_name_conflict_delete_required",
                    "signature_register_arg_duplicate_delete_required",
                    "signature_writeback_size_eligible",
                ]
            .iter()
            .any(|name| expr_path_last_segment_is(callee, name))
            {
                return true;
            }
            if ["off", "balanced", "aggressive"]
                .iter()
                .any(|name| expr_path_last_segment_is(callee, name))
            {
                return cx
                    .sess()
                    .source_map()
                    .span_to_snippet(callee.span)
                    .is_ok_and(|snippet| snippet.contains("TypeWritebackApplyPolicy::"));
            }
            false
        }
        ExprKind::Lit(lit) => {
            let LitKind::Str(symbol, _) = lit.node else {
                return false;
            };
            symbol.as_str().starts_with("signature mutation refused:")
        }
        _ => false,
    }
}

fn plugin_type_writeback_mutation_kind_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    if !matches!(expr.kind, ExprKind::Path(_)) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(expr.span)
        .is_ok_and(|snippet| snippet.contains("r2types::TypeWritebackMutationKind::"))
}

fn plugin_direct_type_writeback_analysis_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = expr.kind else {
        return false;
    };
    if [
        "build_type_writeback_analysis",
        "build_type_writeback_analysis_with_semantics",
        "infer_local_struct_artifacts_from_ssa",
        "local_field_accesses_from_struct_artifacts",
    ]
    .iter()
    .any(|name| expr_path_last_segment_is(callee, name))
    {
        return true;
    }

    cx.sess()
        .source_map()
        .span_to_snippet(callee.span)
        .is_ok_and(|snippet| {
            snippet.contains("FunctionFacts::new")
                || snippet.contains("FunctionFacts::default")
                || snippet.contains("r2types::FunctionFacts::new")
                || snippet.contains("r2types::FunctionFacts::default")
        })
}

fn plugin_type_writeback_apply_threshold_expr(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::MethodCall(method, _, _, _) => matches!(
            method.ident.as_str(),
            "effective_threshold" | "mutation_min_confidence"
        ),
        ExprKind::Field(_, ident) => matches!(
            ident.name.as_str(),
            "type_min_confidence" | "rename_min_confidence" | "struct_min_confidence"
        ),
        _ => false,
    }
}

fn plugin_function_facts_types_ownership_expr(expr: &Expr<'_>) -> bool {
    matches!(
        expr.kind,
        ExprKind::Field(_, ident) if ident.name.as_str() == "types"
    )
}

fn plugin_function_facts_report_ownership_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    if !enclosing_item_snippet_contains(cx, expr, "FunctionAnalysisSharedBundle")
        && !enclosing_item_snippet_contains(cx, expr, "FunctionAnalysisSessionReport")
    {
        return false;
    }
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(expr.span) else {
        return false;
    };
    if !snippet.contains("function_facts") {
        return false;
    }
    match expr.kind {
        ExprKind::Field(_, ident) => matches!(
            ident.name.as_str(),
            "plans" | "assumptions" | "assumption_usage" | "semantics" | "summary_view"
        ),
        ExprKind::MethodCall(method, _, _, _) => {
            matches!(method.ident.as_str(), "decompile_route" | "diagnostics")
        }
        _ => false,
    }
}

fn function_facts_owner_field_assignment_expr(expr: &Expr<'_>) -> bool {
    let ExprKind::Assign(lhs, _, _) = expr.kind else {
        return false;
    };
    let ExprKind::Field(base, ident) = lhs.kind else {
        return false;
    };
    if !matches!(
        ident.name.as_str(),
        "types"
            | "summary_view"
            | "assumption_usage"
            | "proof"
            | "decompile_route"
            | "semantics"
            | "render"
            | "control"
    ) {
        return false;
    }
    field_base_mentions_function_facts(base)
}

fn field_base_mentions_function_facts(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Path(QPath::Resolved(_, path)) => path
            .segments
            .last()
            .is_some_and(|segment| segment.ident.name.as_str() == "function_facts"),
        ExprKind::Field(base, ident) => {
            ident.name.as_str() == "function_facts" || field_base_mentions_function_facts(base)
        }
        _ => false,
    }
}

fn plugin_type_writeback_json_projection_ownership_expr(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> bool {
    if !enclosing_item_snippet_contains(cx, expr, "WritebackPayloadJsonInput") {
        return false;
    }
    matches!(
        expr.kind,
        ExprKind::Field(_, ident)
            if matches!(
                ident.name.as_str(),
                "signature"
                    | "signature_render_authorized"
                    | "signature_writeback_authorized"
                    | "signature_action_decision"
                    | "callconv_action_decision"
                    | "signature_certificate_sources"
                    | "signature_writeback_refusal"
                    | "var_type_candidates"
                    | "var_rename_candidates"
                    | "external_struct_names"
                    | "field_access_certificate_names"
                    | "struct_decls"
                    | "global_type_links"
                    | "plans"
                    | "assumptions"
                    | "assumption_usage"
                    | "mutation_plan"
                    | "diagnostics"
            )
    )
}

fn plugin_function_analysis_report_json_projection_ownership_expr(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> bool {
    if !enclosing_item_snippet_contains(cx, expr, "function_analysis_session_report_json") {
        return false;
    }
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(expr.span) else {
        return false;
    };
    if !snippet.contains("report_payload.") {
        return false;
    }
    matches!(
        expr.kind,
        ExprKind::Field(_, ident)
            if matches!(
                ident.name.as_str(),
                "function_name"
                    | "function_addr"
                    | "cfg_summary"
                    | "plans"
                    | "assumptions"
                    | "assumption_usage"
                    | "semantic_build_plan"
                    | "semantic_route"
                    | "summary_diagnostics"
                    | "prefer_bounded_type_plan"
            )
    )
}

fn plugin_typed_external_context_ownership_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(expr.span) else {
        return false;
    };
    [
        "r2types::ExternalContextJson",
        "r2types::ExternalContextMetadataJson",
        "r2types::ExternalSignatureJson",
        "r2types::ExternalSignatureParamJson",
        "r2types::ExternalVarJson",
        "r2types::ExternalBaseTypeJson",
        "r2types::ExternalBaseTypeMemberJson",
        "r2types::ExternalEnumVariantJson",
        "r2types::ExternalCalleeJson",
        "r2types::parse_external_context_json(",
        "r2types::parse_external_context(",
    ]
    .iter()
    .any(|needle| snippet.contains(needle))
}

fn plugin_typed_external_context_ownership_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    snippet.contains("fn typed_function_context_to_parsed")
        || (snippet.contains("R2SleighFunctionContext")
            && snippet.contains("ParsedExternalContext")
            && snippet.contains("parse_typed_external_context"))
}

fn plugin_external_type_parser_renderer_type_ownership_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("fn parse_external_type")
                && snippet.contains("r2dec::CType")
                && !snippet.contains("r2types::CTypeLike")
        })
}

fn plugin_signature_confidence_renderer_type_ownership_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            (snippet.contains("struct InferredParam") && snippet.contains("r2dec::CType"))
                || (snippet.contains("fn compute_signature_confidence")
                    && snippet.contains("r2dec::CType"))
        })
}

fn plugin_signature_spec_renderer_type_ownership_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("fn signature_spec") && snippet.contains("r2dec::CType")
        })
}

fn plugin_ctype_bridge_ownership_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            [
                "fn type_like_to_ctype",
                "fn ctype_to_type_like",
                "fn materialize_signature_ctype",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
        })
}

fn plugin_raw_direct_call_target_expr(expr: &Expr<'_>) -> bool {
    matches!(
        expr.kind,
        ExprKind::Field(_, ident) if ident.name.as_str() == "direct_target"
    )
}

fn plugin_renderer_config_arch_target_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = expr.kind else {
        return false;
    };
    if !expr_path_last_segment_is(callee, "for_arch") {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(callee.span)
        .is_ok_and(|snippet| snippet.contains("DecompilerConfig::for_arch"))
}

fn plugin_variable_recovery_ownership_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = expr.kind else {
        return false;
    };
    if expr_path_last_segment_is(callee, "recover_vars_from_ssa")
        && cx
            .sess()
            .source_map()
            .span_to_snippet(callee.span)
            .is_ok_and(|snippet| snippet.contains("r2types::recover_vars_from_ssa"))
    {
        return true;
    }
    if !expr_path_last_segment_is(callee, "new") && !expr_path_last_segment_is(callee, "new_with_abi")
    {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(callee.span)
        .is_ok_and(|snippet| snippet.contains("VariableRecovery::new"))
}

fn engine_r2dec_variable_recovery_ownership_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = expr.kind else {
        return false;
    };
    if !expr_path_last_segment_is(callee, "new") && !expr_path_last_segment_is(callee, "new_with_abi")
    {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(callee.span)
        .is_ok_and(|snippet| snippet.contains("VariableRecovery::new"))
}

fn engine_r2dec_fallback_comment_ownership_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = expr.kind else {
        return false;
    };
    if ![
        "block_guard_fallback_comment",
        "artifact_guard_fallback_comment",
        "semantic_fallback_comment",
    ]
    .iter()
    .any(|name| expr_path_last_segment_is(callee, name))
    {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(callee.span)
        .is_ok_and(|snippet| snippet.contains("r2dec::"))
}

fn plugin_metadata_type_hint_policy_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            [
                "fn size_to_signed_int_type",
                "fn size_to_unsigned_int_type",
                "fn scalar_kind_to_type",
                "fn metadata_type_hint",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
        })
}

fn plugin_semantic_report_projection_ownership_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            [
                "struct CompiledSemanticInfo",
                "struct MemorySummaryInfo",
                "struct InterpreterDispatchInfo",
                "struct VmStateUpdateInfo",
                "struct VmGuardConditionInfo",
                "struct VmGuardedExitInfo",
                "struct VmMemoryConditionInfo",
                "struct VmTransferArmInfo",
                "struct VmStepSummaryInfo",
                "fn compiled_semantic_info",
                "fn compiled_semantic_info_with_replay_seed",
                "fn compiled_semantic_info_with_seed",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
        })
}

fn plugin_report_json_schema_ownership_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            [
                "struct InterprocSummaryJson",
                "struct InferredTypeWritebackJson",
                "struct FunctionAnalysisSessionReportJson",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
        })
}

fn plugin_interproc_scope_report_ownership_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            [
                "fn symbolic_scope_view_json",
                "fn merged_interproc_scope_report",
                "\"phase\": \"symbolic_scope\"",
                "\"payloads\": payloads",
                "\"seeds\": seeds",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
        })
}

fn plugin_type_writeback_report_assembly_ownership_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            [
                "fn type_writeback_payload_from_engine_report",
                "struct BoundedCfgTypePayloadInput",
                "fn bounded_cfg_type_payload(",
                "struct SemanticTypeFallbackPayloadInput",
                "fn semantic_type_fallback_payload(",
                "struct WritebackPayloadJsonInput",
                "fn writeback_payload_json",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
        })
}

fn plugin_semantic_report_projection_ownership_expr(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> bool {
    let ExprKind::Call(callee, _) = expr.kind else {
        return false;
    };
    if ![
        "compiled_semantic_info",
        "compiled_semantic_info_with_replay_seed",
    ]
    .iter()
    .any(|name| expr_path_last_segment_is(callee, name))
    {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(callee.span)
        .is_ok_and(|snippet| snippet.contains("r2sym::"))
}

fn plugin_metadata_type_hint_policy_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    if !matches!(expr.kind, ExprKind::Path(_)) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(expr.span)
        .is_ok_and(|snippet| {
            [
                "r2il::ScalarKind::",
                "r2il::PointerHint::",
                "ScalarKind::",
                "PointerHint::",
            ]
            .iter()
                .any(|needle| snippet.contains(needle))
        })
}

fn r2dec_route_policy_ownership_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            [
                "fn semantic_route_plan(",
                "fn detached_semantic_route_plan(",
                "fn detached_semantic_linearization_reason(",
                "fn preferred_semantic_fallback_comment(",
                "fn preferred_semantic_linearization_reason(",
                "fn preferred_semantic_structuring_reason(",
                "fn preferred_semantic_summary_islands_reason(",
                "fn preferred_vm_summary_reason(",
                "fn cfg_guard_reason(",
                "fn cfg_guard_reason_from_summary(",
                "pub enum SemanticRoutePlan",
                "pub use planner::SemanticRoutePlan",
                "fn route_facts_to_plan(",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
        })
}

fn r2dec_missing_route_defaults_to_standard_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("decompile_route()")
                && (snippet.contains("SemanticRoutePlan::Standard")
                    || (snippet.contains("DecompileRouteFacts")
                        && snippet.contains("DecompileRouteKind::FallbackComment")
                        && snippet.contains("RenderPermission::refuse")))
        })
}

fn r2dec_build_function_requires_route_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            if snippet.contains("pub fn build_function(&self, func: &SSAFunction) -> CFunction") {
                return true;
            }
            snippet
                .contains("pub fn build_function_from_input(&self, input: &DecompilerInput) -> CFunction")
                && (!snippet.contains("let Some(semantic_route)")
                    || !snippet.contains("function_facts.decompile_route()")
                    || !snippet.contains("render_permission_residual_reason"))
        })
}

fn r2dec_summary_render_route_side_channel_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            let signature = snippet.split_once('{').map_or(snippet.as_str(), |(sig, _)| sig);
            if snippet.contains("pub fn render_semantic_worker_summary(") {
                return signature.contains("SemanticRoutePlan")
                    || !signature.contains("FunctionFacts")
                    || !snippet.contains("decompile_route()")
                    || !snippet.contains("RenderPermissionKind::SummaryComment");
            }
            if snippet.contains("pub fn render_vm_semantic_summary(") {
                return !signature.contains("FunctionFacts")
                    || !snippet.contains("decompile_route()")
                    || !snippet.contains("DecompileRouteKind::VmSummary")
                    || !snippet.contains("RenderPermissionKind::SummaryComment");
            }
            false
        })
}

fn engine_prepared_decompile_evidence_side_channel_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            [
                "fn decompile_callsite_argument_facts(",
                "fn decompile_call_result_facts(",
                "fn decompile_render_facts(",
                "fn decompile_control_facts(",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
                || [
                    ".set_callsites(",
                    ".set_call_results(",
                    ".set_control(",
                    ".set_render(",
                ]
                .iter()
                .any(|needle| snippet.contains(needle))
        })
}

fn r2dec_local_header_arity_repair_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            (snippet.contains("fn merge_params_with_external_signature(")
                && snippet.contains("recovered_params.len().max(signature.params.len())"))
                || (snippet.contains("certified_standard_mode")
                    && snippet.contains("ret_type:")
                    && snippet.contains("inferred_ret_type.clone()"))
        })
}

fn r2dec_local_authoritative_call_arg_inference_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("fn infer_call_authoritative_arg")
                || snippet.contains("fn infer_stack_call_authoritative_args")
        })
}

fn r2dec_route_policy_ownership_expr(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Call(callee, _) => [
            "semantic_route_plan",
            "detached_semantic_route_plan",
            "detached_semantic_linearization_reason",
            "preferred_semantic_fallback_comment",
            "preferred_semantic_linearization_reason",
            "preferred_semantic_structuring_reason",
            "preferred_semantic_summary_islands_reason",
            "preferred_vm_summary_reason",
            "cfg_guard_reason",
            "cfg_guard_reason_from_summary",
        ]
        .iter()
        .any(|name| expr_path_last_segment_is(callee, name)),
        _ => false,
    }
}

fn r2dec_switch_case_value_ownership_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(span)
        .is_ok_and(|snippet| {
            [
                "fn estimate_switch_case_bias",
                "fn switch_case_display_bias",
                "fn guarded_dense_zero_based_switch_bias",
                "fn filter_switch_case_outliers",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
        })
}

fn r2dec_switch_case_value_ownership_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::MethodCall(method, _, _, _) => {
            let method = method.ident.as_str();
            matches!(
                method,
                "estimate_switch_case_bias"
                    | "switch_case_display_bias"
                    | "guarded_dense_zero_based_switch_bias"
                    | "filter_switch_case_outliers"
            ) || (method == "saturating_add_signed"
                && enclosing_item_snippet_contains(cx, expr, "switch"))
        }
        ExprKind::Call(callee, _) => [
            "estimate_switch_case_bias",
            "switch_case_display_bias",
            "guarded_dense_zero_based_switch_bias",
            "filter_switch_case_outliers",
        ]
        .iter()
        .any(|name| expr_path_last_segment_is(callee, name)),
        _ => false,
    }
}

fn r2dec_switch_selector_single_fact_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(span)
        .is_ok_and(|snippet| {
            snippet.contains("fn resolve_switch_expr_for_block_with_selector(")
                || snippet.contains("fn resolve_switch_expr_from_control_facts(")
        })
        && cx
            .sess()
            .source_map()
            .span_to_snippet(span)
            .is_ok_and(|snippet| {
                snippet.contains("switches.len() == 1")
                    || snippet.contains("switch_selector_expr_by_block.len() == 1")
            })
}

fn r2dec_certified_prepared_switch_selector_proof_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn resolve_switch_expr_for_block_with_selector(")
        || !snippet.contains("switch_selector_expr_for_block")
        || !snippet.contains("requires_certified_rendering")
    {
        return false;
    }
    let Some(prepared_selector_at) = snippet.find("switch_selector_expr_for_block") else {
        return false;
    };
    snippet
        .find("requires_certified_rendering")
        .is_none_or(|guard_at| guard_at > prepared_selector_at)
}

fn r2dec_prepared_direct_target_reparse_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(span)
        .is_ok_and(|snippet| {
            snippet.contains("fn prepared_direct_call_target")
                && (snippet.contains("prepared_call_target_var")
                    || snippet.contains("parse_address_from_var_name")
                    || snippet.contains("prepared_canonical_value_root"))
        })
}

fn r2dec_prepared_call_view_direct_target_side_channel_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("fn populate_calls")
                && (snippet.contains(
                    "lookup_callee_identity_for_site(inputs, site, call_site.direct_target)",
                ) || snippet.contains("direct_target: call_site.direct_target"))
        })
}

fn r2dec_direct_prepared_callsite_certificates_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("fn certified_callsite_argument_values")
                && (snippet.contains("r2ssa::CallsiteCertificate")
                    || snippet.contains("r2types::CallsiteArgumentFacts"))
        })
}

fn r2dec_certified_call_arg_prefix_proof_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("fn certified_standard_output_residual_reason_with_effect_proofs")
                && snippet.contains("argument_values")
                && snippet.contains(".take(proof.values.len())")
        })
}

fn r2dec_direct_prepared_render_certificates_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("fn certified_standard_output_residual_reason_with_effect_proofs")
                && (snippet.contains("prepared.certificates()")
                    || snippet.contains("memory_certificate_for_op_site")
                    || snippet.contains("return_certificate_for_op")
                    || snippet.contains("callsite_certificate_for_op")
                    || snippet.contains("certificates.expressions")
                    || snippet.contains("certificates.stack_slots")
                    || snippet.contains("certificates.memory_accesses")
                    || snippet.contains("certificates.returns")
                    || snippet.contains("certificates.callsites"))
        })
}

fn r2dec_direct_prepared_callsite_certificates_impl_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(span)
        .is_ok_and(|snippet| {
            (snippet.contains("fn certified_callsite_for_op")
                && snippet.contains("callsite_certificate_for_op"))
                || (snippet.contains("fn certified_synthesized_call_expr_for_source_call")
                    && (snippet.contains("prepared_call_site_for_op")
                        || snippet.contains("resolved_call_target(call_site)")))
        })
}

fn r2dec_call_result_stack_owner_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(span)
        .is_ok_and(|snippet| {
            snippet.contains("fn fallback_owned_call_result_stack_local_name_for_source")
                || snippet.contains("fallback_stack_local")
                || (snippet.contains("fn derive_stable_owned_call_result_name_for_alias")
                    && (snippet.contains("semantic_stack_owner_name_for_alias")
                        || snippet.contains("resolve_stack_var(")))
                || (snippet.contains("fn stable_owned_call_result_expr_for_name")
                    && (snippet.contains("semantic_stack_owner_name_for_alias")
                        || snippet.contains(".forwarded_value_for_name("))
                    && !snippet.contains("call_result_alias_has_stack_owner_provenance"))
        })
}

fn r2dec_uncertified_switch_selector_root_fallback_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    if !snippet.contains("fn resolve_switch_expr_for_block_with_selector(")
        || !snippet.contains("switch_selector_roots_map")
    {
        return false;
    }
    let Some(root_fallback_at) = snippet.find("switch_selector_roots_map") else {
        return false;
    };
    snippet
        .find("requires_certified_rendering")
        .is_none_or(|guard_at| guard_at > root_fallback_at)
}

fn r2dec_call_result_stack_owner_fallback_expr(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> bool {
    match expr.kind {
        ExprKind::Call(callee, _) => expr_path_last_segment_is(
            callee,
            "fallback_owned_call_result_stack_local_name_for_source",
        ),
        ExprKind::MethodCall(method, _, _, _) => {
            let method = method.ident.as_str();
            method == "fallback_owned_call_result_stack_local_name_for_source"
                || (method == "semantic_stack_owner_name_for_alias"
                    && enclosing_item_snippet_contains(
                        cx,
                        expr,
                        "derive_stable_owned_call_result_name_for_alias",
                    ))
        }
        _ => false,
    }
}

fn r2dec_call_result_source_expr_owner_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(span)
        .is_ok_and(|snippet| {
            [
                "fn fallback_owned_call_result_register_name_from_matching_source_call",
                "fn fallback_owned_call_result_register_name_from_matching_definition",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
                || (snippet.contains("raw_call_exprs_match_for_source_owner_definition")
                    && [
                        "stable_owned_call_result_name_for_source",
                        "should_materialize_call_result_at_source",
                        "materializable_call_result_expr_for_call_expr",
                    ]
                    .iter()
                    .any(|needle| snippet.contains(needle)))
        })
}

fn r2dec_certified_call_result_return_register_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn fallback_owned_call_result_return_name_for_source")
        || !snippet.contains("fallback_owned_call_result_return_name_for_alias")
        || !snippet.contains("direct_call_result_aliases_set")
    {
        return false;
    }
    let fallback_at = snippet
        .find("source_call_allows_return_register_owner")
        .or_else(|| snippet.find("direct_call_result_aliases_set"))
        .unwrap_or(0);
    snippet
        .find("requires_certified_rendering")
        .is_none_or(|guard_at| guard_at > fallback_at)
}

fn r2dec_certified_call_result_alias_owner_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn derive_stable_owned_call_result_name_for_source")
        || !snippet.contains("fallback_owned_call_result_register_name_for_alias")
        || !snippet.contains("direct_call_result_aliases_set")
    {
        return false;
    }
    let fallback_at = snippet
        .find("direct_call_result_aliases_set")
        .or_else(|| snippet.find("fallback_owned_call_result_register_name_for_alias"))
        .unwrap_or(0);
    snippet
        .find("requires_certified_rendering")
        .is_none_or(|guard_at| guard_at > fallback_at)
}

fn r2dec_certified_local_call_ownership_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if snippet.contains("fn stable_owned_call_result_name_for_source") {
        let Some(local_owner_at) = snippet.find("ownership_for_source") else {
            return false;
        };
        return snippet
            .find("requires_certified_rendering")
            .is_none_or(|guard_at| guard_at > local_owner_at);
    }
    if snippet.contains("fn source_call_for_visible_owner_name") {
        let Some(local_owner_at) = snippet.find("source_for_visible_owner_name") else {
            return false;
        };
        return snippet
            .find("requires_certified_rendering")
            .is_none_or(|guard_at| guard_at > local_owner_at);
    }
    if snippet.contains("fn call_result_source_for_ssa_name")
        && (snippet.contains("source_for_alias")
            || snippet.contains("call_result_source_for_name")
            || snippet.contains("prepared_semantic_view"))
    {
        let local_at = snippet
            .find("source_for_alias")
            .or_else(|| snippet.find("call_result_source_for_name"))
            .or_else(|| snippet.find("prepared_semantic_view"))
            .unwrap_or(usize::MAX);
        let Some(certified_at) = snippet.find("if self.requires_certified_rendering()") else {
            return true;
        };
        return certified_at > local_at
            || !snippet[..local_at].contains("certified_call_result_source_for_ssa_name");
    }
    false
}

fn r2dec_certified_call_result_preservation_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn should_preserve_owned_call_result_visible_name")
        || !snippet.contains("has_visible_owner_name")
    {
        return false;
    }
    let Some(fallback_at) = snippet.find("has_visible_owner_name") else {
        return false;
    };
    snippet
        .find("requires_certified_rendering")
        .is_none_or(|guard_at| guard_at > fallback_at)
}

fn r2dec_certified_duplicate_call_pruning_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if (snippet.contains("fn prune_duplicate_tail_call_statements")
        || snippet.contains("fn prune_duplicate_call_statements_by_source"))
        && snippet.contains("collect_rendered_call_sources_for_expr")
    {
        return true;
    }
    snippet.contains("fn collect_duplicate_pruning_call_sources_for_expr")
        && !snippet.contains("collect_certified_rendered_call_sources_for_expr")
}

fn r2dec_certified_visible_owner_source_lookup_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    snippet.contains("fn source_call_for_visible_owner_name")
        && snippet.contains("prepared_source_call_for_visible_owner_name")
        && !snippet.contains("stable_owned_call_result_name_for_source")
}

fn r2dec_certified_prepared_result_owner_expr_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn stable_owned_call_result_expr_for_source")
        || !snippet.contains("result_owner.clone()")
    {
        return false;
    }
    let Some(prepared_expr_at) = snippet.find("result_owner.clone()") else {
        return false;
    };
    let certified_name_at = snippet
        .find("if self.requires_certified_rendering()")
        .filter(|guard_at| *guard_at < prepared_expr_at)
        .and_then(|guard_at| {
            snippet[guard_at..prepared_expr_at]
                .contains("prepared_result_owner_name_for_source")
                .then_some(guard_at)
        });
    certified_name_at.is_none()
}

fn r2dec_certified_prepared_result_owner_fact_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn stable_owned_call_result_name_for_source")
        && !snippet.contains("fn stable_owned_call_result_expr_for_source")
    {
        return false;
    }
    snippet.contains("prepared_result_owner_name_for_source")
        && !snippet.contains("has_certified_call_result_owner_fact_for_source")
}

fn r2dec_certified_stack_return_render_facts_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    snippet.contains("fn certified_unique_scalar_stack_return_expr")
        && snippet.contains("return_stack_slots")
        && !snippet.contains("render_facts")
}

fn r2dec_certified_stack_local_identity_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    (snippet.contains("fn certified_standard_output_residual_reason_with_effect_proofs")
        && snippet.contains("has_stack_slot_offset(offset)")
        && !snippet.contains("certified_stack_local_identity_is_exact"))
        || (snippet.contains("fn build_function")
            && snippet.contains("body_visible_stack_offsets")
        && !snippet.contains("certified_recovered_stack_local_is_exact"))
        || (snippet.contains("fn stack_offset_for_visible_storage_name")
            && (snippet.contains("strip_prefix(\"local_\")")
                || snippet.contains("strip_prefix(\"arg_\")"))
            && !snippet.contains("certified_stack_offset_for_visible_storage_name"))
        || (snippet.contains("fn stack_offsets_for_visible_storage_name")
            && snippet.contains("canonical_stack_offset_for_visible_storage_name")
            && !snippet.contains("requires_certified_rendering()"))
        || (snippet.contains("fn stack_slot_provenance_for_name")
            && snippet.contains("render_stack_slot_for_name")
            && !snippet.contains("certified_stack_offset_for_visible_storage_name"))
        || (snippet.contains("fn stack_slot_provenance_for_var")
            && snippet.contains("render_stack_slot_for_name"))
    }

fn r2dec_certified_stack_local_type_ownership_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    (snippet.contains("fn build_function")
        && snippet.contains("certified_standard_mode")
        && snippet.contains("choose_more_specific_runtime_type")
        && !snippet.contains("typed_stack_local_type_for_name_offset"))
        || (snippet.contains("fn certified_standard_output_residual_reason_with_effect_proofs")
            && snippet.contains("local.ty")
            && !snippet.contains("certified_stack_local_type_matches"))
}

fn r2dec_certified_local_type_hints_item(cx: &LateContext<'_>, span: rustc_span::Span) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    snippet.contains("certified_standard_mode")
        && snippet.contains("FoldInputs")
        && (snippet.contains("type_hints: &type_hints") || snippet.contains("type_oracle,"))
}

fn r2dec_certified_member_field_certificate_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    (snippet.contains("fn render_access_expr_from_addr")
        && snippet.contains("member_access_expr")
        && !snippet.contains("certified_field_name_for_offset"))
        || snippet.contains("member_access_for_op_any_direction")
        || snippet.contains("array_access_for_op_any_direction")
}

fn r2dec_certified_branch_render_proof_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    snippet.contains("fn structure_region")
        && snippet.contains("Region::IfThenElse")
        && snippet.contains("CStmt::if_stmt")
        && !snippet.contains("record_branch_render_proof")
}

fn r2dec_certified_branch_condition_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if snippet.contains("fn extract_condition_from_block") {
        let local_at = snippet
            .find("local_branch_condition_expr")
            .or_else(|| snippet.find("symbolic_actionable_compiled_condition_expr"))
            .or_else(|| snippet.find("symbolic_branch_condition_expr"));
        let Some(local_at) = local_at else {
            return false;
        };
        return snippet
            .find("requires_certified_rendering")
            .is_none_or(|guard_at| guard_at > local_at);
    }
    if snippet.contains("fn get_branch_condition_with_predicate")
        && snippet.contains("extract_condition(op)")
    {
        let Some(fallback_at) = snippet.find("extract_condition(op)") else {
            return false;
        };
        return snippet
            .find("requires_certified_rendering")
            .is_none_or(|guard_at| guard_at > fallback_at);
    }
    false
}

fn r2dec_certified_loop_structure_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    snippet.contains("fn structure_region")
        && (snippet.contains("Region::WhileLoop") || snippet.contains("Region::DoWhileLoop"))
        && (snippet.contains("CStmt::while_loop") || snippet.contains("CStmt::DoWhile"))
        && !snippet.contains("certified_loop_render_proof")
}

fn r2dec_certified_switch_structure_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    snippet.contains("fn structure_switch_region")
        && snippet.contains("CStmt::Switch")
        && !snippet.contains("certified_switch_render_proof")
}

fn r2dec_certified_raw_call_arg_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn certified_call_args_for_site_with_direct_target")
        || !snippet.contains("let args = self.render_call_args_for_site_with_direct_target")
    {
        return false;
    }
    if !snippet.contains("raw_call_args_match_function_facts")
        || !snippet.contains("canonical_argument_values")
    {
        return true;
    }
    false
}

fn r2dec_certified_prepared_call_arg_expr_proof_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    snippet.contains("fn certified_call_args_for_site_with_direct_target")
        && snippet.contains("prepared_call_args_for_site_with_direct_target")
}

fn r2dec_certified_executable_post_call_repair_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn op_to_stmt_impl") || !snippet.contains("requires_certified_rendering")
    {
        return false;
    }
    [
        "local_post_call_source_for_ssa_name",
        "raw_local_post_call_source_for_ssa_name_in_block",
        "recovered_owned_call_result_definition_rhs",
        "recovered_owned_call_result_definition_rhs_for_visible_name",
        "call_result_exprs_map()",
        "call_result_aliases_map()",
        "lookup_definition_raw",
        "direct_definition_expr",
    ]
    .iter()
    .any(|needle| snippet.contains(needle))
}

fn r2dec_certified_call_render_proof_local_equality_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if ![
        "fn certified_source_for_rendered_call_expr",
        "fn source_proof_for_call_expr",
        "fn source_matches_for_call_expr",
        "fn collect_certified_rendered_call_sources_for_expr",
    ]
    .iter()
    .any(|needle| snippet.contains(needle))
    {
        return false;
    }
    [
        "source_proof_for_call_expr",
        "source_matches_for_call_expr",
        "call_result_exprs_map",
        "raw_call_exprs_match_for_source_owner_definition",
    ]
    .iter()
    .any(|needle| snippet.contains(needle))
}

fn r2dec_direct_zero_arg_call_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn op_to_stmt_impl")
        || !snippet.contains("SSAOp::Call")
        || !snippet.contains("CExpr::call(func_expr, vec![])")
    {
        return false;
    }
    let fallback_at = snippet
        .find("CExpr::call(func_expr, vec![])")
        .unwrap_or(0);
    snippet
        .find("requires_certified_rendering")
        .is_none_or(|guard_at| guard_at > fallback_at)
}

fn r2dec_certified_call_result_replay_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if ![
        "fn recovered_owned_call_result_definition_rhs_for_visible_name",
        "fn recovered_owned_call_result_definition_rhs",
        "fn op_to_stmt_impl",
    ]
    .iter()
    .any(|needle| snippet.contains(needle))
        || !snippet.contains("call_result_exprs_map")
        || !snippet.contains("synthesized_call_expr_for_source_call(source_call)")
    {
        return false;
    }

    let mut search_from = 0;
    while let Some(relative_at) = snippet[search_from..].find("call_result_exprs_map") {
        let cached_at = search_from + relative_at;
        let window_start = cached_at.saturating_sub(900);
        let before_cached = &snippet[window_start..cached_at];
        if !before_cached.contains("if self.requires_certified_rendering()")
            || !before_cached.contains("synthesized_call_expr_for_source_call(source_call)")
        {
            return true;
        }
        search_from = cached_at + "call_result_exprs_map".len();
    }
    false
}

fn r2dec_certified_return_local_expr_fallback_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn fold_block")
        || !snippet.contains("certified_return_expr_for_op")
        || !snippet.contains("best_visible_definition(&target.display_name())")
    {
        return false;
    }

    let local_definition_at = snippet
        .find("best_visible_definition(&target.display_name())")
        .unwrap_or(usize::MAX);
    let local_semantic_at = snippet
        .find("render_semantic_value_by_name(\n                                &target.display_name()")
        .or_else(|| snippet.find("render_semantic_value_by_name(&target.display_name()"))
        .unwrap_or(usize::MAX);
    let local_at = local_definition_at.min(local_semantic_at);
    let Some(proof_at) = snippet.find("certified_return_expr_for_op(block.addr, return_op_idx)")
    else {
        return true;
    };

    proof_at > local_at
}

fn r2dec_certified_return_call_result_fact_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    snippet.contains("fn certified_return_expr_for_value")
        && snippet.contains("call_result_certificate_for_value")
        && !snippet.contains("certified_call_result_fact_for_value")
}

fn r2dec_certified_local_post_call_source_fact_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn local_post_call_source_for_ssa_name_in_block")
        || !snippet.contains("raw_local_post_call_source_for_ssa_name_in_block")
    {
        return false;
    }
    let Some(certified_at) = snippet.find("if self.requires_certified_rendering()") else {
        return true;
    };
    let raw_at = snippet
        .find("raw_local_post_call_source_for_ssa_name_in_block")
        .unwrap_or(usize::MAX);
    if certified_at > raw_at {
        return true;
    }
    let certified_block = &snippet[certified_at..raw_at.min(snippet.len())];
    !certified_block.contains("return None;")
}

fn r2dec_call_result_source_expr_owner_fallback_expr(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> bool {
    match expr.kind {
        ExprKind::Call(callee, _) => [
            "fallback_owned_call_result_register_name_from_matching_source_call",
            "fallback_owned_call_result_register_name_from_matching_definition",
        ]
        .iter()
        .any(|name| expr_path_last_segment_is(callee, name)),
        ExprKind::MethodCall(method, _, _, _) => {
            let method = method.ident.as_str();
            matches!(
                method,
                "fallback_owned_call_result_register_name_from_matching_source_call"
                    | "fallback_owned_call_result_register_name_from_matching_definition"
            ) || (method == "raw_call_exprs_match_for_source_owner_definition"
                && enclosing_item_name(cx, expr)
                    .as_deref()
                    .is_some_and(is_call_result_source_expr_owner_boundary_name))
        }
        _ => false,
    }
}

fn is_call_result_source_expr_owner_boundary_name(name: &str) -> bool {
    matches!(
        name,
        "stable_owned_call_result_name_for_source"
            | "should_materialize_call_result_at_source"
            | "materializable_call_result_expr_for_call_expr"
            | "fallback_owned_call_result_register_name_from_matching_source_call"
            | "fallback_owned_call_result_register_name_from_matching_definition"
    )
}

fn r2dec_uncertified_field_placeholder_name(name: &str) -> bool {
    matches!(
        name,
        "fallback_aggregate_field_name" | "typedef_name_looks_aggregate"
    )
}

fn r2dec_direct_prepared_call_result_certificates_expr(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> bool {
    match expr.kind {
        ExprKind::Field(_, field) => {
            matches!(field.name.as_str(), "call_results" | "call_results_by_callsite")
                && cx
                    .sess()
                    .source_map()
                    .span_to_snippet(expr.span)
                    .is_ok_and(|snippet| snippet.contains("certificates()."))
        }
        ExprKind::MethodCall(method, _, _, _) => {
            method.ident.as_str() == "call_result_certificates_for_callsite"
        }
        _ => false,
    }
}

fn r2dec_direct_prepared_control_facts_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Field(_, field) => {
            field.name.as_str() == "prepared_predicates"
                || (matches!(field.name.as_str(), "predicates" | "switches")
                    && cx
                        .sess()
                        .source_map()
                        .span_to_snippet(expr.span)
                        .is_ok_and(|snippet| snippet.contains("predicates()")))
                || (matches!(field.name.as_str(), "loops" | "switches")
                    && cx
                        .sess()
                        .source_map()
                        .span_to_snippet(expr.span)
                        .is_ok_and(|snippet| snippet.contains("certificates()")))
        }
        ExprKind::MethodCall(method, _, _, _) => {
            method.ident.as_str() == "infer_switch_selector_var"
        }
        _ => false,
    }
}

fn plugin_engine_policy_ownership_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            let banned_items = [
                "static TYPE_WRITEBACK_CACHE",
                "fn auto_callback_policy_for_depth",
                "fn auto_callback_plan_for_depth",
                "fn function_exceeds_auto_callback_budget",
                "fn sleigh_mode_allows_deep_auto_callbacks",
                "fn mode_allows_deep_auto_callbacks",
                "fn caller_prefers_bounded_type_plan",
                "fn analysis_policy_for_depth",
                "fn r2sleigh_interproc_helper_scope_budget_allows",
                "fn engine_analyze_request_with_scope_facts",
                "pub extern \"C\" fn r2dec_function_with_context",
                "pub extern \"C\" fn r2dec_function_with_context_scope",
                "pub extern \"C\" fn r2dec_function_with_session_context",
                "fn r2dec_function_with_context_impl",
                "fn r2dec_function_with_session_context_output",
                "pub extern \"C\" fn r2dec_named_native_worker_summary",
                "pub extern \"C\" fn r2dec_semantic_worker_linearization_scope_ffi",
                "pub extern \"C\" fn r2dec_block_guard_comment_ffi",
                "fn r2sleigh_session_artifact_cache_key",
                "fn r2sleigh_alias_function_analysis_artifact_cache",
                "fn function_analysis_artifact_cache_identity_hash_with_parsed_context_and_scope_facts",
                "fn alias_cached_function_analysis_artifact",
                "fn build_interproc_summary_set_with_scope_facts",
                "fn get_cached_function_analysis_artifact_with_parsed_context_and_scope_facts",
                "fn function_root_interproc_summary",
                "pub fn interproc_root_summary",
                "struct EngineInterprocRootSummaryRequest",
                "struct EngineInterprocRootSummaryResponse",
                "pub extern \"C\" fn r2sleigh_session_analyze",
                "pub extern \"C\" fn r2sleigh_session_result_report_json",
                "pub extern \"C\" fn r2sleigh_session_result_free",
                "pub extern \"C\" fn r2sleigh_session_interproc_summary_json",
                "pub extern \"C\" fn r2sleigh_data_ref_cache_",
                "pub extern \"C\" fn r2sleigh_data_ref_cache_key",
                "pub struct R2SleighSessionInput",
                concat!("fn session_", "analysis_input"),
                "struct SessionAnalysisInput",
                "struct TypeWritebackInferenceInput",
                "struct FunctionAnalysisSharedBundle",
            ];
            banned_items
                .iter()
                .any(|needle| snippet.contains(needle))
                || (snippet.contains("fn build_function_analysis_shared_bundle")
                    && snippet.contains("EngineAnalyzeRequest::full_semantics_for_function"))
                || (snippet.contains(
                    "fn function_analysis_artifact_cache_identity_hash_with_parsed_context_and_scope_facts",
                ) && snippet.contains("EngineAnalyzeRequest::full_semantics_for_function"))
                || (snippet.contains(
                    "fn build_function_analysis_artifact_with_scope_context_and_scope_facts",
                ) && snippet.contains("EngineAnalyzeRequest::full_semantics_for_function"))
                || (snippet.contains(
                    "fn get_cached_function_analysis_artifact_with_parsed_context_and_scope_facts",
                ) && snippet.contains("EngineAnalyzeRequest::full_semantics_for_function"))
                || (snippet.contains("fn r2sleigh_session_artifact_cache_key")
                    && (snippet.contains("interproc_iter.max")
                        || snippet.contains("interproc_max_iters.max")
                        || snippet.contains("TypeWritebackInferenceInput {")))
                || (snippet.contains("fn infer_signature_cc_from_analysis")
                    && snippet.contains("collect_register_type_hints"))
                || (snippet.contains("fn recover_vars_for_ffi")
                    && snippet.contains("collect_register_type_hints"))
        })
}

fn engine_artifacts_facts_side_channel_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("struct EngineArtifacts")
                && (snippet.contains("semantic_artifact") || snippet.contains("route:"))
        })
}

fn plugin_engine_policy_ownership_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Call(callee, _) => {
            if cx
                .sess()
                .source_map()
                .span_to_snippet(expr.span)
                .is_ok_and(|snippet| {
                    snippet.contains("EngineFunctionDecompileRequest::")
                        || snippet.contains("EngineAnalyzeRequest::")
                })
            {
                return true;
            }
            if expr_path_last_segment_is(callee, "new")
                && cx
                    .sess()
                    .source_map()
                    .span_to_snippet(expr.span)
                    .is_ok_and(|snippet| snippet.contains("EngineSession::new"))
            {
                return true;
            }
            [
                "render_semantic_worker_linearization",
                "compile_summary_dense_worker_artifact_from_interproc_summary",
                "compile_semantic_artifact_default_with_scope",
                "augment_semantic_artifact_with_interproc_summary",
                "build_semantic_type_fallback_plan",
                "guarded_worker_summary",
                "function_semantic_summary_seed_for_name",
                "function_semantic_summary_seed_for_name_with_linkage",
                "has_native_worker_summary_family",
                "render_direct_named_native_worker_summary",
                "decompile_route_decision",
                "function_analysis_report_payload_from_type_response",
                "auto_callback_plan_for_policy",
                "r2sleigh_session_artifact_cache_key",
                "r2sleigh_alias_function_analysis_artifact_cache",
                "function_analysis_artifact_cache_identity_hash_with_parsed_context_and_scope_facts",
                "alias_cached_function_analysis_artifact",
                "build_interproc_summary_set_with_scope_facts",
                "solve_interproc_summary_set",
                "full_semantics",
                "from_compile_missing_semantics",
                "should_use_direct_named_native_worker_decompile",
                "should_use_direct_named_native_worker_type_projection",
            ]
            .iter()
            .any(|name| expr_path_last_segment_is(callee, name))
        }
        ExprKind::MethodCall(method, _, _, _) => {
            matches!(
                method.ident.as_str(),
                "cached_analyze"
                    | "decompile_summary"
                    | "decompile_summary_preprobe"
                    | "type_function"
            )
        }
        ExprKind::Struct(qpath, fields, _) => {
            (qpath_last_segment_is(qpath, "EngineTypeAnalysisRequest")
                && fields.iter().any(|field| {
                    field.ident.name.as_str() == "caller_prefers_bounded_type_plan"
                }))
                || (qpath_last_segment_is(qpath, "EngineSummaryDecompileRequest")
                    && fields
                        .iter()
                        .any(|field| field.ident.name.as_str() == "fallback_comment"))
                || qpath_last_segment_is(qpath, "EngineDetachedSemanticWorkerSummaryRequest")
                || qpath_last_segment_is(qpath, "EngineAnalyzeRequestParts")
                || qpath_last_segment_is(qpath, "EngineAnalyzeRequest")
                || qpath_last_segment_is(qpath, "EngineSummaryPreprobeRequest")
        }
        ExprKind::Path(_) => cx
            .sess()
            .source_map()
            .span_to_snippet(expr.span)
            .is_ok_and(|snippet| {
                snippet.ends_with("EngineSemanticMode::Full")
                    || snippet.ends_with("EngineSemanticMode::Optional")
                    || snippet.ends_with("EngineSemanticRoutePlan")
            }),
        _ => false,
    }
}

fn engine_decompiler_context_side_channel_expr(expr: &Expr<'_>) -> bool {
    matches!(
        expr.kind,
        ExprKind::MethodCall(method, _, _, _)
            if matches!(
                method.ident.as_str(),
                "with_semantic_route"
                    | "with_render_permission"
                    | "with_runtime_type_inference_policy"
                    | "with_prepared_semantic_view_policy"
            )
    )
}

fn engine_r2dec_summary_render_route_side_channel_expr(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> bool {
    let ExprKind::Call(callee, args) = expr.kind else {
        return false;
    };
    let expected_arity = if expr_path_last_segment_is(callee, "render_semantic_worker_summary") {
        3
    } else if expr_path_last_segment_is(callee, "render_vm_semantic_summary") {
        2
    } else {
        return false;
    };
    args.len() > expected_arity
        || args.iter().any(|arg| {
            cx.sess()
                .source_map()
                .span_to_snippet(arg.span)
                .is_ok_and(|snippet| {
                    snippet.contains("EngineSemanticRoutePlan")
                        || snippet.contains("SemanticRoutePlan")
                        || snippet.contains("to_decompiler_route(")
                })
        })
}

fn engine_r2dec_route_conversion_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("fn to_decompiler_route(")
                || snippet.contains("pub enum EngineSemanticRoutePlan")
                || snippet.contains("struct EngineSemanticRoutePlan")
                || snippet.contains("fn decompile_route_facts_from_decision(")
                || snippet.contains("fn decompile_route_from_facts(")
                || snippet.contains("r2dec::SemanticRoutePlan")
        })
}

fn engine_decompiler_context_side_channel_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    (snippet.contains("struct EngineDecompileRequest")
        || snippet.contains("struct DecompileRenderCacheKeyInput"))
        && snippet.contains("callee_resolution:")
}

fn engine_decompile_facts_spine_ownership_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    if snippet.contains("fn attach_prepared_decompile_evidence(") {
        return false;
    }
    [
        ".set_callee_resolution(",
        ".set_callsites(",
        ".set_call_results(",
        ".set_control(",
    ]
    .iter()
    .any(|needle| snippet.contains(needle))
}

fn raw_attach_prepared_decompile_evidence_signature(snippet: &str) -> bool {
    snippet.contains("fn attach_prepared_decompile_evidence(")
        && (snippet.contains("function_names:") || snippet.contains("symbols:"))
}

fn raw_attach_prepared_decompile_evidence_signature_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| raw_attach_prepared_decompile_evidence_signature(&snippet))
}

fn raw_attach_prepared_decompile_evidence_signature_impl_item(
    cx: &LateContext<'_>,
    item: &ImplItem<'_>,
) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| raw_attach_prepared_decompile_evidence_signature(&snippet))
}

fn engine_summary_decompile_route_side_channel_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    if snippet.contains("fn summary_decompile_function_facts_with_route(") {
        return false;
    }
    (snippet.contains("struct EngineSummaryDecompileRequest")
        && (snippet.contains("named_worker_guarded:")
            || snippet.contains("fallback_comment: Option")))
        || (snippet.contains("fn render_engine_summary_decompile_request")
            && snippet.contains("request.fallback_comment"))
        || (snippet.contains("fn decompile_summary")
            && snippet.contains("named_worker_summary_route(request.named_worker_guarded"))
}

fn engine_summary_only_decompile_api_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            let header = snippet.split_once('{').map_or(snippet.as_str(), |(head, _)| head);
            header.contains("EngineSummaryDecompileRequest")
                || header.contains("fn decompile_summary(")
                || header.contains("fn decompile_summary_preprobe(")
        })
}

fn engine_summary_only_decompile_api_impl_item(
    cx: &LateContext<'_>,
    item: &ImplItem<'_>,
) -> bool {
    if engine_summary_only_decompile_api_name(item.ident.name.as_str()) {
        return true;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| snippet.contains("EngineSummaryDecompileRequest"))
}

fn engine_summary_only_decompile_api_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::MethodCall(method, ..) => {
            engine_summary_only_decompile_api_name(method.ident.as_str())
        }
        ExprKind::Call(callee, _) => {
            expr_path_last_segment_is(callee, "decompile_summary")
                || expr_path_last_segment_is(callee, "decompile_summary_preprobe")
                || cx
                    .sess()
                    .source_map()
                    .span_to_snippet(callee.span)
                    .is_ok_and(|snippet| snippet.contains("EngineSummaryDecompileRequest::"))
        }
        ExprKind::Struct(qpath, ..) => {
            qpath_last_segment_is(qpath, "EngineSummaryDecompileRequest")
        }
        ExprKind::Path(ref qpath) => {
            qpath_last_segment_is(qpath, "EngineSummaryDecompileRequest")
        }
        _ => false,
    }
}

fn engine_summary_only_decompile_api_name(name: &str) -> bool {
    matches!(
        name,
        "EngineSummaryDecompileRequest" | "decompile_summary" | "decompile_summary_preprobe"
    )
}

fn engine_lower_level_decompile_api_bypass_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    let header = item_header(&snippet);
    header.contains("pub struct EngineDecompileRequest")
        || public_decompile_signature_accepts_engine_decompile_request(header)
}

fn engine_lower_level_decompile_api_bypass_impl_item(
    cx: &LateContext<'_>,
    item: &ImplItem<'_>,
) -> bool {
    if item.ident.name.as_str() != "decompile" {
        return false;
    }
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    public_decompile_signature_accepts_engine_decompile_request(item_header(&snippet))
}

fn public_decompile_signature_accepts_engine_decompile_request(header: &str) -> bool {
    header.contains("pub fn decompile(") && header.contains("EngineDecompileRequest")
}

fn item_header(snippet: &str) -> &str {
    snippet.split_once('{').map_or(snippet, |(head, _)| head)
}

fn engine_render_time_semantics_suppression_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    (snippet.contains("fn render_engine_decompile_request")
        && (snippet.contains("set_semantics(None)")
            || snippet.contains("suppress_unrenderable_summary")))
        || snippet.contains("fn should_suppress_unrenderable_standard_summary_artifact")
}

fn engine_decompile_type_override_side_channel_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    snippet.contains("fn decompile_function")
        && (snippet.contains(".function_facts.types.merged_signature")
            || snippet.contains(".function_facts.types.signature_certificate"))
}

fn engine_decompile_fallback_comment_side_channel_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    (snippet.contains("struct EngineDecompileRequest")
        && snippet.contains("fallback_comment: Option"))
        || (snippet.contains("fn render_engine_decompile_request")
            && snippet.contains("request.fallback_comment"))
}

fn engine_decompile_route_type_facts_side_channel_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    (snippet.contains("fn decompile_route_decision")
        || snippet.contains("fn plan_decompile_request")
        || snippet.contains("fn should_skip_runtime_type_inference"))
        && snippet.contains("type_facts:")
}

fn engine_decompiler_input_route_replan_side_channel_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    if snippet.contains("fn decompiler_input_from_prepared_facts")
        && (snippet.contains("decompile_route_decision(")
            || snippet.contains("decompiler_context_with_route_decision("))
    {
        return true;
    }
    if !snippet.contains("fn decompile_function") {
        return false;
    }
    let Some(facts_at) = snippet.find("function_facts_for_decompile(") else {
        return false;
    };
    snippet[facts_at..].contains("decompile_route_decision(")
}

fn engine_decompiler_input_helper_not_test_support_only_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    snippet.contains("pub fn decompiler_input_from_prepared_facts")
        && !snippet.contains("#[cfg(test)]")
}

fn engine_decompile_render_cache_pre_route_facts_impl_item(
    cx: &LateContext<'_>,
    span: rustc_span::Span,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(span) else {
        return false;
    };
    if !snippet.contains("fn decompile_function") {
        return false;
    }
    let Some(cache_at) = snippet.find("decompile_render_cache_key") else {
        return false;
    };
    let route_at = snippet
        .find("function_facts_for_decompile(")
        .or_else(|| snippet.find(".set_decompile_route(Some(decompile_route_facts_from_decision"));
    let Some(route_at) = route_at else {
        return true;
    };
    cache_at < route_at
}

fn r2dec_decompiler_context_route_side_channel_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    snippet.contains("struct DecompilerContext")
        && (snippet.contains("semantic_route:")
            || snippet.contains("render_permission:")
            || snippet.contains("skip_runtime_type_inference:")
            || snippet.contains("use_prepared_semantic_view:"))
}

fn r2dec_decompiler_context_callee_resolution_side_channel_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    snippet.contains("struct DecompilerContext") && snippet.contains("callee_resolution:")
}

fn r2dec_direct_type_facts_mutator_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    snippet.contains("fn from_analysis_inputs") && snippet.contains("FunctionTypeFacts")
}

fn r2dec_local_signature_enrichment_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("fn from_function_facts")
                && snippet.contains("enrich_known_function_signatures_from_names")
        })
}

fn r2dec_direct_type_facts_mutator_impl_item(
    cx: &LateContext<'_>,
    item: &ImplItem<'_>,
) -> bool {
    let name = item.ident.name.as_str();
    if !matches!(
        name,
        "type_facts_mut"
            | "with_type_facts"
            | "set_type_facts"
            | "set_known_function_signatures"
            | "set_external_type_db"
    ) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("FunctionTypeFacts")
                || snippet.contains("type_facts_mut")
                || snippet.contains(".function_facts.types")
        })
}

fn r2dec_decompiler_context_route_side_channel_method(name: &str) -> bool {
    matches!(
        name,
        "with_semantic_route"
            | "with_render_permission"
            | "with_runtime_type_inference_policy"
            | "with_prepared_semantic_view_policy"
    )
}

fn plugin_unprepared_decompile_oracle_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::MethodCall(method, _receiver, [arg], _) = expr.kind else {
        return false;
    };
    if method.ident.as_str() != "decompile" {
        return false;
    }

    cx.sess()
        .source_map()
        .span_to_snippet(arg.span)
        .is_ok_and(|snippet| snippet.contains("artifact.ssa_func"))
}

fn plugin_decompiler_input_executable_c_oracle_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    if !item_is_test_only(cx, item) && !item_is_inside_test_context(cx, item) {
        return false;
    }

    let Ok(snippet) = cx.sess().source_map().span_to_snippet(item.span) else {
        return false;
    };
    if !snippet.contains("decompiler_input_from_artifact(")
        || !snippet.contains(".decompile_input(")
    {
        return false;
    }

    snippet.lines().any(|line| {
        let line = line.trim();
        line.contains(".contains(\"")
            && line
                .match_indices(".contains(\"")
                .any(|(idx, _)| !contains_call_is_negated_in_line(line, idx))
            && plugin_executable_c_body_oracle_line(line)
    })
}

fn plugin_decompiler_input_test_bypass_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    if !item_is_test_only(cx, item) && !item_is_inside_test_context(cx, item) {
        return false;
    }

    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("decompiler_input_from_artifact(")
                && snippet.contains(".decompile_input(")
        })
}

fn plugin_executable_c_body_oracle_line(line: &str) -> bool {
    [
        "return ",
        "if (",
        "for (",
        "while (",
        "switch (",
        "case ",
        " = sym.imp.",
        "sym.imp.",
    ]
    .iter()
    .any(|needle| line.contains(needle))
}

fn plugin_decompile_metadata_policy_ownership_item(
    cx: &LateContext<'_>,
    item: &Item<'_>,
) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains("fn parse_addr_name_map")
                || snippet.contains("fn resolve_decompiler_display_name")
                || snippet.contains("fn strip_display_name_prefixes")
                || snippet.contains("EngineFunctionDecompileRequest")
                && (snippet.contains("parse_addr_name_map")
                    || snippet.contains("resolve_decompiler_display_name"))
        })
}

fn plugin_direct_r2dec_op_lowering_expr(expr: &Expr<'_>) -> bool {
    matches!(
        expr.kind,
        ExprKind::Call(callee, _) if expr_path_last_segment_is(callee, "lower_ssa_ops_to_stmts")
    )
}

fn plugin_direct_clike_block_decompile_export_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, args) = expr.kind else {
        return false;
    };
    if !expr_path_last_segment_is(callee, "export_instruction") {
        return false;
    }
    args.iter().any(|arg| {
        cx.sess()
            .source_map()
            .span_to_snippet(arg.span)
            .is_ok_and(|snippet| snippet.contains("InstructionAction::Dec"))
    }) && args.iter().any(|arg| {
        cx.sess()
            .source_map()
            .span_to_snippet(arg.span)
            .is_ok_and(|snippet| snippet.contains("ExportFormat::CLike"))
    })
}

fn plugin_direct_r2dec_ast_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = expr.kind else {
        return false;
    };
    cx.sess()
        .source_map()
        .span_to_snippet(callee.span)
        .is_ok_and(|snippet| snippet.contains("r2dec::CStmt::"))
}

fn plugin_direct_r2dec_fallback_comment_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = expr.kind else {
        return false;
    };
    if ![
        "block_guard_fallback_comment",
        "artifact_guard_fallback_comment",
        "semantic_fallback_comment",
    ]
    .iter()
    .any(|name| expr_path_last_segment_is(callee, name))
    {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(callee.span)
        .is_ok_and(|snippet| snippet.contains("r2dec::"))
}

fn plugin_direct_r2dec_decompiler_ownership_expr(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> bool {
    match expr.kind {
        ExprKind::Call(callee, _) => cx
            .sess()
            .source_map()
            .span_to_snippet(callee.span)
            .is_ok_and(|snippet| {
                snippet.contains("r2dec::Decompiler::new")
                    || snippet.contains("r2dec::DecompilerInput::new")
            }),
        ExprKind::MethodCall(method, ..) => {
            matches!(method.ident.as_str(), "decompile" | "decompile_input")
        }
        _ => false,
    }
}

fn plugin_decompile_one_function_direct_r2dec_expr(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> bool {
    if !enclosing_item_snippet_contains(cx, expr, "decompile_one_function")
        && !enclosing_item_snippet_contains(cx, expr, "r2dec_function")
    {
        return false;
    }

    match expr.kind {
        ExprKind::Call(callee, _) => cx
            .sess()
            .source_map()
            .span_to_snippet(callee.span)
            .is_ok_and(|snippet| {
                snippet.contains("r2dec::Decompiler::new")
                    || snippet.contains("r2dec::DecompilerInput::new")
                    || snippet.contains("r2dec::lower_ssa_ops_to_stmts")
                    || (snippet.contains("r2dec::") && snippet.contains("lower"))
            }),
        ExprKind::MethodCall(method, ..) => matches!(
            method.ident.as_str(),
            "decompile" | "decompile_input" | "build_function" | "build_function_from_input"
        ),
        ExprKind::Struct(qpath, ..) => {
            qpath_last_segment_is(qpath, "Decompiler")
                || qpath_last_segment_is(qpath, "DecompilerInput")
                || cx
                    .sess()
                    .source_map()
                    .span_to_snippet(expr.span)
                    .is_ok_and(|snippet| {
                        snippet.contains("r2dec::Decompiler")
                            || snippet.contains("r2dec::DecompilerInput")
                    })
        }
        _ => false,
    }
}

fn r2dec_source_shaped_decompile_oracle_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
        return false;
    }
    if !item_is_inside_test_context(cx, item) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            snippet.contains(".decompile(&func)")
                && source_shaped_positive_contains_oracle_snippet(&snippet)
        })
}

fn item_is_inside_test_context(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    if cx
        .sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| snippet.contains("#[test]") || snippet.contains("mod tests"))
    {
        return true;
    }

    for (_, node) in cx.tcx.hir_parent_iter(item.hir_id()) {
        if let rustc_hir::Node::Item(parent) = node
            && cx
                .sess()
                .source_map()
                .span_to_snippet(parent.span)
                .is_ok_and(|snippet| snippet.contains("mod tests"))
        {
            return true;
        }
    }
    false
}

fn source_shaped_positive_contains_oracle_snippet(snippet: &str) -> bool {
    const SHAPES: [&str; 6] = ["return ", "if (", "for (", "while (", "switch (", "case "];
    for line in snippet.lines() {
        if !line.contains(".contains(\"") || !SHAPES.iter().any(|shape| line.contains(shape)) {
            continue;
        }
        for (contains_idx, _) in line.match_indices(".contains(\"") {
            if !contains_call_is_negated_in_line(line, contains_idx) {
                return true;
            }
        }
    }
    false
}

fn contains_call_is_negated_in_line(line: &str, contains_idx: usize) -> bool {
    let prefix = &line[..contains_idx];
    prefix
        .rsplit(['&', '|', '('])
        .next()
        .is_some_and(|segment| segment.contains('!'))
}

fn r2dec_default_true_branch_condition_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::MethodCall(method, _, _, _) = expr.kind else {
        return false;
    };
    if !matches!(method.ident.as_str(), "unwrap_or" | "unwrap_or_else") {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(expr.span)
        .is_ok_and(|snippet| {
            snippet.contains("extract_condition_from_block")
                && snippet.contains("CExpr::IntLit(1)")
        })
}

fn r2dec_uncertified_stack_local_synthesis_expr(expr: &Expr<'_>) -> bool {
    matches!(
        expr.kind,
        ExprKind::MethodCall(method, _, _, _)
            if matches!(method.ident.as_str(), "has_definitions" | "has_stack_slots")
    )
}

fn r2dec_certified_stack_owner_proof_recomposition_expr(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> bool {
    let directly_reads_stack_owner_recovery = match expr.kind {
        ExprKind::MethodCall(method, _, _, _) => {
            matches!(
                method.ident.as_str(),
                "preferred_stack_alias_name" | "stack_slot_provenance_for_name"
            )
        }
        ExprKind::Call(callee, _) => [
            "preferred_stack_alias_name",
            "stack_slot_provenance_for_name",
        ]
        .iter()
        .any(|name| expr_path_last_segment_is(callee, name)),
        _ => false,
    };

    let recomposes_from_stack_offset = matches!(
        expr.kind,
        ExprKind::MethodCall(method, _, _, _) if method.ident.as_str() == "has_stack_slot_offset"
    );

    if !directly_reads_stack_owner_recovery && !recomposes_from_stack_offset {
        return false;
    }

    let Some((name, snippet)) = enclosing_item_name_and_snippet(cx, expr) else {
        return false;
    };
    if directly_reads_stack_owner_recovery && !certified_call_result_stack_owner_helper_name(&name)
    {
        return false;
    }
    if recomposes_from_stack_offset && !certified_stack_owner_helper_name(&name) {
        return false;
    }
    if snippet_calls_function_facts_stack_predicate(&snippet) {
        return false;
    }
    if directly_reads_stack_owner_recovery {
        return true;
    }
    snippet_recomposes_stack_owner_proof(&snippet)
}

fn certified_call_result_stack_owner_helper_name(name: &str) -> bool {
    name.contains("certified")
        && name.contains("call_result")
        && (name.contains("stack")
            || name.contains("owner")
            || name.contains("alias")
            || name.contains("source")
            || name.contains("expr")
            || name.contains("name"))
}

fn certified_stack_owner_helper_name(name: &str) -> bool {
    name.contains("certified")
        && name.contains("stack")
        && (name.contains("owner")
            || name.contains("local")
            || name.contains("visible_storage")
            || name.contains("storage_name"))
}

fn snippet_calls_function_facts_stack_predicate(snippet: &str) -> bool {
    [
        "FunctionFacts::",
        "function_facts.function_facts_stack",
        "function_facts.certified_stack",
        "function_facts.stack_owner",
        "function_facts.has_exact_stack",
        "stack_owner_authorizes",
    ]
    .iter()
    .any(|needle| snippet.contains(needle))
}

fn snippet_recomposes_stack_owner_proof(snippet: &str) -> bool {
    [
        "visible_bindings",
        "VisibleBinding",
        "binding.",
        "FunctionTypeFacts",
        "type_facts",
        "typed_stack",
        "stack_slots",
        "stack_type_is_renderable",
        "stack_owner_type_is_renderable",
        "local.ty",
        "slot.ty",
    ]
    .iter()
    .any(|needle| snippet.contains(needle))
}

fn r2dec_direct_stable_stack_values_get_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::MethodCall(method, receiver, _, _) = expr.kind else {
        return false;
    };
    method.ident.as_str() == "get"
        && expr_references_stable_stack_values(receiver)
        && !enclosing_item_name(cx, expr)
            .as_deref()
            .is_some_and(|name| name == "stable_stack_value_for_offset")
}

fn r2dec_unguarded_local_store_owner_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = expr.kind else {
        return false;
    };
    if !expr_path_last_segment_is(callee, "local_store_owner_expr_for_offset") {
        return false;
    }
    !enclosing_item_snippet_contains(cx, expr, "certified_rendering_required")
        && !enclosing_item_snippet_contains(cx, expr, "requires_certified_rendering()")
        && !enclosing_item_snippet_contains(cx, expr, "prepared-only")
        && !enclosing_item_snippet_contains(cx, expr, "prepared only")
}

fn expr_references_stable_stack_values(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Field(base, ident) => {
            ident.name.as_str() == "stable_stack_values"
                || expr_references_stable_stack_values(base)
        }
        ExprKind::MethodCall(_, receiver, args, _) => {
            expr_references_stable_stack_values(receiver)
                || args.iter().any(expr_references_stable_stack_values)
        }
        ExprKind::Call(callee, args) => {
            expr_references_stable_stack_values(callee)
                || args.iter().any(expr_references_stable_stack_values)
        }
        ExprKind::AddrOf(_, _, inner)
        | ExprKind::Unary(_, inner)
        | ExprKind::Cast(inner, _)
        | ExprKind::DropTemps(inner) => expr_references_stable_stack_values(inner),
        _ => false,
    }
}

fn r2types_role_name_signature_hint_expr(expr: &Expr<'_>) -> bool {
    matches!(
        expr.kind,
        ExprKind::Call(callee, _)
            if expr_path_last_segment_is(callee, "signature_hint_for_name_candidates")
                || expr_path_last_segment_is(callee, "signature_hint_for_role_name")
                || expr_path_last_segment_is(callee, "type_projection_for_name_candidates")
    )
}

fn item_is_test_only(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| snippet.contains("#[cfg(test)]") || snippet.contains("#[test]"))
        || item_has_leading_test_attr(cx, item)
}

fn impl_item_is_test_only(cx: &LateContext<'_>, item: &ImplItem<'_>) -> bool {
    cx
        .sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| snippet.contains("#[cfg(test)]") || snippet.contains("#[test]"))
        || impl_item_has_leading_cfg_test(cx, item)
}

fn is_inside_test_item(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    for (_, node) in cx.tcx.hir_parent_iter(expr.hir_id) {
        if let rustc_hir::Node::Item(item) = node
            && cx
                .sess()
                .source_map()
                .span_to_snippet(item.span)
                .is_ok_and(|snippet| snippet.contains("mod tests") || snippet.contains("#[test]"))
        {
            return true;
        }
    }
    false
}

fn is_inside_cfg_test_item_source(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    for (_, node) in cx.tcx.hir_parent_iter(expr.hir_id) {
        if let rustc_hir::Node::Item(item) = node
            && item_has_leading_cfg_test(cx, item)
        {
            return true;
        }
    }
    false
}

fn item_has_leading_test_attr(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    let source_map = cx.sess().source_map();
    let loc = source_map.lookup_char_pos(item.span.lo());
    let path = loc
        .file
        .name
        .prefer_local_unconditionally()
        .to_string_lossy()
        .into_owned();
    let Ok(source) = std::fs::read_to_string(path) else {
        return false;
    };
    let line = loc.line;
    let start = line.saturating_sub(4).max(1);
    source
        .lines()
        .skip(start - 1)
        .take(line - start + 1)
        .any(|line| line.contains("#[cfg(test)]") || line.contains("#[test]"))
}

fn item_has_leading_cfg_test(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    item_has_leading_test_attr(cx, item)
}

fn impl_item_has_leading_cfg_test(cx: &LateContext<'_>, item: &ImplItem<'_>) -> bool {
    let source_map = cx.sess().source_map();
    let loc = source_map.lookup_char_pos(item.span.lo());
    let path = loc
        .file
        .name
        .prefer_local_unconditionally()
        .to_string_lossy()
        .into_owned();
    let Ok(source) = std::fs::read_to_string(path) else {
        return false;
    };
    let line = loc.line;
    let start = line.saturating_sub(4).max(1);
    source
        .lines()
        .skip(start - 1)
        .take(line - start + 1)
        .any(|line| line.contains("#[cfg(test)]"))
}

fn expr_references_known_function_signatures(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Field(base, ident) => {
            ident.name.as_str() == "known_function_signatures"
                || expr_references_known_function_signatures(base)
        }
        ExprKind::MethodCall(_, receiver, args, _) => {
            expr_references_known_function_signatures(receiver)
                || args.iter().any(expr_references_known_function_signatures)
        }
        ExprKind::AddrOf(_, _, inner)
        | ExprKind::Unary(_, inner)
        | ExprKind::Cast(inner, _)
        | ExprKind::DropTemps(inner) => expr_references_known_function_signatures(inner),
        _ => false,
    }
}

fn expr_references_callee_facts(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Field(base, ident) => {
            ident.name.as_str() == "callee_facts" || expr_references_callee_facts(base)
        }
        ExprKind::MethodCall(_, receiver, args, _) => {
            expr_references_callee_facts(receiver) || args.iter().any(expr_references_callee_facts)
        }
        ExprKind::AddrOf(_, _, inner)
        | ExprKind::Unary(_, inner)
        | ExprKind::Cast(inner, _)
        | ExprKind::DropTemps(inner) => expr_references_callee_facts(inner),
        _ => false,
    }
}

fn raw_callee_import_policy_expr(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Call(callee, _) => {
            expr_path_last_segment_is(callee, "callee_name_is_import_like")
                || expr_path_last_segment_is(callee, "from_direct_target")
        }
        ExprKind::MethodCall(method, _, _, _) => matches!(
            method.ident.as_str(),
            "identity_for_callsite"
                | "identity_for_direct_addr"
                | "is_import_policy_authorized"
                | "target_policy_for_callsite_or_identity"
        ),
        _ => false,
    }
}

fn raw_call_target_address_parser_expr(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Call(callee, _) => expr_path_last_segment_is(callee, "extract_call_address"),
        ExprKind::MethodCall(method, _, _, _)
            if method.ident.as_str() == "prepared_constish_target_addr" =>
        {
            true
        }
        ExprKind::MethodCall(method, _, [arg], _) => {
            method.ident.as_str() == "strip_prefix" && call_target_address_prefix_literal(arg)
        }
        _ => false,
    }
}

fn call_target_address_prefix_literal(expr: &Expr<'_>) -> bool {
    let ExprKind::Lit(lit) = expr.kind else {
        return false;
    };
    let LitKind::Str(symbol, _) = lit.node else {
        return false;
    };
    matches!(symbol.as_str(), "ram:" | "const:")
}

fn call_target_policy_ownership_expr(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Call(callee, _) => {
            [
                "is_modeled_callee_identity",
                "modeled_callee_addr_for_identity",
            ]
            .iter()
            .any(|name| expr_path_last_segment_is(callee, name))
        }
        ExprKind::MethodCall(method, receiver, _, _)
            if method.ident.as_str() == "contains_key"
                && expr_references_callee_facts(receiver) =>
        {
            true
        }
        ExprKind::MethodCall(method, _, _, _) => matches!(
            method.ident.as_str(),
            "is_import_policy_authorized"
                | "identity_for_callsite"
                | "summary_helper_view_for_name"
                | "helper_view_for_name"
                | "is_modeled_callee_identity"
                | "modeled_callee_addr_for_identity"
                | "target_policy_for_callsite_or_identity"
        ),
        ExprKind::Struct(_, fields, _) => fields.iter().any(|field| {
            field.ident.name.as_str() == "direct_target_context" && expr_is_some_call(field.expr)
        }),
        _ => false,
    }
}

fn expr_is_some_call(expr: &Expr<'_>) -> bool {
    matches!(
        expr.kind,
        ExprKind::Call(callee, _) if expr_path_last_segment_is(callee, "Some")
    )
}

fn expr_is_none_path(expr: &Expr<'_>) -> bool {
    matches!(expr.kind, ExprKind::Path(ref qpath) if qpath_last_segment_is(qpath, "None"))
}

fn callee_resolution_fallback_ownership_expr(expr: &Expr<'_>) -> bool {
    matches!(
        expr.kind,
        ExprKind::Call(callee, _)
            if [
                "from_direct_call_targets",
                "identity_for_direct_target_in_context",
                "identity_for_name_in_context",
            ]
            .iter()
            .any(|name| expr_path_last_segment_is(callee, name))
    )
}

fn uncertified_call_arg_call_policy_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    if !enclosing_item_name(cx, expr)
        .as_deref()
        .is_some_and(is_call_arg_render_boundary_name)
    {
        return false;
    }

    match expr.kind {
        ExprKind::MethodCall(method, _, args, _) => match method.ident.as_str() {
            "is_imported_call_target" | "is_modeled_call_target" => true,
            "imported_or_modeled_call_target_for_optional_site" => {
                args.is_empty() || args.iter().any(expr_is_none_path)
            }
            _ => false,
        },
        ExprKind::Call(callee, _) => ["is_imported_call_target", "is_modeled_call_target"]
            .iter()
            .any(|name| expr_path_last_segment_is(callee, name)),
        _ => false,
    }
}

fn is_call_arg_render_boundary_name(name: &str) -> bool {
    matches!(
        name,
        "call_arg_requires_result_rebuild"
            | "choose_preferred_imported_call_arg_expr"
            | "render_imported_call_arg"
            | "render_authoritative_source_call_arg"
            | "normalize_imported_call_arg_expr"
            | "finalize_authoritative_imported_call_arg_expr"
            | "normalize_call_arg_expr_with_import_policy"
    )
}

fn call_arg_source_name_authority_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    if !enclosing_item_name(cx, expr)
        .as_deref()
        .is_some_and(is_call_arg_authority_boundary_name)
    {
        return false;
    }

    let ExprKind::MethodCall(method, receiver, _, _) = expr.kind else {
        return false;
    };
    if !matches!(method.ident.as_str(), "is_some" | "is_none" | "is_some_and") {
        return false;
    }
    if method.ident.as_str() == "is_some_and"
        && cx
            .sess()
            .source_map()
            .span_to_snippet(expr.span)
            .is_ok_and(|snippet| snippet.contains("source_var_name_has_prepared_call_arg_authority"))
    {
        return false;
    }
    expr_references_call_arg_source_var_name(receiver)
}

fn call_arg_source_call_authority_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    if !enclosing_item_name(cx, expr)
        .as_deref()
        .is_some_and(is_call_arg_authority_boundary_name)
    {
        return false;
    }

    let ExprKind::MethodCall(method, receiver, _, _) = expr.kind else {
        return false;
    };
    if !matches!(method.ident.as_str(), "is_some" | "is_none" | "is_some_and") {
        return false;
    }
    expr_references_call_arg_source_call(receiver)
}

fn is_call_arg_authority_boundary_name(name: &str) -> bool {
    matches!(
        name,
        "certified_call_args_for_site"
            | "certified_call_args_for_site_with_direct_target"
            | "call_arg_binding_has_render_authority"
    )
}

fn expr_references_call_arg_source_var_name(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Field(base, ident) => {
            ident.name.as_str() == "source_var_name"
                || expr_references_call_arg_source_var_name(base)
        }
        ExprKind::MethodCall(_, receiver, args, _) => {
            expr_references_call_arg_source_var_name(receiver)
                || args.iter().any(expr_references_call_arg_source_var_name)
        }
        ExprKind::Call(callee, args) => {
            expr_references_call_arg_source_var_name(callee)
                || args.iter().any(expr_references_call_arg_source_var_name)
        }
        ExprKind::Block(block, _) => block
            .expr
            .is_some_and(expr_references_call_arg_source_var_name),
        ExprKind::AddrOf(_, _, inner)
        | ExprKind::Unary(_, inner)
        | ExprKind::Cast(inner, _)
        | ExprKind::DropTemps(inner) => expr_references_call_arg_source_var_name(inner),
        _ => false,
    }
}

fn expr_references_call_arg_source_call(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Field(base, ident) => {
            ident.name.as_str() == "source_call" || expr_references_call_arg_source_call(base)
        }
        ExprKind::MethodCall(_, receiver, args, _) => {
            expr_references_call_arg_source_call(receiver)
                || args.iter().any(expr_references_call_arg_source_call)
        }
        ExprKind::Call(callee, args) => {
            expr_references_call_arg_source_call(callee)
                || args.iter().any(expr_references_call_arg_source_call)
        }
        ExprKind::Block(block, _) => block
            .expr
            .is_some_and(expr_references_call_arg_source_call),
        ExprKind::AddrOf(_, _, inner)
        | ExprKind::Unary(_, inner)
        | ExprKind::Cast(inner, _)
        | ExprKind::DropTemps(inner) => expr_references_call_arg_source_call(inner),
        _ => false,
    }
}

fn enclosing_item_name(cx: &LateContext<'_>, expr: &Expr<'_>) -> Option<String> {
    for (_, node) in cx.tcx.hir_parent_iter(expr.hir_id) {
        match node {
            rustc_hir::Node::ImplItem(item) => return Some(item.ident.name.as_str().to_string()),
            rustc_hir::Node::TraitItem(item) => return Some(item.ident.name.as_str().to_string()),
            _ => {}
        }
    }
    None
}

fn enclosing_item_name_and_snippet(
    cx: &LateContext<'_>,
    expr: &Expr<'_>,
) -> Option<(String, String)> {
    for (_, node) in cx.tcx.hir_parent_iter(expr.hir_id) {
        match node {
            rustc_hir::Node::Item(item) => {
                let snippet = cx.sess().source_map().span_to_snippet(item.span).ok()?;
                let name = function_name_from_snippet(&snippet)?;
                return Some((name, snippet));
            }
            rustc_hir::Node::ImplItem(item) => {
                let snippet = cx.sess().source_map().span_to_snippet(item.span).ok()?;
                return Some((item.ident.name.as_str().to_string(), snippet));
            }
            rustc_hir::Node::TraitItem(item) => {
                let snippet = cx.sess().source_map().span_to_snippet(item.span).ok()?;
                return Some((item.ident.name.as_str().to_string(), snippet));
            }
            _ => {}
        }
    }
    None
}

fn function_name_from_snippet(snippet: &str) -> Option<String> {
    let after_fn = snippet.split_once("fn ")?.1;
    let name = after_fn
        .split(|ch: char| !(ch == '_' || ch.is_ascii_alphanumeric()))
        .next()?;
    (!name.is_empty()).then(|| name.to_string())
}

fn enclosing_item_snippet_contains(cx: &LateContext<'_>, expr: &Expr<'_>, needle: &str) -> bool {
    for (_, node) in cx.tcx.hir_parent_iter(expr.hir_id) {
        match node {
            rustc_hir::Node::Item(item) => {
                return cx
                    .sess()
                    .source_map()
                    .span_to_snippet(item.span)
                    .is_ok_and(|snippet| snippet.contains(needle));
            }
            rustc_hir::Node::ImplItem(item) => {
                return cx
                    .sess()
                    .source_map()
                    .span_to_snippet(item.span)
                    .is_ok_and(|snippet| snippet.contains(needle));
            }
            _ => {}
        }
    }
    false
}

fn summary_route_executable_c_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    if matches!(expr.kind, ExprKind::Field(_, _))
        && enclosing_item_snippet_contains(cx, expr, "render_semantic_worker_linearization")
        && cx
            .sess()
            .source_map()
            .span_to_snippet(expr.span)
            .is_ok_and(|snippet| {
                snippet.contains("plan.signature.signature") || snippet.contains("decl.decl")
            })
    {
        return true;
    }

    if cx
        .sess()
        .source_map()
        .span_to_snippet(expr.span)
        .is_ok_and(|snippet| {
            snippet.lines().count() <= 2
                && ["switch (", "case 0x", "default:", "break;"]
                    .iter()
                    .any(|needle| snippet.contains(needle))
        })
    {
        return true;
    }

    match expr.kind {
        ExprKind::MethodCall(method, _, _, _)
            if method.ident.as_str() == "render_authorized_signature"
                && enclosing_item_snippet_contains(cx, expr, "CFunction") =>
        {
            true
        }
        ExprKind::Lit(lit) => {
            let LitKind::Str(symbol, _) = lit.node else {
                return false;
            };
            let text = symbol.as_str();
            let trimmed = text.trim();
            if trimmed.contains("switch (") {
                return true;
            }
            ["case ", "default:", "break;", "return "]
                .iter()
                .any(|prefix| trimmed.starts_with(prefix))
        }
        ExprKind::Call(callee, _) => {
            if cx
                .sess()
                .source_map()
                .span_to_snippet(expr.span)
                .is_ok_and(|snippet| snippet.contains("CStmt::"))
            {
                return false;
            }
            ["Return", "Expr", "merge_params_with_external_signature"]
                .iter()
                .any(|name| expr_path_last_segment_is(callee, name))
        }
        ExprKind::Field(_, ident) => {
            ident.name.as_str() == "register_params"
                && enclosing_item_snippet_contains(cx, expr, "CFunction")
        }
        _ => false,
    }
}

fn summary_render_executable_cstmt_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    if is_inside_test_item(cx, expr) {
        return false;
    }
    if enclosing_item_snippet_contains(cx, expr, "RenderPermissionKind::CertifiedC") {
        return false;
    }
    if !matches!(expr.kind, ExprKind::Call(_, _) | ExprKind::Struct(_, _, _)) {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(expr.span)
        .is_ok_and(|snippet| {
            let snippet = snippet.trim_start();
            [
                "CStmt::Return",
                "CStmt::Expr",
                "CStmt::If",
                "CStmt::While",
                "CStmt::DoWhile",
                "CStmt::For",
                "CStmt::Switch",
                "CStmt::if_stmt",
                "CStmt::while_loop",
            ]
            .iter()
            .any(|needle| snippet.starts_with(needle))
        })
}

fn summary_route_structured_worker_expr(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::MethodCall(method, _, _, _) => {
            method.ident.as_str() == "structure_semantic_worker_islands"
        }
        ExprKind::Call(callee, _) => {
            expr_path_last_segment_is(callee, "semantic_worker_structured_body")
                || expr_path_last_segment_is(callee, "structure_semantic_worker_islands")
        }
        _ => false,
    }
}

fn expr_path_last_segment_is(expr: &Expr<'_>, name: &str) -> bool {
    match expr.kind {
        ExprKind::Path(ref qpath) => qpath_last_segment_is(qpath, name),
        _ => false,
    }
}

fn qpath_last_segment_is(qpath: &QPath<'_>, name: &str) -> bool {
    match qpath {
        QPath::Resolved(_, path) => path
            .segments
            .last()
            .is_some_and(|segment| segment.ident.name.as_str() == name),
        QPath::TypeRelative(_, segment) => segment.ident.name.as_str() == name,
    }
}

fn is_r2dec_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("crates/r2dec/src/")
}

fn is_r2dec_span(cx: &LateContext<'_>, span: rustc_span::Span) -> bool {
    let filename = cx.sess().source_map().span_to_filename(span);
    format!("{filename:?}").contains("crates/r2dec/src/")
}

fn is_r2dec_analysis_span(cx: &LateContext<'_>, span: rustc_span::Span) -> bool {
    let filename = cx.sess().source_map().span_to_filename(span);
    format!("{filename:?}").contains("crates/r2dec/src/analysis/")
}

fn is_r2dec_op_lower_span(cx: &LateContext<'_>, span: rustc_span::Span) -> bool {
    let filename = cx.sess().source_map().span_to_filename(span);
    format!("{filename:?}").contains("crates/r2dec/src/fold/op_lower/")
}

fn is_r2dec_analysis_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("crates/r2dec/src/analysis/")
}

fn is_r2dec_op_lower_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("crates/r2dec/src/fold/op_lower/")
}

fn is_r2dec_lib_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("crates/r2dec/src/lib.rs")
}

fn is_r2dec_lib_span(cx: &LateContext<'_>, span: rustc_span::Span) -> bool {
    let filename = cx.sess().source_map().span_to_filename(span);
    format!("{filename:?}").contains("crates/r2dec/src/lib.rs")
}

fn is_r2dec_summary_render_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    let filename = format!("{filename:?}");
    filename.contains("crates/r2dec/src/consumer_summary.rs")
        || filename.contains("crates/r2dec/src/consumer_linear.rs")
        || filename.contains("crates/r2dec/src/consumer_vm.rs")
}

fn is_r2dec_summary_or_structured_consumer_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    let filename = format!("{filename:?}");
    filename.contains("crates/r2dec/src/consumer_summary.rs")
        || filename.contains("crates/r2dec/src/consumer_linear.rs")
        || filename.contains("crates/r2dec/src/consumer_vm.rs")
        || filename.contains("crates/r2dec/src/consumer_structured.rs")
        || filename.contains("crates/r2dec/src/summary_render_executable_cstmt.rs")
}

fn is_r2dec_route_render_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    let filename = format!("{filename:?}");
    filename.contains("crates/r2dec/src/consumer_structured.rs")
        || filename.contains("crates/r2dec/src/lib.rs")
}

fn is_r2plugin_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("r2plugin/src/")
}

fn is_r2plugin_lib_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("r2plugin/src/lib.rs")
}

fn is_r2plugin_span(cx: &LateContext<'_>, span: rustc_span::Span) -> bool {
    let filename = cx.sess().source_map().span_to_filename(span);
    format!("{filename:?}").contains("r2plugin/src/")
}

fn is_r2plugin_type_hint_policy_span(cx: &LateContext<'_>, span: rustc_span::Span) -> bool {
    let filename = cx.sess().source_map().span_to_filename(span);
    let filename = format!("{filename:?}");
    filename.contains("r2plugin/src/types.rs")
        || filename.contains("r2plugin/src/metadata_type_hint_ownership.rs")
}

fn is_r2engine_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("crates/r2engine/src/")
}

fn is_r2engine_lib_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("crates/r2engine/src/lib.rs")
}

fn is_r2engine_span(cx: &LateContext<'_>, span: rustc_span::Span) -> bool {
    let filename = cx.sess().source_map().span_to_filename(span);
    format!("{filename:?}").contains("crates/r2engine/src/")
}

fn is_r2engine_lib_span(cx: &LateContext<'_>, span: rustc_span::Span) -> bool {
    let filename = cx.sess().source_map().span_to_filename(span);
    format!("{filename:?}").contains("crates/r2engine/src/lib.rs")
}

fn is_r2types_span(cx: &LateContext<'_>, span: rustc_span::Span) -> bool {
    let filename = cx.sess().source_map().span_to_filename(span);
    format!("{filename:?}").contains("crates/r2types/src/")
}

fn is_r2types_non_role_registry_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    let filename = format!("{filename:?}");
    filename.contains("crates/r2types/src/") && !filename.contains("crates/r2types/src/role_registry.rs")
}

fn is_canonical_ssa_var_classifier(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("crates/r2ssa/src/var.rs")
}

#[test]
fn ui() {
    dylint_testing::ui_test(env!("CARGO_PKG_NAME"), "ui");
}

#[test]
fn r2plugin_post_analysis_does_not_own_type_writeback_fixpoint() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("r2plugin/r_anal_sleigh.c");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    assert!(
        !source.contains("r2sleigh_type_writeback_fixpoint_"),
        "r2plugin must not call type-writeback fixpoint ABI; orchestration belongs in r2engine"
    );
    assert!(
        !source.contains("collect_fixpoint_neighbor_candidates"),
        "r2plugin must not own type-writeback fixpoint neighbor collection"
    );
    assert!(
        !source.contains("\"type fixpoint"),
        "r2plugin must not own type-writeback fixpoint budget stages"
    );
    for forbidden in [
        concat!("r2sleigh_type_writeback_", "cache_"),
        concat!("apply_type_writeback_", "session_result"),
        concat!("compute_callee_", "dependency_hash"),
        concat!("propagate_signature_", "to_direct_callers"),
        concat!("apply_inferred_", "signature_fact"),
        concat!("apply_inferred_", "callconv"),
        concat!("r2sleigh_session_result_", "mutations"),
        concat!("r2sleigh_session_result_type_", "writeback_json"),
        concat!("r2sleigh_bounded_", "type_json_ffi"),
    ] {
        assert!(
            !source.contains(forbidden),
            "r2plugin must not own type-writeback policy surface {forbidden:?}"
        );
    }
}

#[test]
fn r2engine_render_semantic_route_has_no_route_side_channel() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2engine/src/lib.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let marker = "pub fn render_semantic_route";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("\npub fn target_query_route_decision")
        .unwrap_or_else(|| panic!("missing semantic route end marker in {}", path.display()));
    let body = &rest[..end];

    assert!(
        !body.contains("route: &EngineSemanticRoutePlan"),
        "render_semantic_route must derive route/refusal from FunctionFacts::decompile_route, not a sibling EngineSemanticRoutePlan argument"
    );
    assert!(
        body.contains("decompile_route_output_from_function_facts"),
        "render_semantic_route must delegate route/refusal output to the FunctionFacts route-output helper"
    );
    for forbidden in [
        "summary-only decompile route lacks certified native FunctionFacts render proof",
        "artifact_guard_fallback_comment(",
    ] {
        assert!(
            !body.contains(forbidden),
            "render_semantic_route must not synthesize route/refusal output outside FunctionFacts: {forbidden:?}"
        );
    }

    let marker = "fn decompile_route_output_from_function_facts";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("\npub fn function_analysis_cache_key")
        .unwrap_or_else(|| panic!("missing decompile_route_output_from_function_facts end marker"));
    let route_output_body = &rest[..end];
    assert!(
        route_output_body.contains(".decompile_route()"),
        "route-output helper must read the canonical FunctionFacts decompile route"
    );
    for forbidden in [
        "summary-only decompile route lacks certified native FunctionFacts render proof",
        "artifact_guard_fallback_comment(",
        "(empty output)",
    ] {
        assert!(
            !route_output_body.contains(forbidden),
            "route-output helper must not synthesize fallback output outside FunctionFacts: {forbidden:?}"
        );
    }

    let marker = "fn render_engine_decompile_request";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("\nfn refused_decompile_response")
        .unwrap_or_else(|| panic!("missing render_engine_decompile_request end marker"));
    let request_body = &rest[..end];
    assert!(
        request_body.contains("decompile_route_output_from_function_facts"),
        "empty or fallback decompile output must be derived from FunctionFacts route facts"
    );
    for forbidden in [
        "decompile_empty_output_fallback_comment",
        "(empty output)",
        "skipped decompilation for {function_name}",
    ] {
        assert!(
            !request_body.contains(forbidden),
            "render_engine_decompile_request must not synthesize fallback output outside FunctionFacts: {forbidden:?}"
        );
    }
}

#[test]
fn r2engine_engine_semantic_route_plan_stays_deleted() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    for rel in ["crates/r2engine/src/route.rs", "crates/r2engine/src/lib.rs"] {
        let path = root.join(rel);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
        for forbidden in [
            "pub enum EngineSemanticRoutePlan",
            "EngineSemanticRoutePlan::",
            "fn decompile_route_kind(",
            "fn decompile_route_facts_from_decision(",
            "EngineSemanticRoutePlanJson",
        ] {
            assert!(
                !source.contains(forbidden),
                "r2engine production route spine must use DecompileRouteFacts directly; found {forbidden:?} in {rel}"
            );
        }
    }
}

#[test]
fn r2engine_decompile_response_exposes_function_facts_not_route_decision() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2engine/src/lib.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let marker = "pub struct EngineDecompileResponse";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("\npub struct EngineSession")
        .unwrap_or_else(|| panic!("missing EngineDecompileResponse end marker"));
    let body = &rest[..end];

    assert!(
        body.contains("pub function_facts: FunctionFacts"),
        "EngineDecompileResponse must return the stamped FunctionFacts spine"
    );
    assert!(
        !body.contains("pub decision: EngineRouteDecision"),
        "EngineDecompileResponse must not expose a durable parallel route decision; derive route/refusal from FunctionFacts::decompile_route"
    );
}

#[test]
fn r2engine_decompile_does_not_replan_after_functionfacts_stamping() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2engine/src/lib.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let start = source
        .find("fn decompile(&self, request: EngineDecompileRequest)")
        .unwrap_or_else(|| panic!("missing EngineSession::decompile"));
    let end = source[start..]
        .find("\n    pub fn symbolic_summary")
        .map(|offset| start + offset)
        .unwrap_or_else(|| panic!("missing method after EngineSession::decompile"));
    let body = &source[start..end];

    assert!(
        body.contains("decompile_diagnostics_from_function_facts(&request.function_facts)"),
        "EngineSession::decompile must derive diagnostics from stamped FunctionFacts"
    );
    for forbidden in [
        "plan_decompile_request(",
        "decompile_route_facts_from_decision(",
        "set_decompile_route(",
        "EngineTypedRouteDecision::Decompile",
    ] {
        assert!(
            !body.contains(forbidden),
            "EngineSession::decompile must not replan or restamp decompile route after FunctionFacts cache-key stamping: {forbidden:?}"
        );
    }

    let facts_start = source
        .find("pub fn function_facts_for_decompile(")
        .unwrap_or_else(|| panic!("missing function_facts_for_decompile"));
    let facts_end = source[facts_start..]
        .find("\n#[cfg(test)]")
        .map(|offset| facts_start + offset)
        .unwrap_or_else(|| panic!("missing function_facts_for_decompile end marker"));
    let facts_body = &source[facts_start..facts_end];
    assert!(
        facts_body.contains("if function_facts.decompile_route().is_none()"),
        "function_facts_for_decompile must preserve an already stamped FunctionFacts route"
    );
    assert!(
        !facts_body.contains("function_facts.set_decompile_route(Some(route_decision.route.clone()));\n    function_facts"),
        "function_facts_for_decompile must not unconditionally overwrite a stamped route"
    );
}

#[test]
fn r2plugin_function_decompile_export_is_engine_only() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("r2plugin/src/lib.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let c_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("r2plugin/r_anal_sleigh.c");
    let c_source = std::fs::read_to_string(&c_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", c_path.display()));
    let extract = |start_marker: &str, end_marker: &str| {
        let start = source
            .find(start_marker)
            .unwrap_or_else(|| panic!("missing {start_marker} in {}", path.display()));
        let rest = &source[start..];
        let end = rest
            .find(end_marker)
            .unwrap_or_else(|| panic!("missing {end_marker} after {start_marker}"));
        &rest[..end]
    };
    let engine_impl = extract(
        "fn r2sleigh_engine_decompile_function_output",
        "\n// ============================================================================\n// radare2 Deep Integration FFI - Variable Recovery and Data Refs",
    );

    assert!(
        engine_impl.contains("run_engine_decompile_on_large_stack")
            && engine_impl.contains("EngineFunctionDecompileRequestInput::single_function"),
        "engine decompile wrapper must build an engine-owned decompile request and run it through EngineSession"
    );
    assert!(
        c_source.contains("r2sleigh_engine_decompile_function"),
        "C plugin glue must call the typed engine decompile boundary"
    );

    for forbidden in [
        "r2dec_function_with_context",
        "r2dec_function_with_context_scope",
        "r2dec_function_with_context_impl",
        "r2dec_function_with_session_context",
        "R2DecFunctionWithContextInputs",
        "r2dec_named_native_worker_summary",
        "r2dec_semantic_worker_linearization_scope_ffi",
        "r2dec_block_guard_comment_ffi",
        "r2dec_block(",
        "r2dec_block_ast_json",
    ] {
        assert!(
            !source.contains(forbidden),
            "r2plugin Rust must not expose legacy direct decompile ABI {forbidden:?}"
        );
        assert!(
            !c_source.contains(forbidden),
            "C plugin glue must not declare or call legacy direct decompile ABI {forbidden:?}"
        );
    }

    for forbidden in [
        "r2dec::Decompiler::new",
        "r2dec::DecompilerInput::new",
        "r2dec::render_semantic_worker_summary",
        "r2dec::render_vm_semantic_summary",
        "r2types::FunctionFacts::new",
        "FunctionFacts::new",
        "with_decompile_route",
        "decompile_route_decision",
    ] {
        assert!(
            !engine_impl.contains(forbidden),
            "engine decompile wrapper must not contain plugin-side decompile/render policy fragment {forbidden:?}"
        );
    }
}

#[test]
fn r2plugin_renderer_dependency_stays_deleted() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let manifest_path = root.join("r2plugin/Cargo.toml");
    let manifest = std::fs::read_to_string(&manifest_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", manifest_path.display()));
    let dependencies = manifest
        .split("\n[dev-dependencies]")
        .next()
        .unwrap_or(manifest.as_str());
    assert!(
        !manifest.contains("r2dec = { path = \"../crates/r2dec\" }"),
        "r2plugin must not depend on renderer/decompiler directly, even in dev-dependencies"
    );
    for forbidden in [
        "features = [\"dec\"]",
    ] {
        assert!(
            !dependencies.contains(forbidden),
            "r2plugin production manifest must not link renderer/decompiler edge {forbidden:?}"
        );
    }

    let rust_path = root.join("r2plugin/src/lib.rs");
    let rust_source = std::fs::read_to_string(&rust_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", rust_path.display()));
    assert!(
        !rust_source.contains("r2dec::"),
        "r2plugin Rust source must not directly call renderer/decompiler APIs"
    );
    assert!(
        !rust_source.contains("pub extern \"C\" fn r2dec_highlight_c_ansi"),
        "r2plugin must not expose renderer-owned C highlight FFI"
    );

    let c_path = root.join("r2plugin/r_anal_sleigh.c");
    let c_source = std::fs::read_to_string(&c_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", c_path.display()));
    for forbidden in ["r2dec_highlight_c_ansi", "sleigh_console_color_enabled"] {
        assert!(
            !c_source.contains(forbidden),
            "C plugin glue must not call renderer-owned highlighting helper {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_render_context_uses_function_render_facts_for_exprs_and_returns() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let start = source
        .find("pub(crate) struct CertifiedRenderContext")
        .unwrap_or_else(|| panic!("missing CertifiedRenderContext in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("\nimpl LowerFrame")
        .unwrap_or_else(|| panic!("missing CertifiedRenderContext end marker in {}", path.display()));
    let body = &rest[..end];

    assert!(
        body.contains("render_facts: &'a FunctionRenderFacts"),
        "CertifiedRenderContext must carry canonical FunctionFacts render evidence"
    );
    assert!(
        body.contains("self.render_facts.expression_is_renderable(value)"),
        "certified expression renderability must be read from FunctionRenderFacts"
    );
    assert!(
        body.contains("self.render_facts.return_for_op(block_addr, op_idx)"),
        "certified return renderability must be read from FunctionRenderFacts"
    );
    assert!(
        !body.contains(".certificates()\n            .expressions")
            && !body.contains("return_certificate_for_op"),
        "CertifiedRenderContext must not use prepared SSA expression/return certificates as render authority"
    );
}

#[test]
fn r2dec_certified_return_expr_uses_functionfacts_not_prepared_or_visible_fallbacks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let start_marker = "fn certified_return_expr_for_value";
    let start = source
        .find(start_marker)
        .unwrap_or_else(|| panic!("missing {start_marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("fn certified_return_expr_contains_raw_storage_name")
        .unwrap_or_else(|| panic!("missing certified return helper end marker"));
    let body = &rest[..end];

    for required in [
        "self.certified_call_result_fact_for_value(value)",
        "self.render_certified_memory_expr_for_fact(",
        "self.certified_const_expr(var)",
        "proof.expression_is_renderable(value)",
    ] {
        assert!(
            body.contains(required),
            "certified return rendering must use FunctionFacts-backed helper {required:?}"
        );
    }

    for forbidden in [
        "prepared_semantic_view",
        "owner_expr_for_value_id",
        "owner_expr_for_var",
        "prepared_canonical_value_root",
        "stack_reload_certificate_for_value",
        "render_memory_access_from_visible_expr",
        "memory_certificate_for_op_site",
        "const_to_expr",
        "lookup_definition",
        "best_visible_definition",
        "get_expr(",
    ] {
        assert!(
            !body.contains(forbidden),
            "certified return rendering must not use prepared/local/visible fallback {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_runtime_type_inference_does_not_seed_raw_function_names() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/lib.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let start_marker = "fn build_function_internal";
    let start = source
        .find(start_marker)
        .unwrap_or_else(|| panic!("missing {start_marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("fn infer_return_type")
        .unwrap_or_else(|| panic!("missing build_function_internal end marker"));
    let body = &rest[..end];

    assert!(
        body.contains("type_inference.set_external_signature")
            && body.contains("type_inference.add_function_type"),
        "runtime type inference should still consume typed signature/function facts"
    );
    for forbidden in [
        "type_inference.set_function_names",
        "self.context.function_names.clone()",
    ] {
        assert!(
            !body.contains(forbidden),
            "r2dec runtime type inference must not seed raw function-name side channel {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_internal_decompile_requires_prepared_artifact() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/lib.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let start_marker = "fn build_function_internal";
    let start = source
        .find(start_marker)
        .unwrap_or_else(|| panic!("missing {start_marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("fn infer_return_type")
        .unwrap_or_else(|| panic!("missing build_function_internal end marker"));
    let body = &rest[..end];

    assert!(
        body.contains("prepared: &r2ssa::SsaArtifact"),
        "build_function_internal must require prepared SsaArtifact evidence by type"
    );
    for forbidden in [
        "prepared: Option<&r2ssa::SsaArtifact>",
        "prepared.is_some()",
        "prepared.expect(",
        "set_decompile_prep_facts(func.decompile_prep_facts())",
        "prepared_ssa: None",
        "prepared_objects: None",
        "prepared_memory: None",
    ] {
        assert!(
            !body.contains(forbidden),
            "internal executable decompile must not preserve unprepared fallback {forbidden:?}"
        );
    }
    assert!(
        body.contains("type_inference.set_prepared_ssa(prepared)")
            && body.contains("prepared_ssa: Some(prepared)")
            && body.contains("prepared_objects: Some(prepared.objects())")
            && body.contains("prepared_memory: Some(prepared.memory())"),
        "internal executable decompile must pass prepared evidence through type inference and FoldInputs"
    );
}

#[test]
fn r2dec_raw_address_rendering_does_not_use_function_string_symbol_maps() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let op_lower_path = root.join("crates/r2dec/src/fold/op_lower/mod.rs");
    let calls_path = root.join("crates/r2dec/src/fold/op_lower/calls.rs");
    let memory_renderer_path = root.join("crates/r2dec/src/fold/op_lower/memory_renderer.rs");
    let return_resolver_path = root.join("crates/r2dec/src/fold/op_lower/return_resolver.rs");
    let lower_path = root.join("crates/r2dec/src/analysis/lower.rs");
    let op_lower = std::fs::read_to_string(&op_lower_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", op_lower_path.display()));
    let calls = std::fs::read_to_string(&calls_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", calls_path.display()));
    let memory_renderer = std::fs::read_to_string(&memory_renderer_path).unwrap_or_else(|err| {
        panic!(
            "failed to read {}: {err}",
            memory_renderer_path.display()
        )
    });
    let return_resolver = std::fs::read_to_string(&return_resolver_path).unwrap_or_else(|err| {
        panic!("failed to read {}: {err}", return_resolver_path.display())
    });
    let lower = std::fs::read_to_string(&lower_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", lower_path.display()));

    fn extract_source<'a>(source: &'a str, start_marker: &str, end_marker: &str) -> &'a str {
        let start = source
            .find(start_marker)
            .unwrap_or_else(|| panic!("missing {start_marker}"));
        let rest = &source[start..];
        let end = rest
            .find(end_marker)
            .unwrap_or_else(|| panic!("missing {end_marker} after {start_marker}"));
        &rest[..end]
    }
    let get_expr = extract_source(&op_lower, "pub fn get_expr", "\n    fn op_to_expr_impl");
    let literalish = extract_source(
        &op_lower,
        "fn literalish_call_arg_expr_for_addr",
        "fn evaluate_hex_digit_offset_call_arg_expr",
    );
    let const_to_expr = extract_source(&return_resolver, "pub(crate) fn const_to_expr", "\n}");
    let resolve_addr_literal = extract_source(&lower, "fn resolve_addr_literal", "\n    fn binary_expr");

    for (name, body) in [
        ("get_expr", get_expr),
        ("literalish_call_arg_expr_for_addr", literalish),
        ("const_to_expr", const_to_expr),
        ("resolve_addr_literal", resolve_addr_literal),
    ] {
        for forbidden in [
            "lookup_function",
            "lookup_string",
            "lookup_symbol",
            ".function_names",
            ".strings",
            ".symbols",
            "StringLit",
            "parse_address_from_var_name",
        ] {
            assert!(
                !body.contains(forbidden),
                "{name} must not use raw function/string/symbol map rendering via {forbidden:?}"
            );
        }
    }

    for (name, body) in [
        ("op_lower", op_lower.as_str()),
        ("calls", calls.as_str()),
        ("memory_renderer", memory_renderer.as_str()),
    ] {
        for forbidden in [
            "fn lookup_function",
            "fn lookup_string",
            "fn lookup_symbol",
            ".lookup_function(",
            ".lookup_string(",
            ".lookup_symbol(",
        ] {
            assert!(
                !body.contains(forbidden),
                "{name} must not carry raw address-to-function/string/symbol lookup path {forbidden:?}"
            );
        }
    }
}

#[test]
fn r2dec_certified_render_gate_uses_engine_permission_not_prepared_presence() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let op_lower_path = root.join("crates/r2dec/src/fold/op_lower/mod.rs");
    let context_path = root.join("crates/r2dec/src/fold/context.rs");
    let prepared_path = root.join("crates/r2dec/src/analysis/prepared_semantic.rs");
    let op_lower = std::fs::read_to_string(&op_lower_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", op_lower_path.display()));
    let context = std::fs::read_to_string(&context_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", context_path.display()));
    let prepared = std::fs::read_to_string(&prepared_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", prepared_path.display()));

    let marker = "pub(crate) fn requires_certified_rendering";
    let start = op_lower
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", op_lower_path.display()));
    let body = &op_lower[start..op_lower[start..]
        .find("\n    pub(super) fn is_certified_materialized_phi_carrier")
        .map(|offset| start + offset)
        .unwrap_or_else(|| panic!("missing certified render gate end marker"))];

    let field = "pub(crate) certified_rendering_required: bool";
    if let Some(field_at) = context.find(field) {
        let prefix = &context[..field_at];
        assert!(
            prefix.ends_with("#[cfg(test)]\n    #[allow(dead_code)]\n    "),
            "standalone certified_rendering_required must be test-only fixture scaffolding"
        );
    }
    for required in [
        "self.inputs.function_facts.decompile_route()",
        "route.kind == r2types::DecompileRouteKind::Standard",
        "route.render_permission.kind == r2sym::RenderPermissionKind::CertifiedC",
        "route.render_permission.owner == r2sym::ProofOwner::R2engine",
    ] {
        assert!(
            body.contains(required),
            "requires_certified_rendering must derive from engine-owned FunctionFacts route proof {required:?}"
        );
    }
    assert!(
        !body.contains("self.inputs.certified_rendering_required"),
        "requires_certified_rendering must not read standalone certified render side-channel"
    );
    assert!(
        !body.contains("prepared_ssa.is_some()"),
        "prepared SSA presence is evidence input, not executable-C render permission"
    );

    let input_marker = "pub(crate) struct PreparedSemanticViewInputs";
    let input_start = prepared
        .find(input_marker)
        .unwrap_or_else(|| panic!("missing {input_marker} in {}", prepared_path.display()));
    let input_rest = &prepared[input_start..];
    let input_end = input_rest
        .find("\nimpl PreparedSemanticView")
        .unwrap_or_else(|| panic!("missing PreparedSemanticView impl after inputs"));
    let input_block = &input_rest[..input_end];
    if let Some(field_at) = input_block.find(field) {
        let prefix = &input_block[..field_at];
        let nearby = &prefix[prefix.len().saturating_sub(80)..];
        assert!(
            nearby.contains("#[cfg(test)]"),
            "PreparedSemanticViewInputs standalone certified_rendering_required must be test-only fixture scaffolding"
        );
    }
    for required in [
        "prepared_view_requires_certified_rendering(inputs.function_facts)",
        "function_facts.decompile_route()",
        "route.kind == r2types::DecompileRouteKind::Standard",
        "route.render_permission.kind == r2sym::RenderPermissionKind::CertifiedC",
        "route.render_permission.owner == r2sym::ProofOwner::R2engine",
    ] {
        assert!(
            prepared.contains(required),
            "PreparedSemanticView must derive certified mode from FunctionFacts route proof {required:?}"
        );
    }
}

#[test]
fn r2dec_certified_source_call_args_do_not_replay_prepared_or_local_args() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/calls.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let marker = "pub(super) fn render_authoritative_source_args_for_call";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let helper_end = rest
        .find("\n    fn ")
        .unwrap_or_else(|| panic!("missing helper end after {marker}"));
    let helper = &rest[..helper_end];

    assert!(
        helper.contains("self.certified_callsite_for_op"),
        "certified source-call replay must start from FunctionFacts callsite evidence"
    );
    assert!(
        helper.contains("self.certified_render_context()"),
        "certified source-call replay must require the certified render context"
    );
    assert!(
        helper.contains("self.certified_call_arg_expr_for_value"),
        "certified source-call replay must render only FunctionFacts argument values"
    );
    for forbidden in [
        "self.inputs.prepared_ssa",
        "prepared_call_args_for_site",
        "prepared_call_view",
        "call_args_map()",
        "render_authoritative_source_call_arg",
    ] {
        assert!(
            !helper.contains(forbidden),
            "certified source-call replay must not use local/prepared argument source {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_c_residualizes_non_engine_owner_and_requires_effect_proofs() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/lib.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    let permission_marker = "fn render_permission_residual_reason";
    let permission_start = source
        .find(permission_marker)
        .unwrap_or_else(|| panic!("missing {permission_marker} in {}", path.display()));
    let permission_rest = &source[permission_start..];
    let permission_end = permission_rest
        .find("\nfn render_permission_allows_executable_c")
        .unwrap_or_else(|| panic!("missing render permission helper end marker"));
    let permission_body = &permission_rest[..permission_end];

    for required in [
        "r2sym::RenderPermissionKind::CertifiedC",
        "permission.owner != r2sym::ProofOwner::R2engine",
        "CertifiedC render permission from non-engine proof owner",
    ] {
        assert!(
            permission_body.contains(required),
            "CertifiedC render permission must fail closed unless r2engine owns the proof: {required:?}"
        );
    }
    assert!(
        !permission_body.contains("r2sym::RenderPermissionKind::CertifiedC => None"),
        "CertifiedC must not bypass residualization without checking proof owner"
    );

    let contract_marker = "fn certified_standard_output_residual_reason_with_effect_proofs";
    let contract_start = source
        .find(contract_marker)
        .unwrap_or_else(|| panic!("missing {contract_marker} in {}", path.display()));
    let contract_rest = &source[contract_start..];
    let contract_end = contract_rest
        .find("\nfn field_accesses_are_certified")
        .unwrap_or_else(|| panic!("missing certified Standard verifier end marker"));
    let contract_body = &contract_rest[..contract_end];

    assert!(
        contract_body.contains("missing exact FunctionFacts render proof"),
        "certified Standard output must residualize executable effects when exact render proofs are absent"
    );
    for forbidden in [
        "counts.calls > callsite_facts.by_callsite.len()",
        "counts.returns_with_value > render_facts.returns_by_op.len()",
        "counts.memory_like_accesses > render_facts.memory_accesses.len()",
    ] {
        assert!(
            !contract_body.contains(forbidden),
            "certified Standard verification must not fall back to count-only proof acceptance: {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_production_foldinputs_authority_reads_use_functionfacts_accessors() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let context_path = root.join("crates/r2dec/src/fold/context.rs");
    let context = std::fs::read_to_string(&context_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", context_path.display()));
    let accessor_block_start = context
        .find("impl<'a> FoldInputs<'a>")
        .unwrap_or_else(|| panic!("missing FoldInputs accessors in {}", context_path.display()));
    let accessor_block = &context[accessor_block_start..context[accessor_block_start..]
        .find("\n#[derive(Debug, Clone, Default)]")
        .map(|offset| accessor_block_start + offset)
        .unwrap_or_else(|| panic!("missing FoldInputs accessor block end marker"))];
    let struct_start = context
        .find("pub(crate) struct FoldInputs<'a>")
        .unwrap_or_else(|| panic!("missing FoldInputs struct in {}", context_path.display()));
    let struct_rest = &context[struct_start..];
    let struct_end = struct_rest
        .find("\n}\n\nimpl<'a> FoldInputs<'a>")
        .unwrap_or_else(|| panic!("missing FoldInputs struct end marker"));
    let struct_body = &struct_rest[..struct_end];
    assert!(
        struct_body.contains("pub(crate) function_facts: &'a FunctionFacts"),
        "FoldInputs must carry a non-optional FunctionFacts spine"
    );
    assert!(
        !struct_body.contains("pub(crate) function_facts: Option<&'a FunctionFacts>"),
        "FoldInputs must not make the FunctionFacts spine optional"
    );
    for forbidden in [
        "pub(crate) callee_facts:",
        "pub(crate) callee_resolution:",
        "pub(crate) callsite_facts:",
        "pub(crate) call_result_facts:",
        "pub(crate) call_render_facts:",
        "pub(crate) control_facts:",
        "pub(crate) render_facts:",
        "pub(crate) semantic_artifact:",
        "pub(crate) summary_view:",
    ] {
        assert!(
            !struct_body.contains(forbidden),
            "FoldInputs must not carry duplicate decompile authority side fields: {forbidden:?}"
        );
    }

    for required in [
        "fn callee_facts(&self)",
        "fn callee_resolution(&self)",
        "fn callsite_facts(&self)",
        "fn call_result_facts(&self)",
        "fn call_render_facts(&self)",
        "fn control_facts(&self)",
        "fn render_facts(&self)",
        "fn summary_view(&self)",
        ".callee_resolution()",
        ".callsites()",
        ".call_results()",
        ".call_render()",
        ".control()",
        ".render()",
        ".summary_view()",
        "self.function_facts.type_facts().callee_facts",
    ] {
        assert!(
            accessor_block.contains(required),
            "FoldInputs authority access must derive from FunctionFacts before fixture fallback: {required:?}"
        );
    }

    for relative in [
        "crates/r2dec/src/fold/op_lower/mod.rs",
        "crates/r2dec/src/fold/op_lower/calls.rs",
        "crates/r2dec/src/fold/op_lower/lowering.rs",
        "crates/r2dec/src/fold/op_lower/memory_renderer.rs",
        "crates/r2dec/src/fold/flags.rs",
        "crates/r2dec/src/analysis/prepared_semantic.rs",
    ] {
        let path = root.join(relative);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
        for forbidden in [
            "self.inputs.callee_facts,",
            "self.inputs.callee_resolution,",
            "self.inputs.callsite_facts,",
            "self.inputs.call_result_facts,",
            "self.inputs.call_render_facts,",
            "self.inputs.control_facts,",
            "self.inputs.render_facts,",
            "self.inputs.semantic_artifact?",
            "self.inputs.summary_view,",
            "inputs.callee_resolution,",
            "inputs.callsite_facts,",
            "inputs.call_result_facts,",
            "inputs.call_render_facts,",
            "inputs.control_facts,",
            "inputs.render_facts,",
            "inputs.semantic_artifact?",
            "inputs.summary_view,",
        ] {
            assert!(
                !source.contains(forbidden),
                "{relative} must read decompile authority through FunctionFacts-derived accessors, not {forbidden:?}"
            );
        }
    }
}

#[test]
fn r2dec_prepared_semantic_view_inputs_use_functionfacts_only() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let path = root.join("crates/r2dec/src/analysis/prepared_semantic.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let struct_start = source
        .find("pub(crate) struct PreparedSemanticViewInputs<'a>")
        .unwrap_or_else(|| panic!("missing PreparedSemanticViewInputs in {}", path.display()));
    let struct_rest = &source[struct_start..];
    let struct_end = struct_rest
        .find("\n}\n\nimpl<'a> PreparedSemanticViewInputs<'a>")
        .unwrap_or_else(|| panic!("missing PreparedSemanticViewInputs end marker"));
    let struct_body = &struct_rest[..struct_end];
    let impl_start = source
        .find("impl<'a> PreparedSemanticViewInputs<'a>")
        .unwrap_or_else(|| panic!("missing PreparedSemanticViewInputs impl"));
    let impl_rest = &source[impl_start..];
    let impl_end = impl_rest
        .find("\n}\n\nimpl PreparedSemanticView")
        .unwrap_or_else(|| panic!("missing PreparedSemanticViewInputs impl end marker"));
    let impl_body = &impl_rest[..impl_end];

    assert!(
        struct_body.contains("pub(crate) function_facts: &'a FunctionFacts"),
        "PreparedSemanticViewInputs must require a non-optional FunctionFacts spine"
    );
    assert!(
        !struct_body.contains("function_facts: Option<&'a FunctionFacts>"),
        "PreparedSemanticViewInputs must not make FunctionFacts optional"
    );
    for forbidden in [
        "pub(crate) callee_resolution:",
        "pub(crate) callsite_facts:",
        "pub(crate) call_result_facts:",
        "pub(crate) call_render_facts:",
        "pub(crate) control_facts:",
    ] {
        assert!(
            !struct_body.contains(forbidden),
            "PreparedSemanticViewInputs must not carry duplicate prepared-view authority side fields: {forbidden:?}"
        );
    }
    for required in [
        "self.function_facts.callee_resolution()",
        "self.function_facts.callsites()",
        "self.function_facts.call_results()",
        "self.function_facts.call_render()",
        "self.function_facts.control()",
    ] {
        assert!(
            impl_body.contains(required),
            "PreparedSemanticViewInputs accessor must read canonical FunctionFacts: {required:?}"
        );
    }
    for forbidden in [".or(self.", ".and_then(FunctionFacts::"] {
        assert!(
            !impl_body.contains(forbidden),
            "PreparedSemanticViewInputs accessors must not fall back to side-channel facts: {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_statement_calls_use_function_call_render_facts() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/lowering.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let helper_marker = "fn lower_certified_statement_call";
    let helper_start = source
        .find(helper_marker)
        .unwrap_or_else(|| panic!("missing {helper_marker} in {}", path.display()));
    let helper_rest = &source[helper_start..];
    let helper_end = helper_rest
        .find("pub(super) fn lower_op")
        .unwrap_or_else(|| panic!("missing lower_op after {helper_marker}"));
    let helper = &helper_rest[..helper_end];

    assert!(
        helper.contains("self.certified_call_render_fact_for_op"),
        "certified statement calls must read FunctionFacts call-render disposition"
    );
    assert!(
        helper.contains("match render_fact.disposition"),
        "certified statement calls must branch on canonical CallsiteRenderFact disposition"
    );
    assert!(
        helper.contains("CallsiteRenderDisposition::AssignedResult")
            && helper.contains("CallsiteRenderDisposition::SideEffectStatement"),
        "certified statement-call rendering must explicitly handle canonical statement dispositions"
    );

    let lower_marker = "pub(super) fn lower_op";
    let lower_start = source
        .find(lower_marker)
        .unwrap_or_else(|| panic!("missing {lower_marker} in {}", path.display()));
    let lower_rest = &source[lower_start..];
    let lower_end = lower_rest
        .find("pub(crate) fn op_to_expr")
        .unwrap_or_else(|| panic!("missing op_to_expr after lower_op"));
    let lower_op = &lower_rest[..lower_end];

    assert!(
        lower_op.contains("self.lower_certified_statement_call"),
        "lower_op must delegate certified statement-call disposition to the FunctionFacts gate"
    );
    for forbidden in [
        "materializable_call_result_expr_for_call_expr",
        "CallsiteRenderDisposition::AssignedResult",
        "CallsiteRenderDisposition::SideEffectStatement",
    ] {
        assert!(
            !lower_op.contains(forbidden),
            "lower_op must not choose certified call-render disposition locally via {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_non_certified_statement_calls_do_not_record_functionfacts_proofs() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/lowering.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let helper_marker = "fn lower_certified_statement_call";
    let helper_start = source
        .find(helper_marker)
        .unwrap_or_else(|| panic!("missing {helper_marker} in {}", path.display()));
    let helper_rest = &source[helper_start..];
    let branch_start = helper_rest
        .find("if !self.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("missing non-certified branch in {helper_marker}"));
    let branch_rest = &helper_rest[branch_start..];
    let branch_end = branch_rest
        .find("let Some(callsite)")
        .unwrap_or_else(|| panic!("missing certified branch after non-certified branch"));
    let branch = &branch_rest[..branch_end];

    for forbidden in [
        "record_call_effect_render_proof",
        "record_certified_call_arg_memory_render_proofs",
        "CallsiteRenderDisposition::AssignedResult",
        "CallsiteRenderDisposition::SideEffectStatement",
    ] {
        assert!(
            !branch.contains(forbidden),
            "non-certified call lowering must not synthesize FunctionFacts proof state via {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_member_render_uses_function_render_facts() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let op_lower_path = root.join("crates/r2dec/src/fold/op_lower/mod.rs");
    let op_lower = std::fs::read_to_string(&op_lower_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", op_lower_path.display()));
    let helper_marker = "fn certified_field_name_for_offset";
    let helper_start = op_lower
        .find(helper_marker)
        .unwrap_or_else(|| panic!("missing {helper_marker} in {}", op_lower_path.display()));
    let helper_rest = &op_lower[helper_start..];
    let helper_end = helper_rest
        .find("fn exact_field_name_from_type_hint")
        .unwrap_or_else(|| panic!("missing exact_field_name_from_type_hint after {helper_marker}"));
    let helper = &helper_rest[..helper_end];

    assert!(
        helper.contains("self.inputs.render_facts"),
        "certified member rendering must read FunctionRenderFacts"
    );
    assert!(
        helper.contains("member_access_for_op("),
        "certified member rendering must require a direction-exact per-op FunctionRenderFacts member proof"
    );
    assert!(
        helper.contains("array_access_for_op("),
        "certified array rendering must require a direction-exact per-op FunctionRenderFacts array proof"
    );
    for forbidden in [
        "member_access_for_op_any_direction",
        "array_access_for_op_any_direction",
    ] {
        assert!(
            !helper.contains(forbidden),
            "certified structured memory rendering must not accept wrong-direction proof via {forbidden:?}"
        );
    }
    assert!(
        helper.contains("is_write"),
        "certified structured memory rendering must thread read/write direction into proof lookup"
    );
    assert!(
        helper.contains("field_access_certificates"),
        "certified member rendering should still require type-layout field certificates"
    );

    let lib_path = root.join("crates/r2dec/src/lib.rs");
    let lib = std::fs::read_to_string(&lib_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", lib_path.display()));
    let verifier_marker = "fn proved_member_access_counts";
    let verifier_start = lib
        .find(verifier_marker)
        .unwrap_or_else(|| panic!("missing {verifier_marker} in {}", lib_path.display()));
    let verifier_rest = &lib[verifier_start..];
    let verifier_end = verifier_rest
        .find("fn collect_certified_stmt_contract")
        .unwrap_or_else(|| panic!("missing collect_certified_stmt_contract after {verifier_marker}"));
    let verifier = &verifier_rest[..verifier_end];

    assert!(
        verifier.contains("effect_render_proofs")
            && verifier.contains("memory_access_for_op")
            && verifier.contains("proof.address")
            && verifier.contains("proof.value")
            && verifier.contains("member_accesses_by_op")
            && verifier.contains("field_name.to_ascii_lowercase()"),
        "certified output verifier must compare rendered member names to emitted memory proofs tied to FunctionRenderFacts member proofs"
    );
    for forbidden in [
        "render_facts.member_accesses_by_op.values().flatten()",
        "certified_layout_field_names",
        "first_uncertified_return_field_member",
        "field_access_certificates",
        "certified_names",
        "certified_count >= counts.field_accesses",
        "certified_count >= counts.return_field_members",
    ] {
        assert!(
            !verifier.contains(forbidden),
            "certified output verifier must not bless field syntax from name-only/type-only proof {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_array_and_semantic_render_do_not_use_aggregate_or_pretty_fallbacks() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let op_lower_path = root.join("crates/r2dec/src/fold/op_lower/mod.rs");
    let op_lower = std::fs::read_to_string(&op_lower_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", op_lower_path.display()));

    let memory_renderer_path = root.join("crates/r2dec/src/fold/op_lower/memory_renderer.rs");
    let memory_renderer = std::fs::read_to_string(&memory_renderer_path).unwrap_or_else(|err| {
        panic!(
            "failed to read {}: {err}",
            memory_renderer_path.display()
        )
    });
    let certified_memory_marker = "fn certified_memory_address_expr";
    let certified_memory_start = memory_renderer.find(certified_memory_marker).unwrap_or_else(|| {
        panic!(
            "missing {certified_memory_marker} in {}",
            memory_renderer_path.display()
        )
    });
    let certified_memory_rest = &memory_renderer[certified_memory_start..];
    let certified_memory_end = certified_memory_rest
        .find("pub(super) fn render_authoritative_memory_access_by_name")
        .unwrap_or_else(|| {
            panic!("missing render_authoritative_memory_access_by_name after {certified_memory_marker}")
        });
    let certified_memory = &certified_memory_rest[..certified_memory_end];

    for required in [
        "self.certified_memory_access_for_current_op(is_write)",
        "self.certified_memory_address_expr(fact)",
        "self.render_certified_value_expr_for_var(&addr)",
        "self.certified_return_expr_contains_raw_storage_name(&expr)",
    ] {
        assert!(
            certified_memory.contains(required),
            "certified memory rendering must use FunctionFacts/render-proof path {required:?}"
        );
    }

    for forbidden in [
        "lookup_symbol",
        "lookup_string",
        "lookup_function",
        "parse_address_from_var_name",
        "resolve_stack_var",
        "stack_var_for_addr_var",
        "stable_stack_values",
        "lookup_definition",
        "definition_for_name",
        "best_visible_definition",
        "render_memory_access_from_visible_expr",
        "render_authoritative_memory_access_by_name",
        "prepared_named_memory_expr_for_current_op",
        "prepared_named_memory_def_expr_for_current_op",
        "fallback_addr_expr",
        "fallback_rendered",
        "get_expr(",
    ] {
        assert!(
            !certified_memory.contains(forbidden),
            "certified memory rendering must not use raw symbol/string/stack/visible fallback path {forbidden:?}"
        );
    }

    let indexed_marker = "pub(super) fn indexed_pointer_add_expr";
    let indexed_start = memory_renderer
        .find(indexed_marker)
        .unwrap_or_else(|| panic!("missing {indexed_marker} in {}", memory_renderer_path.display()));
    let indexed_rest = &memory_renderer[indexed_start..];
    let indexed_end = indexed_rest
        .find("fn scaled_index_expr")
        .unwrap_or_else(|| panic!("missing scaled_index_expr after {indexed_marker}"));
    let indexed = &indexed_rest[..indexed_end];
    assert!(
        indexed.contains("self.requires_certified_rendering()")
            && indexed.contains("return None"),
        "certified mode must not turn pointer arithmetic into [] without exact array render proof"
    );

    let semantic_marker = "pub(crate) fn render_semantic_value";
    let semantic_start = op_lower
        .find(semantic_marker)
        .unwrap_or_else(|| panic!("missing {semantic_marker} in {}", op_lower_path.display()));
    let semantic_rest = &op_lower[semantic_start..];
    let semantic_end = semantic_rest
        .find("fn render_value_ref")
        .unwrap_or_else(|| panic!("missing render_value_ref after {semantic_marker}"));
    let semantic = &semantic_rest[..semantic_end];
    assert!(
        semantic.contains("expr_contains_structured_memory_syntax"),
        "certified mode must not clone structured SemanticValue::Scalar C expressions directly"
    );

    let lib_path = root.join("crates/r2dec/src/lib.rs");
    let lib = std::fs::read_to_string(&lib_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", lib_path.display()));
    let verifier_marker = "fn array_accesses_are_certified";
    let verifier_start = lib
        .find(verifier_marker)
        .unwrap_or_else(|| panic!("missing {verifier_marker} in {}", lib_path.display()));
    let verifier_rest = &lib[verifier_start..];
    let verifier_end = verifier_rest
        .find("fn field_accesses_are_certified")
        .unwrap_or_else(|| panic!("missing field_accesses_are_certified after {verifier_marker}"));
    let verifier = &verifier_rest[..verifier_end];
    assert!(
        verifier.contains("effect_render_proofs")
            && verifier.contains("memory_access_for_op")
            && verifier.contains("proof.address")
            && verifier.contains("proof.value")
            && verifier.contains("array_accesses_by_op")
            && verifier.contains("array.access == memory.access"),
        "array rendering must be certified from emitted memory proofs tied to exact FunctionRenderFacts array-access proof"
    );
    for forbidden in [
        "array_index_certificates",
        "certified_array_indexes",
        "certified_array_field_names",
        "certified_count >= counts.array_accesses",
    ] {
        assert!(
            !verifier.contains(forbidden),
            "array render verification must not use aggregate/type-only proof {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_local_post_call_source_refuses_before_raw_scan() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let marker = "pub(super) fn local_post_call_source_for_ssa_name_in_block";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("fn raw_local_post_call_source_for_ssa_name_in_block")
        .unwrap_or_else(|| panic!("missing raw local post-call helper after {marker}"));
    let body = &rest[..end];
    let certified_at = body
        .find("if self.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("{marker} must branch on certified rendering"));
    let raw_at = body
        .find("raw_local_post_call_source_for_ssa_name_in_block")
        .unwrap_or_else(|| panic!("{marker} must call the raw local scanner for non-certified mode"));
    assert!(
        certified_at < raw_at,
        "certified local post-call source lookup must refuse before raw SSA adjacency scanning"
    );
    assert!(
        body[certified_at..raw_at].contains("return None;"),
        "certified local post-call source lookup must return None before raw SSA adjacency scanning"
    );
}

#[test]
fn r2dec_certified_branch_condition_refuses_without_functionfacts_comparison() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/flags.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let marker = "pub(super) fn certified_branch_condition_from_block";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("fn branch_compare_provenance_expr")
        .unwrap_or_else(|| panic!("missing branch_compare_provenance_expr after {marker}"));
    let body = &rest[..end];

    for required in [
        "self.control_facts()?.branch_for_block(block.addr)?",
        "predicate.condition",
        ".comparison",
        "self.prepared_compare_provenance_expr(comparison)",
    ] {
        assert!(
            body.contains(required),
            "certified branch condition must require FunctionFacts control proof {required:?}"
        );
    }
    for forbidden in [
        "prepared_branch_condition_expr",
        "prepared_predicate_candidate_for_branch_block",
        "prepared_predicate_candidate_for_var",
        "local_branch_condition_expr",
        "current_block_addr.replace",
        "current_op_idx.replace",
    ] {
        assert!(
            !body.contains(forbidden),
            "certified branch condition must not use local/prepared fallback {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_prepared_branch_extraction_uses_functionfacts_control_gate() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/flags.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let marker = "pub fn extract_condition_from_block";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("pub(super) fn certified_branch_condition_from_block")
        .unwrap_or_else(|| panic!("missing certified branch helper after {marker}"));
    let body = &rest[..end];

    let prepared_gate = "self.requires_certified_rendering() || self.inputs.prepared_ssa.is_some()";
    let prepared_gate_at = body
        .find(prepared_gate)
        .unwrap_or_else(|| panic!("{marker} must gate prepared SSA through certified control facts"));
    let certified_call_at = body
        .find("certified_branch_condition_from_block(block)")
        .unwrap_or_else(|| panic!("{marker} must call certified_branch_condition_from_block"));
    let local_recovery_at = body
        .find("local_branch_condition_expr")
        .unwrap_or_else(|| panic!("{marker} still contains the non-prepared legacy branch path"));
    assert!(
        prepared_gate_at < certified_call_at && certified_call_at < local_recovery_at,
        "prepared branch extraction must reach FunctionFacts control gate before local recovery"
    );

    for forbidden in [
        "symbolic_actionable_compiled_condition_expr",
        "symbolic_actionable_memory_condition_expr",
        "symbolic_branch_condition_expr",
        "symbolic_actionable_compiled_condition(block.addr)",
    ] {
        assert!(
            !body.contains(forbidden),
            "executable branch extraction must not use semantic artifact shortcut {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_branch_comparison_operands_use_render_facts_only() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/flags.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    fn extract<'a>(source: &'a str, marker: &str, end_marker: &str) -> &'a str {
        let start = source
            .find(marker)
            .unwrap_or_else(|| panic!("missing {marker}"));
        let rest = &source[start..];
        let end = rest
            .find(end_marker)
            .unwrap_or_else(|| panic!("missing {end_marker} after {marker}"));
        &rest[..end]
    }

    let prepared_compare = extract(
        &source,
        "fn prepared_compare_provenance_expr",
        "fn certified_compare_provenance_expr",
    );
    assert!(
        prepared_compare.contains("if self.requires_certified_rendering()")
            && prepared_compare.contains("return self.certified_compare_provenance_expr(prov);"),
        "prepared comparison rendering must delegate to certified comparison renderer in certified mode"
    );

    let certified_compare = extract(
        &source,
        "fn certified_compare_provenance_expr",
        "fn certified_predicate_operand_expr",
    );
    for required in [
        "self.prepared_var_for_value_id(prov.lhs)",
        "self.prepared_var_for_value_id(prov.rhs)",
        "self.certified_predicate_operand_expr(lhs_var, compare_width)",
        "self.certified_predicate_operand_expr(rhs_var, compare_width)",
        "self.compare_provenance_expr_from_operands(prov, lhs, rhs)",
    ] {
        assert!(
            certified_compare.contains(required),
            "certified predicate comparison must require {required:?}"
        );
    }
    for forbidden in [
        "resolve_prepared_predicate_operand_with_width",
        "prepared_predicate_view",
        "stack_slot_provenance_for_name",
        "best_visible_definition",
        "resolve_predicate_operand",
        "arg_alias_for_rendered_name",
        "predicate_owned_call_result_expr_for_name",
    ] {
        assert!(
            !certified_compare.contains(forbidden),
            "certified predicate comparison must not use local/prepared operand fallback {forbidden:?}"
        );
    }

    let certified_operand = extract(
        &source,
        "fn certified_predicate_operand_expr",
        "fn compare_provenance_expr_from_operands",
    );
    assert!(
        certified_operand.contains("render_certified_value_expr_for_var(var)"),
        "certified predicate operands must render through FunctionRenderFacts"
    );
    for forbidden in [
        "prepared_predicate_view",
        "stack_slot_provenance_for_name",
        "best_visible_definition",
        "resolve_predicate_operand",
        "lookup_definition",
        "render_semantic_value",
    ] {
        assert!(
            !certified_operand.contains(forbidden),
            "certified predicate operand must not use local/prepared fallback {forbidden:?}"
        );
    }
}

#[test]
fn r2plugin_sla_ssa_func_does_not_own_decompile_cfg_guard() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("r2plugin/r_anal_sleigh.c");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let section = source
        .find("/* ========== Function-level SSA commands ========== */")
        .unwrap_or_else(|| panic!("missing function-level SSA command section"));
    let start = source[section..]
        .find("if (!strcmp (cmd, \"sla.ssa.func\"))")
        .map(|offset| section + offset)
        .unwrap_or_else(|| panic!("missing sla.ssa.func command block"));
    let end = source[start..]
        .find("if (!strcmp (cmd, \"sla.ssa.func.opt\"))")
        .map(|offset| start + offset)
        .unwrap_or_else(|| panic!("missing sla.ssa.func.opt command block"));
    let ssa_func_block = &source[start..end];

    for forbidden in [
        "r2dec_cfg_guard_comment_ffi",
        "compute_decompile_cfg_risk_summary",
        "DecompileCFGRiskSummary",
        "is_autogenerated_function_name",
    ] {
        assert!(
            !source.contains(forbidden),
            "plugin C must not retain local decompile CFG guard policy {forbidden:?}"
        );
    }
    assert!(
        !ssa_func_block.contains("/* r2dec:"),
        "sla.ssa.func must not print decompiler-owned CFG guard comments"
    );
}

#[test]
fn r2plugin_sla_dec_does_not_build_interproc_scope_in_c() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("r2plugin/r_anal_sleigh.c");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let start = source
        .find("if (!strncmp (cmd, \"sla.dec\", 7))")
        .unwrap_or_else(|| panic!("missing sla.dec command block"));
    let end = source[start..]
        .find("if (!strcmp (cmd, \"sla.cfg\")")
        .map(|offset| start + offset)
        .unwrap_or_else(|| panic!("missing sla.cfg command block after sla.dec"));
    let decompile_block = &source[start..end];

    assert!(
        decompile_block.contains("r2sleigh_engine_decompile_function (&decompile_input)"),
        "sla.dec must route decompile through the engine FFI"
    );
    for forbidden in [
        "build_type_interproc_scope",
        "build_symbolic_function_scope_with_target",
        "SymFunctionScope sym_scope",
        "SleighInterprocSeeds interproc_seeds",
        "have_sym_scope",
        "sym_scope.functions",
        "interproc_seeds.items",
        "sleigh_interproc_seeds_init",
        "R2SleighSessionPolicyPlan",
        "sleigh_session_policy_plan_for_function",
        "r2sleigh_session_policy_plan_for_depth",
        "session_policy_plan.",
        "R2SleighSessionInput session_input",
        "sleigh_session_input_init (&session_input",
        "r2dec_function_with_session_context",
        "SLEIGH_TYPE_WRITEBACK_OFF",
    ] {
        assert!(
            !decompile_block.contains(forbidden),
            "sla.dec must not own interprocedural scope or session policy construction {forbidden:?}"
        );
    }
}

#[test]
fn r2plugin_decompile_path_does_not_repair_cfg_or_switches() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let path = root.join("r2plugin/r_anal_sleigh.c");
    let rust_path = root.join("r2plugin/src/lib.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let rust_source = std::fs::read_to_string(&rust_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", rust_path.display()));
    let decompile_start = source
        .find("if (!strncmp (cmd, \"sla.dec\", 7))")
        .unwrap_or_else(|| panic!("missing sla.dec command block"));
    let decompile_end = source[decompile_start..]
        .find("if (!strcmp (cmd, \"sla.cfg\")")
        .map(|offset| decompile_start + offset)
        .unwrap_or_else(|| panic!("missing sla.cfg command block after sla.dec"));
    let decompile_block = &source[decompile_start..decompile_end];
    let lift_start = source
        .find("static bool lift_function_blocks(")
        .unwrap_or_else(|| panic!("missing lift_function_blocks helper"));
    let lift_end = source[lift_start..]
        .find("\nstatic SleighMode sleigh_mode_from_analysis_depth")
        .map(|offset| lift_start + offset)
        .unwrap_or_else(|| panic!("missing lift_function_blocks end marker"));
    let lift_body = &source[lift_start..lift_end];

    assert!(
        decompile_block.contains("r2sleigh_engine_decompile_function (&decompile_input)"),
        "sla.dec must route decompile through the engine FFI"
    );
    assert!(
        decompile_block.contains("lift_function_blocks (anal, fcn, ctx, &blocks)"),
        "sla.dec must use the strict function-block lifter before engine handoff"
    );
    for forbidden in [
        "recover_missing_switch_ops",
        "recover_missing_delta_switch_op",
        "split_missing_switch_case_targets",
        "find_best_switch_metadata_block",
        "r2il_block_set_switch_info",
        "lift_function_block_healed",
        "lift_function_linear_gap_blocks",
        "include_linear_gap_blocks",
        "r2il_block_rewrite_layout",
        "r2il_block_new_branch",
        "r2il_block_has_trailing_indirect_branch",
    ] {
        assert!(
            !source.contains(forbidden),
            "plugin C must not retain local CFG/switch/control repair helper {forbidden:?}"
        );
        assert!(
            !rust_source.contains(forbidden),
            "plugin Rust must not export local CFG/switch/control repair helper {forbidden:?}"
        );
        assert!(
            !decompile_block.contains(forbidden) && !lift_body.contains(forbidden),
            "live plugin decompile path must not repair CFG/switch/control locally: {forbidden:?}"
        );
    }
}

#[test]
fn r2plugin_sla_dec_preserves_lift_quality_for_engine() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let c_path = root.join("r2plugin/r_anal_sleigh.c");
    let rust_path = root.join("r2plugin/src/lib.rs");
    let engine_path = root.join("crates/r2engine/src/lib.rs");
    let c_source = std::fs::read_to_string(&c_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", c_path.display()));
    let rust_source = std::fs::read_to_string(&rust_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", rust_path.display()));
    let engine_source = std::fs::read_to_string(&engine_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", engine_path.display()));

    let decompile_start = c_source
        .find("if (!strncmp (cmd, \"sla.dec\", 7))")
        .unwrap_or_else(|| panic!("missing sla.dec command block"));
    let decompile_end = c_source[decompile_start..]
        .find("if (!strcmp (cmd, \"sla.cfg\")")
        .map(|offset| decompile_start + offset)
        .unwrap_or_else(|| panic!("missing sla.cfg command block after sla.dec"));
    let decompile_block = &c_source[decompile_start..decompile_end];
    let lift_handoff_start = decompile_block
        .find("bool lift_ok = lift_function_blocks")
        .unwrap_or_else(|| panic!("sla.dec must keep lift success as an input fact"));
    let lift_handoff_end = decompile_block[lift_handoff_start..]
        .find("sleigh_profile_add (anal, fcn, SLEIGH_PROFILE_STAGE_LIFT")
        .map(|offset| lift_handoff_start + offset)
        .unwrap_or_else(|| panic!("missing lift profile marker after lift handoff"));
    let lift_handoff = &decompile_block[lift_handoff_start..lift_handoff_end];
    assert!(
        !lift_handoff.contains("return strdup(\"\")"),
        "sla.dec must not return empty output before r2engine sees lift-quality refusal"
    );

    let engine_input_start = decompile_block
        .find("R2SleighEngineDecompileInput decompile_input = {")
        .unwrap_or_else(|| panic!("missing engine decompile input"));
    let engine_input_end = decompile_block[engine_input_start..]
        .find("};")
        .map(|offset| engine_input_start + offset)
        .unwrap_or_else(|| panic!("missing engine decompile input end"));
    let engine_input = &decompile_block[engine_input_start..engine_input_end];
    for required in [
        ".blocks = lift_ok ? (const R2ILBlock **)blocks.blocks : NULL",
        ".num_blocks = lift_ok ? blocks.count : 0",
        ".lift_quality = blocks.quality",
    ] {
        assert!(
            engine_input.contains(required),
            "sla.dec must pass lift-quality handoff field {required:?}"
        );
    }
    assert!(
        decompile_block.contains("r2sleigh_engine_decompile_function (&decompile_input)"),
        "sla.dec must route incomplete lift input to r2engine"
    );
    for forbidden in [
        "R2SleighLiftQuality quality = {0}",
        "memset (&decompile_input.lift_quality",
        "incomplete lifted function input",
        "empty lifted function input",
    ] {
        assert!(
            !decompile_block.contains(forbidden),
            "sla.dec must not own lift-quality refusal or synthesize quality locally: {forbidden:?}"
        );
    }

    let ffi_start = rust_source
        .find("fn r2sleigh_engine_decompile_function_output")
        .unwrap_or_else(|| panic!("missing Rust engine decompile FFI wrapper"));
    let ffi_end = rust_source[ffi_start..]
        .find("// radare2 Deep Integration FFI - Variable Recovery and Data Refs")
        .map(|offset| ffi_start + offset)
        .unwrap_or_else(|| panic!("missing Rust engine decompile FFI wrapper end"));
    let ffi_body = &rust_source[ffi_start..ffi_end];
    for required in [
        "engine_function_input_quality_from_ffi(input.lift_quality)",
        "block_slice.is_none() && input_quality.refusal_reason().is_none()",
        "blocks: block_slice",
        "parse_typed_external_context_for_engine(",
        "EngineFunctionDecompileRequestInput::single_function_from_engine_context(",
        ".with_input_quality(input_quality)",
        "run_engine_decompile_on_large_stack(decompile_input)",
        "quality.expected_blocks",
        "quality.lifted_blocks",
        "quality.read_failures",
        "quality.invalid_blocks",
        "quality.null_lift_failures",
        "quality.truncated_blocks",
    ] {
        assert!(
            ffi_body.contains(required),
            "Rust decompile FFI must preserve lift-quality evidence: {required:?}"
        );
    }
    for forbidden in [
        "types::build_function_input(",
        "types::hash_string_payload(&external_context)",
        "EngineFunctionInputQuality::complete(input.num_blocks)",
        "EngineFunctionDecompileRequest::full_semantics_for_function(",
        ".decompile_function(",
        "function_context.external_context_json",
        "cstr_or_default(input.function_context.external_context_json",
    ] {
        assert!(
            !ffi_body.contains(forbidden),
            "Rust decompile FFI must not bypass typed engine evidence or input-quality refusal: {forbidden:?}"
        );
    }

    let typed_parser_start = engine_source
        .find("pub fn parse_typed_external_context(")
        .unwrap_or_else(|| panic!("missing typed external context parser"));
    let typed_parser_rest = &engine_source[typed_parser_start..];
    let typed_parser_end = typed_parser_rest
        .find("\npub fn parse_typed_external_context_for_engine(")
        .unwrap_or_else(|| panic!("missing typed parser end marker"));
    let typed_parser_body = &typed_parser_rest[..typed_parser_end];
    for forbidden in [
        "fallback_json",
        "parse_external_context_json(fallback",
        "serde_json::from_str::<r2types::ExternalContextJson>",
        "known_signatures: fallback",
        "fallback.assumptions",
    ] {
        assert!(
            !typed_parser_body.contains(forbidden),
            "typed external context parsing must not repair missing typed facts from raw JSON fallback: {forbidden:?}"
        );
    }
    assert!(
        !c_source.contains("fallback_external_context_json"),
        "C typed context collector must not preserve raw external-context JSON fallback"
    );

    let engine_check_start = engine_source
        .find("pub fn decompile_function_from_input(")
        .unwrap_or_else(|| panic!("missing engine decompile input entry"));
    let engine_check_end = engine_source[engine_check_start..]
        .find("self.decompile_function(EngineFunctionDecompileRequest::full_semantics_for_function")
        .map(|offset| engine_check_start + offset)
        .unwrap_or_else(|| panic!("missing engine decompile dispatch"));
    let engine_check = &engine_source[engine_check_start..engine_check_end];
    for required in [
        "let actual_lifted_blocks = input.function.blocks.len();",
        ".refusal_reason_for_actual_lifted_blocks(actual_lifted_blocks)",
        "function_input_quality_facts(",
        "Some(input_quality)",
    ] {
        assert!(
            engine_check.contains(required),
            "engine must validate lift quality against the actual block vector before rendering: {required:?}"
        );
    }
}

#[test]
fn r2engine_decompile_raw_request_stays_private() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let path = root.join("crates/r2engine/src/lib.rs");
    let plugin_lib_path = root.join("r2plugin/src/lib.rs");
    let plugin_decompiler_path = root.join("r2plugin/src/decompiler.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let plugin_lib = std::fs::read_to_string(&plugin_lib_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", plugin_lib_path.display()));
    let plugin_decompiler = std::fs::read_to_string(&plugin_decompiler_path).unwrap_or_else(|err| {
        panic!(
            "failed to read {}: {err}",
            plugin_decompiler_path.display()
        )
    });
    let request_start = source
        .find("pub(crate) struct EngineFunctionDecompileRequest")
        .unwrap_or_else(|| panic!("missing raw decompile request"));
    let request_rest = &source[request_start..];
    let request_end = request_rest
        .find("\n}\n\n#[derive(Debug, Clone)]\npub struct EngineFunctionDecompileRequestInput")
        .unwrap_or_else(|| panic!("missing raw decompile request end"));
    let request_body = &request_rest[..request_end];

    for required in [
        "pub(crate) struct EngineFunctionDecompileRequest",
        "pub(crate) fn full_semantics_for_function(input: EngineFunctionDecompileRequestInput) -> Self",
        "pub(crate) fn decompile_function(",
        "pub fn decompile_function_from_input(",
    ] {
        assert!(
            source.contains(required),
            "raw decompile request must stay private while checked input API remains public: {required:?}"
        );
    }
    for forbidden in [
        "\npub struct EngineFunctionDecompileRequest {",
        "\n    pub fn decompile_function(",
    ] {
        assert!(
            !source.contains(forbidden),
            "raw decompile request API must not be public: {forbidden:?}"
        );
    }
    for forbidden in [
        "pub analysis: EngineAnalyzeRequest",
        "pub input_quality: Option<EngineFunctionInputQuality>",
    ] {
        assert!(
            !request_body.contains(forbidden),
            "raw decompile request fields must stay private: {forbidden:?}"
        );
    }

    let input_start = source
        .find("pub struct EngineFunctionDecompileRequestInput")
        .unwrap_or_else(|| panic!("missing checked decompile request input"));
    let input_rest = &source[input_start..];
    let input_end = input_rest
        .find("\n}\n\nimpl EngineFunctionDecompileRequestInput")
        .unwrap_or_else(|| panic!("missing checked decompile request input end"));
    let input_body = &input_rest[..input_end];
    for forbidden in [
        "pub function:",
        "pub ptr_bits:",
        "pub parsed_context:",
        "pub external_context_fallback_hash:",
        "pub scope_facts:",
        "pub interproc_max_iterations:",
        "pub symbolic_scope:",
        "pub input_quality:",
    ] {
        assert!(
            !input_body.contains(forbidden),
            "checked decompile request input fields must stay private: {forbidden:?}"
        );
    }
    for required in [
        "pub fn single_function(",
        "pub fn single_function_from_engine_context(",
        "pub fn with_input_quality(",
        "scope_facts: InterprocScopeFacts::empty()",
        "interproc_max_iterations: 1",
        "symbolic_scope: None",
    ] {
        assert!(
            source.contains(required),
            "external one-function decompile callers must use the narrow constructor path: {required:?}"
        );
    }
    assert!(
        plugin_lib.contains("EngineFunctionDecompileRequestInput::single_function"),
        "r2plugin/src/lib.rs must route function decompile requests through the narrow engine constructor"
    );
    assert!(
        !plugin_decompiler.contains("DetachedEngineDecompileRequest")
            && !plugin_decompiler.contains("decompile_detached_blocks_with_engine"),
        "r2plugin/src/decompiler.rs must not preserve the detached raw decompile test adapter"
    );
    for (label, plugin_source) in [
        ("r2plugin/src/lib.rs", plugin_lib.as_str()),
        ("r2plugin/src/decompiler.rs", plugin_decompiler.as_str()),
    ] {
        assert!(
            !plugin_source.contains("EngineFunctionDecompileRequestInput {"),
            "{label} must not construct decompile request inputs with policy fields directly"
        );
    }
}

#[test]
fn r2engine_raw_decompiler_input_helper_is_test_only() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let engine_manifest_path = root.join("crates/r2engine/Cargo.toml");
    let plugin_manifest_path = root.join("r2plugin/Cargo.toml");
    let engine_path = root.join("crates/r2engine/src/lib.rs");
    let engine_manifest = std::fs::read_to_string(&engine_manifest_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", engine_manifest_path.display()));
    let plugin_manifest = std::fs::read_to_string(&plugin_manifest_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", plugin_manifest_path.display()));
    let engine_source = std::fs::read_to_string(&engine_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", engine_path.display()));

    for (label, source) in [
        ("r2engine manifest", engine_manifest.as_str()),
        ("r2plugin manifest", plugin_manifest.as_str()),
        ("r2engine source", engine_source.as_str()),
    ] {
        assert!(
            !source.contains("decompiler-input-test-support"),
            "{label} must not expose the deleted raw decompiler input test-support feature"
        );
    }

    let helper_start = engine_source
        .find("pub fn decompiler_input_from_prepared_facts")
        .unwrap_or_else(|| panic!("missing decompiler_input_from_prepared_facts test helper"));
    let helper_prefix_start = helper_start.saturating_sub(64);
    let helper_prefix = &engine_source[helper_prefix_start..helper_start];
    assert!(
        helper_prefix.contains("#[cfg(test)]"),
        "raw r2dec::DecompilerInput assembly helper must be cfg(test)-only"
    );
    assert!(
        !helper_prefix.contains("feature ="),
        "raw r2dec::DecompilerInput assembly helper must not be feature-gated into production"
    );
}

#[test]
fn r2engine_render_cache_mutation_is_crate_private() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let engine_path = root.join("crates/r2engine/src/lib.rs");
    let plugin_lib_path = root.join("r2plugin/src/lib.rs");
    let plugin_decompiler_path = root.join("r2plugin/src/decompiler.rs");
    let plugin_types_path = root.join("r2plugin/src/types.rs");
    let engine_source = std::fs::read_to_string(&engine_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", engine_path.display()));
    let plugin_lib = std::fs::read_to_string(&plugin_lib_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", plugin_lib_path.display()));
    let plugin_decompiler = std::fs::read_to_string(&plugin_decompiler_path).unwrap_or_else(|err| {
        panic!(
            "failed to read {}: {err}",
            plugin_decompiler_path.display()
        )
    });
    let plugin_types = std::fs::read_to_string(&plugin_types_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", plugin_types_path.display()));

    for forbidden in [
        "pub use cache::{CacheCounters, EngineSessionCacheMetrics, SessionCache}",
        "pub use cache::SessionCache",
        "pub struct DecompileRenderCacheKeyInput",
        "pub fn decompile_render_cache_key",
        "pub fn cached_render",
        "pub fn cached_render_with_decision",
        "pub fn insert_render",
        "pub fn cached_artifacts",
        "pub fn cached_artifacts_with_decision",
        "pub fn insert_artifacts",
    ] {
        assert!(
            !engine_source.contains(forbidden),
            "r2engine cache internals must not be public bypass surfaces: {forbidden:?}"
        );
    }

    let render_key_start = engine_source
        .find("impl RenderCacheKey")
        .unwrap_or_else(|| panic!("missing RenderCacheKey impl"));
    let render_key_rest = &engine_source[render_key_start..];
    let render_key_end = render_key_rest
        .find("\n}\n\npub(crate) struct DecompileRenderCacheKeyInput")
        .unwrap_or_else(|| panic!("missing RenderCacheKey impl end"));
    let render_key_impl = &render_key_rest[..render_key_end];
    for forbidden in ["pub fn from_artifact(", "pub fn from_payload("] {
        assert!(
            !render_key_impl.contains(forbidden),
            "render cache keys must be minted only inside r2engine: {forbidden:?}"
        );
    }

    for (label, plugin_source) in [
        ("r2plugin/src/lib.rs", plugin_lib.as_str()),
        ("r2plugin/src/decompiler.rs", plugin_decompiler.as_str()),
        ("r2plugin/src/types.rs", plugin_types.as_str()),
    ] {
        for forbidden in [
            "RenderCacheKey",
            "SessionCache",
            "cached_render",
            "insert_render",
            "cached_artifacts",
            "insert_artifacts",
        ] {
            assert!(
                !plugin_source.contains(forbidden),
                "{label} must not use r2engine render/cache internals: {forbidden:?}"
            );
        }
    }
}

#[test]
fn r2engine_decompile_route_helpers_are_not_public_plugin_api() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let engine_lib_path = root.join("crates/r2engine/src/lib.rs");
    let engine_route_path = root.join("crates/r2engine/src/route.rs");
    let plugin_lib_path = root.join("r2plugin/src/lib.rs");
    let plugin_decompiler_path = root.join("r2plugin/src/decompiler.rs");
    let engine_lib = std::fs::read_to_string(&engine_lib_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", engine_lib_path.display()));
    let engine_route = std::fs::read_to_string(&engine_route_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", engine_route_path.display()));
    let plugin_lib = std::fs::read_to_string(&plugin_lib_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", plugin_lib_path.display()));
    let plugin_decompiler = std::fs::read_to_string(&plugin_decompiler_path).unwrap_or_else(|err| {
        panic!(
            "failed to read {}: {err}",
            plugin_decompiler_path.display()
        )
    });

    let pub_route_start = engine_lib
        .find("pub use route::{")
        .unwrap_or_else(|| panic!("missing public route re-export block"));
    let pub_route_rest = &engine_lib[pub_route_start..];
    let pub_route_end = pub_route_rest
        .find("};")
        .unwrap_or_else(|| panic!("missing public route re-export block end"));
    let public_route_exports = &pub_route_rest[..pub_route_end];

    for forbidden in [
        "decompile_route_decision,",
        "plan_decompile_request,",
        "semantic_route_plan,",
        "semantic_route_plan_from_context,",
        "semantic_route_from_artifact_plan,",
        "semantic_route_reason,",
        "detached_semantic_route_plan,",
        "detached_semantic_linearization_reason,",
        "decompile_probe_decision,",
        "decompile_probe_decision_for_identity,",
        "should_skip_runtime_type_inference,",
    ] {
        assert!(
            !public_route_exports.contains(forbidden),
            "r2engine must not re-export decompile route policy helpers: {forbidden:?}"
        );
    }

    for forbidden in [
        "pub fn plan_decompile_request(",
        "pub fn semantic_route_plan(",
        "pub fn semantic_route_plan_from_context(",
        "pub fn decompile_route_decision(",
        "pub fn detached_semantic_route_plan(",
        "pub fn detached_semantic_linearization_reason(",
        "pub fn decompile_probe_decision(",
        "pub fn decompile_probe_decision_for_identity(",
        "pub fn should_skip_runtime_type_inference(",
    ] {
        assert!(
            !engine_route.contains(forbidden),
            "decompile route policy helpers must stay crate-private: {forbidden:?}"
        );
    }

    for (label, plugin_source) in [
        ("r2plugin/src/lib.rs", plugin_lib.as_str()),
        ("r2plugin/src/decompiler.rs", plugin_decompiler.as_str()),
    ] {
        for forbidden in [
            "r2engine::decompile_route_decision",
            "r2engine::semantic_route_plan",
            "r2engine::plan_decompile_request",
            "r2engine::decompile_probe_decision",
            "r2engine::detached_semantic_route_plan",
            "r2engine::detached_semantic_linearization_reason",
            "r2engine::should_skip_runtime_type_inference",
        ] {
            assert!(
                !plugin_source.contains(forbidden),
                "{label} must not own or test decompile route policy directly: {forbidden:?}"
            );
        }
    }
}

#[test]
fn r2sleigh_export_dec_is_residual_only_and_does_not_depend_on_r2dec() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let manifest_path = root.join("crates/r2sleigh-export/Cargo.toml");
    let source_path = root.join("crates/r2sleigh-export/src/lib.rs");
    let manifest = std::fs::read_to_string(&manifest_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", manifest_path.display()));
    let source = std::fs::read_to_string(&source_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", source_path.display()));

    for forbidden in [
        "r2dec",
        "CodeGenerator",
        "CodeGenConfig",
        "lower_ssa_ops_to_stmts",
        "CStmt",
        "DecompilerInput",
        "DecompilerContext",
        "Decompiler::",
    ] {
        assert!(
            !manifest.contains(forbidden),
            "r2sleigh-export manifest must not depend on raw r2dec renderer surface: {forbidden:?}"
        );
        assert!(
            !source.contains(forbidden),
            "r2sleigh-export source must not use raw r2dec renderer surface: {forbidden:?}"
        );
    }

    let start = source
        .find("fn export_dec(")
        .unwrap_or_else(|| panic!("missing export_dec"));
    let rest = &source[start..];
    let end = rest
        .find("\nfn sorted_set")
        .unwrap_or_else(|| panic!("missing export_dec end marker"));
    let body = &rest[..end];
    for required in [
        "DecResidualJson",
        "r2sleigh-export residual",
        "FunctionFacts render proof",
        "executable C suppressed",
    ] {
        assert!(
            body.contains(required),
            "r2sleigh-export dec must stay explicit residual-only output: {required:?}"
        );
    }
}

#[test]
fn r2dec_raw_code_generator_is_not_public_api() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let lib_path = root.join("crates/r2dec/src/lib.rs");
    let codegen_path = root.join("crates/r2dec/src/codegen.rs");
    let lib_source = std::fs::read_to_string(&lib_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", lib_path.display()));
    let codegen_source = std::fs::read_to_string(&codegen_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", codegen_path.display()));

    for forbidden in [
        "pub mod codegen;",
        "pub use codegen::{",
        "pub use codegen::CodeGenerator",
        "pub use codegen::generate",
    ] {
        assert!(
            !lib_source.contains(forbidden),
            "r2dec must not expose raw code generation outside the FunctionFacts render gate: {forbidden:?}"
        );
    }

    for forbidden in [
        "pub struct CodeGenerator",
        "pub fn new(config: CodeGenConfig)",
        "pub fn generate_function",
        "pub fn generate_stmt",
        "pub fn generate_expr",
        "pub fn generate(func:",
    ] {
        assert!(
            !codegen_source.contains(forbidden),
            "raw C code generation must remain crate-internal: {forbidden:?}"
        );
    }

    assert!(
        lib_source.contains("pub(crate) mod codegen;")
            && lib_source.contains("pub use codegen::CodeGenConfig;"),
        "r2dec should expose only configuration, not raw AST-to-C rendering"
    );
}

#[test]
fn r2dec_certified_standard_preserves_final_ast_proof_identity() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let lib_path = root.join("crates/r2dec/src/lib.rs");
    let structure_path = root.join("crates/r2dec/src/structure.rs");
    let op_lower_path = root.join("crates/r2dec/src/fold/op_lower/mod.rs");
    let lib_source = std::fs::read_to_string(&lib_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", lib_path.display()));
    let structure_source = std::fs::read_to_string(&structure_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", structure_path.display()));
    let op_lower_source = std::fs::read_to_string(&op_lower_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", op_lower_path.display()));

    assert!(
        structure_source.contains("pub(crate) fn structure_preserving_render_proof_identity"),
        "certified Standard rendering needs a no-cleanup structuring entrypoint"
    );
    let preserving_start = structure_source
        .find("pub(crate) fn structure_preserving_render_proof_identity")
        .unwrap_or_else(|| panic!("missing proof-preserving structuring entrypoint"));
    let preserving_rest = &structure_source[preserving_start..];
    let preserving_end = preserving_rest
        .find("\n    /// Structure a region")
        .unwrap_or_else(|| panic!("missing proof-preserving structuring end marker"));
    let preserving_body = &preserving_rest[..preserving_end];
    assert!(
        !preserving_body.contains("Self::cleanup("),
        "proof-preserving structuring must not rewrite control nodes after recording proofs"
    );
    let guarded_switch_call = structure_source
        .find("self.try_structure_guarded_switch_with_default(")
        .unwrap_or_else(|| panic!("missing guarded-switch rewrite call"));
    let guarded_switch_prefix_start = guarded_switch_call.saturating_sub(160);
    let guarded_switch_prefix = &structure_source[guarded_switch_prefix_start..guarded_switch_call];
    assert!(
        guarded_switch_prefix.contains("if !self.fold_ctx.requires_certified_rendering()"),
        "guarded-switch/default fusion must stay disabled in certified Standard mode until FunctionFacts carries an exact guarded-switch proof"
    );
    let switch_region_start = structure_source
        .find("fn structure_switch_region")
        .unwrap_or_else(|| panic!("missing structure_switch_region"));
    let switch_region_rest = &structure_source[switch_region_start..];
    let switch_region_end = switch_region_rest
        .find("\n    fn structure_block_prefix_stmts")
        .unwrap_or_else(|| panic!("missing structure_switch_region end marker"));
    let switch_region_body = &switch_region_rest[..switch_region_end];
    assert!(
        switch_region_body.contains("if self.fold_ctx.requires_certified_rendering()")
            && switch_region_body.contains("vec![case_stmt]")
            && switch_region_body.contains("vec![case_stmt, CStmt::Break]"),
        "certified switch rendering must not synthesize case breaks; non-certified mode may keep legacy break insertion"
    );

    let render_start = lib_source
        .find("fn build_function_internal")
        .unwrap_or_else(|| panic!("missing build_function_internal"));
    let render_rest = &lib_source[render_start..];
    let render_end = render_rest
        .find("\n    /// Convert a CStmt")
        .unwrap_or_else(|| panic!("missing build_function_internal end marker"));
    let render_body = &render_rest[..render_end];
    for required in [
        "if route_is_standard(semantic_route) && !certified_rendering_required",
        "Standard executable rendering requires engine-owned CertifiedC permission",
        "certified_standard_mode && route_is_standard(semantic_route)",
        "signature_has_complete_render_param_types(signature)",
        "structurer.structure_preserving_render_proof_identity()",
        "if !certified_standard_mode && route_is_standard(semantic_route)",
        "fold_ctx.normalize_final_stmt_calls(body_stmt)",
        "fold_ctx.prune_duplicate_call_statements_by_source(&mut c_function.body)",
        "if !certified_standard_mode {",
        "prune_dead_temp_assignments_in_function_body(&mut c_function, &fold_ctx)",
    ] {
        assert!(
            render_body.contains(required),
            "certified Standard render path must keep post-proof mutations out of certified mode: {required:?}"
        );
    }
    let validator_start = lib_source
        .find("fn certified_standard_output_residual_reason_with_effect_proofs")
        .unwrap_or_else(|| panic!("missing certified Standard output validator"));
    let validator_rest = &lib_source[validator_start..];
    let validator_end = validator_rest
        .find("\nfn expression_proof_is_materialized_phi_copy")
        .unwrap_or_else(|| panic!("missing certified Standard output validator end marker"));
    let validator_body = &validator_rest[..validator_end];
    for forbidden in [
        "proof_counts.returns.max(render_facts.returns_by_op.len())",
        "raw_memory_proofs.max(render_facts.memory_accesses.len())",
    ] {
        assert!(
            !validator_body.contains(forbidden),
            "certified final-output validation must count emitted effect proofs, not global source facts: {forbidden:?}"
        );
    }
    for required in [
        "certified_control_transfer_residual_reason(func)",
        "CStmt::Break => Some(format!(",
        "CStmt::Continue => Some(format!(",
        "CStmt::Goto(label) => Some(format!(",
        "unproved switch case fallthrough",
        "unproved switch default fallthrough",
        "certified_stmt_list_is_terminal(&case.body)",
    ] {
        assert!(
            lib_source.contains(required),
            "certified final-output validation must reject unproved control transfers and switch fallthrough: {required:?}"
        );
    }
    for forbidden in [
        "if !certified_standard_mode || route_is_standard(&semantic_route)",
        "if certified_standard_mode {\n            fold_ctx.prune_duplicate",
        "if certified_standard_mode {\n            prune_dead_temp_assignments_in_function_body",
        "if certified_standard_mode {\n            let body = CStmt::Block(std::mem::take(&mut c_function.body));",
        "let appended_stack_return = if certified_standard_mode",
        "appended_stack_return && certified_standard_mode",
    ] {
        assert!(
            !render_body.contains(forbidden),
            "certified Standard render path must not mutate final AST after proof capture: {forbidden:?}"
        );
    }
    let params_start = lib_source
        .find("fn params_from_authorized_signature")
        .unwrap_or_else(|| panic!("missing params_from_authorized_signature"));
    let params_rest = &lib_source[params_start..];
    let params_end = params_rest
        .find("\nfn signature_has_complete_render_param_types")
        .unwrap_or_else(|| panic!("missing params_from_authorized_signature end marker"));
    let params_body = &params_rest[..params_end];
    assert!(
        !params_body.contains("CType::Unknown"),
        "certified render-authorized signature params must not silently materialize unknown C types"
    );

    assert!(
        !op_lower_source.contains("fn prune_duplicate_tail_call_statements"),
        "certified tail-call pruning deleted executable calls after proof capture and must stay removed"
    );
    assert!(
        !op_lower_source.contains("fn certified_unique_scalar_stack_return_expr"),
        "certified stack-return recovery is a renderer-side repair and must stay deleted"
    );
    let duplicate_start = op_lower_source
        .find("fn duplicate_pruning_source_for_call_expr")
        .unwrap_or_else(|| panic!("missing duplicate pruning helper"));
    let duplicate_rest = &op_lower_source[duplicate_start..];
    let duplicate_end = duplicate_rest
        .find("\n    fn collect_certified_rendered_call_sources_for_stmt")
        .unwrap_or_else(|| panic!("missing duplicate pruning helper end"));
    let duplicate_body = &duplicate_rest[..duplicate_end];
    assert!(
        duplicate_body.contains("self.requires_certified_rendering()")
            && duplicate_body.contains("None"),
        "duplicate-call pruning must fail closed in certified rendering"
    );
}

#[test]
fn r2plugin_does_not_expose_data_ref_cache_policy() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let c_path = root.join("r2plugin/r_anal_sleigh.c");
    let lib_path = root.join("r2plugin/src/lib.rs");
    let types_path = root.join("r2plugin/src/types.rs");
    let c_source = std::fs::read_to_string(&c_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", c_path.display()));
    let lib_source = std::fs::read_to_string(&lib_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", lib_path.display()));
    let types_source = std::fs::read_to_string(&types_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", types_path.display()));

    for forbidden in [
        "DataRefCacheEntry",
        "compute_xref_cache_key",
        "typed_data_refs_hash",
        "data_ref_cache_get",
        "data_ref_cache_put",
        "data_ref_cache_clear",
        "r2sleigh_data_ref_cache_",
        "xref_cache_hits",
        "xref_recomputes",
    ] {
        assert!(
            !c_source.contains(forbidden),
            "C plugin glue must not own data-ref/xref cache policy fragment {forbidden:?}"
        );
    }

    for (source_name, source) in [
        ("r2plugin/src/lib.rs", lib_source.as_str()),
        ("r2plugin/src/types.rs", types_source.as_str()),
    ] {
        for forbidden in [
            "pub extern \"C\" fn r2sleigh_data_ref_cache_",
            "r2sleigh_data_ref_cache_ffi",
            "data_ref_cache_key_ffi",
        ] {
            assert!(
                !source.contains(forbidden),
                "{source_name} must not expose data-ref cache policy ABI {forbidden:?}"
            );
        }
    }
}

#[test]
fn r2plugin_auto_callbacks_do_not_own_policy_in_c() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let path = root.join("r2plugin/r_anal_sleigh.c");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    let callback_start = source
        .find("radare2 Deep Integration Callbacks")
        .unwrap_or_else(|| panic!("missing deep integration callback section"));
    let callback_end = source[callback_start..]
        .find("\nRAnalPlugin r_anal_plugin_sleigh =")
        .map(|offset| callback_start + offset)
        .unwrap_or_else(|| panic!("missing callback section end"));
    let callbacks = &source[callback_start..callback_end];

    assert!(
        source.contains(concat!("r2sleigh_", "auto_callback_plan_for_depth")),
        "C callbacks must ask r2engine-owned auto-callback policy through FFI"
    );

    for forbidden in [
        concat!("#define SLEIGH_AUTO_", "CALLBACK_MAX_BLOCKS"),
        concat!("#define SLEIGH_AUTO_", "CALLBACK_MAX_COST"),
        concat!("#define SLEIGH_AUTO_", "CALLBACK_MAX_LINEAR_SIZE"),
        "static bool function_exceeds_auto_callback_budget",
        "static bool sleigh_mode_allows_deep_auto_callbacks",
    ] {
        assert!(
            !source.contains(forbidden),
            "plugin C must not own auto-callback policy fragment {forbidden:?}"
        );
    }

    for forbidden in [
        "sleigh_mode_allows_deep_auto_callbacks",
        "function_exceeds_auto_callback_budget",
        "bool auto_cost_exceeded",
    ] {
        assert!(
            !callbacks.contains(forbidden),
            "radare2 callback glue must consume engine auto-callback plans, not local policy {forbidden:?}"
        );
    }
}

#[test]
fn r2plugin_symbolic_scope_caps_are_engine_owned() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let path = root.join("r2plugin/r_anal_sleigh.c");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    assert!(
        source.contains(concat!("r2sleigh_", "symbolic_scope_function_plan")),
        "C symbolic scope builder must ask r2engine-owned function admission policy through FFI"
    );
    assert!(
        source.contains(concat!(
            "r2sleigh_",
            "runtime_materialized_source_plan"
        )),
        "C runtime-materialized source lifting must ask r2engine-owned cap policy through FFI"
    );

    for forbidden in [
        "#define SLEIGH_SYM_HELPER_MAX_FUNCTIONS",
        "#define SLEIGH_RUNTIME_MATERIALIZED_MAX_BYTES",
        "#define SLEIGH_RUNTIME_MATERIALIZED_SLOT_BYTES",
        "scope->count < SLEIGH_SYM_HELPER_MAX_FUNCTIONS",
        "scope_skip_budget",
    ] {
        assert!(
            !source.contains(forbidden),
            "plugin C must not own symbolic/interproc scope cap policy fragment {forbidden:?}"
        );
    }
}

#[test]
fn r2plugin_standalone_signature_and_semantic_compile_abis_stay_deleted() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let rust_path = root.join("r2plugin/src/lib.rs");
    let sym_path = root.join("r2plugin/src/analysis/sym.rs");
    let c_path = root.join("r2plugin/r_anal_sleigh.c");
    let e2e_path = root.join("tests/e2e/integration_tests.rs");
    let rust_source = std::fs::read_to_string(&rust_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", rust_path.display()));
    let sym_source = std::fs::read_to_string(&sym_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", sym_path.display()));
    let c_source = std::fs::read_to_string(&c_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", c_path.display()));
    let e2e_source = std::fs::read_to_string(&e2e_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", e2e_path.display()));

    for (source_name, source) in [
        ("r2plugin/src/lib.rs", rust_source.as_str()),
        ("r2plugin/src/analysis/sym.rs", sym_source.as_str()),
        ("r2plugin/r_anal_sleigh.c", c_source.as_str()),
        ("tests/e2e/integration_tests.rs", e2e_source.as_str()),
    ] {
        for forbidden in [
            "r2sleigh_infer_signature_cc_json",
            "r2sym_compile_semantics_scope",
            "infer_signature_cc_json_non_x86_allows_empty_callconv",
        ] {
            assert!(
                !source.contains(forbidden),
                "{source_name} must not retain standalone non-engine ABI {forbidden:?}"
            );
        }
    }
}

#[test]
fn r2plugin_session_debug_command_family_and_abi_stay_deleted() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let c_path = root.join("r2plugin/r_anal_sleigh.c");
    let rust_path = root.join("r2plugin/src/lib.rs");
    let doc_path = root.join("doc/plugin-rfe-2026.md");
    let c_source = std::fs::read_to_string(&c_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", c_path.display()));
    let rust_source = std::fs::read_to_string(&rust_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", rust_path.display()));
    let doc_source = std::fs::read_to_string(&doc_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", doc_path.display()));

    for forbidden in [
        "cmd_matches_exact_or_arg (cmd, \"sla.facts\")",
        "cmd_matches_exact_or_arg (cmd, \"sla.plan\")",
        "cmd_matches_exact_or_arg (cmd, \"sla.session\")",
        "strncmp (cmd, \"sla.facts\"",
        "strncmp (cmd, \"sla.plan\"",
        "strncmp (cmd, \"sla.session\"",
        "R2SleighSessionInput",
        "R2SleighSessionResult",
        "r2sleigh_session_analyze",
        "r2sleigh_session_result_report_json",
        "r2sleigh_session_result_free",
        "r2sleigh_session_interproc_summary_json",
        "sleigh_session_input_init",
        "sleigh_analyze_type_session",
        "SleighInterprocSeeds",
        "sleigh_interproc_seeds_",
        "build_type_interproc_scope",
        "collect_type_interproc_seed_names_from_scope",
    ] {
        assert!(
            !c_source.contains(forbidden),
            "C plugin must not retain deleted session/debug command ABI fragment {forbidden:?}"
        );
    }

    for forbidden in [
        "pub struct R2SleighSessionInput",
        "pub struct R2SleighSessionResult",
        "pub extern \"C\" fn r2sleigh_session_analyze",
        "pub extern \"C\" fn r2sleigh_session_result_report_json",
        "pub extern \"C\" fn r2sleigh_session_result_free",
        "pub extern \"C\" fn r2sleigh_session_interproc_summary_json",
        concat!("fn session_", "analysis_input"),
        "struct SessionAnalysisInput",
        "struct TypeWritebackInferenceInput",
        "struct FunctionAnalysisSharedBundle",
        "fn build_function_analysis_shared_bundle",
        "pub extern \"C\" fn r2sleigh_get_symbolic_scope_targets_json",
        "pub extern \"C\" fn r2sleigh_get_runtime_materialized_sources_json",
    ] {
        assert!(
            !rust_source.contains(forbidden),
            "Rust plugin must not retain deleted session/debug ABI fragment {forbidden:?}"
        );
    }

    for forbidden in ["`a:sla.facts`", "`a:sla.facts.json`", "`a:sla.plan`"] {
        assert!(
            !doc_source.contains(forbidden),
            "docs must not advertise deleted command {forbidden:?}"
        );
    }
}

#[test]
fn r2plugin_legacy_debug_command_redirects_stay_deleted() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let c_path = root.join("r2plugin/r_anal_sleigh.c");
    let r2r_path = root.join("tests/r2r/db/extras/r2sleigh_integration_extended");
    let c_source = std::fs::read_to_string(&c_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", c_path.display()));
    let r2r_source = std::fs::read_to_string(&r2r_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", r2r_path.display()));

    for required in [
        "static bool sleigh_direct_sla_debug_only_command",
        "static bool sleigh_direct_sym_debug_only_command",
        "sleigh_direct_sla_debug_only_command (cmd)",
        "sleigh_direct_sym_debug_only_command (cmd)",
    ] {
        assert!(
            c_source.contains(required),
            "plugin must gate debug-only direct command spelling with {required:?}"
        );
    }
    for forbidden in [
        "sleigh_legacy_debug_replacement",
        "sleigh_legacy_sym_debug_replacement",
        "command moved to",
        "moved to a:sla.debug",
        "moved to a:sym.debug",
        "return \"a:sla.debug.",
        "return \"a:sym.debug.",
    ] {
        assert!(
            !c_source.contains(forbidden),
            "plugin must not retain legacy debug command redirect {forbidden:?}"
        );
        assert!(
            !r2r_source.contains(forbidden),
            "r2r must not preserve legacy debug redirect oracle {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_param_aliases_require_functionfacts_bindings() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let lib_path = root.join("crates/r2dec/src/lib.rs");
    let stack_path = root.join("crates/r2dec/src/fold/stack.rs");
    let lib_source = std::fs::read_to_string(&lib_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", lib_path.display()));
    let stack_source = std::fs::read_to_string(&stack_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", stack_path.display()));

    let marker = "fn build_param_register_aliases";
    let start = lib_source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", lib_path.display()));
    let rest = &lib_source[start..];
    let end = rest
        .find("/// Decompiler configuration.")
        .unwrap_or_else(|| panic!("missing decompiler config after {marker}"));
    let alias_builder = &rest[..end];
    for required in [
        "allow_positional_aliases: bool",
        "if allow_positional_aliases",
        "for (idx, reg_name) in abi_arg_regs.iter().enumerate()",
        "for (idx, (ssa_var, _)) in recovered_params.iter().enumerate()",
        "for (idx, reg_param) in register_params.iter().enumerate()",
    ] {
        assert!(
            alias_builder.contains(required),
            "param alias builder must make positional aliases explicitly non-certified: {required:?}"
        );
    }

    let production_call = lib_source
        .find("let param_register_aliases = build_param_register_aliases(")
        .unwrap_or_else(|| panic!("missing production build_param_register_aliases call"));
    let call_rest = &lib_source[production_call..];
    let call_end = call_rest
        .find(");")
        .unwrap_or_else(|| panic!("missing end of production build_param_register_aliases call"));
    let call = &call_rest[..call_end];
    assert!(
        call.contains("!certified_standard_mode"),
        "certified Standard rendering must disable ABI/recovered positional param aliases"
    );

    let stack_marker = "pub(super) fn arg_alias_for_register_name";
    let stack_start = stack_source
        .find(stack_marker)
        .unwrap_or_else(|| panic!("missing {stack_marker} in {}", stack_path.display()));
    let stack_rest = &stack_source[stack_start..];
    let stack_end = stack_rest
        .find("pub(super) fn arg_alias_for_rendered_name")
        .unwrap_or_else(|| panic!("missing arg_alias_for_rendered_name after {stack_marker}"));
    let stack_body = &stack_rest[..stack_end];
    let certified_at = stack_body
        .find("if self.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("arg alias lookup must check certified rendering"));
    let fallback_at = stack_body
        .find("self.inputs.arch.arg_alias_for_register_name(reg_name)")
        .unwrap_or_else(|| panic!("missing non-certified architecture arg alias fallback"));
    assert!(
        certified_at < fallback_at,
        "certified rendering must refuse before architecture argN fallback"
    );
}

#[test]
fn r2dec_certified_structuring_skips_slot_merge_return_repair() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/structure.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    let marker = "Region::IfThenElse";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("Region::WhileLoop")
        .unwrap_or_else(|| panic!("missing Region::WhileLoop after {marker}"));
    let if_then_else = &rest[..end];
    let non_certified_at = if_then_else
        .find("if !self.fold_ctx.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("if/else structuring must have a non-certified repair block"));
    let slot_repair_at = if_then_else
        .find("self.try_structure_if_else_with_slot_merge_returns")
        .unwrap_or_else(|| panic!("missing slot-merge return repair call"));
    let register_repair_at = if_then_else
        .find("self.try_structure_if_else_with_register_merge_returns")
        .unwrap_or_else(|| panic!("missing register-merge return repair call"));
    assert!(
        non_certified_at < slot_repair_at && slot_repair_at < register_repair_at,
        "slot-merge return repair must be gated before certified structuring reaches register/FunctionFacts paths"
    );
    let before_slot = &if_then_else[non_certified_at..slot_repair_at];
    assert!(
        before_slot.contains("try_structure_symbolic_actionable_if"),
        "slot-merge return repair must stay inside the non-certified local repair block"
    );
    let register_marker = "if let Some(rewritten) = self.try_structure_if_else_with_register_merge_returns";
    let non_certified_block_end = if_then_else[non_certified_at..]
        .find(register_marker)
        .map(|offset| non_certified_at + offset)
        .unwrap_or_else(|| panic!("missing register-merge call after non-certified block"));
    let non_certified_block = &if_then_else[non_certified_at..non_certified_block_end];
    assert!(
        non_certified_block.contains("self.try_structure_if_else_with_slot_merge_returns"),
        "slot-merge return repair must be textually inside the non-certified repair block"
    );
    let between_slot_and_register = &if_then_else[slot_repair_at..register_repair_at];
    assert!(
        between_slot_and_register.contains("return rewritten"),
        "slot-merge return repair must not fall through into certified structuring after rewriting"
    );

    let slot_fn_start = source
        .find("fn try_structure_if_else_with_slot_merge_returns")
        .unwrap_or_else(|| panic!("missing try_structure_if_else_with_slot_merge_returns"));
    let slot_fn_rest = &source[slot_fn_start..];
    let slot_fn_end = slot_fn_rest
        .find("fn try_structure_if_else_with_register_merge_returns")
        .unwrap_or_else(|| panic!("missing register merge function after slot merge function"));
    let slot_fn = &slot_fn_rest[..slot_fn_end];
    let certified_refusal_at = slot_fn
        .find("if self.fold_ctx.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("slot-merge return repair must defensively refuse certified mode"));
    let frame_slot_at = slot_fn
        .find(".frame_slot_merges_map()")
        .unwrap_or_else(|| panic!("slot-merge return repair must read frame_slot_merges_map"));
    assert!(
        certified_refusal_at < frame_slot_at,
        "slot-merge return repair must refuse certified mode before reading local frame-slot merge data"
    );
    for forbidden in [
        "self.certified_branch_render_proof",
        "self.control_render_proofs.push",
        "record_return_value_render_proof",
    ] {
        assert!(
            !slot_fn.contains(forbidden),
            "slot-merge return repair must not mint certified proof state: {forbidden:?}"
        );
    }

    let append_start = source
        .find("fn append_merged_slot_return_if_needed")
        .unwrap_or_else(|| panic!("missing append_merged_slot_return_if_needed"));
    let append_rest = &source[append_start..];
    let append_end = append_rest
        .find("fn has_merged_slot_return_expr")
        .unwrap_or_else(|| panic!("missing has_merged_slot_return_expr after append helper"));
    let append_body = &append_rest[..append_end];
    let append_certified_at = append_body
        .find("if self.fold_ctx.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("append_merged_slot_return_if_needed must refuse certified mode"));
    let append_return_at = append_body
        .find("CStmt::Return(Some(expr))")
        .unwrap_or_else(|| panic!("append_merged_slot_return_if_needed must append return in non-certified mode"));
    assert!(
        append_certified_at < append_return_at,
        "slot merge append helper must refuse certified mode before constructing executable returns"
    );

    let rewrite_start = source
        .find("fn rewrite_trailing_return_with_merged_expr")
        .unwrap_or_else(|| panic!("missing rewrite_trailing_return_with_merged_expr"));
    let rewrite_body = &source[rewrite_start..];
    let residual_at = rewrite_body
        .find("r2sleigh residual: unresolved value return for control-only exit")
        .unwrap_or_else(|| panic!("missing residual return rewrite branch"));
    let guard_at = rewrite_body[..residual_at]
        .rfind("!self.fold_ctx.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("residual-comment-to-return rewrite must be non-certified only"));
    assert!(
        guard_at < residual_at,
        "residual comments must not be rewritten into executable returns in certified mode"
    );
}

#[test]
fn r2dec_certified_switch_selector_uses_render_facts_only() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let marker = "fn resolve_switch_expr_from_control_facts";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("fn refine_switch_selector_expr")
        .unwrap_or_else(|| panic!("missing refine_switch_selector_expr after {marker}"));
    let body = &rest[..end];
    let certified_at = body
        .find("if self.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("{marker} must branch for certified rendering"));
    let local_at = body[certified_at..]
        .find("let rooted = self")
        .map(|offset| certified_at + offset)
        .unwrap_or_else(|| panic!("{marker} must keep local selector rendering after certified branch"));
    let certified_branch = &body[certified_at..local_at];

    assert!(
        certified_branch.contains("render_certified_value_expr_for_var(selector)"),
        "certified switch selector rendering must use FunctionRenderFacts value proof"
    );
    for forbidden in [
        "semanticize_visible_expr",
        "refine_switch_selector_expr",
        "resolve_predicate_operand",
        "switch_selector_roots_map",
        "prepared_semantic_view",
        "best_visible_definition",
        "call_result_source_for_ssa_name",
        "local_post_call_source_for_ssa_name",
    ] {
        assert!(
            !certified_branch.contains(forbidden),
            "certified switch selector rendering must not use local/prepared fallback {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_if_rendering_uses_branch_render_proof_gate() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/structure.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    for required in [
        "fn certified_branch_render_proof",
        "predicate.comparison.is_some()",
        "Some(predicate.id) == proof.branch_condition",
        "Some(predicate.condition) == proof.branch_condition_value",
        "self.certified_branch_render_proof(*cond_block, predicate, condition_value)",
        "self.certified_branch_render_proof(cond_block, predicate, condition_value)?",
    ] {
        assert!(
            source.contains(required),
            "certified if rendering must require branch proof gate {required:?}"
        );
    }
}

#[test]
fn r2dec_certified_final_return_normalization_does_not_recover_local_semantics() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let marker = "pub(crate) fn normalize_final_stmt_calls";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("missing {marker} in {}", path.display()));
    let rest = &source[start..];
    let end = rest
        .find("fn normalize_final_stmt_expr")
        .unwrap_or_else(|| panic!("missing normalize_final_stmt_expr after {marker}"));
    let body = &rest[..end];
    let return_at = body
        .find("CStmt::Return(expr)")
        .unwrap_or_else(|| panic!("{marker} must handle return statements"));
    let other_at = body[return_at..]
        .find("other => other")
        .map(|offset| return_at + offset)
        .unwrap_or(body.len());
    let return_arm = &body[return_at..other_at];
    let certified_at = return_arm
        .find("if self.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("return arm must branch for certified rendering"));
    let legacy_at = return_arm[certified_at..]
        .find("normalize_final_return_expr_candidate(expr)")
        .map(|offset| certified_at + offset)
        .unwrap_or_else(|| panic!("return arm must keep legacy return normalization after certified branch"));
    let certified_branch = &return_arm[certified_at..legacy_at];

    for forbidden in [
        "normalize_final_return_expr_candidate",
        "normalize_final_call_expr",
        "resolve_return_candidate",
        "semanticize_visible_expr",
        "best_visible_definition",
        "lookup_definition",
    ] {
        assert!(
            !certified_branch.contains(forbidden),
            "certified final return normalization must not use local semantic fallback {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_raw_carrier_definition_recovery_stays_deleted() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/return_resolver.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    for forbidden in [
        "certified_raw_carrier_definition",
        "format!(\"{}_{}\", base.to_ascii_uppercase(), version)",
    ] {
        assert!(
            !source.contains(forbidden),
            "certified raw-carrier definition recovery must stay deleted: {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_rendering_does_not_materialize_raw_carrier_locals() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/lib.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    for forbidden in [
        "materialize_certified_raw_carrier_locals",
        "fn collect_raw_carrier_assignment_names",
        "fn collect_raw_carrier_read_names",
        "fn rewrite_certified_raw_carrier_",
        "fn certified_raw_carrier_type",
        "format!(\"value_{index}\")",
    ] {
        assert!(
            !source.contains(forbidden),
            "certified rendering must not synthesize raw-carrier C locals via {forbidden:?}"
        );
    }

    assert!(
        source.contains("lower.starts_with(\"value_\")"),
        "generated carrier names must remain uncertified render artifacts"
    );
}

#[test]
fn r2dec_certified_call_result_materialization_uses_functionfacts_owner_only() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    fn extract<'a>(source: &'a str, marker: &str, end_marker: &str) -> &'a str {
        let start = source
            .find(marker)
            .unwrap_or_else(|| panic!("missing {marker}"));
        let rest = &source[start..];
        let end = rest
            .find(end_marker)
            .unwrap_or_else(|| panic!("missing {end_marker} after {marker}"));
        &rest[..end]
    }

    let materialize = extract(
        &source,
        "pub(crate) fn should_materialize_call_result_at_source",
        "fn should_skip_unused_transient_call_result_owner",
    );
    let certified_at = materialize
        .find("if self.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("call-result materialization must branch for certified mode"));
    let local_at = materialize
        .find("let owner_name = self.stable_owned_call_result_name_for_source(source_call)?;")
        .unwrap_or_else(|| panic!("missing non-certified owner-name path"));
    let certified_branch = &materialize[certified_at..local_at];
    assert!(
        certified_branch
            .contains("return self.certified_assigned_call_result_owner_expr_for_source(source_call);"),
        "certified call-result materialization must delegate to the FunctionFacts owner gate"
    );
    for forbidden in [
        "call_result_aliases_map",
        "direct_call_result_aliases_set",
        "source_call_allows_return_register_owner",
        "call_result_candidate_names_have_observable_use",
        "stack_slot_provenance_for_name",
        "stack_offset_for_visible_storage_name",
    ] {
        assert!(
            !certified_branch.contains(forbidden),
            "certified call-result materialization must not use local fallback policy {forbidden:?}"
        );
    }

    let certified_owner_gate = extract(
        &source,
        "fn certified_assigned_call_result_owner_expr_for_source",
        "fn certified_call_result_owner_name_for_source",
    );
    for required in [
        "self.inputs.call_render_facts",
        "fact_for_site(callsite)",
        "CallsiteRenderDisposition::AssignedResult",
        "self.certified_call_result_owner_expr_for_source(source_call)",
    ] {
        assert!(
            certified_owner_gate.contains(required),
            "certified assigned call-result owner gate must require {required:?}"
        );
    }
    for forbidden in [
        "call_result_aliases_map",
        "direct_call_result_aliases_set",
        "prepared_semantic_view",
        "ownership()",
        "use_info()",
        "local_post_call_source",
    ] {
        assert!(
            !certified_owner_gate.contains(forbidden),
            "certified assigned call-result owner gate must not use {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_call_result_owner_lookups_bypass_local_ownership_tables() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    fn extract<'a>(source: &'a str, marker: &str, end_marker: &str) -> &'a str {
        let start = source
            .find(marker)
            .unwrap_or_else(|| panic!("missing {marker}"));
        let rest = &source[start..];
        let end = rest
            .find(end_marker)
            .unwrap_or_else(|| panic!("missing {end_marker} after {marker}"));
        &rest[..end]
    }

    let source_lookup = extract(
        &source,
        "pub(super) fn materialized_call_result_source_for_visible_name",
        "fn certified_materialized_call_result_source_for_visible_name",
    );
    let certified_at = source_lookup
        .find("if self.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("visible owner source lookup must branch for certified mode"));
    let local_at = source_lookup
        .find("let resolved_name = self")
        .unwrap_or_else(|| panic!("missing non-certified visible-name lookup path"));
    assert!(
        source_lookup[certified_at..local_at]
            .contains("return self.certified_materialized_call_result_source_for_visible_name(name);"),
        "certified visible owner source lookup must bypass local ownership tables"
    );

    let certified_source_lookup = extract(
        &source,
        "fn certified_materialized_call_result_source_for_visible_name",
        "pub(crate) fn call_result_source_for_ssa_name",
    );
    for required in [
        "self.inputs.call_result_facts",
        "facts.by_callsite.keys()",
        "certified_assigned_call_result_owner_expr_for_source(source_call)",
    ] {
        assert!(
            certified_source_lookup.contains(required),
            "certified visible owner lookup must use canonical source {required:?}"
        );
    }
    for forbidden in [
        "self.ownership()",
        "source_for_visible_owner_name",
        "call_result_source_for_ssa_name",
        "prepared_semantic_view",
        "use_info()",
    ] {
        assert!(
            !certified_source_lookup.contains(forbidden),
            "certified visible owner lookup must not use local/prepared source {forbidden:?}"
        );
    }

    let source_name_lookup = extract(
        &source,
        "pub(crate) fn call_result_source_for_ssa_name",
        "pub(super) fn local_post_call_source_for_ssa_name",
    );
    let certified_at = source_name_lookup
        .find("if self.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("SSA-name source lookup must branch for certified mode"));
    let local_at = source_name_lookup
        .find("let source_call = self")
        .unwrap_or_else(|| panic!("missing non-certified source lookup path"));
    let certified_branch = &source_name_lookup[certified_at..local_at];
    assert!(
        certified_branch.contains("return self.certified_call_result_source_for_ssa_name(ssa_name);"),
        "certified SSA-name source lookup must delegate before local source discovery"
    );
    for forbidden in [
        "self.ownership()",
        "source_for_alias",
        "self.use_info()",
        "call_result_source_for_name",
        "prepared_semantic_view",
        "find_ssa_name_for_rendered_alias",
    ] {
        assert!(
            !certified_branch.contains(forbidden),
            "certified SSA-name source lookup must not use local/prepared source {forbidden:?}"
        );
    }

    let certified_expr_lookup = extract(
        &source,
        "fn certified_stable_owned_call_result_expr_for_name",
        "fn certified_call_result_source_for_stack_owner_alias",
    );
    for required in [
        "certified_call_result_fact_for_name(name)",
        "self.certified_call_result_owner_expr_for_source(source_call)",
    ] {
        assert!(
            certified_expr_lookup.contains(required),
            "certified owner expression lookup must require canonical fact {required:?}"
        );
    }
    for forbidden in [
        "direct_call_result_aliases_set",
        "call_result_alias_has_stack_owner_provenance",
        "local_post_call_source_for_ssa_name",
        "certified_call_result_source_for_stack_owner_alias",
        "self.ownership()",
        "prepared_semantic_view",
        "use_info()",
    ] {
        assert!(
            !certified_expr_lookup.contains(forbidden),
            "certified owner expression lookup must not use local/prepared source {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_call_result_register_owner_fallbacks_stay_fail_closed() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    fn extract<'a>(source: &'a str, marker: &str, end_marker: &str) -> &'a str {
        let start = source
            .find(marker)
            .unwrap_or_else(|| panic!("missing {marker}"));
        let rest = &source[start..];
        let end = rest
            .find(end_marker)
            .unwrap_or_else(|| panic!("missing {end_marker} after {marker}"));
        &rest[..end]
    }

    for forbidden in [
        "fn fallback_owned_call_result_register_name_for_alias",
        "fn fallback_owned_call_result_return_name_for_alias",
    ] {
        assert!(
            !source.contains(forbidden),
            "renderer-local register alias owner fallback must stay deleted: {forbidden:?}"
        );
    }

    let fallback_source = extract(
        &source,
        "fn fallback_owned_call_result_return_name_for_source",
        "pub(crate) fn stable_owned_call_result_name_for_source",
    );
    assert!(
        fallback_source.contains("None"),
        "fallback_owned_call_result_return_name_for_source must fail closed until FunctionFacts carries explicit owner evidence"
    );
    for forbidden in [
        "is_register_like_base_name",
        "is_return_register_name",
        "rendered_visible_name_for_ssa_name",
        "direct_call_result_aliases_set",
        "source_call_allows_return_register_owner",
    ] {
        assert!(
            !fallback_source.contains(forbidden),
            "return-register call-result owner fallback must not infer ownership from local aliases: {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_stack_home_store_suppression_uses_value_owner_fact_only() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    fn extract<'a>(source: &'a str, marker: &str, end_marker: &str) -> &'a str {
        let start = source
            .find(marker)
            .unwrap_or_else(|| panic!("missing {marker}"));
        let rest = &source[start..];
        let end = rest
            .find(end_marker)
            .unwrap_or_else(|| panic!("missing {end_marker} after {marker}"));
        &rest[..end]
    }

    let wrapper = extract(
        &source,
        "fn is_materialized_call_result_stack_home_store",
        "fn is_certified_materialized_call_result_stack_home_store",
    );
    let certified_at = wrapper
        .find("if self.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("stack-home store suppression must branch for certified mode"));
    let local_at = wrapper
        .find("let Some(offset) = self")
        .unwrap_or_else(|| panic!("missing non-certified stack-home suppression path"));
    assert!(
        wrapper[certified_at..local_at]
            .contains("return self.is_certified_materialized_call_result_stack_home_store(addr, val);"),
        "certified stack-home suppression must bypass local source recovery"
    );

    let certified = extract(
        &source,
        "fn is_certified_materialized_call_result_stack_home_store",
        "fn op_to_stmt_impl",
    );
    for required in [
        "self.prepared_value_id_for_var(val)",
        "self.certified_call_result_fact_for_value(value)",
        "facts.owner_for_value(value)",
        "ValueOwner::StackSlot",
        "*owner_offset != offset",
        "self.certified_assigned_call_result_owner_expr_for_source(source_call)",
    ] {
        assert!(
            certified.contains(required),
            "certified stack-home suppression must require canonical proof {required:?}"
        );
    }
    for forbidden in [
        "raw_local_post_call_source_for_ssa_name_in_block",
        "local_post_call_source_for_ssa_name",
        "call_result_source_for_ssa_name",
        "has_certified_call_result_owner_fact_for_source",
        "stable_owned_call_result_name_for_source",
        "resolve_stack_var",
        "visible_names_share_stack_slot",
        "stack_offset_for_visible_storage_name(&owner_name)",
    ] {
        assert!(
            !certified.contains(forbidden),
            "certified stack-home suppression must not use local fallback {forbidden:?}"
        );
    }
}

#[test]
fn r2dec_certified_semanticize_visible_expr_uses_certified_helper_only() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2dec/src/fold/op_lower/mod.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    fn extract<'a>(source: &'a str, marker: &str, end_marker: &str) -> &'a str {
        let start = source
            .find(marker)
            .unwrap_or_else(|| panic!("missing {marker}"));
        let rest = &source[start..];
        let end = rest
            .find(end_marker)
            .unwrap_or_else(|| panic!("missing {end_marker} after {marker}"));
        &rest[..end]
    }

    let semanticize = extract(
        &source,
        "fn semanticize_visible_expr",
        "fn certified_semanticize_visible_expr",
    );
    let certified_at = semanticize
        .find("if self.requires_certified_rendering()")
        .unwrap_or_else(|| panic!("semanticize_visible_expr must branch for certified mode"));
    let local_at = semanticize
        .find("if depth > Self::MAX_SEMANTIC_RENDER_DEPTH")
        .unwrap_or_else(|| panic!("missing non-certified semanticization path"));
    assert!(
        semanticize[certified_at..local_at]
            .contains("return self.certified_semanticize_visible_expr(expr, depth, visited);"),
        "certified semanticization must bypass local semanticization before any local lookup"
    );

    let certified = extract(
        &source,
        "fn certified_semanticize_visible_expr",
        "fn canonicalize_visible_address_expr",
    );
    for required in [
        "certified_semanticized_var_expr",
        "stable_owned_call_result_expr_for_name",
        "render_certified_value_expr_for_var",
        "certified_prepared_var_for_visible_name",
    ] {
        assert!(
            certified.contains(required),
            "certified semanticization must use canonical helper {required:?}"
        );
    }
    for forbidden in [
        "render_semantic_value_by_name",
        "lookup_definition_raw",
        "render_memory_access_from_visible_expr",
        "render_exact_member_from_raw_subscript",
        "semantic_deref_candidate_for_name",
        "call_result_exprs_map",
        "synthesized_call_expr_for_source_call",
        "find_ssa_name_for_rendered_alias",
    ] {
        assert!(
            !certified.contains(forbidden),
            "certified semanticization must not use local semantic/render fallback {forbidden:?}"
        );
    }
}

#[test]
fn function_facts_spine_fields_stay_private() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let facts_path = root.join("crates/r2types/src/function_facts.rs");
    let facts_source = std::fs::read_to_string(&facts_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", facts_path.display()));
    let start = facts_source
        .find("pub struct FunctionFacts")
        .expect("missing FunctionFacts");
    let rest = &facts_source[start..];
    let end = rest
        .find("\n}\n\nimpl FunctionFacts")
        .expect("missing FunctionFacts body end");
    let body = &rest[..end];
    for forbidden in [
        "pub types:",
        "pub semantics:",
        "pub proof:",
        "pub decompile_route:",
        "pub input_quality:",
        "pub control:",
        "pub render:",
        "pub summary_view:",
        "pub assumption_usage:",
    ] {
        assert!(
            !body.contains(forbidden),
            "FunctionFacts spine field must stay private: {forbidden}"
        );
    }
    let attach_start = facts_source
        .find("pub fn attach_prepared_decompile_evidence")
        .expect("missing attach_prepared_decompile_evidence");
    let attach_rest = &facts_source[attach_start..];
    let attach_end = attach_rest
        .find("\n    pub fn interproc_summary_set")
        .expect("missing attach_prepared_decompile_evidence end marker");
    let attach_body = &attach_rest[..attach_end];
    for required in [
        "merge_callee_resolution_facts(",
        "merge_callsite_facts(",
        "merge_call_result_facts(",
        "merge_call_render_facts(",
        "merge_control_facts(",
        "merge_render_facts(",
    ] {
        assert!(
            attach_body.contains(required),
            "prepared decompile evidence must merge into FunctionFacts instead of replacing existing canonical facts: {required}"
        );
    }
    for forbidden in [
        "self.callee_resolution = prepared_callee_resolution_facts",
        "self.callsites = prepared_callsite_argument_facts",
        "self.call_results = prepared_call_result_facts",
        "self.call_render = prepared_call_render_facts",
        "self.control = prepared_control_facts",
        "self.render = prepared_render_facts",
    ] {
        assert!(
            !attach_body.contains(forbidden),
            "prepared evidence attachment must not overwrite existing FunctionFacts groups: {forbidden}"
        );
    }

    let r2dec_path = root.join("crates/r2dec/src/lib.rs");
    let r2dec_source = std::fs::read_to_string(&r2dec_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", r2dec_path.display()));
    for forbidden in [
        "pub function_facts: FunctionFacts",
        "pub context: DecompilerContext",
        "pub fn render_semantic_worker_linearization(",
    ] {
        assert!(
            !r2dec_source.contains(forbidden),
            "r2dec must not expose mutable decompile spine state: {forbidden}"
        );
    }
    for required in [
        "pub fn function_facts(&self) -> &FunctionFacts",
        "pub fn context(&self) -> &DecompilerContext",
    ] {
        assert!(
            r2dec_source.contains(required),
            "r2dec must expose read-only spine accessor: {required}"
        );
    }
}

#[test]
fn standard_certified_c_requires_executable_proof_not_just_easy_control() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .join("crates/r2sym/src/semantics/claims.rs");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let start = source
        .find("pub fn standard_control_render_permission")
        .expect("missing standard_control_render_permission");
    let rest = &source[start..];
    let end = rest
        .find("\n    }\n}\n\nfn proof_owner_from_label")
        .expect("missing standard_control_render_permission end");
    let body = &rest[..end];
    for required in [
        "self.certified_signatures == 0",
        "self.certified_returns == 0",
        "self.certified_expressions == 0",
        "self.certified_memory_accesses == 0",
        "self.certified_callsites == 0",
        "uncertified Standard executable rendering",
    ] {
        assert!(
            body.contains(required),
            "CertifiedC gate must require executable proof condition: {required}"
        );
    }
    assert!(
        !body.contains("standard route has no structured-control proof obligations"),
        "Standard CertifiedC must not be granted only because CFG has no loop/switch obligations"
    );
}
