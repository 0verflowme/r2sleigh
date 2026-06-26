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
    /// Warns when production `r2dec` builds `CalleeResolutionFacts` internally.
    ///
    /// ### Why is this bad?
    ///
    /// Callee resolution is an engine/type-system contract. If the decompiler
    /// reconstructs it from prepared callsites and raw maps, rendering becomes a
    /// second owner for call identity and can silently turn missing engine facts
    /// into confident callee policy.
    ///
    /// ### Example
    ///
    /// ```rust
    /// CalleeResolutionFacts::from_direct_call_targets(targets, &ctx);
    /// ```
    ///
    /// Pass the engine-owned `CalleeResolutionFacts` through
    /// `DecompilerContext::with_callee_resolution()` instead.
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
    /// Use instead an `r2engine::EngineSemanticRoutePlan`, converting it to the
    /// decompiler route enum only at the render boundary.
    pub R2DEC_ROUTE_POLICY_OWNERSHIP,
    Warn,
    "r2dec must consume engine route decisions, not own route/refusal policy"
);

rustc_session::declare_lint!(
    /// ### What it does
    ///
    /// Warns when `r2engine` applies decompile route or render permission by
    /// filling legacy `r2dec::DecompilerContext` side-channel fields.
    ///
    /// ### Why is this bad?
    ///
    /// The decompile spine is `FunctionFacts`. Engine-owned route, refusal,
    /// proof coverage, and render permission must travel through
    /// `FunctionFacts::decompile_route`; otherwise plugin/decompiler callers
    /// can observe different policy depending on which side channel was set.
    ///
    /// ### Example
    ///
    /// ```rust
    /// context.with_semantic_route(Some(route));
    /// context.with_render_permission(Some(permission));
    /// ```
    ///
    /// Use instead `FunctionFacts::set_decompile_route(...)`.
    pub R2ENGINE_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
    Warn,
    "r2engine must carry decompile route decisions through FunctionFacts"
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
    /// Warns when production `r2plugin` code directly reconstructs type
    /// signature writeback authority instead of consuming a typed `r2types`
    /// decision.
    ///
    /// ### Why is this bad?
    ///
    /// Signature certificates, source authority, and stale-certificate refusal
    /// are type-system policy. Keeping that logic in plugin glue creates a
    /// second owner and lets FFI code decide which type facts are authoritative.
    ///
    /// ### Example
    ///
    /// ```rust
    /// certificate.authorizes_signature_writeback();
    /// "signature mutation refused: ...";
    /// ```
    ///
    /// Use instead `r2types::signature_writeback_decision()` and serialize the
    /// resulting typed authority report.
    pub R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
    Warn,
    "r2plugin must not inspect signature certificates to decide writeback authority"
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
    /// Warns when production `r2plugin` code constructs
    /// `r2dec::VariableRecovery` directly.
    ///
    /// ### Why is this bad?
    ///
    /// Variable recovery feeds signature, callconv, and type writeback facts.
    /// Those are engine/type-system contracts, not plugin glue policy. If the
    /// plugin constructs the renderer's variable recovery directly, it becomes
    /// a second owner for recovered signature evidence.
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
    "r2plugin must not construct r2dec::VariableRecovery; r2engine owns recovered signature evidence"
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
    /// Use instead `decompiler_input_from_artifact(...)` and
    /// `Decompiler::decompile_input(...)`.
    pub R2PLUGIN_UNPREPARED_DECOMPILE_ORACLE,
    Warn,
    "r2plugin artifact render tests must use DecompilerInput, not raw SSAFunction decompile"
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
    R2DEC_SUMMARY_ROUTE_EXECUTABLE_C,
    R2DEC_ROUTE_POLICY_OWNERSHIP,
    R2ENGINE_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
    R2DEC_SWITCH_CASE_VALUE_OWNERSHIP,
    R2DEC_CALL_RESULT_STACK_OWNER_FALLBACK,
    R2DEC_CALL_RESULT_SOURCE_EXPR_OWNER_FALLBACK,
    R2PLUGIN_RAW_DIRECT_CALL_TARGET,
    R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
    R2PLUGIN_TYPE_WRITEBACK_APPLY_THRESHOLD_OWNERSHIP,
    R2PLUGIN_RENDERER_CONFIG_ARCH_TARGET_OWNERSHIP,
    R2PLUGIN_VARIABLE_RECOVERY_OWNERSHIP,
    R2PLUGIN_METADATA_TYPE_HINT_OWNERSHIP,
    R2PLUGIN_ENGINE_POLICY_OWNERSHIP,
    R2PLUGIN_UNPREPARED_DECOMPILE_ORACLE,
    R2DEC_SOURCE_SHAPED_DECOMPILE_ORACLE,
    R2DEC_DEFAULT_TRUE_BRANCH_CONDITION,
    R2TYPES_ROLE_NAME_SIGNATURE_HINT_OWNERSHIP
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
        R2DEC_SUMMARY_ROUTE_EXECUTABLE_C,
        R2DEC_ROUTE_POLICY_OWNERSHIP,
        R2ENGINE_DECOMPILER_CONTEXT_ROUTE_SIDE_CHANNEL,
        R2DEC_SWITCH_CASE_VALUE_OWNERSHIP,
        R2DEC_CALL_RESULT_STACK_OWNER_FALLBACK,
        R2DEC_CALL_RESULT_SOURCE_EXPR_OWNER_FALLBACK,
        R2PLUGIN_RAW_DIRECT_CALL_TARGET,
        R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
        R2PLUGIN_TYPE_WRITEBACK_APPLY_THRESHOLD_OWNERSHIP,
        R2PLUGIN_RENDERER_CONFIG_ARCH_TARGET_OWNERSHIP,
        R2PLUGIN_VARIABLE_RECOVERY_OWNERSHIP,
        R2PLUGIN_METADATA_TYPE_HINT_OWNERSHIP,
        R2PLUGIN_ENGINE_POLICY_OWNERSHIP,
        R2PLUGIN_UNPREPARED_DECOMPILE_ORACLE,
        R2DEC_SOURCE_SHAPED_DECOMPILE_ORACLE,
        R2DEC_DEFAULT_TRUE_BRANCH_CONDITION,
        R2TYPES_ROLE_NAME_SIGNATURE_HINT_OWNERSHIP,
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

        if is_r2dec_span(cx, item.span) && r2dec_source_shaped_decompile_oracle_item(cx, item) {
            span_lint(
                cx,
                R2DEC_SOURCE_SHAPED_DECOMPILE_ORACLE,
                item.span,
                "r2dec tests must prove fold/AST/certificate invariants instead of source-shaped raw decompile text",
            );
        }
    }

    fn check_impl_item(&mut self, cx: &LateContext<'tcx>, item: &'tcx ImplItem<'tcx>) {
        if is_r2dec_span(cx, item.span) && r2dec_switch_case_value_ownership_item(cx, item.span) {
            span_lint(
                cx,
                R2DEC_SWITCH_CASE_VALUE_OWNERSHIP,
                item.span,
                "r2dec must not define switch case display-bias helpers; canonical switch facts own case values",
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
    }

    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        if is_canonical_ssa_var_classifier(cx, expr) {
            return;
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
                "source_var_name is only a hint; call-argument rendering needs source_value_id, source_call, or prepared semantic authority",
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

        if is_r2plugin_path(cx, expr)
            && !is_inside_test_item(cx, expr)
            && plugin_type_writeback_policy_expr(expr)
        {
            span_lint(
                cx,
                R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
                expr.span,
                "r2plugin must not inspect signature certificates to decide writeback authority; consume the r2types authority result",
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
                "r2plugin tests must render prepared artifacts through DecompilerInput",
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

fn plugin_type_writeback_policy_expr(expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::MethodCall(method, _, _, _) => {
            matches!(
                method.ident.as_str(),
                "authorizes_signature_writeback" | "render_authorized_signature"
            )
        }
        ExprKind::Call(callee, _) => {
            [
                "signature_writeback_decision",
                "type_writeback_mutation_plan",
                "type_writeback_mutation_plan_with_policy",
            ]
            .iter()
            .any(|name| expr_path_last_segment_is(callee, name))
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
    if !expr_path_last_segment_is(callee, "new") && !expr_path_last_segment_is(callee, "new_with_abi")
    {
        return false;
    }
    cx.sess()
        .source_map()
        .span_to_snippet(callee.span)
        .is_ok_and(|snippet| snippet.contains("VariableRecovery::new"))
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
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
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
        })
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

fn plugin_engine_policy_ownership_item(cx: &LateContext<'_>, item: &Item<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| {
            [
                "static TYPE_WRITEBACK_CACHE",
                "fn caller_prefers_bounded_type_plan",
                "fn analysis_policy_for_depth",
            ]
            .iter()
            .any(|needle| snippet.contains(needle))
        })
}

fn plugin_engine_policy_ownership_expr(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Call(callee, _) => {
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
                "should_use_direct_named_native_worker_decompile",
                "should_use_direct_named_native_worker_type_projection",
            ]
            .iter()
            .any(|name| expr_path_last_segment_is(callee, name))
        }
        ExprKind::MethodCall(method, _, _, _) => {
            method.ident.as_str() == "decompile_summary"
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
        }
        ExprKind::Path(_) => cx
            .sess()
            .source_map()
            .span_to_snippet(expr.span)
            .is_ok_and(|snippet| {
                snippet.ends_with("EngineSemanticMode::Full")
                    || snippet.ends_with("EngineSemanticMode::Optional")
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
}

fn impl_item_is_test_only(cx: &LateContext<'_>, item: &ImplItem<'_>) -> bool {
    cx.sess()
        .source_map()
        .span_to_snippet(item.span)
        .is_ok_and(|snippet| snippet.contains("#[cfg(test)]") || snippet.contains("#[test]"))
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
        ExprKind::Call(callee, _) if expr_path_last_segment_is(callee, "from_direct_call_targets")
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

fn is_r2dec_summary_render_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    let filename = format!("{filename:?}");
    filename.contains("crates/r2dec/src/consumer_summary.rs")
        || filename.contains("crates/r2dec/src/consumer_linear.rs")
        || filename.contains("crates/r2dec/src/consumer_vm.rs")
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
