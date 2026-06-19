#![feature(rustc_private)]
#![warn(unused_extern_crates)]

extern crate rustc_ast;
extern crate rustc_hir;
extern crate rustc_lint;
extern crate rustc_session;

use clippy_utils::diagnostics::span_lint;
use rustc_ast::LitKind;
use rustc_hir::{Expr, ExprKind};
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

rustc_session::declare_lint_pass!(R2sleighLintPass => [
    STRING_PREFIX_SEMANTIC_CLASSIFICATION,
    R2_JSON_COMMAND_INTERNAL_SEAM,
    R2DEC_DIRECT_KNOWN_SIGNATURE_LOOKUP,
    R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
    R2PLUGIN_TYPE_WRITEBACK_APPLY_THRESHOLD_OWNERSHIP
]);

#[unsafe(no_mangle)]
pub fn register_lints(sess: &rustc_session::Session, lint_store: &mut rustc_lint::LintStore) {
    dylint_linting::init_config(sess);
    lint_store.register_lints(&[
        STRING_PREFIX_SEMANTIC_CLASSIFICATION,
        R2_JSON_COMMAND_INTERNAL_SEAM,
        R2DEC_DIRECT_KNOWN_SIGNATURE_LOOKUP,
        R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
        R2PLUGIN_TYPE_WRITEBACK_APPLY_THRESHOLD_OWNERSHIP,
    ]);
    lint_store.register_late_pass(|_| Box::new(R2sleighLintPass));
}

impl<'tcx> LateLintPass<'tcx> for R2sleighLintPass {
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

        if is_r2plugin_path(cx, expr) && plugin_type_writeback_policy_expr(expr) {
            span_lint(
                cx,
                R2PLUGIN_TYPE_WRITEBACK_POLICY_OWNERSHIP,
                expr.span,
                "r2plugin must not inspect signature certificates to decide writeback authority; consume the r2types authority result",
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
        symbol.as_str().as_ref(),
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
            method.ident.as_str() == "authorizes_signature_writeback"
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

fn is_r2dec_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("crates/r2dec/src/")
}

fn is_r2plugin_path(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("r2plugin/src/")
}

fn is_canonical_ssa_var_classifier(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("crates/r2ssa/src/var.rs")
}

#[test]
fn ui() {
    dylint_testing::ui_test(env!("CARGO_PKG_NAME"), "ui");
}
