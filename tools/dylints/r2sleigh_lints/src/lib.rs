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

rustc_session::declare_lint_pass!(R2sleighLintPass => [
    STRING_PREFIX_SEMANTIC_CLASSIFICATION,
    R2_JSON_COMMAND_INTERNAL_SEAM
]);

#[unsafe(no_mangle)]
pub fn register_lints(sess: &rustc_session::Session, lint_store: &mut rustc_lint::LintStore) {
    dylint_linting::init_config(sess);
    lint_store.register_lints(&[
        STRING_PREFIX_SEMANTIC_CLASSIFICATION,
        R2_JSON_COMMAND_INTERNAL_SEAM,
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

fn is_canonical_ssa_var_classifier(cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
    let filename = cx.sess().source_map().span_to_filename(expr.span);
    format!("{filename:?}").contains("crates/r2ssa/src/var.rs")
}

#[test]
fn ui() {
    dylint_testing::ui_test(env!("CARGO_PKG_NAME"), "ui");
}
