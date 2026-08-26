//! C code generation with pretty printing.
//!
//! This module generates readable C source code from the AST.

use crate::ast::{
    BinaryOp, CExpr, CFunction, CStmt, CType, UnaryOp, has_render_observations,
    stmt_has_render_observations,
};
use crate::observation_journal::ObservationSealAuthority;

/// Threshold for detecting 64-bit negative values stored as unsigned.
/// Values above this are likely negative offsets (within ~65536 of u64::MAX).
/// This handles cases like stack offsets: 0xffffffffffffffb8 represents -72.
const LIKELY_NEGATIVE_THRESHOLD: u64 = 0xffffffffffff0000;

/// Above this, an integer literal reads better in hexadecimal.
///
/// Small numbers are counts, indices and sizes, and a reader wants those in
/// decimal. Anything larger is almost always a mask, a flag word, an address
/// or a magic value that was written in hex in the source and is only
/// recognisable that way: `0xdead` says what `57005` hides.
const HEX_LITERAL_THRESHOLD: u64 = 0x100;

/// How a non-negative integer literal is spelled.
pub(crate) fn format_unsigned_literal(value: u64) -> String {
    if value >= HEX_LITERAL_THRESHOLD {
        format!("0x{value:x}")
    } else {
        value.to_string()
    }
}

/// Code generator configuration.
#[derive(Debug, Clone)]
pub struct CodeGenConfig {
    /// Indentation string (e.g., "    " or "\t").
    pub indent: String,
    /// Maximum line width before wrapping.
    pub max_line_width: usize,
    /// Whether to emit comments.
    pub emit_comments: bool,
    /// Whether to use C99 types (uint32_t vs unsigned int).
    pub use_c99_types: bool,
}

impl Default for CodeGenConfig {
    fn default() -> Self {
        Self {
            indent: "    ".to_string(),
            max_line_width: 100,
            emit_comments: true,
            use_c99_types: true,
        }
    }
}

/// Owned AST after every semantics-preserving emission rewrite has run.
///
/// Observation sealing must inspect this exact function. The emitter accepts
/// no raw `CFunction`, which prevents a private clone from being rewritten
/// after the provenance journal has certified a different tree.
pub(crate) struct EmissionReadyFunction {
    function: CFunction,
}

impl EmissionReadyFunction {
    pub(crate) fn function(&self) -> &CFunction {
        assert!(
            !has_render_observations(&self.function),
            "marked C AST reached an emission/public boundary without journal sealing"
        );
        &self.function
    }

    pub(crate) fn function_mut_for_observation_seal(
        &mut self,
        _authority: &mut ObservationSealAuthority,
    ) -> &mut CFunction {
        &mut self.function
    }

    pub(crate) fn discard_observation_markers(
        &mut self,
        _authority: &mut ObservationSealAuthority,
    ) {
        crate::ast::discard_render_observations(&mut self.function);
    }

    /// Remove lexical proof markers only after exact observation sealing has
    /// inspected the same emission-ready tree.
    pub(crate) fn strip_structured_region_markers(
        &mut self,
        regions: &crate::structured_region::SealedStructuredRegionArtifact,
    ) -> Result<(), crate::structured_region::StructuredRegionFinalizationError> {
        crate::structured_region::strip_final_region_markers(&mut self.function.body, regions)
    }

    pub(crate) fn into_function(self) -> CFunction {
        assert!(
            !has_render_observations(&self.function),
            "marked C AST reached a public boundary without journal sealing"
        );
        self.function
    }

    #[cfg(test)]
    pub(crate) const fn function_for_marker_test(&self) -> &CFunction {
        &self.function
    }
}

/// Run all AST rewrites required solely by textual C emission.
pub(crate) fn prepare_function_for_emission(func: &CFunction) -> EmissionReadyFunction {
    EmissionReadyFunction {
        function: CFunction {
            body: prepare_stmt_sequence_for_emission(&func.body),
            ..func.clone()
        },
    }
}

/// C code generator.
pub(crate) struct CodeGenerator {
    config: CodeGenConfig,
    output: String,
    indent_level: usize,
    /// The names of the function being written, so a reference can be spelled.
    symbols: crate::symbol::SymbolTable,
}

impl CodeGenerator {
    /// Create a new code generator.
    pub(crate) fn new(config: CodeGenConfig) -> Self {
        Self {
            config,
            output: String::new(),
            indent_level: 0,
            symbols: crate::symbol::SymbolTable::new(),
        }
    }

    /// Generate code for a function.
    pub(crate) fn generate_function(&mut self, ready: &EmissionReadyFunction) -> String {
        let func = ready.function();
        self.symbols = func.symbols.borrow().clone();
        self.output.clear();

        // Function signature
        self.emit_type(&func.ret_type);
        self.output.push(' ');
        self.output.push_str(&func.name);
        self.output.push('(');

        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.output.push_str(", ");
            }
            self.emit_type(&param.ty);
            self.output.push(' ');
            self.output.push_str(self.symbols.name(param.name));
        }

        if func.params.is_empty() {
            // An empty list is only `void` when it was actually recovered.
            // Otherwise leave it unspecified rather than asserting the function
            // takes no arguments.
            if func.params_known {
                self.output.push_str("void");
            }
        }

        self.output.push_str(")\n{\n");
        self.indent_level += 1;

        // Local variable declarations
        for local in &func.locals {
            self.emit_indent();
            self.emit_type(&local.ty);
            self.output.push(' ');
            self.output.push_str(self.symbols.name(local.name));
            self.output.push_str(";\n");
        }

        if !func.locals.is_empty() {
            self.output.push('\n');
        }

        // Function body
        self.emit_stmt_sequence(&func.body);

        self.indent_level -= 1;
        self.output.push_str("}\n");

        self.output.clone()
    }

    /// Generate code for a statement.
    pub(crate) fn generate_stmt(&mut self, stmt: &CStmt) -> String {
        assert!(
            !stmt_has_render_observations(stmt),
            "marked C statement reached codegen without journal sealing"
        );
        self.output.clear();
        self.emit_stmt(stmt);
        self.output.clone()
    }

    /// Generate code for an expression.
    #[cfg(test)]
    pub(crate) fn generate_expr(&mut self, expr: &CExpr) -> String {
        self.output.clear();
        self.emit_expr(expr, 0);
        self.output.clone()
    }

    /// Emit a statement.
    fn emit_stmt(&mut self, stmt: &CStmt) {
        let stmt = stmt.unobserved();
        match stmt {
            CStmt::StructuredRegion { stmt, .. } => self.emit_stmt(stmt),
            CStmt::Empty => {}
            CStmt::Expr(expr) => {
                self.emit_indent();
                if let Some(compact) = scalar_update_expr(expr) {
                    self.emit_expr(&compact, 0);
                } else {
                    self.emit_expr(expr, 0);
                }
                self.output.push_str(";\n");
            }
            CStmt::Decl { ty, name, init } => {
                self.emit_indent();
                self.emit_type(ty);
                self.output.push(' ');
                self.output.push_str(self.symbols.name(*name));
                if let Some(init_expr) = init {
                    self.output.push_str(" = ");
                    self.emit_expr(init_expr, 0);
                }
                self.output.push_str(";\n");
            }
            CStmt::Block(stmts) => {
                self.emit_indent();
                self.output.push_str("{\n");
                self.indent_level += 1;
                self.emit_stmt_sequence(stmts);
                self.indent_level -= 1;
                self.emit_indent();
                self.output.push_str("}\n");
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                self.emit_indent();
                self.output.push_str("if (");
                self.emit_expr(cond, 0);
                self.output.push_str(") ");
                self.emit_stmt_body(then_body);

                if let Some(else_stmt) = else_body {
                    // Check if else body is another if (else-if chain)
                    if matches!(else_stmt.unobserved(), CStmt::If { .. }) {
                        self.output.push_str(" else ");
                        self.emit_stmt_inline(else_stmt);
                    } else {
                        self.output.push_str(" else ");
                        self.emit_stmt_body(else_stmt);
                    }
                }
                self.output.push('\n');
            }
            CStmt::While { cond, body } => {
                self.emit_indent();
                self.output.push_str("while (");
                self.emit_expr(cond, 0);
                self.output.push_str(") ");
                self.emit_stmt_body(body);
                self.output.push('\n');
            }
            CStmt::DoWhile { body, cond } => {
                self.emit_indent();
                self.output.push_str("do ");
                self.emit_stmt_body(body);
                self.output.push_str(" while (");
                self.emit_expr(cond, 0);
                self.output.push_str(");\n");
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                self.emit_indent();
                self.output.push_str("for (");

                if let Some(init_stmt) = init {
                    self.emit_stmt_inline(init_stmt);
                }
                self.output.push_str("; ");

                if let Some(cond_expr) = cond {
                    self.emit_expr(cond_expr, 0);
                }
                self.output.push_str("; ");

                if let Some(update_expr) = update {
                    if let Some(compact) = scalar_update_expr(update_expr) {
                        self.emit_expr(&compact, 0);
                    } else {
                        self.emit_expr(update_expr, 0);
                    }
                }
                self.output.push_str(") ");
                self.emit_stmt_body(body);
                self.output.push('\n');
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                self.emit_indent();
                self.output.push_str("switch (");
                self.emit_expr(expr, 0);
                self.output.push_str(") {\n");

                for case in cases {
                    self.emit_indent();
                    self.output.push_str("case ");
                    self.emit_expr(&case.value, 0);
                    self.output.push_str(":\n");
                    self.indent_level += 1;
                    self.emit_stmt_sequence(&case.body);
                    self.indent_level -= 1;
                }

                if let Some(default_stmts) = default {
                    self.emit_indent();
                    self.output.push_str("default:\n");
                    self.indent_level += 1;
                    self.emit_stmt_sequence(default_stmts);
                    self.indent_level -= 1;
                }

                self.emit_indent();
                self.output.push_str("}\n");
            }
            CStmt::Return(val) => {
                self.emit_indent();
                self.output.push_str("return");
                if let Some(expr) = val {
                    self.output.push(' ');
                    self.emit_expr(expr, 0);
                }
                self.output.push_str(";\n");
            }
            CStmt::Break => {
                self.emit_indent();
                self.output.push_str("break;\n");
            }
            CStmt::Continue => {
                self.emit_indent();
                self.output.push_str("continue;\n");
            }
            CStmt::Goto(label) => {
                self.emit_indent();
                self.output.push_str("goto ");
                self.output.push_str(label);
                self.output.push_str(";\n");
            }
            CStmt::Label(label) => {
                // Labels are not indented
                self.output.push_str(label);
                self.output.push_str(":\n");
            }
            CStmt::Comment(text) => {
                if self.config.emit_comments {
                    self.emit_indent();
                    self.output.push_str("/* ");
                    self.emit_comment_text(text);
                    self.output.push_str(" */\n");
                }
            }
            CStmt::Observed { .. } => unreachable!("unobserved statement expected"),
        }
    }

    /// Emit a straight-line sequence, coalescing adjacent scalar self-updates.
    fn emit_stmt_sequence(&mut self, stmts: &[CStmt]) {
        for stmt in stmts {
            self.emit_stmt(stmt);
        }
    }

    /// Emit a statement body (handles braces for single statements).
    fn emit_stmt_body(&mut self, stmt: &CStmt) {
        let stmt = stmt.unobserved();
        match stmt {
            CStmt::Block(stmts) => {
                self.output.push_str("{\n");
                self.indent_level += 1;
                self.emit_stmt_sequence(stmts);
                self.indent_level -= 1;
                self.emit_indent();
                self.output.push('}');
            }
            _ => {
                self.output.push_str("{\n");
                self.indent_level += 1;
                self.emit_stmt(stmt);
                self.indent_level -= 1;
                self.emit_indent();
                self.output.push('}');
            }
        }
    }

    /// Emit a statement inline (no newline, for for-loop init).
    fn emit_stmt_inline(&mut self, stmt: &CStmt) {
        let stmt = stmt.unobserved();
        match stmt {
            CStmt::Expr(expr) => {
                if let Some(compact) = scalar_update_expr(expr) {
                    self.emit_expr(&compact, 0);
                } else {
                    self.emit_expr(expr, 0);
                }
            }
            CStmt::Decl { ty, name, init } => {
                self.emit_type(ty);
                self.output.push(' ');
                self.output.push_str(self.symbols.name(*name));
                if let Some(init_expr) = init {
                    self.output.push_str(" = ");
                    self.emit_expr(init_expr, 0);
                }
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                self.output.push_str("if (");
                self.emit_expr(cond, 0);
                self.output.push_str(") ");
                self.emit_stmt_body(then_body);
                if let Some(else_stmt) = else_body {
                    self.output.push_str(" else ");
                    if matches!(else_stmt.unobserved(), CStmt::If { .. }) {
                        self.emit_stmt_inline(else_stmt);
                    } else {
                        self.emit_stmt_body(else_stmt);
                    }
                }
            }
            _ => {}
        }
    }

    /// Emit an expression with parent precedence for parenthesization.
    fn emit_expr(&mut self, expr: &CExpr, parent_prec: u8) {
        let expr = expr.unobserved();
        let my_prec = expr.precedence();
        let need_parens = my_prec < parent_prec;

        if need_parens {
            self.output.push('(');
        }

        match expr {
            CExpr::IntLit(val) => {
                let rendered = match u64::try_from(*val) {
                    Ok(magnitude) => format_unsigned_literal(magnitude),
                    Err(_) => val.to_string(),
                };
                self.output.push_str(&rendered);
            }
            CExpr::UIntLit(val) => {
                // Check if this looks like a negative offset (high bit set, close to max)
                if *val > LIKELY_NEGATIVE_THRESHOLD {
                    // Convert to negative: two's complement
                    let neg = (!*val).wrapping_add(1);
                    self.output.push_str(&format!("-0x{:x}", neg));
                } else {
                    self.output
                        .push_str(&format!("{}U", format_unsigned_literal(*val)));
                }
            }
            CExpr::FloatLit(val) => {
                self.output.push_str(&format!("{:.6}", val));
            }
            CExpr::StringLit(s) => {
                self.output.push('"');
                for c in s.chars() {
                    match c {
                        '\n' => self.output.push_str("\\n"),
                        '\r' => self.output.push_str("\\r"),
                        '\t' => self.output.push_str("\\t"),
                        '\\' => self.output.push_str("\\\\"),
                        '"' => self.output.push_str("\\\""),
                        c if c.is_ascii_graphic() || c == ' ' => self.output.push(c),
                        c => self.output.push_str(&format!("\\x{:02x}", c as u32)),
                    }
                }
                self.output.push('"');
            }
            CExpr::CharLit(c) => {
                self.output.push('\'');
                match c {
                    '\n' => self.output.push_str("\\n"),
                    '\r' => self.output.push_str("\\r"),
                    '\t' => self.output.push_str("\\t"),
                    '\\' => self.output.push_str("\\\\"),
                    '\'' => self.output.push_str("\\'"),
                    c if c.is_ascii_graphic() || *c == ' ' => self.output.push(*c),
                    c => self.output.push_str(&format!("\\x{:02x}", *c as u32)),
                }
                self.output.push('\'');
            }
            CExpr::Var(id) => {
                self.output.push_str(self.symbols.name(*id));
            }
            // The kind is what makes the name allowed, not how it prints.
            CExpr::External { name, .. } => {
                self.output.push_str(name);
            }
            CExpr::Unary { op, operand } => {
                if op.is_postfix() {
                    self.emit_expr(operand, my_prec);
                    self.output.push_str(op.as_str());
                } else {
                    self.output.push_str(op.as_str());
                    self.emit_expr(operand, my_prec);
                }
            }
            CExpr::Binary { op, left, right } => {
                if let Some((render_op, magnitude)) = additive_negative_rhs_rewrite(*op, right) {
                    self.emit_expr(left, my_prec);
                    self.output.push(' ');
                    self.output.push_str(render_op.as_str());
                    self.output.push(' ');
                    self.emit_positive_literal_magnitude(magnitude);
                } else if let Some((render_op, positive_rhs)) =
                    additive_negative_product_rhs_rewrite(*op, right)
                {
                    self.emit_expr(left, my_prec);
                    self.output.push(' ');
                    self.output.push_str(render_op.as_str());
                    self.output.push(' ');
                    self.emit_expr(&positive_rhs, my_prec + 1);
                } else {
                    self.emit_expr(left, my_prec);
                    self.output.push(' ');
                    self.output.push_str(op.as_str());
                    self.output.push(' ');
                    // Right associativity for assignment operators
                    let right_prec = if matches!(
                        op,
                        BinaryOp::Assign
                            | BinaryOp::AddAssign
                            | BinaryOp::SubAssign
                            | BinaryOp::MulAssign
                            | BinaryOp::DivAssign
                            | BinaryOp::ModAssign
                            | BinaryOp::BitAndAssign
                            | BinaryOp::BitOrAssign
                            | BinaryOp::BitXorAssign
                            | BinaryOp::ShlAssign
                            | BinaryOp::ShrAssign
                    ) {
                        my_prec
                    } else {
                        my_prec + 1
                    };
                    self.emit_expr(right, right_prec);
                }
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.emit_expr(cond, my_prec + 1);
                self.output.push_str(" ? ");
                self.emit_expr(then_expr, 0);
                self.output.push_str(" : ");
                self.emit_expr(else_expr, my_prec);
            }
            CExpr::Cast { ty, expr: inner } => {
                self.output.push('(');
                self.emit_type(ty);
                self.output.push(')');
                self.emit_expr(inner, my_prec);
            }
            CExpr::Call { func, args, .. } => {
                self.emit_expr(func, my_prec);
                self.output.push('(');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.emit_expr(arg, 0);
                }
                self.output.push(')');
            }
            CExpr::Subscript { base, index } => {
                self.emit_expr(base, my_prec);
                self.output.push('[');
                self.emit_expr(index, 0);
                self.output.push(']');
            }
            CExpr::Member { base, member } => {
                self.emit_expr(base, my_prec);
                self.output.push('.');
                self.output.push_str(member);
            }
            CExpr::PtrMember { base, member } => {
                self.emit_expr(base, my_prec);
                self.output.push_str("->");
                self.output.push_str(member);
            }
            CExpr::Sizeof(inner) => {
                self.output.push_str("sizeof(");
                self.emit_expr(inner, 0);
                self.output.push(')');
            }
            CExpr::SizeofType(ty) => {
                self.output.push_str("sizeof(");
                self.emit_type(ty);
                self.output.push(')');
            }
            CExpr::AddrOf(inner) => {
                self.output.push('&');
                self.emit_expr(inner, my_prec);
            }
            CExpr::Deref(inner) => {
                self.output.push('*');
                self.emit_expr(inner, my_prec);
            }
            CExpr::Comma(exprs) => {
                for (i, e) in exprs.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.emit_expr(e, my_prec + 1);
                }
            }
            CExpr::Paren(inner) => {
                self.output.push('(');
                self.emit_expr(inner, 0);
                self.output.push(')');
            }
            CExpr::Observed { .. } => unreachable!("unobserved expression expected"),
        }

        if need_parens {
            self.output.push(')');
        }
    }

    /// Emit a type.
    fn emit_type(&mut self, ty: &CType) {
        // Use the Display implementation
        self.output.push_str(&ty.to_string());
    }

    /// Emit indentation.
    fn emit_indent(&mut self) {
        for _ in 0..self.indent_level {
            self.output.push_str(&self.config.indent);
        }
    }

    fn emit_comment_text(&mut self, text: &str) {
        self.output.push_str(&sanitize_comment_text(text));
    }

    fn emit_positive_literal_magnitude(&mut self, literal: PositiveLiteralMagnitude) {
        if literal.prefer_hex {
            self.output.push_str(&format!("0x{:x}", literal.value));
        } else {
            self.output
                .push_str(&format_unsigned_literal(literal.value));
        }
    }
}

#[cfg(test)]
fn generate(func: &CFunction) -> String {
    let mut codegen = CodeGenerator::new(CodeGenConfig::default());
    let ready = prepare_function_for_emission(func);
    codegen.generate_function(&ready)
}

fn prepare_stmt_sequence_for_emission(stmts: &[CStmt]) -> Vec<CStmt> {
    let nested = stmts
        .iter()
        .map(prepare_stmt_for_emission)
        .collect::<Vec<_>>();
    let mut prepared = Vec::with_capacity(nested.len());
    let mut index = 0;
    while index < nested.len() {
        if let Some((run_len, stmt)) = coalesced_scalar_update_run(&nested[index..]) {
            prepared.push(stmt);
            index += run_len;
        } else {
            prepared.push(nested[index].clone());
            index += 1;
        }
    }
    prepared
}

fn prepare_stmt_for_emission(stmt: &CStmt) -> CStmt {
    match stmt {
        CStmt::StructuredRegion { marker, stmt } => {
            CStmt::structured_region(*marker, prepare_stmt_for_emission(stmt.as_ref()))
        }
        CStmt::Observed { id, stmt } => {
            CStmt::observed(*id, prepare_stmt_for_emission(stmt.as_ref()))
        }
        CStmt::Block(stmts) => CStmt::Block(prepare_stmt_sequence_for_emission(stmts)),
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => CStmt::If {
            cond: cond.clone(),
            then_body: Box::new(prepare_stmt_for_emission(then_body)),
            else_body: else_body
                .as_deref()
                .map(prepare_stmt_for_emission)
                .map(Box::new),
        },
        CStmt::While { cond, body } => CStmt::While {
            cond: cond.clone(),
            body: Box::new(prepare_stmt_for_emission(body)),
        },
        CStmt::DoWhile { body, cond } => CStmt::DoWhile {
            body: Box::new(prepare_stmt_for_emission(body)),
            cond: cond.clone(),
        },
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => CStmt::For {
            init: init.as_deref().map(prepare_stmt_for_emission).map(Box::new),
            cond: cond.clone(),
            update: update.clone(),
            body: Box::new(prepare_stmt_for_emission(body)),
        },
        CStmt::Switch {
            expr,
            cases,
            default,
        } => CStmt::Switch {
            expr: expr.clone(),
            cases: cases
                .iter()
                .map(|case| crate::ast::SwitchCase {
                    value: case.value.clone(),
                    body: prepare_stmt_sequence_for_emission(&case.body),
                })
                .collect(),
            default: default
                .as_ref()
                .map(|stmts| prepare_stmt_sequence_for_emission(stmts)),
        },
        CStmt::Decl { .. }
        | CStmt::Expr(_)
        | CStmt::Return(_)
        | CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => stmt.clone(),
    }
}

fn coalesced_scalar_update_run(stmts: &[CStmt]) -> Option<(usize, CStmt)> {
    let (name, first_delta) = scalar_self_update_delta(stmts.first()?)?;
    let mut total = first_delta;
    let mut run_len = 1;

    for stmt in &stmts[1..] {
        let Some((next_name, delta)) = scalar_self_update_delta(stmt) else {
            break;
        };
        if next_name != name {
            break;
        }
        total = total.checked_add(delta)?;
        run_len += 1;
    }

    if run_len < 2 {
        return None;
    }

    let stmt = scalar_update_stmt(name, total)?;
    // Coalescing multiple updates creates a new occurrence. None of the source
    // statement/use/write markers has an exact position in it, so the ledger
    // must report them unaccounted instead of transferring them to synthetic C.
    Some((run_len, stmt))
}

fn scalar_update_stmt(name: crate::symbol::SymbolId, delta: i64) -> Option<CStmt> {
    if delta == 0 {
        // Removing the whole run would also remove the source definitions it
        // represents. Keep the original statements until an explicit elision
        // proof, rather than carrying exact render observations onto an empty
        // statement that emits no C.
        return None;
    }
    let (op, amount) = if delta < 0 {
        (BinaryOp::SubAssign, delta.checked_abs()?)
    } else {
        (BinaryOp::AddAssign, delta)
    };
    Some(CStmt::Expr(CExpr::binary(
        op,
        CExpr::Var(name),
        CExpr::IntLit(amount),
    )))
}

fn scalar_update_expr(expr: &CExpr) -> Option<CExpr> {
    let (name, delta) = scalar_self_update_delta_expr(expr)?;
    match delta {
        1 => Some(CExpr::Unary {
            op: UnaryOp::PostInc,
            operand: Box::new(CExpr::Var(name)),
        }),
        -1 => Some(CExpr::Unary {
            op: UnaryOp::PostDec,
            operand: Box::new(CExpr::Var(name)),
        }),
        0 => None,
        _ => match scalar_update_stmt(name, delta)? {
            CStmt::Expr(expr) => Some(expr),
            _ => None,
        },
    }
}

fn scalar_self_update_delta(stmt: &CStmt) -> Option<(crate::symbol::SymbolId, i64)> {
    let stmt = stmt.unobserved();
    let CStmt::Expr(expr) = stmt else {
        return None;
    };
    scalar_self_update_delta_expr(expr)
}

fn scalar_self_update_delta_expr(expr: &CExpr) -> Option<(crate::symbol::SymbolId, i64)> {
    let expr = expr.unobserved();
    let CExpr::Binary { op, left, right } = expr else {
        return None;
    };
    let CExpr::Var(lhs_name) = left.unobserved() else {
        return None;
    };
    match op {
        BinaryOp::Assign => update_delta_for_rhs(*lhs_name, right),
        BinaryOp::AddAssign => literal_i64(right).map(|delta| (*lhs_name, delta)),
        BinaryOp::SubAssign => {
            literal_i64(right).and_then(|delta| delta.checked_neg().map(|v| (*lhs_name, v)))
        }
        _ => None,
    }
}

fn update_delta_for_rhs(
    lhs_name: crate::symbol::SymbolId,
    rhs: &CExpr,
) -> Option<(crate::symbol::SymbolId, i64)> {
    let rhs = rhs.unobserved();
    let CExpr::Binary { op, left, right } = rhs else {
        return None;
    };

    match op {
        BinaryOp::Add => {
            if expr_is_var(left, lhs_name) {
                literal_i64(right).map(|delta| (lhs_name, delta))
            } else if expr_is_var(right, lhs_name) {
                literal_i64(left).map(|delta| (lhs_name, delta))
            } else {
                None
            }
        }
        BinaryOp::Sub if expr_is_var(left, lhs_name) => {
            literal_i64(right).and_then(|delta| delta.checked_neg().map(|v| (lhs_name, v)))
        }
        _ => None,
    }
}

fn expr_is_var(expr: &CExpr, name: crate::symbol::SymbolId) -> bool {
    matches!(expr.unobserved(), CExpr::Var(candidate) if *candidate == name)
}

fn literal_i64(expr: &CExpr) -> Option<i64> {
    let expr = expr.unobserved();
    match expr {
        CExpr::IntLit(value) => Some(*value),
        CExpr::UIntLit(value) => i64::try_from(*value).ok(),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy)]
struct PositiveLiteralMagnitude {
    value: u64,
    prefer_hex: bool,
}

fn additive_negative_rhs_rewrite(
    op: BinaryOp,
    rhs: &CExpr,
) -> Option<(BinaryOp, PositiveLiteralMagnitude)> {
    let magnitude = negative_literal_magnitude(rhs)?;
    match op {
        BinaryOp::Add => Some((BinaryOp::Sub, magnitude)),
        BinaryOp::Sub => Some((BinaryOp::Add, magnitude)),
        _ => None,
    }
}

fn negative_literal_magnitude(expr: &CExpr) -> Option<PositiveLiteralMagnitude> {
    let expr = expr.unobserved();
    match expr {
        CExpr::IntLit(value) if *value < 0 => Some(PositiveLiteralMagnitude {
            value: value.unsigned_abs(),
            prefer_hex: false,
        }),
        CExpr::UIntLit(value) if *value > LIKELY_NEGATIVE_THRESHOLD => {
            Some(PositiveLiteralMagnitude {
                value: (!*value).wrapping_add(1),
                prefer_hex: true,
            })
        }
        _ => None,
    }
}

fn additive_negative_product_rhs_rewrite(op: BinaryOp, rhs: &CExpr) -> Option<(BinaryOp, CExpr)> {
    let positive_rhs = negative_product_positive_rhs(rhs)?;
    match op {
        BinaryOp::Add => Some((BinaryOp::Sub, positive_rhs)),
        BinaryOp::Sub => Some((BinaryOp::Add, positive_rhs)),
        _ => None,
    }
}

fn negative_product_positive_rhs(expr: &CExpr) -> Option<CExpr> {
    let expr = expr.unobserved();
    match expr {
        CExpr::Binary {
            op: BinaryOp::Mul,
            left,
            right,
        } => {
            if let Some(magnitude) = negative_literal_magnitude(right) {
                return positive_product_expr((**left).clone(), magnitude);
            }
            if let Some(magnitude) = negative_literal_magnitude(left) {
                return positive_product_expr((**right).clone(), magnitude);
            }
            None
        }
        CExpr::Paren(inner) => negative_product_positive_rhs(inner),
        _ => None,
    }
}

fn positive_product_expr(term: CExpr, magnitude: PositiveLiteralMagnitude) -> Option<CExpr> {
    if magnitude.value == 1 {
        return Some(term);
    }
    let literal = if magnitude.prefer_hex {
        CExpr::UIntLit(magnitude.value)
    } else {
        CExpr::IntLit(i64::try_from(magnitude.value).ok()?)
    };
    Some(CExpr::binary(BinaryOp::Mul, term, literal))
}

fn sanitize_comment_text(text: &str) -> String {
    crate::sanitize_comment_text(text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{CLocal, CParam};

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    #[test]
    fn test_generate_simple_function() {
        let symbols = test_table();
        let func = CFunction {
            name: "add".to_string(),
            ret_type: CType::i32(),
            params: vec![
                CParam {
                    ty: CType::i32(),
                    name: crate::symbol::declare(&symbols, "a"),
                },
                CParam {
                    ty: CType::i32(),
                    name: crate::symbol::declare(&symbols, "b"),
                },
            ],
            locals: vec![],
            body: vec![CStmt::Return(Some(CExpr::binary(
                BinaryOp::Add,
                CExpr::var(crate::symbol::declare(&symbols, "a")),
                CExpr::var(crate::symbol::declare(&symbols, "b")),
            )))],
            params_known: true,
            symbols: std::rc::Rc::new(symbols),
        };

        let code = generate(&func);
        assert!(code.contains("int32_t add(int32_t a, int32_t b)"));
        assert!(code.contains("return a + b;"));
    }

    #[test]
    fn unsealed_observation_wrappers_cannot_reach_codegen() {
        let symbols = test_table();
        let value = crate::symbol::declare(&symbols, "value");
        let plain = CFunction {
            name: "observed".to_string(),
            ret_type: CType::i32(),
            params: vec![],
            locals: vec![],
            body: vec![CStmt::If {
                cond: CExpr::binary(BinaryOp::Gt, CExpr::var(value), CExpr::int(0)),
                then_body: Box::new(CStmt::Return(Some(CExpr::binary(
                    BinaryOp::Add,
                    CExpr::var(value),
                    CExpr::int(1),
                )))),
                else_body: Some(Box::new(CStmt::Return(Some(CExpr::int(0))))),
            }],
            params_known: true,
            symbols: std::rc::Rc::new(symbols),
        };
        let mut observed = plain.clone();
        let mut observation_owner = crate::ast::RenderObservationOwner::new();
        let (_, observed_value) = observation_owner
            .observe_expr(CExpr::var(value))
            .expect("allocate value observation");
        let (_, observed_cond) = observation_owner
            .observe_expr(CExpr::binary(
                BinaryOp::Gt,
                CExpr::var(value),
                CExpr::int(0),
            ))
            .expect("allocate condition observation");
        let (_, observed_stmt) = observation_owner
            .observe_stmt(CStmt::If {
                cond: observed_cond,
                then_body: Box::new(CStmt::Return(Some(CExpr::binary(
                    BinaryOp::Add,
                    observed_value,
                    CExpr::int(1),
                )))),
                else_body: Some(Box::new(CStmt::Return(Some(CExpr::int(0))))),
            })
            .expect("allocate statement observation");
        observed.body = vec![observed_stmt];

        let statement_refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            CodeGenerator::new(CodeGenConfig::default()).generate_stmt(&observed.body[0])
        }));
        assert!(
            statement_refused.is_err(),
            "marked statement bypassed journal sealing"
        );
        let ready = prepare_function_for_emission(&observed);
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            CodeGenerator::new(CodeGenConfig::default()).generate_function(&ready)
        }));
        assert!(refused.is_err(), "marked AST bypassed journal sealing");
        assert!(!generate(&plain).is_empty());
    }

    #[test]
    fn coalesced_updates_drop_observations_without_exact_occurrences() {
        let symbols = test_table();
        let value = crate::symbol::declare(&symbols, "value");
        let update = |amount| {
            CStmt::Expr(CExpr::assign(
                CExpr::var(value),
                CExpr::binary(BinaryOp::Add, CExpr::var(value), CExpr::int(amount)),
            ))
        };
        let plain_updates = vec![update(1), update(2)];
        let (_, plain_update) =
            coalesced_scalar_update_run(&plain_updates).expect("plain scalar run");
        let mut owner = crate::ast::RenderObservationOwner::new();
        let mut observed_updates = Vec::new();
        let mut expected_ids = Vec::new();
        for amount in [1, 2] {
            let (expr_id, expr) = owner
                .observe_expr(CExpr::assign(
                    CExpr::var(value),
                    CExpr::binary(BinaryOp::Add, CExpr::var(value), CExpr::int(amount)),
                ))
                .expect("allocate update observation");
            let (stmt_id, stmt) = owner
                .observe_stmt(CStmt::Expr(expr))
                .expect("allocate update statement observation");
            expected_ids.extend([expr_id, stmt_id]);
            observed_updates.push(stmt);
        }
        let (_, observed_update) =
            coalesced_scalar_update_run(&observed_updates).expect("observed scalar run");
        let mut transformed =
            CFunction::new("updates", CType::Void).with_body(vec![observed_update]);
        let reachable =
            crate::ast::strip_render_observations(&mut transformed, owner.expected_count())
                .expect("coalescing preserved a valid observation domain");

        assert_eq!(transformed.body, vec![plain_update]);
        for id in expected_ids {
            assert!(
                !reachable.contains(id),
                "a coalesced update has no exact source occurrence for marker {id:?}"
            );
        }
    }

    #[test]
    fn test_generate_if_else() {
        let symbols = test_table();
        let sym_x = crate::symbol::declare(&symbols, "x");
        let stmt = CStmt::if_stmt(
            CExpr::binary(BinaryOp::Gt, CExpr::var(sym_x), CExpr::int(0)),
            CStmt::ret(Some(CExpr::int(1))),
            Some(CStmt::ret(Some(CExpr::int(0)))),
        );

        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        // The generator renders from the table the fixture declared into.
        codegen.symbols = symbols.borrow().clone();
        let code = codegen.generate_stmt(&stmt);

        assert!(code.contains("if (x > 0)"));
        assert!(code.contains("return 1;"));
        assert!(code.contains("else"));
        assert!(code.contains("return 0;"));
    }

    #[test]
    fn test_generate_while_loop() {
        let symbols = test_table();
        let sym_i = crate::symbol::declare(&symbols, "i");
        let stmt = CStmt::while_loop(
            CExpr::binary(BinaryOp::Lt, CExpr::var(sym_i), CExpr::int(10)),
            CStmt::expr(CExpr::binary(
                BinaryOp::AddAssign,
                CExpr::var(sym_i),
                CExpr::int(1),
            )),
        );

        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        // The generator renders from the table the fixture declared into.
        codegen.symbols = symbols.borrow().clone();
        let code = codegen.generate_stmt(&stmt);

        assert!(code.contains("while (i < 10)"));
        assert!(code.contains("i++"));
    }

    #[test]
    fn test_generate_compound_unit_updates_as_inc_dec() {
        let symbols = test_table();
        let sym_i = crate::symbol::declare(&symbols, "i");
        let i = sym_i;
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        // The generator renders from the table the fixture declared into.
        codegen.symbols = symbols.borrow().clone();
        assert_eq!(
            codegen.generate_expr(&CExpr::binary(
                BinaryOp::AddAssign,
                CExpr::var(i),
                CExpr::int(1),
            )),
            "i += 1"
        );
        assert!(
            codegen
                .generate_stmt(&CStmt::expr(CExpr::binary(
                    BinaryOp::AddAssign,
                    CExpr::var(i),
                    CExpr::int(1),
                )))
                .contains("i++;")
        );
    }

    #[test]
    fn test_emit_types() {
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());

        codegen.output.clear();
        codegen.emit_type(&CType::i32());
        assert_eq!(codegen.output, "int32_t");

        codegen.output.clear();
        codegen.emit_type(&CType::ptr(CType::u8()));
        assert_eq!(codegen.output, "uint8_t*");

        codegen.output.clear();
        codegen.emit_type(&CType::Void);
        assert_eq!(codegen.output, "void");
    }

    #[test]
    fn test_expression_precedence() {
        let symbols = test_table();
        let sym_a = crate::symbol::declare(&symbols, "a");
        let sym_b = crate::symbol::declare(&symbols, "b");
        let sym_c = crate::symbol::declare(&symbols, "c");
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        // The generator renders from the table the fixture declared into.
        codegen.symbols = symbols.borrow().clone();

        // a + b * c should not need parens around b * c
        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::var(sym_a),
            CExpr::binary(BinaryOp::Mul, CExpr::var(sym_b), CExpr::var(sym_c)),
        );
        let code = codegen.generate_expr(&expr);
        assert_eq!(code, "a + b * c");

        // (a + b) * c needs parens
        codegen.output.clear();
        let expr = CExpr::binary(
            BinaryOp::Mul,
            CExpr::binary(BinaryOp::Add, CExpr::var(sym_a), CExpr::var(sym_b)),
            CExpr::var(sym_c),
        );
        let code = codegen.generate_expr(&expr);
        assert_eq!(code, "(a + b) * c");
    }

    #[test]
    fn test_additive_negative_literals_render_without_stack_placeholder_noise() {
        let symbols = test_table();
        let sym_stack_8 = crate::symbol::declare(&symbols, "stack_8");
        let sym_rsp = crate::symbol::declare(&symbols, "rsp");
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        // The generator renders from the table the fixture declared into.
        codegen.symbols = symbols.borrow().clone();

        let expr = CExpr::binary(BinaryOp::Add, CExpr::var(sym_stack_8), CExpr::int(-8));
        assert_eq!(codegen.generate_expr(&expr), "stack_8 - 8");

        let expr = CExpr::binary(
            BinaryOp::Sub,
            CExpr::var(sym_rsp),
            CExpr::uint(0xffffffffffffffb8),
        );
        assert_eq!(codegen.generate_expr(&expr), "rsp + 0x48");
    }

    #[test]
    fn test_additive_negative_linear_terms_render_as_subtraction() {
        let symbols = test_table();
        let sym_a = crate::symbol::declare(&symbols, "a");
        let sym_b = crate::symbol::declare(&symbols, "b");
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        // The generator renders from the table the fixture declared into.
        codegen.symbols = symbols.borrow().clone();

        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::var(sym_a),
            CExpr::binary(BinaryOp::Mul, CExpr::var(sym_b), CExpr::int(-1)),
        );
        assert_eq!(codegen.generate_expr(&expr), "a - b");

        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::var(sym_a),
            CExpr::binary(BinaryOp::Mul, CExpr::var(sym_b), CExpr::int(-4)),
        );
        assert_eq!(codegen.generate_expr(&expr), "a - b * 4");
    }

    #[test]
    fn test_string_literal_escaping() {
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        let expr = CExpr::StringLit("line1\n\t\"quote\"\\slash\u{0001}".to_string());
        let code = codegen.generate_expr(&expr);
        assert_eq!(code, "\"line1\\n\\t\\\"quote\\\"\\\\slash\\x01\"");
    }

    #[test]
    fn test_comment_text_is_sanitized_at_render_boundary() {
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        let code = codegen.generate_stmt(&CStmt::comment("bad */\nnext"));

        assert!(code.contains("bad * / next"));
        assert!(!code.contains("bad */"));
    }

    #[test]
    fn emission_preserves_placement_owned_local_declarations() {
        let symbols = test_table();
        let x = crate::symbol::declare(&symbols, "x");
        let func = CFunction {
            name: "test".to_string(),
            ret_type: CType::Void,
            params: vec![],
            locals: vec![
                CLocal {
                    ty: CType::i32(),
                    name: x,
                    stack_offset: Some(-8),
                },
                CLocal {
                    ty: CType::ptr(CType::i8()),
                    name: crate::symbol::declare(&symbols, "p"),
                    stack_offset: Some(-16),
                },
            ],
            body: vec![
                CStmt::expr(CExpr::assign(CExpr::var(x), CExpr::int(1))),
                CStmt::Return(None),
            ],
            params_known: true,
            symbols: std::rc::Rc::new(symbols),
        };

        let code = generate(&func);
        assert!(code.contains("int32_t x;"));
        assert!(code.contains("int8_t* p;"));
        assert!(code.contains("x = 1;"));
        assert!(!code.contains("int32_t x = 1;"));
    }

    #[test]
    fn test_coalesces_adjacent_scalar_self_updates() {
        let symbols = test_table();
        let mut func = CFunction::new("updates", CType::Void).with_body(vec![
            CStmt::expr(CExpr::assign(
                CExpr::var(crate::symbol::declare(&symbols, "acc")),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::var(crate::symbol::declare(&symbols, "acc")),
                    CExpr::int(3),
                ),
            )),
            CStmt::expr(CExpr::assign(
                CExpr::var(crate::symbol::declare(&symbols, "acc")),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::int(4),
                    CExpr::var(crate::symbol::declare(&symbols, "acc")),
                ),
            )),
            CStmt::expr(CExpr::assign(
                CExpr::var(crate::symbol::declare(&symbols, "acc")),
                CExpr::binary(
                    BinaryOp::Sub,
                    CExpr::var(crate::symbol::declare(&symbols, "acc")),
                    CExpr::int(2),
                ),
            )),
            CStmt::Return(None),
        ]);
        func.symbols = std::rc::Rc::new(symbols);

        let code = generate(&func);

        assert!(
            code.contains("acc += 5;"),
            "expected collapsed scalar update, got:\n{code}"
        );
        assert_eq!(code.matches("acc = acc").count(), 0, "{code}");
    }

    #[test]
    fn test_scalar_self_update_coalesce_stops_at_observable_statement() {
        let symbols = test_table();
        let mut func = CFunction::new("updates", CType::Void).with_body(vec![
            CStmt::expr(CExpr::assign(
                CExpr::var(crate::symbol::declare(&symbols, "acc")),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::var(crate::symbol::declare(&symbols, "acc")),
                    CExpr::int(1),
                ),
            )),
            CStmt::expr(CExpr::call(
                CExpr::var(crate::symbol::declare(&symbols, "observe")),
                vec![CExpr::var(crate::symbol::declare(&symbols, "acc"))],
            )),
            CStmt::expr(CExpr::assign(
                CExpr::var(crate::symbol::declare(&symbols, "acc")),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::var(crate::symbol::declare(&symbols, "acc")),
                    CExpr::int(2),
                ),
            )),
            CStmt::expr(CExpr::assign(
                CExpr::var(crate::symbol::declare(&symbols, "acc")),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::var(crate::symbol::declare(&symbols, "acc")),
                    CExpr::int(3),
                ),
            )),
        ]);
        func.symbols = std::rc::Rc::new(symbols);

        let code = generate(&func);

        assert!(
            code.contains("acc++;\n    observe(acc);\n    acc += 5;"),
            "observable call should break the update run, got:\n{code}"
        );
    }

    #[test]
    fn zero_sum_scalar_updates_remain_explicit() {
        let symbols = test_table();
        let acc = crate::symbol::declare(&symbols, "acc");
        let mut func = CFunction::new("updates", CType::Void).with_body(vec![
            CStmt::expr(CExpr::assign(
                CExpr::var(acc),
                CExpr::binary(BinaryOp::Add, CExpr::var(acc), CExpr::int(1)),
            )),
            CStmt::expr(CExpr::assign(
                CExpr::var(acc),
                CExpr::binary(BinaryOp::Sub, CExpr::var(acc), CExpr::int(1)),
            )),
        ]);
        func.symbols = std::rc::Rc::new(symbols);

        let code = generate(&func);

        assert!(
            code.contains("acc++;\n    acc--;"),
            "zero-sum definitions must not disappear without an elision proof:\n{code}"
        );
    }
}
