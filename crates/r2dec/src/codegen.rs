//! C code generation with pretty printing.
//!
//! This module generates readable C source code from the AST.

use std::collections::{HashMap, HashSet};

use crate::ast::{BinaryOp, CExpr, CFunction, CLocal, CStmt, CType, UnaryOp};

/// Threshold for detecting 64-bit negative values stored as unsigned.
/// Values above this are likely negative offsets (within ~65536 of u64::MAX).
/// This handles cases like stack offsets: 0xffffffffffffffb8 represents -72.
const LIKELY_NEGATIVE_THRESHOLD: u64 = 0xffffffffffff0000;

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

/// C code generator.
pub struct CodeGenerator {
    config: CodeGenConfig,
    output: String,
    indent_level: usize,
}

impl CodeGenerator {
    /// Create a new code generator.
    pub fn new(config: CodeGenConfig) -> Self {
        Self {
            config,
            output: String::new(),
            indent_level: 0,
        }
    }

    /// Generate code for a function.
    pub fn generate_function(&mut self, func: &CFunction) -> String {
        self.output.clear();
        let (locals, body) = inline_local_declaration_initializers(func);

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
            self.output.push_str(&param.name);
        }

        if func.params.is_empty() {
            self.output.push_str("void");
        }

        self.output.push_str(")\n{\n");
        self.indent_level += 1;

        // Local variable declarations
        for local in &locals {
            self.emit_indent();
            self.emit_type(&local.ty);
            self.output.push(' ');
            self.output.push_str(&local.name);
            self.output.push_str(";\n");
        }

        if !locals.is_empty() {
            self.output.push('\n');
        }

        // Function body
        self.emit_stmt_sequence(&body);

        self.indent_level -= 1;
        self.output.push_str("}\n");

        self.output.clone()
    }

    /// Generate code for a statement.
    pub fn generate_stmt(&mut self, stmt: &CStmt) -> String {
        self.output.clear();
        self.emit_stmt(stmt);
        self.output.clone()
    }

    /// Generate code for an expression.
    pub fn generate_expr(&mut self, expr: &CExpr) -> String {
        self.output.clear();
        self.emit_expr(expr, 0);
        self.output.clone()
    }

    /// Emit a statement.
    fn emit_stmt(&mut self, stmt: &CStmt) {
        match stmt {
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
                self.output.push_str(name);
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
                    if matches!(else_stmt.as_ref(), CStmt::If { .. }) {
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
        }
    }

    /// Emit a straight-line sequence, coalescing adjacent scalar self-updates.
    fn emit_stmt_sequence(&mut self, stmts: &[CStmt]) {
        let mut idx = 0;
        while idx < stmts.len() {
            if let Some((run_len, stmt)) = coalesced_scalar_update_run(&stmts[idx..]) {
                self.emit_stmt(&stmt);
                idx += run_len;
            } else {
                self.emit_stmt(&stmts[idx]);
                idx += 1;
            }
        }
    }

    /// Emit a statement body (handles braces for single statements).
    fn emit_stmt_body(&mut self, stmt: &CStmt) {
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
                self.output.push_str(name);
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
                    if matches!(else_stmt.as_ref(), CStmt::If { .. }) {
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
        let my_prec = expr.precedence();
        let need_parens = my_prec < parent_prec;

        if need_parens {
            self.output.push('(');
        }

        match expr {
            CExpr::IntLit(val) => {
                if *val < 0 {
                    self.output.push_str(&format!("{}", val));
                } else if *val > 0xffff {
                    self.output.push_str(&format!("0x{:x}", val));
                } else {
                    self.output.push_str(&format!("{}", val));
                }
            }
            CExpr::UIntLit(val) => {
                // Check if this looks like a negative offset (high bit set, close to max)
                if *val > LIKELY_NEGATIVE_THRESHOLD {
                    // Convert to negative: two's complement
                    let neg = (!*val).wrapping_add(1);
                    self.output.push_str(&format!("-0x{:x}", neg));
                } else if *val > 0xffff {
                    self.output.push_str(&format!("0x{:x}U", val));
                } else {
                    self.output.push_str(&format!("{}U", val));
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
            CExpr::Var(name) => {
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
            CExpr::Call { func, args } => {
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
        if literal.prefer_hex || literal.value > 0xffff {
            self.output.push_str(&format!("0x{:x}", literal.value));
        } else {
            self.output.push_str(&literal.value.to_string());
        }
    }
}

/// Generate C code for a function.
pub fn generate(func: &CFunction) -> String {
    let mut codegen = CodeGenerator::new(CodeGenConfig::default());
    codegen.generate_function(func)
}

fn inline_local_declaration_initializers(func: &CFunction) -> (Vec<CLocal>, Vec<CStmt>) {
    let local_types = func
        .locals
        .iter()
        .map(|local| (local.name.clone(), local.ty.clone()))
        .collect::<HashMap<_, _>>();
    if local_types.is_empty() {
        return (func.locals.clone(), func.body.clone());
    }

    let global_counts = count_vars_in_stmts(&func.body, &local_types);
    let mut declared = HashSet::new();
    let body = inline_decls_in_stmt_list(&func.body, &local_types, &global_counts, &mut declared);
    let locals = func
        .locals
        .iter()
        .filter(|local| !declared.contains(&local.name))
        .cloned()
        .collect();
    (locals, body)
}

fn inline_decls_in_stmt_list(
    stmts: &[CStmt],
    local_types: &HashMap<String, CType>,
    global_counts: &HashMap<String, usize>,
    declared: &mut HashSet<String>,
) -> Vec<CStmt> {
    let block_counts = count_vars_in_stmts(stmts, local_types);
    stmts
        .iter()
        .map(|stmt| {
            if let Some((name, init)) = assignment_decl_candidate(stmt)
                && can_inline_decl(
                    name,
                    init,
                    local_types,
                    global_counts,
                    &block_counts,
                    declared,
                )
            {
                declared.insert(name.to_string());
                return CStmt::Decl {
                    ty: local_types[name].clone(),
                    name: name.to_string(),
                    init: Some(init.clone()),
                };
            }
            inline_decls_in_stmt(stmt, local_types, global_counts, declared)
        })
        .collect()
}

fn inline_decls_in_stmt(
    stmt: &CStmt,
    local_types: &HashMap<String, CType>,
    global_counts: &HashMap<String, usize>,
    declared: &mut HashSet<String>,
) -> CStmt {
    match stmt {
        CStmt::Block(stmts) => CStmt::Block(inline_decls_in_stmt_list(
            stmts,
            local_types,
            global_counts,
            declared,
        )),
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => CStmt::If {
            cond: cond.clone(),
            then_body: Box::new(inline_decls_in_stmt(
                then_body,
                local_types,
                global_counts,
                declared,
            )),
            else_body: else_body.as_ref().map(|stmt| {
                Box::new(inline_decls_in_stmt(
                    stmt,
                    local_types,
                    global_counts,
                    declared,
                ))
            }),
        },
        CStmt::While { cond, body } => CStmt::While {
            cond: cond.clone(),
            body: Box::new(inline_decls_in_stmt(
                body,
                local_types,
                global_counts,
                declared,
            )),
        },
        CStmt::DoWhile { body, cond } => CStmt::DoWhile {
            body: Box::new(inline_decls_in_stmt(
                body,
                local_types,
                global_counts,
                declared,
            )),
            cond: cond.clone(),
        },
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            let for_counts = count_vars_in_stmt(stmt, local_types);
            let init = init.as_ref().map(|init| {
                if let Some((name, init_expr)) = assignment_decl_candidate(init)
                    && can_inline_decl(
                        name,
                        init_expr,
                        local_types,
                        global_counts,
                        &for_counts,
                        declared,
                    )
                {
                    declared.insert(name.to_string());
                    Box::new(CStmt::Decl {
                        ty: local_types[name].clone(),
                        name: name.to_string(),
                        init: Some(init_expr.clone()),
                    })
                } else {
                    Box::new(inline_decls_in_stmt(
                        init,
                        local_types,
                        global_counts,
                        declared,
                    ))
                }
            });
            CStmt::For {
                init,
                cond: cond.clone(),
                update: update.clone(),
                body: Box::new(inline_decls_in_stmt(
                    body,
                    local_types,
                    global_counts,
                    declared,
                )),
            }
        }
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
                    body: inline_decls_in_stmt_list(
                        &case.body,
                        local_types,
                        global_counts,
                        declared,
                    ),
                })
                .collect(),
            default: default.as_ref().map(|stmts| {
                inline_decls_in_stmt_list(stmts, local_types, global_counts, declared)
            }),
        },
        other => other.clone(),
    }
}

fn can_inline_decl(
    name: &str,
    init: &CExpr,
    local_types: &HashMap<String, CType>,
    global_counts: &HashMap<String, usize>,
    scope_counts: &HashMap<String, usize>,
    declared: &HashSet<String>,
) -> bool {
    local_types.contains_key(name)
        && !declared.contains(name)
        && !expr_reads_var(init, name)
        && global_counts.get(name).copied().unwrap_or(0)
            == scope_counts.get(name).copied().unwrap_or(0)
}

fn assignment_decl_candidate(stmt: &CStmt) -> Option<(&str, &CExpr)> {
    let CStmt::Expr(CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        right,
    }) = stmt
    else {
        return None;
    };
    let CExpr::Var(name) = left.as_ref() else {
        return None;
    };
    Some((name.as_str(), right.as_ref()))
}

fn expr_reads_var(expr: &CExpr, name: &str) -> bool {
    let mut found = false;
    expr.visit(&mut |node| {
        if matches!(node, CExpr::Var(candidate) if candidate == name) {
            found = true;
        }
    });
    found
}

fn count_vars_in_stmts(
    stmts: &[CStmt],
    local_types: &HashMap<String, CType>,
) -> HashMap<String, usize> {
    let mut counts = HashMap::new();
    for stmt in stmts {
        count_vars_in_stmt_into(stmt, local_types, &mut counts);
    }
    counts
}

fn count_vars_in_stmt(
    stmt: &CStmt,
    local_types: &HashMap<String, CType>,
) -> HashMap<String, usize> {
    let mut counts = HashMap::new();
    count_vars_in_stmt_into(stmt, local_types, &mut counts);
    counts
}

fn count_vars_in_stmt_into(
    stmt: &CStmt,
    local_types: &HashMap<String, CType>,
    counts: &mut HashMap<String, usize>,
) {
    match stmt {
        CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
            count_vars_in_expr_into(expr, local_types, counts);
        }
        CStmt::Decl { name, init, .. } => {
            if local_types.contains_key(name) {
                *counts.entry(name.clone()).or_insert(0) += 1;
            }
            if let Some(init) = init {
                count_vars_in_expr_into(init, local_types, counts);
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                count_vars_in_stmt_into(stmt, local_types, counts);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            count_vars_in_expr_into(cond, local_types, counts);
            count_vars_in_stmt_into(then_body, local_types, counts);
            if let Some(else_body) = else_body {
                count_vars_in_stmt_into(else_body, local_types, counts);
            }
        }
        CStmt::While { cond, body } | CStmt::DoWhile { body, cond } => {
            count_vars_in_expr_into(cond, local_types, counts);
            count_vars_in_stmt_into(body, local_types, counts);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                count_vars_in_stmt_into(init, local_types, counts);
            }
            if let Some(cond) = cond {
                count_vars_in_expr_into(cond, local_types, counts);
            }
            if let Some(update) = update {
                count_vars_in_expr_into(update, local_types, counts);
            }
            count_vars_in_stmt_into(body, local_types, counts);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            count_vars_in_expr_into(expr, local_types, counts);
            for case in cases {
                count_vars_in_expr_into(&case.value, local_types, counts);
                for stmt in &case.body {
                    count_vars_in_stmt_into(stmt, local_types, counts);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    count_vars_in_stmt_into(stmt, local_types, counts);
                }
            }
        }
        CStmt::Return(None)
        | CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

fn count_vars_in_expr_into(
    expr: &CExpr,
    local_types: &HashMap<String, CType>,
    counts: &mut HashMap<String, usize>,
) {
    expr.visit(&mut |node| {
        if let CExpr::Var(name) = node
            && local_types.contains_key(name)
        {
            *counts.entry(name.clone()).or_insert(0) += 1;
        }
    });
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

    Some((run_len, scalar_update_stmt(name, total)?))
}

fn scalar_update_stmt(name: &str, delta: i64) -> Option<CStmt> {
    if delta == 0 {
        return Some(CStmt::Empty);
    }
    let (op, amount) = if delta < 0 {
        (BinaryOp::SubAssign, delta.checked_abs()?)
    } else {
        (BinaryOp::AddAssign, delta)
    };
    Some(CStmt::Expr(CExpr::binary(
        op,
        CExpr::Var(name.to_string()),
        CExpr::IntLit(amount),
    )))
}

fn scalar_update_expr(expr: &CExpr) -> Option<CExpr> {
    let (name, delta) = scalar_self_update_delta_expr(expr)?;
    match delta {
        1 => Some(CExpr::Unary {
            op: UnaryOp::PostInc,
            operand: Box::new(CExpr::Var(name.to_string())),
        }),
        -1 => Some(CExpr::Unary {
            op: UnaryOp::PostDec,
            operand: Box::new(CExpr::Var(name.to_string())),
        }),
        0 => None,
        _ => match scalar_update_stmt(name, delta)? {
            CStmt::Expr(expr) => Some(expr),
            _ => None,
        },
    }
}

fn scalar_self_update_delta(stmt: &CStmt) -> Option<(&str, i64)> {
    let CStmt::Expr(expr) = stmt else {
        return None;
    };
    scalar_self_update_delta_expr(expr)
}

fn scalar_self_update_delta_expr(expr: &CExpr) -> Option<(&str, i64)> {
    let CExpr::Binary { op, left, right } = expr else {
        return None;
    };
    let CExpr::Var(lhs_name) = left.as_ref() else {
        return None;
    };
    match op {
        BinaryOp::Assign => update_delta_for_rhs(lhs_name, right),
        BinaryOp::AddAssign => literal_i64(right).map(|delta| (lhs_name.as_str(), delta)),
        BinaryOp::SubAssign => {
            literal_i64(right).and_then(|delta| delta.checked_neg().map(|v| (lhs_name.as_str(), v)))
        }
        _ => None,
    }
}

fn update_delta_for_rhs<'a>(lhs_name: &'a str, rhs: &CExpr) -> Option<(&'a str, i64)> {
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

fn expr_is_var(expr: &CExpr, name: &str) -> bool {
    matches!(expr, CExpr::Var(candidate) if candidate == name)
}

fn literal_i64(expr: &CExpr) -> Option<i64> {
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
    text.replace("*/", "* /").replace(['\r', '\n'], " ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{CLocal, CParam};

    #[test]
    fn test_generate_simple_function() {
        let func = CFunction {
            name: "add".to_string(),
            ret_type: CType::i32(),
            params: vec![
                CParam {
                    ty: CType::i32(),
                    name: "a".to_string(),
                },
                CParam {
                    ty: CType::i32(),
                    name: "b".to_string(),
                },
            ],
            locals: vec![],
            body: vec![CStmt::Return(Some(CExpr::binary(
                BinaryOp::Add,
                CExpr::var("a"),
                CExpr::var("b"),
            )))],
        };

        let code = generate(&func);
        assert!(code.contains("int32_t add(int32_t a, int32_t b)"));
        assert!(code.contains("return a + b;"));
    }

    #[test]
    fn test_generate_if_else() {
        let stmt = CStmt::if_stmt(
            CExpr::binary(BinaryOp::Gt, CExpr::var("x"), CExpr::int(0)),
            CStmt::ret(Some(CExpr::int(1))),
            Some(CStmt::ret(Some(CExpr::int(0)))),
        );

        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        let code = codegen.generate_stmt(&stmt);

        assert!(code.contains("if (x > 0)"));
        assert!(code.contains("return 1;"));
        assert!(code.contains("else"));
        assert!(code.contains("return 0;"));
    }

    #[test]
    fn test_generate_while_loop() {
        let stmt = CStmt::while_loop(
            CExpr::binary(BinaryOp::Lt, CExpr::var("i"), CExpr::int(10)),
            CStmt::expr(CExpr::binary(
                BinaryOp::AddAssign,
                CExpr::var("i"),
                CExpr::int(1),
            )),
        );

        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        let code = codegen.generate_stmt(&stmt);

        assert!(code.contains("while (i < 10)"));
        assert!(code.contains("i++"));
    }

    #[test]
    fn test_generate_compound_unit_updates_as_inc_dec() {
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());
        assert_eq!(
            codegen.generate_expr(&CExpr::binary(
                BinaryOp::AddAssign,
                CExpr::var("i"),
                CExpr::int(1),
            )),
            "i += 1"
        );
        assert!(
            codegen
                .generate_stmt(&CStmt::expr(CExpr::binary(
                    BinaryOp::AddAssign,
                    CExpr::var("i"),
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
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());

        // a + b * c should not need parens around b * c
        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::var("a"),
            CExpr::binary(BinaryOp::Mul, CExpr::var("b"), CExpr::var("c")),
        );
        let code = codegen.generate_expr(&expr);
        assert_eq!(code, "a + b * c");

        // (a + b) * c needs parens
        codegen.output.clear();
        let expr = CExpr::binary(
            BinaryOp::Mul,
            CExpr::binary(BinaryOp::Add, CExpr::var("a"), CExpr::var("b")),
            CExpr::var("c"),
        );
        let code = codegen.generate_expr(&expr);
        assert_eq!(code, "(a + b) * c");
    }

    #[test]
    fn test_additive_negative_literals_render_without_stack_placeholder_noise() {
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());

        let expr = CExpr::binary(BinaryOp::Add, CExpr::var("stack_8"), CExpr::int(-8));
        assert_eq!(codegen.generate_expr(&expr), "stack_8 - 8");

        let expr = CExpr::binary(
            BinaryOp::Sub,
            CExpr::var("rsp"),
            CExpr::uint(0xffffffffffffffb8),
        );
        assert_eq!(codegen.generate_expr(&expr), "rsp + 0x48");
    }

    #[test]
    fn test_additive_negative_linear_terms_render_as_subtraction() {
        let mut codegen = CodeGenerator::new(CodeGenConfig::default());

        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::var("a"),
            CExpr::binary(BinaryOp::Mul, CExpr::var("b"), CExpr::int(-1)),
        );
        assert_eq!(codegen.generate_expr(&expr), "a - b");

        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::var("a"),
            CExpr::binary(BinaryOp::Mul, CExpr::var("b"), CExpr::int(-4)),
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
    fn test_function_with_locals() {
        let func = CFunction {
            name: "test".to_string(),
            ret_type: CType::Void,
            params: vec![],
            locals: vec![
                CLocal {
                    ty: CType::i32(),
                    name: "x".to_string(),
                    stack_offset: Some(-8),
                },
                CLocal {
                    ty: CType::ptr(CType::i8()),
                    name: "p".to_string(),
                    stack_offset: Some(-16),
                },
            ],
            body: vec![CStmt::Return(None)],
        };

        let code = generate(&func);
        assert!(code.contains("int32_t x;"));
        assert!(code.contains("int8_t* p;"));
    }

    #[test]
    fn test_coalesces_adjacent_scalar_self_updates() {
        let func = CFunction::new("updates", CType::Void).with_body(vec![
            CStmt::expr(CExpr::assign(
                CExpr::var("acc"),
                CExpr::binary(BinaryOp::Add, CExpr::var("acc"), CExpr::int(3)),
            )),
            CStmt::expr(CExpr::assign(
                CExpr::var("acc"),
                CExpr::binary(BinaryOp::Add, CExpr::int(4), CExpr::var("acc")),
            )),
            CStmt::expr(CExpr::assign(
                CExpr::var("acc"),
                CExpr::binary(BinaryOp::Sub, CExpr::var("acc"), CExpr::int(2)),
            )),
            CStmt::Return(None),
        ]);

        let code = generate(&func);

        assert!(
            code.contains("acc += 5;"),
            "expected collapsed scalar update, got:\n{code}"
        );
        assert_eq!(code.matches("acc = acc").count(), 0, "{code}");
    }

    #[test]
    fn test_scalar_self_update_coalesce_stops_at_observable_statement() {
        let func = CFunction::new("updates", CType::Void).with_body(vec![
            CStmt::expr(CExpr::assign(
                CExpr::var("acc"),
                CExpr::binary(BinaryOp::Add, CExpr::var("acc"), CExpr::int(1)),
            )),
            CStmt::expr(CExpr::call(CExpr::var("observe"), vec![CExpr::var("acc")])),
            CStmt::expr(CExpr::assign(
                CExpr::var("acc"),
                CExpr::binary(BinaryOp::Add, CExpr::var("acc"), CExpr::int(2)),
            )),
            CStmt::expr(CExpr::assign(
                CExpr::var("acc"),
                CExpr::binary(BinaryOp::Add, CExpr::var("acc"), CExpr::int(3)),
            )),
        ]);

        let code = generate(&func);

        assert!(
            code.contains("acc++;\n    observe(acc);\n    acc += 5;"),
            "observable call should break the update run, got:\n{code}"
        );
    }
}
