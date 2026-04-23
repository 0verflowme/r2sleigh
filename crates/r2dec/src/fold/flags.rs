use std::borrow::Cow;
use std::collections::HashSet;

use r2ssa::{
    CompareKind as PreparedCompareKind, CompareProvenance, FunctionSSABlock, SSAOp, SSAVar,
};

use super::context::FoldingContext;
use super::op_lower::parse_const_value;
use super::{
    MAX_COND_STACK_ALIAS_DEPTH, MAX_PREDICATE_OPERAND_DEPTH, MAX_PREDICATE_SIMPLIFY_DEPTH,
    MAX_SF_SURROGATE_DEPTH, MAX_SUB_LIKE_DEPTH,
};
use crate::analysis;
use crate::analysis::{FlagCompareKind, FlagCompareProvenance, utils};
use crate::ast::{BinaryOp, CExpr, CType, UnaryOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CompareContext {
    Eq,
    Ne,
    SignedNegative,
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct CompareTuple {
    lhs: CExpr,
    rhs: CExpr,
    context: CompareContext,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SymbolicConditionToken {
    Atom(String),
    LParen,
    RParen,
    Not,
    BitNot,
    Star,
    Slash,
    Percent,
    Plus,
    Minus,
    Shl,
    Shr,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    BitAnd,
    BitXor,
    BitOr,
    And,
    Or,
}

struct SymbolicConditionExprParser<'ctx, 'a> {
    ctx: &'ctx FoldingContext<'a>,
    tokens: Vec<SymbolicConditionToken>,
    pos: usize,
}

impl<'ctx, 'a> SymbolicConditionExprParser<'ctx, 'a> {
    fn new(ctx: &'ctx FoldingContext<'a>, text: &str) -> Option<Self> {
        Some(Self {
            ctx,
            tokens: tokenize_symbolic_condition(text)?,
            pos: 0,
        })
    }

    fn parse(mut self) -> Option<CExpr> {
        let expr = self.parse_logical_or()?;
        (self.pos == self.tokens.len()).then_some(expr)
    }

    fn peek(&self) -> Option<&SymbolicConditionToken> {
        self.tokens.get(self.pos)
    }

    fn next(&mut self) -> Option<SymbolicConditionToken> {
        let token = self.tokens.get(self.pos)?.clone();
        self.pos += 1;
        Some(token)
    }

    fn parse_logical_or(&mut self) -> Option<CExpr> {
        let mut expr = self.parse_logical_and()?;
        while matches!(self.peek(), Some(SymbolicConditionToken::Or)) {
            self.next();
            let rhs = self.parse_logical_and()?;
            expr = CExpr::binary(BinaryOp::Or, expr, rhs);
        }
        Some(expr)
    }

    fn parse_logical_and(&mut self) -> Option<CExpr> {
        let mut expr = self.parse_bit_or()?;
        while matches!(self.peek(), Some(SymbolicConditionToken::And)) {
            self.next();
            let rhs = self.parse_bit_or()?;
            expr = CExpr::binary(BinaryOp::And, expr, rhs);
        }
        Some(expr)
    }

    fn parse_bit_or(&mut self) -> Option<CExpr> {
        let mut expr = self.parse_bit_xor()?;
        while matches!(self.peek(), Some(SymbolicConditionToken::BitOr)) {
            self.next();
            let rhs = self.parse_bit_xor()?;
            expr = CExpr::binary(BinaryOp::BitOr, expr, rhs);
        }
        Some(expr)
    }

    fn parse_bit_xor(&mut self) -> Option<CExpr> {
        let mut expr = self.parse_bit_and()?;
        while matches!(self.peek(), Some(SymbolicConditionToken::BitXor)) {
            self.next();
            let rhs = self.parse_bit_and()?;
            expr = CExpr::binary(BinaryOp::BitXor, expr, rhs);
        }
        Some(expr)
    }

    fn parse_bit_and(&mut self) -> Option<CExpr> {
        let mut expr = self.parse_equality()?;
        while matches!(self.peek(), Some(SymbolicConditionToken::BitAnd)) {
            self.next();
            let rhs = self.parse_equality()?;
            expr = CExpr::binary(BinaryOp::BitAnd, expr, rhs);
        }
        Some(expr)
    }

    fn parse_equality(&mut self) -> Option<CExpr> {
        let mut expr = self.parse_relational()?;
        loop {
            let op = match self.peek() {
                Some(SymbolicConditionToken::Eq) => BinaryOp::Eq,
                Some(SymbolicConditionToken::Ne) => BinaryOp::Ne,
                _ => break,
            };
            self.next();
            let rhs = self.parse_relational()?;
            expr = CExpr::binary(op, expr, rhs);
        }
        Some(expr)
    }

    fn parse_relational(&mut self) -> Option<CExpr> {
        let mut expr = self.parse_shift()?;
        loop {
            let op = match self.peek() {
                Some(SymbolicConditionToken::Lt) => BinaryOp::Lt,
                Some(SymbolicConditionToken::Le) => BinaryOp::Le,
                Some(SymbolicConditionToken::Gt) => BinaryOp::Gt,
                Some(SymbolicConditionToken::Ge) => BinaryOp::Ge,
                _ => break,
            };
            self.next();
            let rhs = self.parse_shift()?;
            expr = CExpr::binary(op, expr, rhs);
        }
        Some(expr)
    }

    fn parse_shift(&mut self) -> Option<CExpr> {
        let mut expr = self.parse_additive()?;
        loop {
            let op = match self.peek() {
                Some(SymbolicConditionToken::Shl) => BinaryOp::Shl,
                Some(SymbolicConditionToken::Shr) => BinaryOp::Shr,
                _ => break,
            };
            self.next();
            let rhs = self.parse_additive()?;
            expr = CExpr::binary(op, expr, rhs);
        }
        Some(expr)
    }

    fn parse_additive(&mut self) -> Option<CExpr> {
        let mut expr = self.parse_multiplicative()?;
        loop {
            let op = match self.peek() {
                Some(SymbolicConditionToken::Plus) => BinaryOp::Add,
                Some(SymbolicConditionToken::Minus) => BinaryOp::Sub,
                _ => break,
            };
            self.next();
            let rhs = self.parse_multiplicative()?;
            expr = CExpr::binary(op, expr, rhs);
        }
        Some(expr)
    }

    fn parse_multiplicative(&mut self) -> Option<CExpr> {
        let mut expr = self.parse_unary()?;
        loop {
            let op = match self.peek() {
                Some(SymbolicConditionToken::Star) => BinaryOp::Mul,
                Some(SymbolicConditionToken::Slash) => BinaryOp::Div,
                Some(SymbolicConditionToken::Percent) => BinaryOp::Mod,
                _ => break,
            };
            self.next();
            let rhs = self.parse_unary()?;
            expr = CExpr::binary(op, expr, rhs);
        }
        Some(expr)
    }

    fn parse_unary(&mut self) -> Option<CExpr> {
        match self.peek() {
            Some(SymbolicConditionToken::Not) => {
                self.next();
                Some(CExpr::unary(UnaryOp::Not, self.parse_unary()?))
            }
            Some(SymbolicConditionToken::BitNot) => {
                self.next();
                Some(CExpr::unary(UnaryOp::BitNot, self.parse_unary()?))
            }
            Some(SymbolicConditionToken::Minus) => {
                self.next();
                Some(CExpr::unary(UnaryOp::Neg, self.parse_unary()?))
            }
            Some(SymbolicConditionToken::Star) => {
                self.next();
                Some(CExpr::deref(self.parse_unary()?))
            }
            _ => self.parse_primary(),
        }
    }

    fn parse_primary(&mut self) -> Option<CExpr> {
        match self.next()? {
            SymbolicConditionToken::LParen => {
                let expr = self.parse_logical_or()?;
                matches!(self.next(), Some(SymbolicConditionToken::RParen)).then_some(expr)
            }
            SymbolicConditionToken::Atom(atom) => {
                let lower = atom.to_ascii_lowercase();
                if lower == "true" {
                    Some(CExpr::IntLit(1))
                } else if lower == "false" {
                    Some(CExpr::IntLit(0))
                } else {
                    Some(
                        self.ctx
                            .parse_expr_from_name(&atom)
                            .unwrap_or(CExpr::Var(atom)),
                    )
                }
            }
            _ => None,
        }
    }
}

fn tokenize_symbolic_condition(text: &str) -> Option<Vec<SymbolicConditionToken>> {
    let mut tokens = Vec::new();
    let chars = text.chars().collect::<Vec<_>>();
    let mut i = 0usize;
    while i < chars.len() {
        let ch = chars[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }
        let rest = &chars[i..];
        let push_two = |token: SymbolicConditionToken, i: &mut usize, tokens: &mut Vec<_>| {
            tokens.push(token);
            *i += 2;
        };
        if rest.len() >= 2 {
            match (rest[0], rest[1]) {
                ('|', '|') => {
                    push_two(SymbolicConditionToken::Or, &mut i, &mut tokens);
                    continue;
                }
                ('&', '&') => {
                    push_two(SymbolicConditionToken::And, &mut i, &mut tokens);
                    continue;
                }
                ('=', '=') => {
                    push_two(SymbolicConditionToken::Eq, &mut i, &mut tokens);
                    continue;
                }
                ('!', '=') => {
                    push_two(SymbolicConditionToken::Ne, &mut i, &mut tokens);
                    continue;
                }
                ('<', '=') => {
                    push_two(SymbolicConditionToken::Le, &mut i, &mut tokens);
                    continue;
                }
                ('>', '=') => {
                    push_two(SymbolicConditionToken::Ge, &mut i, &mut tokens);
                    continue;
                }
                ('<', '<') => {
                    push_two(SymbolicConditionToken::Shl, &mut i, &mut tokens);
                    continue;
                }
                ('>', '>') => {
                    push_two(SymbolicConditionToken::Shr, &mut i, &mut tokens);
                    continue;
                }
                _ => {}
            }
        }
        match ch {
            '(' => tokens.push(SymbolicConditionToken::LParen),
            ')' => tokens.push(SymbolicConditionToken::RParen),
            '!' => tokens.push(SymbolicConditionToken::Not),
            '~' => tokens.push(SymbolicConditionToken::BitNot),
            '*' => tokens.push(SymbolicConditionToken::Star),
            '/' => tokens.push(SymbolicConditionToken::Slash),
            '%' => tokens.push(SymbolicConditionToken::Percent),
            '+' => tokens.push(SymbolicConditionToken::Plus),
            '-' => tokens.push(SymbolicConditionToken::Minus),
            '<' => tokens.push(SymbolicConditionToken::Lt),
            '>' => tokens.push(SymbolicConditionToken::Gt),
            '&' => tokens.push(SymbolicConditionToken::BitAnd),
            '^' => tokens.push(SymbolicConditionToken::BitXor),
            '|' => tokens.push(SymbolicConditionToken::BitOr),
            '=' => return None,
            _ => {
                let start = i;
                while i < chars.len() {
                    let ch = chars[i];
                    if ch.is_whitespace()
                        || matches!(
                            ch,
                            '(' | ')'
                                | '!'
                                | '~'
                                | '*'
                                | '/'
                                | '%'
                                | '+'
                                | '-'
                                | '<'
                                | '>'
                                | '&'
                                | '^'
                                | '|'
                                | '='
                        )
                    {
                        break;
                    }
                    i += 1;
                }
                if start == i {
                    return None;
                }
                tokens.push(SymbolicConditionToken::Atom(
                    chars[start..i].iter().collect(),
                ));
                continue;
            }
        }
        i += 1;
    }
    Some(tokens)
}

impl<'a> FoldingContext<'a> {
    fn finalize_condition_expr(&self, expr: CExpr) -> CExpr {
        let expr = self.normalize_local_branch_expr(expr);
        let expr = self.rewrite_stack_expr(expr);
        let expr = self.rewrite_condition_stack_aliases(expr);
        let expr = self.expand_generic_scalar_predicate_aliases(expr, 0);
        let expr = self.rewrite_call_result_predicate_owners(expr, 0);
        let expr = self.simplify_condition_expr(expr);
        let expr = self.rewrite_call_result_predicate_owners(expr, 0);
        self.simplify_condition_expr(expr)
    }

    fn rewrite_call_result_predicate_owners(&self, expr: CExpr, depth: u32) -> CExpr {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return expr;
        }

        let owner_name_for_source = |ctx: &FoldingContext<'_>, source: (u64, usize)| {
            ctx.stable_owned_call_result_name_for_source(source)
                .filter(|name| {
                    !ctx.is_low_signal_visible_name(name)
                        && !ctx.is_transient_visible_name(name)
                        && !name.ends_with("_home")
                        && !name.starts_with("var_")
                        && !name.starts_with("local_")
                        && !name.starts_with("stack_")
                        && !name.starts_with("arg_")
                })
        };

        match expr {
            CExpr::Var(name) => self
                .call_result_source_for_ssa_name(&name)
                .or_else(|| self.local_post_call_source_for_ssa_name(&name))
                .and_then(|source| owner_name_for_source(self, source))
                .map(CExpr::Var)
                .unwrap_or(CExpr::Var(name)),
            call @ CExpr::Call { .. } => self
                .source_call_for_call_expr(&call)
                .and_then(|source| owner_name_for_source(self, source))
                .map(CExpr::Var)
                .unwrap_or_else(|| {
                    call.map_children(&mut |child| {
                        self.rewrite_call_result_predicate_owners(child, depth + 1)
                    })
                }),
            other => other.map_children(&mut |child| {
                self.rewrite_call_result_predicate_owners(child, depth + 1)
            }),
        }
    }

    fn prepared_branch_condition_expr(&self, block_addr: u64) -> Option<CExpr> {
        self.prepared_predicate_view()
            .and_then(|view| view.branch_expr_for_block(block_addr).cloned())
    }

    fn symbolic_branch_condition_expr(&self, block_addr: u64) -> Option<CExpr> {
        match self
            .inputs
            .semantic_artifact?
            .exact_branch_truth_for_block(block_addr)
        {
            Some(true) => Some(CExpr::IntLit(1)),
            Some(false) => Some(CExpr::IntLit(0)),
            None => None,
        }
    }

    fn symbolic_actionable_compiled_condition(
        &self,
        block_addr: u64,
    ) -> Option<&r2sym::BackwardConditionSummary> {
        self.inputs
            .semantic_artifact?
            .actionable_compiled_condition_for_block(block_addr)
    }

    fn symbolic_actionable_compiled_condition_expr(&self, block_addr: u64) -> Option<CExpr> {
        let compiled = self.symbolic_actionable_compiled_condition(block_addr)?;
        SymbolicConditionExprParser::new(self, compiled.simplified.trim())
            .and_then(SymbolicConditionExprParser::parse)
            .map(|expr| self.finalize_condition_expr(expr))
    }

    fn symbolic_actionable_memory_condition_expr(&self, block_addr: u64) -> Option<CExpr> {
        fn memory_term_rank(term: &r2sym::BackwardMemoryCondition) -> (u8, bool, bool, i64, i64) {
            let evidence_rank = match term.evidence().tier {
                r2sym::SemanticConfidence::Exact => 3,
                r2sym::SemanticConfidence::Likely => 2,
                r2sym::SemanticConfidence::Heuristic => 1,
                r2sym::SemanticConfidence::Residual => 0,
            };
            (
                evidence_rank,
                term.exact_value,
                term.exact_offset,
                -(term.offset_hi - term.offset_lo),
                -term.offset_lo.abs(),
            )
        }

        let term = self
            .inputs
            .semantic_artifact?
            .actionable_memory_terms_for_block(block_addr)
            .into_iter()
            .filter(|term| {
                term.value_expr
                    .as_ref()
                    .is_some_and(|value| value != &term.expr)
            })
            .max_by_key(|term| memory_term_rank(term))?;
        let condition = format!("({} == {})", term.expr.trim(), term.value_expr.as_deref()?);
        SymbolicConditionExprParser::new(self, &condition)
            .and_then(SymbolicConditionExprParser::parse)
            .map(|expr| self.finalize_condition_expr(expr))
    }

    fn prepared_predicate_view(&self) -> Option<Cow<'_, analysis::PreparedSemanticView>> {
        self.prepared_semantic_view().map(Cow::Borrowed)
    }

    fn structured_predicate_candidate_should_win(
        &self,
        current: &CExpr,
        candidate: &CExpr,
    ) -> bool {
        fn lhs(expr: &CExpr) -> Option<&CExpr> {
            match expr {
                CExpr::Binary { left, .. } => Some(left.as_ref()),
                _ => None,
            }
        }

        fn is_simple_named_carrier(expr: &CExpr) -> bool {
            matches!(expr, CExpr::Var(_))
        }

        fn is_structured_scalar_expr(expr: &CExpr) -> bool {
            matches!(
                expr,
                CExpr::Binary {
                    op: BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Shl
                        | BinaryOp::Shr,
                    ..
                }
            )
        }

        fn strips_wrappers(expr: &CExpr) -> &CExpr {
            match expr {
                CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => strips_wrappers(inner),
                _ => expr,
            }
        }

        fn compare_operands(expr: &CExpr) -> Option<(&CExpr, &CExpr)> {
            match strips_wrappers(expr) {
                CExpr::Binary {
                    op:
                        BinaryOp::Eq
                        | BinaryOp::Ne
                        | BinaryOp::Lt
                        | BinaryOp::Le
                        | BinaryOp::Gt
                        | BinaryOp::Ge,
                    left,
                    right,
                } => Some((left.as_ref(), right.as_ref())),
                _ => None,
            }
        }

        let is_semantic_operand = |expr: &CExpr| match strips_wrappers(expr) {
            CExpr::Var(name) => {
                !self.is_low_signal_visible_name(name) && !self.is_transient_visible_name(name)
            }
            CExpr::Binary { .. }
            | CExpr::Member { .. }
            | CExpr::PtrMember { .. }
            | CExpr::Subscript { .. }
            | CExpr::Call { .. } => !self.expr_is_address_artifact_in_scalar_context(expr),
            _ => false,
        };

        let compare_to_zero_shape = |expr: &CExpr| {
            compare_operands(expr).is_some_and(|(lhs, rhs)| {
                (self.is_zero_expr(lhs) && is_semantic_operand(rhs))
                    || (self.is_zero_expr(rhs) && is_semantic_operand(lhs))
            })
        };

        let richer_compare_shape = |expr: &CExpr| {
            compare_operands(expr).is_some_and(|(lhs, rhs)| {
                !self.is_zero_expr(lhs)
                    && !self.is_zero_expr(rhs)
                    && is_semantic_operand(lhs)
                    && is_semantic_operand(rhs)
            })
        };

        let Some(current_lhs) = lhs(current) else {
            return compare_to_zero_shape(current) && richer_compare_shape(candidate);
        };
        let Some(candidate_lhs) = lhs(candidate) else {
            return false;
        };

        (is_simple_named_carrier(current_lhs)
            && is_structured_scalar_expr(candidate_lhs)
            && !self.expr_is_address_artifact_in_scalar_context(candidate))
            || (compare_to_zero_shape(current) && richer_compare_shape(candidate))
    }

    fn prepared_candidate_needs_legacy_compare_help(&self, expr: &CExpr) -> bool {
        fn strips_wrappers(expr: &CExpr) -> &CExpr {
            match expr {
                CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => strips_wrappers(inner),
                CExpr::Unary {
                    op: UnaryOp::Not,
                    operand,
                } => strips_wrappers(operand),
                _ => expr,
            }
        }

        fn compare_operands(expr: &CExpr) -> Option<(&CExpr, &CExpr)> {
            match strips_wrappers(expr) {
                CExpr::Binary {
                    op:
                        BinaryOp::Eq
                        | BinaryOp::Ne
                        | BinaryOp::Lt
                        | BinaryOp::Le
                        | BinaryOp::Gt
                        | BinaryOp::Ge,
                    left,
                    right,
                } => Some((left.as_ref(), right.as_ref())),
                _ => None,
            }
        }

        let generic_scalar_expr = |expr: &CExpr| {
            fn recurse(ctx: &FoldingContext<'_>, expr: &CExpr) -> bool {
                match expr {
                    CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => recurse(ctx, inner),
                    CExpr::Unary { operand, .. } => recurse(ctx, operand),
                    CExpr::Binary { left, right, .. } => recurse(ctx, left) && recurse(ctx, right),
                    CExpr::Var(name) => {
                        ctx.is_generic_stack_local_owner_name(name)
                            || name.starts_with("local_")
                            || name.starts_with("var_")
                            || name.starts_with("stack_")
                            || name.starts_with("arg_")
                    }
                    CExpr::IntLit(_)
                    | CExpr::UIntLit(_)
                    | CExpr::FloatLit(_)
                    | CExpr::CharLit(_) => true,
                    _ => false,
                }
            }

            recurse(self, strips_wrappers(expr))
        };

        compare_operands(expr)
            .is_some_and(|(lhs, rhs)| generic_scalar_expr(lhs) || generic_scalar_expr(rhs))
    }

    fn expand_generic_scalar_predicate_aliases(&self, expr: CExpr, depth: u32) -> CExpr {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return expr;
        }

        match expr {
            CExpr::Var(name)
                if self.is_generic_stack_local_owner_name(&name)
                    || name.starts_with("local_")
                    || name.starts_with("var_")
                    || name.starts_with("stack_") =>
            {
                let resolved = self
                    .lookup_definition(&name)
                    .or_else(|| self.formatted_defs_map().get(&name).cloned());
                if let Some(inner) = resolved
                    && (self.is_predicate_like_expr(&inner)
                        || matches!(
                            inner,
                            CExpr::Binary {
                                op: BinaryOp::Add
                                    | BinaryOp::Sub
                                    | BinaryOp::Mul
                                    | BinaryOp::Div
                                    | BinaryOp::Mod
                                    | BinaryOp::Shl
                                    | BinaryOp::Shr
                                    | BinaryOp::BitAnd
                                    | BinaryOp::BitOr
                                    | BinaryOp::BitXor,
                                ..
                            } | CExpr::Unary { .. }
                        ))
                    && !self.expr_is_address_artifact_in_scalar_context(&inner)
                {
                    return self.expand_generic_scalar_predicate_aliases(
                        self.resolve_predicate_expr_tree(&inner),
                        depth + 1,
                    );
                }
                CExpr::Var(name)
            }
            other => other.map_children(&mut |child| {
                self.expand_generic_scalar_predicate_aliases(child, depth + 1)
            }),
        }
    }

    pub fn extract_condition_from_block(&self, block: &FunctionSSABlock) -> Option<CExpr> {
        if let Some(cond) = self.symbolic_actionable_compiled_condition_expr(block.addr) {
            return Some(cond);
        }

        if let Some(cond) = self.symbolic_actionable_memory_condition_expr(block.addr) {
            return Some(cond);
        }

        if let Some(cond) = self.symbolic_branch_condition_expr(block.addr) {
            return Some(cond);
        }

        let (branch_idx, cond) =
            block
                .ops
                .iter()
                .enumerate()
                .rev()
                .find_map(|(idx, op)| match op {
                    SSAOp::CBranch { cond, .. } => Some((idx, cond)),
                    _ => None,
                })?;
        let prepared_branch_candidate = self.prepared_branch_condition_expr(block.addr);
        let prepared_block_candidate =
            self.prepared_predicate_candidate_for_branch_block(block.addr, cond);
        let prepared_var_candidate = self.prepared_predicate_candidate_for_var(cond);
        let exact_compiled = self.symbolic_actionable_compiled_condition(block.addr);
        let allow_legacy_flag_provenance = exact_compiled.is_none()
            && ![
                prepared_branch_candidate.as_ref(),
                prepared_block_candidate.as_ref(),
                prepared_var_candidate.as_ref(),
            ]
            .into_iter()
            .flatten()
            .any(|expr| !self.prepared_candidate_needs_legacy_compare_help(expr));

        let prev_block_addr = self.current_block_addr.replace(Some(block.addr));
        let prev_op_idx = self.current_op_idx.replace(Some(branch_idx));

        let mut result = None;
        {
            let mut consider = |candidate: Option<CExpr>| {
                if let Some(expr) = candidate {
                    let finalized = self.finalize_condition_expr(expr);
                    if !self.is_degenerate_constant_condition(&finalized) {
                        if let Some(current) = result.as_ref()
                            && self.structured_predicate_candidate_should_win(current, &finalized)
                        {
                            result = Some(finalized);
                            return;
                        }
                        result = self
                            .choose_preferred_scalar_predicate_expr(result.take(), Some(finalized));
                    }
                }
            };

            consider(prepared_branch_candidate);
            consider(prepared_block_candidate);
            consider(prepared_var_candidate);
        }
        if result.is_some() && !allow_legacy_flag_provenance {
            self.current_block_addr.set(prev_block_addr);
            self.current_op_idx.set(prev_op_idx);
            return result;
        }
        {
            let mut consider = |candidate: Option<CExpr>| {
                if let Some(expr) = candidate {
                    let finalized = self.finalize_condition_expr(expr);
                    if !self.is_degenerate_constant_condition(&finalized) {
                        if let Some(current) = result.as_ref()
                            && self.structured_predicate_candidate_should_win(current, &finalized)
                        {
                            result = Some(finalized);
                            return;
                        }
                        result = self
                            .choose_preferred_scalar_predicate_expr(result.take(), Some(finalized));
                    }
                }
            };

            consider(self.local_branch_condition_expr(block, branch_idx, cond, 0));
            if allow_legacy_flag_provenance {
                consider(self.branch_compare_provenance_expr(block, branch_idx, cond, 0));
                let cond_name = cond.display_name();
                if let Some(prov) = self.lookup_flag_compare_provenance(&cond_name) {
                    consider(self.compare_provenance_expr_for_branch(&prov));
                }
            }
        }

        let fallback = self.finalize_condition_expr(self.get_condition_expr(cond));
        let result = match result {
            Some(current) => {
                if self.structured_predicate_candidate_should_win(&fallback, &current) {
                    Some(current)
                } else if self.structured_predicate_candidate_should_win(&current, &fallback) {
                    Some(fallback)
                } else {
                    self.choose_preferred_scalar_predicate_expr(
                        Some(current),
                        Some(fallback.clone()),
                    )
                    .or(Some(fallback))
                }
            }
            None => Some(fallback),
        };

        self.current_block_addr.set(prev_block_addr);
        self.current_op_idx.set(prev_op_idx);
        result
    }

    fn branch_compare_provenance_expr(
        &self,
        block: &FunctionSSABlock,
        branch_idx: usize,
        cond: &SSAVar,
        depth: u32,
    ) -> Option<CExpr> {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return None;
        }

        let cond_name = cond.display_name();
        let allow_legacy_flag_provenance = self
            .current_block_addr
            .get()
            .and_then(|block_addr| {
                self.prepared_branch_condition_expr(block_addr)
                    .or_else(|| {
                        self.prepared_predicate_candidate_for_branch_block(block_addr, cond)
                    })
                    .or_else(|| self.prepared_predicate_candidate_for_var(cond))
            })
            .as_ref()
            .map(|expr| self.prepared_candidate_needs_legacy_compare_help(expr))
            .unwrap_or(true);
        if allow_legacy_flag_provenance
            && let Some(prov) = self.lookup_flag_compare_provenance(&cond_name)
            && let Some(expr) = self.compare_provenance_expr_for_branch(&prov)
        {
            return Some(expr);
        }

        for (idx, op) in block.ops[..branch_idx].iter().enumerate().rev() {
            if op.dst() != Some(cond) {
                continue;
            }

            return match op {
                SSAOp::Copy { src, .. }
                | SSAOp::IntZExt { src, .. }
                | SSAOp::IntSExt { src, .. }
                | SSAOp::Subpiece { src, .. } => {
                    self.branch_compare_provenance_expr(block, idx, src, depth + 1)
                }
                SSAOp::BoolNot { src, .. } => self
                    .branch_compare_provenance_expr(block, idx, src, depth + 1)
                    .map(|expr| CExpr::unary(UnaryOp::Not, expr)),
                _ => None,
            };
        }

        None
    }

    pub(super) fn normalize_assignment_predicate_rhs(&self, rhs: CExpr) -> CExpr {
        let rhs = if self.is_assignment_predicate_expr(&rhs) {
            self.finalize_condition_expr(rhs)
        } else {
            rhs
        };

        match rhs {
            CExpr::Binary { op, left, right }
                if matches!(
                    op,
                    BinaryOp::Eq
                        | BinaryOp::Ne
                        | BinaryOp::Lt
                        | BinaryOp::Le
                        | BinaryOp::Gt
                        | BinaryOp::Ge
                ) =>
            {
                let left = self
                    .stable_owned_call_result_expr_for_call_expr(&left)
                    .unwrap_or(*left);
                let right = self
                    .stable_owned_call_result_expr_for_call_expr(&right)
                    .unwrap_or(*right);
                CExpr::binary(op, left, right)
            }
            other => other,
        }
    }

    pub(super) fn predicate_exprs_map(&self) -> &std::collections::HashMap<String, CExpr> {
        &self.state.analysis_ctx.flags().predicate_exprs
    }

    pub(super) fn flag_compare_provenance_map(
        &self,
    ) -> &std::collections::HashMap<String, FlagCompareProvenance> {
        &self.state.analysis_ctx.flags().compare_provenance
    }

    pub(super) fn lookup_predicate_expr(&self, name: &str) -> Option<CExpr> {
        if let Some(expr) = self.predicate_exprs_map().get(name) {
            return Some(expr.clone());
        }
        let lower = name.to_ascii_lowercase();
        if let Some(expr) = self.predicate_exprs_map().get(&lower) {
            return Some(expr.clone());
        }
        if let Some(ssa_name) = self.find_ssa_name_for_rendered_alias(name)
            && let Some(expr) = self.predicate_exprs_map().get(&ssa_name)
        {
            return Some(expr.clone());
        }
        None
    }

    pub(super) fn predicate_candidate_for_var(&self, var: &SSAVar) -> Option<CExpr> {
        let key = var.display_name();
        let prepared_value_id = self.prepared_value_id_for_var(var);
        let prepared = self
            .prepared_predicates()
            .and_then(|facts| {
                facts
                    .predicates
                    .values()
                    .find(|predicate| Some(predicate.condition) == prepared_value_id)
                    .and_then(|predicate| self.prepared_branch_condition_expr(predicate.block_addr))
            })
            .map(|expr| self.resolve_predicate_expr_tree(&expr))
            .or_else(|| {
                self.prepared_predicate_view()
                    .and_then(|view| view.predicate_expr_for_cond(var).cloned())
                    .map(|expr| self.resolve_predicate_expr_tree(&expr))
            })
            .or_else(|| self.prepared_predicate_candidate_for_var(var));
        let legacy = self
            .lookup_predicate_expr(&key)
            .or_else(|| {
                self.lookup_definition(&key)
                    .filter(|expr| self.is_assignment_predicate_expr(expr))
            })
            .or_else(|| {
                self.formatted_defs_map()
                    .get(&key)
                    .filter(|expr| self.is_assignment_predicate_expr(expr))
                    .cloned()
            })
            .or_else(|| {
                let rendered = self.var_name(var);
                if self.is_transient_visible_name(&rendered)
                    || self.is_low_signal_visible_name(&rendered)
                {
                    return None;
                }
                self.lookup_predicate_expr(&rendered).or_else(|| {
                    self.formatted_defs_map()
                        .get(&rendered)
                        .filter(|expr| self.is_assignment_predicate_expr(expr))
                        .cloned()
                })
            });
        self.choose_preferred_scalar_predicate_expr(prepared, legacy)
    }

    pub(super) fn resolve_predicate_rhs_for_var(&self, src: &SSAVar, fallback: CExpr) -> CExpr {
        let fallback_simplified = self.normalize_assignment_predicate_rhs(fallback);
        if let Some(candidate) = self.predicate_candidate_for_var(src)
            && self.is_assignment_predicate_expr(&candidate)
        {
            return self
                .choose_preferred_scalar_predicate_expr(
                    Some(fallback_simplified.clone()),
                    Some(self.simplify_condition_expr(candidate)),
                )
                .unwrap_or(fallback_simplified);
        }

        fallback_simplified
    }

    fn prepared_predicate_candidate_for_var(&self, var: &SSAVar) -> Option<CExpr> {
        if let Some(expr) = self
            .prepared_predicate_view()
            .and_then(|view| view.predicate_expr_for_cond(var).cloned())
        {
            return Some(self.resolve_predicate_expr_tree(&expr));
        }
        if let Some(predicate) = self
            .prepared_predicates()?
            .predicates
            .values()
            .find(|predicate| Some(predicate.condition) == self.prepared_value_id_for_var(var))
            && let Some(expr) = self
                .prepared_predicate_view()
                .and_then(|view| view.branch_expr_for_block(predicate.block_addr).cloned())
        {
            return Some(self.resolve_predicate_expr_tree(&expr));
        }
        let compare = self
            .prepared_predicates()?
            .predicates
            .values()
            .find(|predicate| Some(predicate.condition) == self.prepared_value_id_for_var(var))?
            .comparison
            .as_ref()?;
        self.prepared_compare_provenance_expr(compare)
    }

    fn prepared_predicate_candidate_for_branch_block(
        &self,
        block_addr: u64,
        var: &SSAVar,
    ) -> Option<CExpr> {
        if let Some(expr) = self
            .prepared_predicate_view()
            .and_then(|view| view.branch_expr_for_block(block_addr).cloned())
        {
            return Some(self.resolve_predicate_expr_tree(&expr));
        }
        let facts = self.prepared_predicates()?;
        let compare = facts
            .predicates
            .values()
            .find(|predicate| {
                predicate.block_addr == block_addr
                    && Some(predicate.condition) == self.prepared_value_id_for_var(var)
            })
            .and_then(|predicate| predicate.comparison.as_ref())
            .or_else(|| {
                facts
                    .block_assumptions
                    .values()
                    .flat_map(|assumptions| assumptions.iter())
                    .find(|assumption| assumption.predecessor == block_addr)
                    .and_then(|assumption| facts.predicates.get(&assumption.predicate))
                    .and_then(|predicate| predicate.comparison.as_ref())
            })?;
        self.prepared_compare_provenance_expr(compare)
    }

    #[cfg(test)]
    pub(super) fn prepared_predicate_candidate_for_branch_block_for_test(
        &self,
        block_addr: u64,
        var: &SSAVar,
    ) -> Option<CExpr> {
        self.prepared_predicate_candidate_for_branch_block(block_addr, var)
    }

    fn prepared_compare_provenance_expr(&self, prov: &CompareProvenance) -> Option<CExpr> {
        let lhs_var = self.prepared_var_for_value_id(prov.lhs)?;
        let rhs_var = self.prepared_var_for_value_id(prov.rhs)?;
        let compare_width = lhs_var.size.max(rhs_var.size);
        let lhs = self.resolve_prepared_predicate_operand_with_width(lhs_var, compare_width);
        let rhs = self.resolve_prepared_predicate_operand_with_width(rhs_var, compare_width);
        match prov.kind {
            PreparedCompareKind::Equal => Some(CExpr::binary(BinaryOp::Eq, lhs, rhs)),
            PreparedCompareKind::NotEqual => Some(CExpr::binary(BinaryOp::Ne, lhs, rhs)),
            PreparedCompareKind::Less | PreparedCompareKind::SignedLess => {
                Some(CExpr::binary(BinaryOp::Lt, lhs, rhs))
            }
            PreparedCompareKind::LessEqual | PreparedCompareKind::SignedLessEqual => {
                Some(CExpr::binary(BinaryOp::Le, lhs, rhs))
            }
        }
    }

    #[cfg(test)]
    pub(super) fn resolve_prepared_predicate_operand(&self, var: &SSAVar) -> CExpr {
        self.resolve_prepared_predicate_operand_with_width(var, var.size)
    }

    fn resolve_prepared_predicate_operand_with_width(
        &self,
        var: &SSAVar,
        compare_width: u32,
    ) -> CExpr {
        let rooted = self
            .prepared_canonical_value_root(var)
            .unwrap_or_else(|| var.clone());
        if rooted.is_const() {
            return utils::compare_const_to_expr_with_width(
                &rooted,
                compare_width.max(rooted.size),
            );
        }
        let original_name = var.display_name();
        let rooted_name = rooted.display_name();
        let mut best = None;

        for candidate in [var, &rooted] {
            let candidate_name = candidate.display_name();
            best = self.choose_preferred_scalar_predicate_expr(
                best,
                self.prepared_predicate_view()
                    .and_then(|view| view.owner_expr_for_var(candidate).cloned())
                    .filter(|expr| {
                        !self.expr_is_address_artifact_in_scalar_context(expr)
                            && !matches!(
                                expr,
                                CExpr::Var(name)
                                    if self.is_low_signal_visible_name(name)
                                        || self.is_transient_visible_name(name)
                                        || name.ends_with("_home")
                                        || name.starts_with("var_")
                                        || name.starts_with("local_")
                                        || name.starts_with("stack_")
                                        || name.starts_with("arg_")
                            )
                    }),
            );
            if let Some(alias) = self
                .stack_slot_provenance_for_name(&candidate_name)
                .filter(|slot| slot.is_scalar_predicate_carrier())
                .map(|slot| slot.offset)
                .and_then(|offset| self.resolve_stack_var(offset))
                .filter(|alias| {
                    !self.is_low_signal_visible_name(alias)
                        && !self.is_transient_visible_name(alias)
                })
            {
                best = self.choose_preferred_scalar_predicate_expr(best, Some(CExpr::Var(alias)));
            }
            best = self.choose_preferred_scalar_predicate_expr(
                best,
                self.call_result_source_for_ssa_name(&candidate_name)
                    .or_else(|| self.local_post_call_source_for_ssa_name(&candidate_name))
                    .and_then(|source| {
                        self.stable_owned_call_result_name_for_source(source)
                            .map(CExpr::Var)
                            .or_else(|| self.stable_owned_call_result_expr_for_source(source))
                            .or_else(|| self.synthesized_call_expr_for_source_call(source))
                    }),
            );
            best = self.choose_preferred_scalar_predicate_expr(
                best,
                self.stack_slot_provenance_for_name(&candidate_name)
                    .map(|slot| slot.offset)
                    .or_else(|| self.extract_stack_offset_from_var(candidate))
                    .and_then(|offset| self.resolve_stack_var(offset))
                    .filter(|name| {
                        !self.is_low_signal_visible_name(name)
                            && !self.is_transient_visible_name(name)
                            && !name.ends_with("_home")
                            && !name.starts_with("var_")
                            && !name.starts_with("local_")
                            && !name.starts_with("stack_")
                            && !name.starts_with("arg_")
                    })
                    .map(CExpr::Var),
            );
            if let Some(alias) = self.arg_alias_for_rendered_name(&candidate_name) {
                best = self.choose_preferred_scalar_predicate_expr(best, Some(CExpr::Var(alias)));
            }
            let visible_name = self.var_name(candidate);
            if !self.is_low_signal_visible_name(&visible_name)
                && !self.is_transient_visible_name(&visible_name)
                && !visible_name.eq_ignore_ascii_case(&candidate_name)
            {
                best = self
                    .choose_preferred_scalar_predicate_expr(best, Some(CExpr::Var(visible_name)));
            }
            best = self.choose_preferred_scalar_predicate_expr(
                best,
                self.best_visible_definition(&candidate_name),
            );
        }
        let resolved = self.resolve_predicate_operand(
            &self.origin_name_to_expr(&rooted_name),
            0,
            &mut HashSet::new(),
        );
        if !original_name.eq_ignore_ascii_case(&rooted_name) {
            let original_resolved = self.resolve_predicate_operand(
                &self.origin_name_to_expr(&original_name),
                0,
                &mut HashSet::new(),
            );
            if let Some(current) = best.as_ref()
                && self.structured_predicate_candidate_should_win(current, &original_resolved)
            {
                best = Some(original_resolved);
            } else {
                best = self.choose_preferred_scalar_predicate_expr(best, Some(original_resolved));
            }
        }
        if let Some(current) = best.as_ref()
            && self.structured_predicate_candidate_should_win(current, &resolved)
        {
            return resolved;
        }
        self.choose_preferred_scalar_predicate_expr(best, Some(resolved.clone()))
            .unwrap_or(resolved)
    }

    fn resolve_predicate_expr_tree(&self, expr: &CExpr) -> CExpr {
        self.resolve_predicate_expr_tree_with_visited(expr, &mut HashSet::new())
    }

    fn resolve_predicate_expr_tree_with_visited(
        &self,
        expr: &CExpr,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        let mut recurse =
            |child: CExpr| self.resolve_predicate_expr_tree_with_visited(&child, visited);
        let mapped = expr.clone().map_children(&mut recurse);
        self.resolve_predicate_operand(&mapped, 0, visited)
    }

    pub(super) fn is_assignment_predicate_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                is_cpu_flag(&name.to_lowercase())
                    || self.flag_only_values_set().contains(name)
                    || self.condition_vars_set().contains(name)
                    || self.lookup_predicate_expr(name).is_some()
            }
            CExpr::Unary {
                op: UnaryOp::Not, ..
            } => true,
            CExpr::Binary { op, .. } => matches!(
                op,
                BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
                    | BinaryOp::And
                    | BinaryOp::Or
                    | BinaryOp::BitAnd
            ),
            CExpr::Paren(inner) => self.is_assignment_predicate_expr(inner),
            CExpr::Cast { expr: inner, .. } => self.is_assignment_predicate_expr(inner),
            _ => false,
        }
    }

    /// Extract a condition expression from a branch operation.
    pub fn extract_condition(&self, op: &SSAOp) -> Option<CExpr> {
        match op {
            SSAOp::CBranch { cond, .. } => {
                if let Some(expr) = self.prepared_predicate_candidate_for_var(cond) {
                    let finalized = self.finalize_condition_expr(expr);
                    if !self.prepared_candidate_needs_legacy_compare_help(&finalized) {
                        return Some(finalized);
                    }
                    return Some(
                        self.choose_preferred_scalar_predicate_expr(
                            Some(finalized.clone()),
                            self.lookup_flag_compare_provenance(&cond.display_name())
                                .and_then(|prov| self.compare_provenance_expr_for_branch(&prov))
                                .map(|expr| self.finalize_condition_expr(expr)),
                        )
                        .unwrap_or(finalized),
                    );
                }
                let cond_name = cond.display_name();
                if let Some(prov) = self.lookup_flag_compare_provenance(&cond_name)
                    && let Some(expr) = self.compare_provenance_expr_for_branch(&prov)
                {
                    return Some(self.finalize_condition_expr(expr));
                }
                let expr = self.get_condition_expr(cond);
                Some(self.finalize_condition_expr(expr))
            }
            _ => None,
        }
    }

    fn local_branch_condition_expr(
        &self,
        block: &FunctionSSABlock,
        branch_idx: usize,
        cond: &SSAVar,
        depth: u32,
    ) -> Option<CExpr> {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return None;
        }

        if cond.is_const() {
            return Some(self.const_to_expr(cond));
        }

        let cond_name = cond.display_name();
        for (idx, op) in block.ops[..branch_idx].iter().enumerate().rev() {
            if op.dst() != Some(cond) {
                continue;
            }
            return match op {
                SSAOp::Copy { src, .. }
                | SSAOp::IntZExt { src, .. }
                | SSAOp::IntSExt { src, .. }
                | SSAOp::Subpiece { src, .. } => self.choose_preferred_scalar_predicate_expr(
                    self.local_branch_condition_expr(block, idx, src, depth + 1),
                    self.local_expr_for_var(block, idx, src, depth + 1),
                ),
                SSAOp::BoolNot { src, .. } => self
                    .choose_preferred_scalar_predicate_expr(
                        self.local_branch_condition_expr(block, idx, src, depth + 1),
                        self.local_expr_for_var(block, idx, src, depth + 1),
                    )
                    .map(|expr| CExpr::unary(UnaryOp::Not, expr)),
                SSAOp::IntEqual { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Eq, a, b, depth + 1)
                }
                SSAOp::IntNotEqual { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Ne, a, b, depth + 1)
                }
                SSAOp::IntLess { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Lt, a, b, depth + 1)
                }
                SSAOp::IntSLess { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Lt, a, b, depth + 1)
                }
                SSAOp::IntLessEqual { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Le, a, b, depth + 1)
                }
                SSAOp::IntSLessEqual { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Le, a, b, depth + 1)
                }
                _ => None,
            };
        }

        if let Some(prov) = self.lookup_flag_compare_provenance(&cond_name)
            && let Some(expr) = self.compare_provenance_expr_for_branch(&prov)
        {
            return Some(expr);
        }

        self.predicate_candidate_for_var(cond)
            .or_else(|| Some(CExpr::Var(self.var_name(cond))))
    }

    fn local_compare_expr(
        &self,
        block: &FunctionSSABlock,
        op_idx: usize,
        op: BinaryOp,
        lhs: &SSAVar,
        rhs: &SSAVar,
        depth: u32,
    ) -> Option<CExpr> {
        let compare_width = lhs.size.max(rhs.size);
        let lhs = self.local_compare_operand_expr(block, op_idx, lhs, depth, compare_width)?;
        let rhs = self.local_compare_operand_expr(block, op_idx, rhs, depth, compare_width)?;
        Some(CExpr::binary(op, lhs, rhs))
    }

    fn local_compare_operand_expr(
        &self,
        block: &FunctionSSABlock,
        op_idx: usize,
        var: &SSAVar,
        depth: u32,
        compare_width: u32,
    ) -> Option<CExpr> {
        if var.is_const() {
            return Some(utils::compare_const_to_expr_with_width(var, compare_width));
        }
        self.local_expr_for_var(block, op_idx, var, depth)
    }

    fn local_expr_for_var(
        &self,
        block: &FunctionSSABlock,
        before_idx: usize,
        var: &SSAVar,
        depth: u32,
    ) -> Option<CExpr> {
        if var.is_const() {
            return Some(self.const_to_expr(var));
        }

        let lower_name = var.name.to_ascii_lowercase();
        if self.inputs.arch.is_stack_base_name(&lower_name)
            || self.inputs.arch.is_frame_pointer_name(&lower_name)
        {
            return Some(CExpr::Var(lower_name));
        }

        if let Some(owner) = self.stable_owned_call_result_expr_for_name(&var.display_name(), true)
        {
            return Some(owner);
        }

        if depth > 0
            && self.inputs.arch.is_return_register_name(&lower_name)
            && self.local_return_register_chain_is_call_result(block, before_idx, var, 0)
        {
            if let Some(call_expr) = self
                .lookup_definition(&var.display_name())
                .filter(|expr| matches!(expr, CExpr::Call { .. }))
            {
                return Some(call_expr);
            }
            return Some(CExpr::Var(self.var_name(var)));
        }

        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return Some(CExpr::Var(self.var_name(var)));
        }

        for (idx, op) in block.ops[..before_idx].iter().enumerate().rev() {
            if op.dst() != Some(var) {
                continue;
            }
            return match op {
                SSAOp::Copy { src, .. }
                | SSAOp::IntZExt { src, .. }
                | SSAOp::IntSExt { src, .. }
                | SSAOp::Subpiece { src, .. } => {
                    self.local_expr_for_var(block, idx, src, depth + 1)
                }
                SSAOp::Load { addr, .. } => self.local_load_expr(block, idx, addr, depth + 1),
                SSAOp::IntEqual { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Eq, a, b, depth + 1)
                }
                SSAOp::IntNotEqual { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Ne, a, b, depth + 1)
                }
                SSAOp::IntLess { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Lt, a, b, depth + 1)
                }
                SSAOp::IntSLess { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Lt, a, b, depth + 1)
                }
                SSAOp::IntLessEqual { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Le, a, b, depth + 1)
                }
                SSAOp::IntSLessEqual { a, b, .. } => {
                    self.local_compare_expr(block, idx, BinaryOp::Le, a, b, depth + 1)
                }
                SSAOp::IntAdd { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::Add, a, b, depth + 1)
                }
                SSAOp::IntSub { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::Sub, a, b, depth + 1)
                }
                SSAOp::IntMult { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::Mul, a, b, depth + 1)
                }
                SSAOp::IntDiv { a, b, .. } | SSAOp::IntSDiv { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::Div, a, b, depth + 1)
                }
                SSAOp::IntRem { a, b, .. } | SSAOp::IntSRem { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::Mod, a, b, depth + 1)
                }
                SSAOp::IntAnd { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::BitAnd, a, b, depth + 1)
                }
                SSAOp::IntOr { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::BitOr, a, b, depth + 1)
                }
                SSAOp::IntXor { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::BitXor, a, b, depth + 1)
                }
                SSAOp::IntLeft { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::Shl, a, b, depth + 1)
                }
                SSAOp::IntRight { a, b, .. } | SSAOp::IntSRight { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::Shr, a, b, depth + 1)
                }
                SSAOp::BoolAnd { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::And, a, b, depth + 1)
                }
                SSAOp::BoolOr { a, b, .. } => {
                    self.local_binary_expr(block, idx, BinaryOp::Or, a, b, depth + 1)
                }
                SSAOp::IntNot { src, .. } => self
                    .local_expr_for_var(block, idx, src, depth + 1)
                    .map(|expr| CExpr::unary(UnaryOp::BitNot, expr)),
                SSAOp::IntNegate { src, .. } => self
                    .local_expr_for_var(block, idx, src, depth + 1)
                    .map(|expr| CExpr::unary(UnaryOp::Neg, expr)),
                SSAOp::BoolNot { src, .. } => self
                    .local_expr_for_var(block, idx, src, depth + 1)
                    .map(|expr| CExpr::unary(UnaryOp::Not, expr)),
                _ => None,
            };
        }

        if let Some(expr) = self.lookup_definition(&var.display_name())
            && matches!(expr, CExpr::Call { .. })
        {
            return Some(expr);
        }

        Some(CExpr::Var(self.var_name(var)))
    }

    fn local_return_register_chain_is_call_result(
        &self,
        block: &FunctionSSABlock,
        before_idx: usize,
        var: &SSAVar,
        depth: u32,
    ) -> bool {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return false;
        }

        let Some((idx, op)) = block.ops[..before_idx]
            .iter()
            .enumerate()
            .rev()
            .find(|(_, op)| op.dst() == Some(var))
        else {
            return false;
        };

        match op {
            SSAOp::CallDefine { .. } => true,
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Subpiece { src, .. } => {
                self.local_return_register_chain_is_call_result(block, idx, src, depth + 1)
            }
            _ => false,
        }
    }

    fn local_binary_expr(
        &self,
        block: &FunctionSSABlock,
        op_idx: usize,
        op: BinaryOp,
        lhs: &SSAVar,
        rhs: &SSAVar,
        depth: u32,
    ) -> Option<CExpr> {
        let compare_width = lhs.size.max(rhs.size);
        let lhs = if lhs.is_const() {
            Some(utils::compare_const_to_expr_with_width(lhs, compare_width))
        } else {
            self.local_expr_for_var(block, op_idx, lhs, depth)
        }?;
        let rhs = if rhs.is_const() {
            Some(utils::compare_const_to_expr_with_width(rhs, compare_width))
        } else {
            self.local_expr_for_var(block, op_idx, rhs, depth)
        }?;
        Some(CExpr::binary(op, lhs, rhs))
    }

    fn normalize_local_branch_expr(&self, expr: CExpr) -> CExpr {
        let normalized = match expr {
            CExpr::Binary {
                op: BinaryOp::Eq,
                left,
                right,
            } => {
                if self.is_zero_expr(right.as_ref())
                    && let Some(inner) = Self::strip_sub_zero_local(left.as_ref())
                {
                    return CExpr::binary(BinaryOp::Eq, inner, CExpr::IntLit(0));
                }
                if self.is_zero_expr(right.as_ref())
                    && let Some(inner) = Self::strip_test_self_local(left.as_ref())
                {
                    return CExpr::binary(BinaryOp::Eq, inner, CExpr::IntLit(0));
                }
                CExpr::Binary {
                    op: BinaryOp::Eq,
                    left,
                    right,
                }
            }
            CExpr::Binary {
                op: BinaryOp::Ne,
                left,
                right,
            } => {
                if self.is_zero_expr(right.as_ref())
                    && let Some(inner) = Self::strip_sub_zero_local(left.as_ref())
                {
                    return CExpr::binary(BinaryOp::Ne, inner, CExpr::IntLit(0));
                }
                if self.is_zero_expr(right.as_ref())
                    && let Some(inner) = Self::strip_test_self_local(left.as_ref())
                {
                    return CExpr::binary(BinaryOp::Ne, inner, CExpr::IntLit(0));
                }
                CExpr::Binary {
                    op: BinaryOp::Ne,
                    left,
                    right,
                }
            }
            other => other,
        };

        if self.is_predicate_like_expr(&normalized) {
            let simplified = self.simplify_condition_expr(normalized);
            let rewritten = self.rewrite_call_result_predicate_owners(simplified, 0);
            self.simplify_condition_expr(rewritten)
        } else {
            normalized
        }
    }

    fn is_degenerate_constant_condition(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::IntLit(_) | CExpr::UIntLit(_) => true,
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                self.is_degenerate_constant_condition(inner)
            }
            CExpr::Unary {
                op: UnaryOp::Not,
                operand,
            } => self.is_degenerate_constant_condition(operand),
            CExpr::Binary {
                op:
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge,
                left,
                right,
            } => self.is_literal_expr(left) && self.is_literal_expr(right),
            _ => false,
        }
    }

    fn strip_sub_zero_local(expr: &CExpr) -> Option<CExpr> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } if matches!(right.as_ref(), CExpr::IntLit(0) | CExpr::UIntLit(0)) => {
                Some(left.as_ref().clone())
            }
            CExpr::Paren(inner) => Self::strip_sub_zero_local(inner),
            CExpr::Cast { expr: inner, .. } => Self::strip_sub_zero_local(inner),
            _ => None,
        }
    }

    fn strip_test_self_local(expr: &CExpr) -> Option<CExpr> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::BitAnd,
                left,
                right,
            } if left == right => Some(left.as_ref().clone()),
            CExpr::Paren(inner) => Self::strip_test_self_local(inner),
            CExpr::Cast { expr: inner, .. } => Self::strip_test_self_local(inner),
            _ => None,
        }
    }

    fn local_load_expr(
        &self,
        block: &FunctionSSABlock,
        op_idx: usize,
        addr: &SSAVar,
        depth: u32,
    ) -> Option<CExpr> {
        let slot = self.stack_slot_provenance_for_var(addr);
        for (store_idx, op) in block.ops[..op_idx].iter().enumerate().rev() {
            if let SSAOp::Store {
                addr: store_addr,
                val,
                ..
            } = op
                && self.local_addrs_match(block, store_idx, store_addr, op_idx, addr, depth + 1)
            {
                let stored = self.local_expr_for_var(block, store_idx, val, depth + 1);
                if slot.is_some_and(|slot| slot.is_scalar_predicate_carrier()) {
                    if let Some(stored) = stored {
                        return Some(stored);
                    }
                    let alias = self
                        .local_expr_for_var(block, op_idx, addr, depth + 1)
                        .and_then(|addr_expr| {
                            self.simplify_stack_access(&addr_expr)
                                .filter(|name| {
                                    !super::op_lower::is_generic_stack_placeholder_alias(name)
                                })
                                .map(CExpr::Var)
                        });
                    if alias.is_some() {
                        return alias;
                    }
                    continue;
                }
                if let Some(stored) = stored {
                    return Some(stored);
                }
                continue;
            }
        }

        let addr_expr = self.local_expr_for_var(block, op_idx, addr, depth + 1)?;
        if let Some(alias) = self.simplify_stack_access(&addr_expr)
            && !super::op_lower::is_generic_stack_placeholder_alias(&alias)
        {
            return Some(CExpr::Var(alias));
        }

        if slot.is_some_and(|slot| slot.is_scalar_predicate_carrier()) {
            return None;
        }

        Some(CExpr::deref(addr_expr))
    }

    fn local_addrs_match(
        &self,
        block: &FunctionSSABlock,
        left_idx: usize,
        left: &SSAVar,
        right_idx: usize,
        right: &SSAVar,
        depth: u32,
    ) -> bool {
        if left == right {
            return true;
        }

        if self
            .extract_stack_offset_from_var(left)
            .zip(self.extract_stack_offset_from_var(right))
            .map(|(lhs, rhs)| lhs == rhs)
            .unwrap_or(false)
        {
            return true;
        }

        self.local_expr_for_var(block, left_idx, left, depth + 1)
            .zip(self.local_expr_for_var(block, right_idx, right, depth + 1))
            .map(|(lhs, rhs)| {
                lhs == rhs
                    || self
                        .simplify_stack_access(&lhs)
                        .zip(self.simplify_stack_access(&rhs))
                        .map(|(lhs_alias, rhs_alias)| lhs_alias == rhs_alias)
                        .unwrap_or(false)
            })
            .unwrap_or(false)
    }

    /// Get the expression for a condition variable, always inlining its definition.
    /// Unlike get_expr(), this bypasses the should_inline() check because we always
    /// want to see the actual condition expression, not a temp variable name.
    pub(super) fn get_condition_expr(&self, var: &SSAVar) -> CExpr {
        // Always inline constants
        if var.is_const() {
            return self.const_to_expr(var);
        }

        let expr = self
            .predicate_candidate_for_var(var)
            .unwrap_or_else(|| CExpr::Var(self.var_name(var)));
        let expr = self.rewrite_stack_expr(expr);
        let expr = self.rewrite_condition_stack_aliases(expr);
        let expr = self.simplify_condition_expr(expr);
        let expr = self.rewrite_call_result_predicate_owners(expr, 0);
        self.simplify_condition_expr(expr)
    }

    pub(super) fn rewrite_condition_stack_aliases(&self, expr: CExpr) -> CExpr {
        let mut visited = HashSet::new();
        self.rewrite_condition_stack_aliases_inner(expr, 0, &mut visited)
    }

    pub(super) fn rewrite_condition_stack_aliases_inner(
        &self,
        expr: CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > MAX_COND_STACK_ALIAS_DEPTH {
            return expr;
        }

        match expr {
            CExpr::Var(name) => self.rewrite_condition_stack_var(name, depth, visited),
            other => other.map_children(&mut |child| {
                self.rewrite_condition_stack_aliases_inner(child, depth + 1, visited)
            }),
        }
    }

    pub(super) fn rewrite_condition_stack_var(
        &self,
        name: String,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > MAX_COND_STACK_ALIAS_DEPTH {
            return CExpr::Var(name);
        }

        if self
            .stack_vars_map()
            .values()
            .any(|candidate| candidate.eq_ignore_ascii_case(&name))
        {
            return CExpr::Var(name);
        }

        if let Some(alias) = self
            .stack_slot_provenance_for_name(&name)
            .map(|slot| slot.offset)
            .and_then(|offset| self.resolve_stack_var(offset))
            .filter(|alias| !alias.eq_ignore_ascii_case(&name))
        {
            return CExpr::Var(alias);
        }

        if let Some(alias) = self.resolve_stack_alias_from_addr_expr(&CExpr::Var(name.clone()), 0)
            && !alias.eq_ignore_ascii_case(&name)
        {
            return CExpr::Var(alias);
        }

        if !visited.insert(name.clone()) {
            return CExpr::Var(name);
        }

        let resolved = self
            .lookup_definition_raw(&name)
            .or_else(|| self.formatted_defs_map().get(&name).cloned())
            .or_else(|| self.lookup_definition(&name));

        let rewritten = if let Some(expr) = resolved {
            let expr = self.rewrite_condition_stack_aliases_inner(expr, depth + 1, visited);
            if let Some(alias) = self.resolve_stack_alias_from_addr_expr(&expr, 0) {
                CExpr::Var(alias)
            } else {
                CExpr::Var(name.clone())
            }
        } else {
            CExpr::Var(name.clone())
        };

        visited.remove(&name);
        rewritten
    }

    pub(super) fn simplify_condition_expr(&self, expr: CExpr) -> CExpr {
        analysis::PredicateSimplifier::new(self).simplify_condition_expr(expr)
    }

    pub(crate) fn simplify_predicate_expr(&self, expr: CExpr) -> CExpr {
        self.simplify_predicate_expr_inner(expr, 0)
    }

    pub(super) fn simplify_predicate_expr_inner(&self, expr: CExpr, depth: u32) -> CExpr {
        if depth > MAX_PREDICATE_SIMPLIFY_DEPTH {
            return expr;
        }

        let normalized = match expr {
            CExpr::Unary { op, operand } => CExpr::Unary {
                op,
                operand: Box::new(self.simplify_predicate_expr_inner(*operand, depth + 1)),
            },
            CExpr::Binary { op, left, right } => CExpr::Binary {
                op,
                left: Box::new(self.simplify_predicate_expr_inner(*left, depth + 1)),
                right: Box::new(self.simplify_predicate_expr_inner(*right, depth + 1)),
            },
            CExpr::Paren(inner) => CExpr::Paren(Box::new(
                self.simplify_predicate_expr_inner(*inner, depth + 1),
            )),
            CExpr::Cast { ty, expr } => CExpr::Cast {
                ty,
                expr: Box::new(self.simplify_predicate_expr_inner(*expr, depth + 1)),
            },
            other => other,
        };

        let rewritten = self.rewrite_predicate_once(normalized.clone());
        if rewritten != normalized {
            return self.simplify_predicate_expr_inner(rewritten, depth + 1);
        }
        rewritten
    }

    pub(super) fn rewrite_predicate_once(&self, expr: CExpr) -> CExpr {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Le,
                left,
                right,
            } => {
                if let Some(rewritten) =
                    self.rewrite_unsigned_nonzero_test(left.as_ref(), right.as_ref())
                {
                    rewritten
                } else {
                    CExpr::binary(BinaryOp::Le, *left, *right)
                }
            }
            CExpr::Binary {
                op: BinaryOp::Ge,
                left,
                right,
            } => {
                if let Some(rewritten) =
                    self.rewrite_unsigned_nonzero_test(right.as_ref(), left.as_ref())
                {
                    rewritten
                } else {
                    CExpr::binary(BinaryOp::Ge, *left, *right)
                }
            }
            CExpr::Binary { op, left, right } if matches!(op, BinaryOp::And | BinaryOp::BitAnd) => {
                if let Some(masked_bool) =
                    self.rewrite_boolean_mask_and(left.as_ref(), right.as_ref())
                {
                    masked_bool
                } else if let Some(gt) =
                    self.rewrite_signed_positive_and(left.as_ref(), right.as_ref())
                {
                    gt
                } else {
                    CExpr::binary(op, *left, *right)
                }
            }
            CExpr::Binary {
                op: BinaryOp::Or,
                left,
                right,
            } => {
                if let Some(le) = self.rewrite_le_from_lt_or_eq(left.as_ref(), right.as_ref()) {
                    le
                } else {
                    CExpr::binary(BinaryOp::Or, *left, *right)
                }
            }
            CExpr::Unary {
                op: UnaryOp::Not,
                operand,
            } => {
                if let Some(rewritten) = self.rewrite_not_unsigned_nonzero_test(operand.as_ref()) {
                    rewritten
                } else {
                    self.negate_condition_expr(*operand)
                }
            }
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } if self.is_zero_expr(right.as_ref()) => *left,
            CExpr::Binary {
                op: BinaryOp::Eq,
                left,
                right,
            } => self.rewrite_zero_comparison(BinaryOp::Eq, *left, *right),
            CExpr::Binary {
                op: BinaryOp::Ne,
                left,
                right,
            } => self.rewrite_zero_comparison(BinaryOp::Ne, *left, *right),
            CExpr::Binary {
                op: BinaryOp::Lt,
                left,
                right,
            } => {
                if self.is_zero_expr(right.as_ref())
                    && let Some(base) = self.strip_sub_zero(left.as_ref())
                {
                    return CExpr::binary(BinaryOp::Lt, base, CExpr::IntLit(0));
                }
                CExpr::binary(BinaryOp::Lt, *left, *right)
            }
            CExpr::Var(name) => {
                if let Some(val) = parse_const_value(&name) {
                    if val > 0x7fffffff {
                        CExpr::UIntLit(val)
                    } else {
                        CExpr::IntLit(val as i64)
                    }
                } else {
                    CExpr::Var(name)
                }
            }
            other => other,
        }
    }

    pub(super) fn rewrite_signed_positive_and(&self, left: &CExpr, right: &CExpr) -> Option<CExpr> {
        let left_ne = self.extract_cmp_zero_operand(left, BinaryOp::Ne);
        let right_ge = self.extract_cmp_zero_operand(right, BinaryOp::Ge);
        if let (Some(a), Some(b)) = (left_ne.clone(), right_ge.clone())
            && a == b
        {
            return Some(CExpr::binary(BinaryOp::Gt, a, CExpr::IntLit(0)));
        }

        let left_ge = self.extract_cmp_zero_operand(left, BinaryOp::Ge);
        let right_ne = self.extract_cmp_zero_operand(right, BinaryOp::Ne);
        if let (Some(a), Some(b)) = (left_ge, right_ne)
            && a == b
        {
            return Some(CExpr::binary(BinaryOp::Gt, a, CExpr::IntLit(0)));
        }

        if let (Some((ne_lhs, ne_rhs)), Some((ge_lhs, ge_rhs))) = (
            self.extract_cmp_operands(left, BinaryOp::Ne),
            self.extract_cmp_operands(right, BinaryOp::Ge),
        ) && ((ne_lhs == ge_lhs && ne_rhs == ge_rhs) || (ne_lhs == ge_rhs && ne_rhs == ge_lhs))
        {
            return Some(CExpr::binary(BinaryOp::Gt, ge_lhs, ge_rhs));
        }

        if let (Some((ge_lhs, ge_rhs)), Some((ne_lhs, ne_rhs))) = (
            self.extract_cmp_operands(left, BinaryOp::Ge),
            self.extract_cmp_operands(right, BinaryOp::Ne),
        ) && ((ne_lhs == ge_lhs && ne_rhs == ge_rhs) || (ne_lhs == ge_rhs && ne_rhs == ge_lhs))
        {
            return Some(CExpr::binary(BinaryOp::Gt, ge_lhs, ge_rhs));
        }

        None
    }

    pub(super) fn rewrite_boolean_mask_and(&self, left: &CExpr, right: &CExpr) -> Option<CExpr> {
        if self.is_predicate_one_expr(left) && self.is_boolean_value_expr(right) {
            return Some(right.clone());
        }
        if self.is_predicate_one_expr(right) && self.is_boolean_value_expr(left) {
            return Some(left.clone());
        }
        None
    }

    pub(super) fn rewrite_le_from_lt_or_eq(&self, left: &CExpr, right: &CExpr) -> Option<CExpr> {
        let (lt_lhs, lt_rhs) = self.extract_cmp_operands(left, BinaryOp::Lt)?;
        let (eq_lhs, eq_rhs) = self.extract_cmp_operands(right, BinaryOp::Eq)?;
        let lt_lhs = self.normalize_predicate_match_operand(&lt_lhs);
        let lt_rhs = self.normalize_predicate_match_operand(&lt_rhs);
        let eq_lhs = self.normalize_predicate_match_operand(&eq_lhs);
        let eq_rhs = self.normalize_predicate_match_operand(&eq_rhs);

        if (lt_lhs == eq_lhs && lt_rhs == eq_rhs) || (lt_lhs == eq_rhs && lt_rhs == eq_lhs) {
            return Some(CExpr::binary(BinaryOp::Le, lt_lhs, lt_rhs));
        }

        None
    }

    pub(super) fn extract_cmp_operands(
        &self,
        expr: &CExpr,
        op: BinaryOp,
    ) -> Option<(CExpr, CExpr)> {
        match expr {
            CExpr::Binary {
                op: expr_op,
                left,
                right,
            } if *expr_op == op => Some((left.as_ref().clone(), right.as_ref().clone())),
            CExpr::Paren(inner) => self.extract_cmp_operands(inner, op),
            CExpr::Cast { expr: inner, .. } => self.extract_cmp_operands(inner, op),
            _ => None,
        }
    }

    fn normalize_predicate_match_operand(&self, expr: &CExpr) -> CExpr {
        match expr {
            CExpr::Paren(inner) => self.normalize_predicate_match_operand(inner),
            CExpr::Cast {
                ty: CType::Bool | CType::Int(_) | CType::UInt(_),
                expr: inner,
            } => {
                let normalized = self.normalize_predicate_match_operand(inner);
                if matches!(
                    normalized,
                    CExpr::Var(_) | CExpr::IntLit(_) | CExpr::UIntLit(_)
                ) {
                    normalized
                } else {
                    CExpr::Cast {
                        ty: match expr {
                            CExpr::Cast { ty, .. } => ty.clone(),
                            _ => unreachable!(),
                        },
                        expr: Box::new(normalized),
                    }
                }
            }
            CExpr::Cast { ty, expr: inner } => CExpr::Cast {
                ty: ty.clone(),
                expr: Box::new(self.normalize_predicate_match_operand(inner)),
            },
            CExpr::Var(name) => self
                .normalize_compare_style_const_name(name)
                .unwrap_or_else(|| CExpr::Var(name.clone())),
            other => other.clone(),
        }
    }

    fn normalize_compare_style_const_name(&self, name: &str) -> Option<CExpr> {
        if let Some(expr) = self.compare_const_expr_from_name(name) {
            return Some(expr);
        }

        fn lit_for_u64(value: u64) -> CExpr {
            if value > 0x7fff_ffff {
                CExpr::UIntLit(value)
            } else {
                CExpr::IntLit(value as i64)
            }
        }

        if let Some(value) = parse_const_value(name) {
            return Some(lit_for_u64(value));
        }

        if let Some(dec) = name.strip_prefix("0d").or_else(|| name.strip_prefix("0D")) {
            return dec.parse::<u64>().ok().map(lit_for_u64);
        }

        if let Some(hex) = name.strip_prefix("0x").or_else(|| name.strip_prefix("0X")) {
            return u64::from_str_radix(hex, 16).ok().map(lit_for_u64);
        }

        if name.len() > 1 && name.chars().all(|c| c.is_ascii_hexdigit()) {
            return u64::from_str_radix(name, 16).ok().map(lit_for_u64);
        }

        name.parse::<i64>().ok().map(CExpr::IntLit)
    }

    fn compare_const_expr_from_name(&self, name: &str) -> Option<CExpr> {
        let raw = name.strip_prefix("const:")?;
        let raw = raw.split('_').next().unwrap_or(raw);

        let value = if let Some(dec) = raw.strip_prefix("0d").or_else(|| raw.strip_prefix("0D")) {
            dec.parse::<u64>().ok()?
        } else if let Some(hex) = raw.strip_prefix("0x").or_else(|| raw.strip_prefix("0X")) {
            u64::from_str_radix(hex, 16).ok()?
        } else if raw.len() > 1 && raw.chars().all(|c| c.is_ascii_hexdigit()) {
            u64::from_str_radix(raw, 16).ok()?
        } else {
            raw.parse::<u64>().ok()?
        };

        Some(if value > 0x7fff_ffff {
            CExpr::UIntLit(value)
        } else {
            CExpr::IntLit(value as i64)
        })
    }

    pub(super) fn extract_cmp_zero_operand(&self, expr: &CExpr, op: BinaryOp) -> Option<CExpr> {
        match expr {
            CExpr::Binary {
                op: expr_op,
                left,
                right,
            } if *expr_op == op => {
                if self.is_zero_expr(right.as_ref()) {
                    return Some(left.as_ref().clone());
                }
                if self.is_zero_expr(left.as_ref()) {
                    return Some(right.as_ref().clone());
                }
                None
            }
            CExpr::Paren(inner) => self.extract_cmp_zero_operand(inner, op),
            CExpr::Cast { expr: inner, .. } => self.extract_cmp_zero_operand(inner, op),
            _ => None,
        }
    }

    pub(super) fn rewrite_zero_comparison(
        &self,
        cmp_op: BinaryOp,
        left: CExpr,
        right: CExpr,
    ) -> CExpr {
        if self.is_zero_expr(&right) {
            if self.is_boolean_value_expr(&left) {
                return match cmp_op {
                    BinaryOp::Eq => self.negate_condition_expr(left),
                    BinaryOp::Ne => left,
                    _ => CExpr::binary(cmp_op, left, right),
                };
            }
            if let Some((sub_lhs, sub_rhs)) = self.extract_sub_operands(&left) {
                let rhs = self.resolve_predicate_operand(&sub_rhs, 0, &mut HashSet::new());
                return CExpr::binary(
                    cmp_op,
                    self.resolve_predicate_operand(&sub_lhs, 0, &mut HashSet::new()),
                    self.normalize_sub_cmp_constant(rhs),
                );
            }
            if let Some(base) = self.strip_test_self(&left) {
                return CExpr::binary(cmp_op, base, CExpr::IntLit(0));
            }
            if let Some((base, value)) = self.strip_sub_const(&left) {
                return CExpr::binary(cmp_op, base, self.normalize_sub_cmp_constant(value));
            }
            if let Some(base) = self.strip_sub_zero(&left) {
                return CExpr::binary(cmp_op, base, CExpr::IntLit(0));
            }
        }

        if self.is_zero_expr(&left) {
            if self.is_boolean_value_expr(&right) {
                return match cmp_op {
                    BinaryOp::Eq => self.negate_condition_expr(right),
                    BinaryOp::Ne => right,
                    _ => CExpr::binary(cmp_op, left, right),
                };
            }
            if let Some((sub_lhs, sub_rhs)) = self.extract_sub_operands(&right) {
                let rhs = self.resolve_predicate_operand(&sub_rhs, 0, &mut HashSet::new());
                return CExpr::binary(
                    cmp_op,
                    self.resolve_predicate_operand(&sub_lhs, 0, &mut HashSet::new()),
                    self.normalize_sub_cmp_constant(rhs),
                );
            }
            if let Some(base) = self.strip_test_self(&right) {
                return CExpr::binary(cmp_op, base, CExpr::IntLit(0));
            }
            if let Some((base, value)) = self.strip_sub_const(&right) {
                return CExpr::binary(cmp_op, base, self.normalize_sub_cmp_constant(value));
            }
            if let Some(base) = self.strip_sub_zero(&right) {
                return CExpr::binary(cmp_op, base, CExpr::IntLit(0));
            }
        }

        CExpr::binary(cmp_op, left, right)
    }

    pub(super) fn rewrite_unsigned_nonzero_test(
        &self,
        left: &CExpr,
        right: &CExpr,
    ) -> Option<CExpr> {
        if !self.is_predicate_one_expr(left) {
            return None;
        }

        let candidate = self.extract_unsigned_truthy_candidate(right)?;
        Some(if self.is_boolean_value_expr(&candidate) {
            candidate
        } else {
            CExpr::binary(BinaryOp::Ne, candidate, CExpr::IntLit(0))
        })
    }

    pub(super) fn rewrite_not_unsigned_nonzero_test(&self, expr: &CExpr) -> Option<CExpr> {
        let CExpr::Binary {
            op: BinaryOp::Le,
            left,
            right,
        } = expr
        else {
            return None;
        };

        if !self.is_predicate_one_expr(left) {
            return None;
        }

        let candidate = self.extract_unsigned_truthy_candidate(right)?;
        Some(if self.is_boolean_value_expr(&candidate) {
            self.negate_condition_expr(candidate)
        } else {
            CExpr::binary(BinaryOp::Eq, candidate, CExpr::IntLit(0))
        })
    }

    pub(super) fn extract_unsigned_truthy_candidate(&self, expr: &CExpr) -> Option<CExpr> {
        match expr {
            CExpr::Paren(inner) => self.extract_unsigned_truthy_candidate(inner),
            CExpr::Cast {
                ty: CType::UInt(_) | CType::Bool,
                expr: inner,
            } => Some(inner.as_ref().clone()),
            _ => None,
        }
    }

    pub(super) fn negate_condition_expr(&self, expr: CExpr) -> CExpr {
        match expr {
            CExpr::Unary {
                op: UnaryOp::Not,
                operand,
            } => *operand,
            CExpr::Binary { op, left, right } => {
                let negated = match op {
                    BinaryOp::Eq => Some(BinaryOp::Ne),
                    BinaryOp::Ne => Some(BinaryOp::Eq),
                    BinaryOp::Lt => Some(BinaryOp::Ge),
                    BinaryOp::Le => Some(BinaryOp::Gt),
                    BinaryOp::Gt => Some(BinaryOp::Le),
                    BinaryOp::Ge => Some(BinaryOp::Lt),
                    _ => None,
                };

                if let Some(op) = negated {
                    CExpr::Binary { op, left, right }
                } else {
                    CExpr::unary(UnaryOp::Not, CExpr::Binary { op, left, right })
                }
            }
            other => CExpr::unary(UnaryOp::Not, other),
        }
    }

    pub(super) fn is_boolean_value_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                is_cpu_flag(&name.to_lowercase())
                    || self.flag_only_values_set().contains(name)
                    || self.condition_vars_set().contains(name)
                    || self.lookup_predicate_expr(name).is_some()
            }
            CExpr::Unary {
                op: UnaryOp::Not, ..
            } => true,
            CExpr::Binary { op, .. } => matches!(
                op,
                BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
                    | BinaryOp::And
                    | BinaryOp::Or
            ),
            CExpr::Paren(inner) => self.is_boolean_value_expr(inner),
            CExpr::Cast {
                ty: CType::Bool,
                expr: _,
            } => true,
            CExpr::Cast { expr: inner, .. } => self.is_boolean_value_expr(inner),
            _ => false,
        }
    }

    pub(super) fn is_predicate_one_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Paren(inner) => self.is_predicate_one_expr(inner),
            CExpr::Cast { expr: inner, .. } => self.is_predicate_one_expr(inner),
            CExpr::IntLit(1) | CExpr::UIntLit(1) => true,
            CExpr::Var(name) => name == "1",
            _ => false,
        }
    }

    pub(super) fn normalize_sub_cmp_constant(&self, value: CExpr) -> CExpr {
        match value {
            CExpr::IntLit(v) if v >= 0x100 => CExpr::Var(format!("0x{:x}", v as u64)),
            CExpr::UIntLit(v) if v >= 0x100 => CExpr::Var(format!("0x{:x}", v)),
            other => other,
        }
    }

    pub(super) fn const_expr_for_comparison(&self, expr: &CExpr) -> Option<CExpr> {
        match expr {
            CExpr::IntLit(_) | CExpr::UIntLit(_) => Some(expr.clone()),
            CExpr::Paren(inner) => self.const_expr_for_comparison(inner),
            CExpr::Cast { expr: inner, .. } => self.const_expr_for_comparison(inner),
            CExpr::Var(name) => self.compare_const_expr_from_name(name).or_else(|| {
                if let Some(val) = parse_const_value(name) {
                    Some(if val > 0x7fffffff {
                        CExpr::UIntLit(val)
                    } else {
                        CExpr::IntLit(val as i64)
                    })
                } else if let Some(hex) =
                    name.strip_prefix("0x").or_else(|| name.strip_prefix("0X"))
                {
                    u64::from_str_radix(hex, 16).ok().map(|val| {
                        if val > 0x7fffffff {
                            CExpr::UIntLit(val)
                        } else {
                            CExpr::IntLit(val as i64)
                        }
                    })
                } else {
                    None
                }
            }),
            _ => None,
        }
    }

    pub(super) fn strip_sub_const(&self, expr: &CExpr) -> Option<(CExpr, CExpr)> {
        let mut visited = HashSet::new();
        self.strip_sub_const_inner(expr, &mut visited)
    }

    pub(super) fn strip_sub_zero(&self, expr: &CExpr) -> Option<CExpr> {
        let mut visited = HashSet::new();
        self.strip_sub_zero_inner(expr, &mut visited)
    }

    pub(super) fn strip_test_self(&self, expr: &CExpr) -> Option<CExpr> {
        let mut visited = HashSet::new();
        self.strip_test_self_inner(expr, &mut visited)
    }

    fn strip_sub_const_inner(
        &self,
        expr: &CExpr,
        visited: &mut HashSet<String>,
    ) -> Option<(CExpr, CExpr)> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => self
                .const_expr_for_comparison(right)
                .map(|value| (left.as_ref().clone(), value)),
            CExpr::Paren(inner) => self.strip_sub_const_inner(inner, visited),
            CExpr::Cast { expr: inner, .. } => self.strip_sub_const_inner(inner, visited),
            CExpr::Var(name) => {
                if !visited.insert(name.clone()) {
                    return None;
                }
                let inner = self
                    .lookup_definition(name)
                    .or_else(|| self.formatted_defs_map().get(name).cloned());
                let result = inner.and_then(|inner| self.strip_sub_const_inner(&inner, visited));
                visited.remove(name);
                result
            }
            _ => None,
        }
    }

    fn strip_sub_zero_inner(&self, expr: &CExpr, visited: &mut HashSet<String>) -> Option<CExpr> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } if self.is_zero_expr(right.as_ref()) => Some(left.as_ref().clone()),
            CExpr::Paren(inner) => self.strip_sub_zero_inner(inner, visited),
            CExpr::Cast { expr: inner, .. } => self.strip_sub_zero_inner(inner, visited),
            CExpr::Var(name) => {
                if !visited.insert(name.clone()) {
                    return None;
                }
                let inner = self
                    .lookup_definition(name)
                    .or_else(|| self.formatted_defs_map().get(name).cloned());
                let result = inner.and_then(|inner| self.strip_sub_zero_inner(&inner, visited));
                visited.remove(name);
                result
            }
            _ => None,
        }
    }

    fn strip_test_self_inner(&self, expr: &CExpr, visited: &mut HashSet<String>) -> Option<CExpr> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::BitAnd,
                left,
                right,
            } if left == right => Some(left.as_ref().clone()),
            CExpr::Paren(inner) => self.strip_test_self_inner(inner, visited),
            CExpr::Cast { expr: inner, .. } => self.strip_test_self_inner(inner, visited),
            CExpr::Var(name) => {
                if !visited.insert(name.clone()) {
                    return None;
                }
                let inner = self
                    .lookup_definition(name)
                    .or_else(|| self.formatted_defs_map().get(name).cloned());
                let result = inner.and_then(|inner| self.strip_test_self_inner(&inner, visited));
                visited.remove(name);
                result
            }
            _ => None,
        }
    }

    pub(super) fn is_zero_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Paren(inner) => self.is_zero_expr(inner),
            CExpr::Cast { expr: inner, .. } => self.is_zero_expr(inner),
            CExpr::IntLit(0) | CExpr::UIntLit(0) => true,
            CExpr::Var(name) => name == "0" || name == "elf_header",
            _ => false,
        }
    }

    pub(super) fn is_predicate_like_expr(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::Var(name) => {
                is_cpu_flag(&name.to_lowercase())
                    || self.flag_only_values_set().contains(name)
                    || self.condition_vars_set().contains(name)
                    || self.lookup_predicate_expr(name).is_some()
            }
            CExpr::Unary {
                op: UnaryOp::Not, ..
            } => true,
            CExpr::Binary { op, .. } => matches!(
                op,
                BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
                    | BinaryOp::And
                    | BinaryOp::Or
                    | BinaryOp::BitAnd
                    | BinaryOp::Sub
            ),
            CExpr::Paren(inner) => self.is_predicate_like_expr(inner),
            CExpr::Cast { expr: inner, .. } => self.is_predicate_like_expr(inner),
            CExpr::IntLit(_) | CExpr::UIntLit(_) => true,
            _ => false,
        }
    }

    pub(super) fn should_expand_predicate_var(&self, name: &str) -> bool {
        if is_cpu_flag(&name.to_lowercase())
            || self.condition_vars_set().contains(name)
            || self.flag_only_values_set().contains(name)
            || self.lookup_predicate_expr(name).is_some()
        {
            return true;
        }

        self.lookup_predicate_expr(name)
            .or_else(|| self.lookup_definition(name))
            .or_else(|| self.formatted_defs_map().get(name).cloned())
            .map(|expr| self.is_predicate_like_expr(&expr))
            .unwrap_or(false)
    }

    pub(crate) fn expand_predicate_vars(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return expr.clone();
        }

        match expr {
            CExpr::Var(name) => {
                if let Some(alias) = self.arg_alias_for_rendered_name(name) {
                    return CExpr::Var(alias);
                }
                if let Some(source) = self
                    .call_result_source_for_ssa_name(name)
                    .or_else(|| self.local_post_call_source_for_ssa_name(name))
                {
                    if let Some(inner @ CExpr::Call { .. }) = self
                        .lookup_definition(name)
                        .or_else(|| self.formatted_defs_map().get(name).cloned())
                    {
                        return inner;
                    }
                    if let Some(inner) = self.synthesized_call_expr_for_source_call(source) {
                        return inner;
                    }
                }
                if let Some(inner) = self.lookup_predicate_expr(name)
                    && inner != CExpr::Var(name.clone())
                {
                    if let CExpr::Var(inner_name) = &inner {
                        if inner_name.starts_with("arg") {
                            return CExpr::Var(inner_name.clone());
                        }
                        if let Some(alias) = self.arg_alias_for_rendered_name(inner_name) {
                            return CExpr::Var(alias);
                        }
                    }
                    if !self.should_expand_predicate_var(name) || !visited.insert(name.clone()) {
                        return CExpr::Var(name.clone());
                    }
                    let expanded = self.expand_predicate_vars(&inner, depth + 1, visited);
                    visited.remove(name);
                    return expanded;
                }
                if let Some(inner) = self
                    .lookup_definition(name)
                    .or_else(|| self.formatted_defs_map().get(name).cloned())
                    && let CExpr::Var(inner_name) = inner
                {
                    if inner_name.starts_with("arg") {
                        return CExpr::Var(inner_name);
                    }
                    if let Some(alias) = self.arg_alias_for_rendered_name(&inner_name) {
                        return CExpr::Var(alias);
                    }
                }
                if !self.should_expand_predicate_var(name) || !visited.insert(name.clone()) {
                    return CExpr::Var(name.clone());
                }

                let expanded = self
                    .lookup_predicate_expr(name)
                    .or_else(|| self.lookup_definition(name))
                    .or_else(|| self.formatted_defs_map().get(name).cloned())
                    .filter(|inner| self.is_predicate_like_expr(inner))
                    .map(|inner| self.expand_predicate_vars(&inner, depth + 1, visited))
                    .unwrap_or_else(|| CExpr::Var(name.clone()));

                visited.remove(name);
                expanded
            }
            CExpr::Unary { op, operand } => {
                CExpr::unary(*op, self.expand_predicate_vars(operand, depth + 1, visited))
            }
            CExpr::Binary { op, left, right } => CExpr::binary(
                *op,
                self.expand_predicate_vars(left, depth + 1, visited),
                self.expand_predicate_vars(right, depth + 1, visited),
            ),
            CExpr::Paren(inner) => CExpr::Paren(Box::new(self.expand_predicate_vars(
                inner,
                depth + 1,
                visited,
            ))),
            CExpr::Cast { ty, expr: inner } => CExpr::Cast {
                ty: ty.clone(),
                expr: Box::new(self.expand_predicate_vars(inner, depth + 1, visited)),
            },
            _ => expr.clone(),
        }
    }

    /// Try to reconstruct a high-level comparison from x86 flag patterns.
    /// Handles patterns like:
    /// - BoolNot(ZF) -> a != b
    /// - ZF -> a == b  
    /// - !ZF && (OF == SF) -> a > b (signed, JG)
    /// - OF == SF -> a >= b (signed, JGE)
    /// - OF != SF -> a < b (signed, JL)
    /// - ZF || (OF != SF) -> a <= b (signed, JLE)
    /// - !CF && !ZF -> a > b (unsigned, JA)
    /// - !CF -> a >= b (unsigned, JAE)
    /// - CF -> a < b (unsigned, JB)
    /// - CF || ZF -> a <= b (unsigned, JBE)
    pub(crate) fn try_reconstruct_condition(&self, expr: &CExpr) -> Option<CExpr> {
        match expr {
            // Pattern: Binary AND - check for signed greater than: !ZF && (OF == SF)
            CExpr::Binary {
                op: BinaryOp::And,
                left,
                right,
            } => {
                if let Some(rel) = self.reconstruct_signed_gt_from_and(left, right) {
                    return Some(rel);
                }
                if let Some(rel) = self.reconstruct_signed_gt_from_and(right, left) {
                    return Some(rel);
                }

                // Try !ZF && (OF == SF) -> a > b (signed)
                if let (Some(zf_name), true) = (self.extract_not_zf(left), self.is_of_eq_sf(right))
                    && let Some((a, b)) = self.lookup_flag_origin(&zf_name)
                {
                    return Some(CExpr::binary(BinaryOp::Gt, CExpr::Var(a), CExpr::Var(b)));
                }
                // Try reversed: (OF == SF) && !ZF
                if let (Some(zf_name), true) = (self.extract_not_zf(right), self.is_of_eq_sf(left))
                    && let Some((a, b)) = self.lookup_flag_origin(&zf_name)
                {
                    return Some(CExpr::binary(BinaryOp::Gt, CExpr::Var(a), CExpr::Var(b)));
                }

                // Try !CF && !ZF -> a > b (unsigned, JA)
                if let (Some(cf_name), Some(zf_name)) =
                    (self.extract_not_cf(left), self.extract_not_zf(right))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&cf_name) {
                        return Some(CExpr::binary(BinaryOp::Gt, CExpr::Var(a), CExpr::Var(b)));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&zf_name) {
                        return Some(CExpr::binary(BinaryOp::Gt, CExpr::Var(a), CExpr::Var(b)));
                    }
                }
                // Try reversed
                if let (Some(cf_name), Some(zf_name)) =
                    (self.extract_not_cf(right), self.extract_not_zf(left))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&cf_name) {
                        return Some(CExpr::binary(BinaryOp::Gt, CExpr::Var(a), CExpr::Var(b)));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&zf_name) {
                        return Some(CExpr::binary(BinaryOp::Gt, CExpr::Var(a), CExpr::Var(b)));
                    }
                }

                None
            }

            // Pattern: Binary OR - check for unsigned less-equal: CF || ZF
            CExpr::Binary {
                op: BinaryOp::Or,
                left,
                right,
            } => {
                if let Some(rel) = self.reconstruct_signed_le_from_or(left, right) {
                    return Some(rel);
                }
                if let Some(rel) = self.reconstruct_signed_le_from_or(right, left) {
                    return Some(rel);
                }

                // Try CF || ZF -> a <= b (unsigned, JBE)
                if let (Some(cf_name), Some(zf_name)) =
                    (self.extract_cf(left), self.extract_zf(right))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&cf_name) {
                        return Some(CExpr::binary(BinaryOp::Le, CExpr::Var(a), CExpr::Var(b)));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&zf_name) {
                        return Some(CExpr::binary(BinaryOp::Le, CExpr::Var(a), CExpr::Var(b)));
                    }
                }
                // Try reversed
                if let (Some(cf_name), Some(zf_name)) =
                    (self.extract_cf(right), self.extract_zf(left))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&cf_name) {
                        return Some(CExpr::binary(BinaryOp::Le, CExpr::Var(a), CExpr::Var(b)));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&zf_name) {
                        return Some(CExpr::binary(BinaryOp::Le, CExpr::Var(a), CExpr::Var(b)));
                    }
                }

                // Try ZF || (OF != SF) -> a <= b (signed, JLE)
                if let (Some(zf_name), true) = (self.extract_zf(left), self.is_of_ne_sf(right))
                    && let Some((a, b)) = self.lookup_flag_origin(&zf_name)
                {
                    return Some(CExpr::binary(BinaryOp::Le, CExpr::Var(a), CExpr::Var(b)));
                }
                // Try reversed
                if let (Some(zf_name), true) = (self.extract_zf(right), self.is_of_ne_sf(left))
                    && let Some((a, b)) = self.lookup_flag_origin(&zf_name)
                {
                    return Some(CExpr::binary(BinaryOp::Le, CExpr::Var(a), CExpr::Var(b)));
                }

                None
            }

            // Pattern: Binary Eq - check for OF == SF (signed >=)
            // AND temp == 0 patterns (TEST/CMP reconstruction)
            CExpr::Binary {
                op: BinaryOp::Eq,
                left,
                right,
            } => {
                if let Some(rel) = self.reconstruct_signed_ge_from_eq(expr) {
                    return Some(rel);
                }

                // OF == SF -> a >= b (signed, JGE)
                if let (Some(of_name), Some(sf_name)) =
                    (self.extract_of(left), self.extract_sf(right))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&of_name) {
                        return Some(CExpr::binary(BinaryOp::Ge, CExpr::Var(a), CExpr::Var(b)));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&sf_name) {
                        return Some(CExpr::binary(BinaryOp::Ge, CExpr::Var(a), CExpr::Var(b)));
                    }
                }
                // Try reversed
                if let (Some(of_name), Some(sf_name)) =
                    (self.extract_of(right), self.extract_sf(left))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&of_name) {
                        return Some(CExpr::binary(BinaryOp::Ge, CExpr::Var(a), CExpr::Var(b)));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&sf_name) {
                        return Some(CExpr::binary(BinaryOp::Ge, CExpr::Var(a), CExpr::Var(b)));
                    }
                }
                // Fallback: temp == 0 where temp is from TEST/CMP
                if let Some(result) = self.try_reconstruct_cmp_zero(left, right, BinaryOp::Eq) {
                    return Some(result);
                }
                // Also try reversed (0 == temp)
                if let Some(result) = self.try_reconstruct_cmp_zero(right, left, BinaryOp::Eq) {
                    return Some(result);
                }
                None
            }

            // Pattern: Binary Ne - check for OF != SF (signed <)
            // AND temp != 0 patterns (TEST/CMP reconstruction)
            CExpr::Binary {
                op: BinaryOp::Ne,
                left,
                right,
            } => {
                if let Some(rel) = self.reconstruct_signed_lt_from_ne(expr) {
                    return Some(rel);
                }

                // OF != SF -> a < b (signed, JL)
                if let (Some(of_name), Some(sf_name)) =
                    (self.extract_of(left), self.extract_sf(right))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&of_name) {
                        return Some(CExpr::binary(BinaryOp::Lt, CExpr::Var(a), CExpr::Var(b)));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&sf_name) {
                        return Some(CExpr::binary(BinaryOp::Lt, CExpr::Var(a), CExpr::Var(b)));
                    }
                }
                // Try reversed
                if let (Some(of_name), Some(sf_name)) =
                    (self.extract_of(right), self.extract_sf(left))
                {
                    if let Some((a, b)) = self.lookup_flag_origin(&of_name) {
                        return Some(CExpr::binary(BinaryOp::Lt, CExpr::Var(a), CExpr::Var(b)));
                    }
                    if let Some((a, b)) = self.lookup_flag_origin(&sf_name) {
                        return Some(CExpr::binary(BinaryOp::Lt, CExpr::Var(a), CExpr::Var(b)));
                    }
                }
                // Fallback: temp != 0 where temp is from TEST/CMP
                if let Some(result) = self.try_reconstruct_cmp_zero(left, right, BinaryOp::Ne) {
                    return Some(result);
                }
                if let Some(result) = self.try_reconstruct_cmp_zero(right, left, BinaryOp::Ne) {
                    return Some(result);
                }
                None
            }

            CExpr::Paren(inner) => self.try_reconstruct_condition(inner),

            CExpr::Cast { ty, expr: inner } => {
                self.try_reconstruct_condition(inner)
                    .map(|reconstructed| CExpr::Cast {
                        ty: ty.clone(),
                        expr: Box::new(reconstructed),
                    })
            }

            // Pattern: !ZF (BoolNot of ZF) means "not equal"
            CExpr::Unary {
                op: UnaryOp::Not,
                operand,
            } => {
                if let CExpr::Var(flag_name) = operand.as_ref() {
                    if let Some(prov) = self.lookup_flag_compare_provenance(flag_name)
                        && let Some(expr) = self.compare_provenance_expr(&prov)
                    {
                        return Some(self.negate_condition_expr(expr));
                    }

                    let flag_lower = flag_name.to_lowercase();
                    if flag_lower.contains("zf") {
                        // !ZF means a != b
                        if let Some((left, right)) = self.lookup_flag_origin(flag_name) {
                            return Some(CExpr::binary(
                                BinaryOp::Ne,
                                CExpr::Var(left),
                                CExpr::Var(right),
                            ));
                        }
                    }
                    // !CF means a >= b (unsigned, JAE)
                    if flag_lower.contains("cf")
                        && let Some((left, right)) = self.lookup_flag_origin(flag_name)
                    {
                        return Some(CExpr::binary(
                            BinaryOp::Ge,
                            CExpr::Var(left),
                            CExpr::Var(right),
                        ));
                    }
                }

                // Try !(CF || ZF) -> a > b (unsigned, JA) - negation of JBE
                if let CExpr::Binary {
                    op: BinaryOp::Or,
                    left: or_left,
                    right: or_right,
                } = operand.as_ref()
                {
                    if let (Some(cf_name), Some(_zf_name)) =
                        (self.extract_cf(or_left), self.extract_zf(or_right))
                        && let Some((a, b)) = self.lookup_flag_origin(&cf_name)
                    {
                        return Some(CExpr::binary(BinaryOp::Gt, CExpr::Var(a), CExpr::Var(b)));
                    }
                    // Try reversed
                    if let (Some(cf_name), Some(_zf_name)) =
                        (self.extract_cf(or_right), self.extract_zf(or_left))
                        && let Some((a, b)) = self.lookup_flag_origin(&cf_name)
                    {
                        return Some(CExpr::binary(BinaryOp::Gt, CExpr::Var(a), CExpr::Var(b)));
                    }
                }

                // Try to recurse into the operand and negate the result
                if let Some(inner) = self.try_reconstruct_condition(operand) {
                    // Negate comparison operators directly instead of wrapping in !()
                    return Some(match inner {
                        CExpr::Binary {
                            op: BinaryOp::Eq,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Ne,
                            left,
                            right,
                        },
                        CExpr::Binary {
                            op: BinaryOp::Ne,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Eq,
                            left,
                            right,
                        },
                        CExpr::Binary {
                            op: BinaryOp::Lt,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Ge,
                            left,
                            right,
                        },
                        CExpr::Binary {
                            op: BinaryOp::Ge,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Lt,
                            left,
                            right,
                        },
                        CExpr::Binary {
                            op: BinaryOp::Gt,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Le,
                            left,
                            right,
                        },
                        CExpr::Binary {
                            op: BinaryOp::Le,
                            left,
                            right,
                        } => CExpr::Binary {
                            op: BinaryOp::Gt,
                            left,
                            right,
                        },
                        other => CExpr::unary(UnaryOp::Not, other),
                    });
                }
                None
            }

            // Pattern: ZF directly means "equal"
            CExpr::Var(flag_name) => {
                if let Some(prov) = self.lookup_flag_compare_provenance(flag_name)
                    && let Some(expr) = self.compare_provenance_expr(&prov)
                {
                    return Some(expr);
                }

                let flag_lower = flag_name.to_lowercase();
                if flag_lower.contains("zf")
                    && let Some((left, right)) = self.lookup_flag_origin(flag_name)
                {
                    return Some(CExpr::binary(
                        BinaryOp::Eq,
                        CExpr::Var(left),
                        CExpr::Var(right),
                    ));
                }
                // CF directly means a < b (unsigned, JB)
                if flag_lower.contains("cf")
                    && let Some((left, right)) = self.lookup_flag_origin(flag_name)
                {
                    return Some(CExpr::binary(
                        BinaryOp::Lt,
                        CExpr::Var(left),
                        CExpr::Var(right),
                    ));
                }
                None
            }

            _ => None,
        }
    }

    /// Try to reconstruct a comparison from `temp == 0` or `temp != 0` patterns.
    ///
    /// For `TEST reg, reg; JZ/JNZ`:
    ///   - `t1 = IntAnd(RBX, RBX)` -> `ZF = (t1 == 0)` -> CBranch(ZF)
    ///   - When we see `Var(t1) == IntLit(0)`, trace t1's definition:
    ///     - If `BitAnd(a, b)` where a == b (TEST): produce `a == 0` / `a != 0`
    ///     - If `Sub(a, b)` (CMP): produce `a == b` / `a != b`
    pub(super) fn try_reconstruct_cmp_zero(
        &self,
        var_side: &CExpr,
        zero_side: &CExpr,
        cmp_op: BinaryOp,
    ) -> Option<CExpr> {
        // zero_side must be 0
        let is_zero = match zero_side {
            CExpr::IntLit(0) => true,
            CExpr::Var(name) if name == "elf_header" || name == "0" => true,
            _ => false,
        };
        if !is_zero {
            return None;
        }

        // var_side must be a variable reference
        let var_name = match var_side {
            CExpr::Var(name) => name,
            _ => return None,
        };

        // Look up the definition of this variable (try SSA key first, then formatted name)
        let def = self
            .definition_for_name(var_name)
            .or_else(|| self.formatted_defs_map().get(var_name))?;

        match def {
            // TEST reg, reg pattern: IntAnd(a, b) where a == b
            CExpr::Binary {
                op: BinaryOp::BitAnd,
                left,
                right,
            } => {
                if left == right {
                    // TEST reg, reg -> reg == 0 / reg != 0
                    return Some(CExpr::binary(cmp_op, *left.clone(), CExpr::IntLit(0)));
                }
                // TEST a, b (different operands) -> (a & b) == 0 / != 0
                Some(CExpr::binary(
                    cmp_op,
                    CExpr::binary(BinaryOp::BitAnd, *left.clone(), *right.clone()),
                    CExpr::IntLit(0),
                ))
            }
            // CMP a, b pattern: Sub(a, b) where the sub is a CMP (result only used for flags)
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => {
                // CMP a, b; JE/JNE -> a == b / a != b
                Some(CExpr::binary(cmp_op, *left.clone(), *right.clone()))
            }
            _ => None,
        }
    }

    // ========== Helper functions for flag pattern detection ==========

    pub(super) fn extract_flag_name(&self, expr: &CExpr, flag: &str) -> Option<String> {
        if let CExpr::Var(name) = expr {
            if is_specific_flag_name(name, flag) {
                return Some(name.clone());
            }

            if let Some(CExpr::Var(inner)) = self
                .lookup_definition(name)
                .or_else(|| self.formatted_defs_map().get(name).cloned())
                && is_specific_flag_name(&inner, flag)
            {
                return Some(inner);
            }
        }
        None
    }

    /// Extract ZF variable name from an expression (if it's a ZF flag reference).
    pub(super) fn extract_zf(&self, expr: &CExpr) -> Option<String> {
        self.extract_flag_name(expr, "zf")
    }

    /// Extract CF variable name from an expression (if it's a CF flag reference).
    pub(super) fn extract_cf(&self, expr: &CExpr) -> Option<String> {
        self.extract_flag_name(expr, "cf")
    }

    /// Extract SF variable name from an expression (if it's a SF flag reference).
    pub(super) fn extract_sf(&self, expr: &CExpr) -> Option<String> {
        self.extract_flag_name(expr, "sf")
    }

    /// Extract OF variable name from an expression (if it's an OF flag reference).
    pub(super) fn extract_of(&self, expr: &CExpr) -> Option<String> {
        self.extract_flag_name(expr, "of")
    }

    /// Extract ZF variable name from a !ZF expression.
    pub(super) fn extract_not_zf(&self, expr: &CExpr) -> Option<String> {
        if let CExpr::Unary {
            op: UnaryOp::Not,
            operand,
        } = expr
        {
            return self.extract_zf(operand);
        }
        None
    }

    /// Extract CF variable name from a !CF expression.
    pub(super) fn extract_not_cf(&self, expr: &CExpr) -> Option<String> {
        if let CExpr::Unary {
            op: UnaryOp::Not,
            operand,
        } = expr
        {
            return self.extract_cf(operand);
        }
        None
    }

    /// Check if expression is OF == SF.
    pub(super) fn is_of_eq_sf(&self, expr: &CExpr) -> bool {
        if let CExpr::Binary {
            op: BinaryOp::Eq,
            left,
            right,
        } = expr
        {
            let has_of_sf = self.extract_of(left).is_some() && self.is_sf_like_expr(right);
            let has_sf_of = self.is_sf_like_expr(left) && self.extract_of(right).is_some();
            return has_of_sf || has_sf_of;
        }
        false
    }

    /// Check if expression is OF != SF.
    pub(super) fn is_of_ne_sf(&self, expr: &CExpr) -> bool {
        if let CExpr::Binary {
            op: BinaryOp::Ne,
            left,
            right,
        } = expr
        {
            let has_of_sf = self.extract_of(left).is_some() && self.is_sf_like_expr(right);
            let has_sf_of = self.is_sf_like_expr(left) && self.extract_of(right).is_some();
            return has_of_sf || has_sf_of;
        }
        // Also check for !(OF == SF)
        if let CExpr::Unary {
            op: UnaryOp::Not,
            operand,
        } = expr
        {
            return self.is_of_eq_sf(operand);
        }
        false
    }

    pub(super) fn reconstruct_signed_gt_from_and(
        &self,
        cmp_expr: &CExpr,
        of_sf_expr: &CExpr,
    ) -> Option<CExpr> {
        let cmp = self.canonical_compare_tuple(cmp_expr)?;
        if cmp.context != CompareContext::Ne {
            return None;
        }

        let (of_name, sf_expr) = self.extract_of_sf_pair(of_sf_expr, false)?;
        let sf_cmp = self.canonical_compare_tuple(sf_expr)?;
        if sf_cmp.context != CompareContext::SignedNegative {
            return None;
        }

        if !self.compare_tuple_operands_match(&cmp, &sf_cmp) {
            return None;
        }
        if !self.compare_tuple_matches_flag_origin(&cmp, &of_name) {
            return None;
        }

        Some(CExpr::binary(BinaryOp::Gt, cmp.lhs, cmp.rhs))
    }

    pub(super) fn reconstruct_signed_le_from_or(
        &self,
        cmp_expr: &CExpr,
        of_sf_expr: &CExpr,
    ) -> Option<CExpr> {
        let cmp = self.canonical_compare_tuple(cmp_expr)?;
        if cmp.context != CompareContext::Eq {
            return None;
        }

        let (of_name, sf_expr) = self.extract_of_sf_pair(of_sf_expr, true)?;
        let sf_cmp = self.canonical_compare_tuple(sf_expr)?;
        if sf_cmp.context != CompareContext::SignedNegative {
            return None;
        }

        if !self.compare_tuple_operands_match(&cmp, &sf_cmp) {
            return None;
        }
        if !self.compare_tuple_matches_flag_origin(&cmp, &of_name) {
            return None;
        }

        Some(CExpr::binary(BinaryOp::Le, cmp.lhs, cmp.rhs))
    }

    pub(super) fn reconstruct_signed_ge_from_eq(&self, expr: &CExpr) -> Option<CExpr> {
        let (_of_name, sf_expr) = self.extract_of_sf_pair(expr, false)?;
        let sf_cmp = self.canonical_compare_tuple(sf_expr)?;
        if sf_cmp.context != CompareContext::SignedNegative {
            return None;
        }

        Some(CExpr::binary(BinaryOp::Ge, sf_cmp.lhs, sf_cmp.rhs))
    }

    pub(super) fn reconstruct_signed_lt_from_ne(&self, expr: &CExpr) -> Option<CExpr> {
        let (_of_name, sf_expr) = self.extract_of_sf_pair(expr, true)?;
        let sf_cmp = self.canonical_compare_tuple(sf_expr)?;
        if sf_cmp.context != CompareContext::SignedNegative {
            return None;
        }

        Some(CExpr::binary(BinaryOp::Lt, sf_cmp.lhs, sf_cmp.rhs))
    }

    pub(super) fn extract_of_sf_pair<'b>(
        &self,
        expr: &'b CExpr,
        want_ne: bool,
    ) -> Option<(String, &'b CExpr)> {
        let op_match = if want_ne { BinaryOp::Ne } else { BinaryOp::Eq };
        if let CExpr::Binary { op, left, right } = expr {
            if *op != op_match {
                return None;
            }
            if let Some(of_name) = self.extract_of(left) {
                return Some((of_name, right));
            }
            if let Some(of_name) = self.extract_of(right) {
                return Some((of_name, left));
            }
        }
        None
    }

    pub(super) fn canonical_compare_tuple(&self, expr: &CExpr) -> Option<CompareTuple> {
        match expr {
            CExpr::Binary {
                op: BinaryOp::Eq,
                left,
                right,
            } => Some(self.normalize_compare_tuple(CompareTuple {
                lhs: self.resolve_predicate_operand(left, 0, &mut HashSet::new()),
                rhs: self.resolve_predicate_operand(right, 0, &mut HashSet::new()),
                context: CompareContext::Eq,
            })),
            CExpr::Binary {
                op: BinaryOp::Ne,
                left,
                right,
            } => Some(self.normalize_compare_tuple(CompareTuple {
                lhs: self.resolve_predicate_operand(left, 0, &mut HashSet::new()),
                rhs: self.resolve_predicate_operand(right, 0, &mut HashSet::new()),
                context: CompareContext::Ne,
            })),
            CExpr::Binary {
                op: BinaryOp::Lt,
                left,
                right,
            } if self.is_zero_expr(right) => {
                if let Some((sub_lhs, sub_rhs)) = self.extract_sub_operands(left) {
                    return Some(self.normalize_compare_tuple(CompareTuple {
                        lhs: self.resolve_predicate_operand(&sub_lhs, 0, &mut HashSet::new()),
                        rhs: self.resolve_predicate_operand(&sub_rhs, 0, &mut HashSet::new()),
                        context: CompareContext::SignedNegative,
                    }));
                }
                Some(self.normalize_compare_tuple(CompareTuple {
                    lhs: self.resolve_predicate_operand(left, 0, &mut HashSet::new()),
                    rhs: CExpr::IntLit(0),
                    context: CompareContext::SignedNegative,
                }))
            }
            CExpr::Paren(inner) => self.canonical_compare_tuple(inner),
            CExpr::Cast { expr: inner, .. } => self.canonical_compare_tuple(inner),
            _ => None,
        }
    }

    pub(super) fn extract_sub_operands(&self, expr: &CExpr) -> Option<(CExpr, CExpr)> {
        self.extract_sub_operands_with_seen(expr, 0, &mut HashSet::new())
    }

    fn extract_sub_operands_with_seen(
        &self,
        expr: &CExpr,
        depth: u32,
        seen: &mut HashSet<String>,
    ) -> Option<(CExpr, CExpr)> {
        if depth > 32 {
            return None;
        }
        match expr {
            CExpr::Binary {
                op: BinaryOp::Sub,
                left,
                right,
            } => Some((left.as_ref().clone(), right.as_ref().clone())),
            CExpr::Paren(inner) => self.extract_sub_operands_with_seen(inner, depth + 1, seen),
            CExpr::Cast { expr: inner, .. } => {
                self.extract_sub_operands_with_seen(inner, depth + 1, seen)
            }
            CExpr::Var(name) => {
                let visit_key = self
                    .value_id_for_name(name)
                    .map(|value_id| format!("sub:value:{}", value_id.0))
                    .unwrap_or_else(|| format!("sub:name:{name}"));
                if !seen.insert(visit_key.clone()) {
                    return None;
                }
                if let Some(def) = self
                    .lookup_definition(name)
                    .or_else(|| self.formatted_defs_map().get(name).cloned())
                {
                    let result = self.extract_sub_operands_with_seen(&def, depth + 1, seen);
                    seen.remove(&visit_key);
                    return result;
                }
                seen.remove(&visit_key);
                None
            }
            _ => None,
        }
    }

    pub(super) fn normalize_compare_tuple(&self, mut tuple: CompareTuple) -> CompareTuple {
        if matches!(tuple.context, CompareContext::Eq | CompareContext::Ne)
            && self.is_literal_expr(&tuple.lhs)
            && !self.is_literal_expr(&tuple.rhs)
        {
            std::mem::swap(&mut tuple.lhs, &mut tuple.rhs);
        }
        tuple
    }

    pub(super) fn compare_tuple_operands_match(&self, a: &CompareTuple, b: &CompareTuple) -> bool {
        a.lhs == b.lhs && a.rhs == b.rhs
    }

    pub(super) fn compare_tuple_matches_flag_origin(
        &self,
        tuple: &CompareTuple,
        of_name: &str,
    ) -> bool {
        let Some(origin) = self.compare_tuple_from_flag_origin(of_name) else {
            return true;
        };

        // If either side still contains opaque temporaries, treat origin matching as
        // advisory only. Local tuple consistency (cmp vs SF-surrogate) remains mandatory.
        if self.expr_contains_opaque_temp(&tuple.lhs)
            || self.expr_contains_opaque_temp(&tuple.rhs)
            || self.expr_contains_opaque_temp(&origin.lhs)
            || self.expr_contains_opaque_temp(&origin.rhs)
            || self.expr_contains_unresolved_memory(&tuple.lhs)
            || self.expr_contains_unresolved_memory(&tuple.rhs)
            || self.expr_contains_unresolved_memory(&origin.lhs)
            || self.expr_contains_unresolved_memory(&origin.rhs)
        {
            return true;
        }

        tuple.lhs == origin.lhs && tuple.rhs == origin.rhs
    }

    pub(super) fn compare_tuple_from_flag_origin(&self, flag_name: &str) -> Option<CompareTuple> {
        let prov = self.lookup_flag_compare_provenance(flag_name)?;
        let lhs = self.resolve_predicate_operand(
            &self.origin_name_to_expr(&prov.lhs),
            0,
            &mut HashSet::new(),
        );
        let rhs = self.resolve_predicate_operand(
            &self.origin_name_to_expr(&prov.rhs),
            0,
            &mut HashSet::new(),
        );

        Some(self.normalize_compare_tuple(CompareTuple {
            lhs,
            rhs,
            context: match prov.kind {
                FlagCompareKind::Equality => CompareContext::Eq,
                FlagCompareKind::UnsignedLess
                | FlagCompareKind::SignedNegative
                | FlagCompareKind::Overflow => CompareContext::SignedNegative,
            },
        }))
    }

    pub(super) fn origin_name_to_expr(&self, name: &str) -> CExpr {
        if let Some(parsed) = self.parse_expr_from_name(name) {
            return parsed;
        }
        CExpr::Var(name.to_string())
    }

    pub(super) fn parse_expr_from_name(&self, name: &str) -> Option<CExpr> {
        if let Some(expr) = self.compare_const_expr_from_name(name) {
            return Some(expr);
        }

        if let Some(val) = parse_const_value(name) {
            return Some(if val > 0x7fffffff {
                CExpr::UIntLit(val)
            } else {
                CExpr::IntLit(val as i64)
            });
        }

        if let Some(dec) = name.strip_prefix("0d").or_else(|| name.strip_prefix("0D"))
            && let Ok(val) = dec.parse::<i64>()
        {
            return Some(CExpr::IntLit(val));
        }

        if let Some(hex) = name.strip_prefix("0x").or_else(|| name.strip_prefix("0X"))
            && let Ok(val) = u64::from_str_radix(hex, 16)
        {
            return Some(if val > 0x7fffffff {
                CExpr::UIntLit(val)
            } else {
                CExpr::IntLit(val as i64)
            });
        }

        if name.chars().all(|c| c.is_ascii_hexdigit()) {
            let has_alpha = name.chars().any(|c| c.is_ascii_alphabetic());
            let has_digit = name.chars().any(|c| c.is_ascii_digit());
            if has_alpha && (has_digit || name.len() > 4) {
                if let Ok(val) = u64::from_str_radix(name, 16) {
                    return Some(if val > 0x7fffffff {
                        CExpr::UIntLit(val)
                    } else {
                        CExpr::IntLit(val as i64)
                    });
                }
            } else if let Ok(dec) = name.parse::<i64>() {
                return Some(CExpr::IntLit(dec));
            }
        }

        if let Ok(dec) = name.parse::<i64>() {
            return Some(CExpr::IntLit(dec));
        }

        None
    }

    pub(super) fn resolve_predicate_operand(
        &self,
        expr: &CExpr,
        depth: u32,
        visited: &mut HashSet<String>,
    ) -> CExpr {
        if depth > MAX_PREDICATE_OPERAND_DEPTH {
            return expr.clone();
        }

        match expr {
            CExpr::Paren(inner) => self.resolve_predicate_operand(inner, depth + 1, visited),
            CExpr::Cast { expr: inner, .. } => {
                self.resolve_predicate_operand(inner, depth + 1, visited)
            }
            CExpr::Deref(inner) => {
                if let Some(stack_var) = self.simplify_stack_access(inner) {
                    CExpr::Var(stack_var)
                } else {
                    expr.clone()
                }
            }
            CExpr::Var(name) => {
                if let Some(parsed) = self.parse_expr_from_name(name) {
                    return parsed;
                }
                if !visited.insert(name.clone()) {
                    return CExpr::Var(name.clone());
                }
                let allow_stack_alias_fallback = |alias: &str| {
                    !alias.ends_with("_home")
                        && !self.is_reserved_param_alias_name(alias)
                        && !alias.starts_with("var_")
                        && !alias.starts_with("local_")
                        && !alias.starts_with("stack_")
                        && !alias.starts_with("arg_")
                };
                let stack_alias_fallback = self
                    .stack_slot_provenance_for_name(name)
                    .filter(|slot| slot.offset < 0)
                    .and_then(|slot| {
                        self.resolve_stack_var(slot.offset).map(|stack_name| {
                            (slot.is_scalar_predicate_carrier(), CExpr::Var(stack_name))
                        })
                    });
                if let Some((false, CExpr::Var(alias))) = stack_alias_fallback.as_ref()
                    && allow_stack_alias_fallback(alias)
                {
                    return CExpr::Var(alias.clone());
                }
                if let Some(owner) = self.stable_owned_call_result_expr_for_name(name, true) {
                    return owner;
                }
                if let Some(source) = self
                    .call_result_source_for_ssa_name(name)
                    .or_else(|| self.local_post_call_source_for_ssa_name(name))
                {
                    if let Some(inner @ CExpr::Call { .. }) = self
                        .lookup_definition(name)
                        .or_else(|| self.formatted_defs_map().get(name).cloned())
                    {
                        return inner;
                    }
                    if let Some(inner) = self.synthesized_call_expr_for_source_call(source) {
                        return inner;
                    }
                }
                if let Some(alias) = self.arg_alias_for_rendered_name(name) {
                    return CExpr::Var(alias);
                }
                if let Some(prepared) = self.prepared_predicate_view() {
                    if let Some(inner) = prepared
                        .predicate_expr_for_name(name)
                        .cloned()
                        .filter(|inner| inner != &CExpr::Var(name.clone()))
                    {
                        return self.resolve_predicate_expr_tree_with_visited(&inner, visited);
                    }
                    if let Some(inner) =
                        prepared.owner_expr_for_name(name).cloned().filter(|inner| {
                            inner != &CExpr::Var(name.clone()) && !matches!(inner, CExpr::AddrOf(_))
                        })
                    {
                        return self.resolve_predicate_expr_tree_with_visited(&inner, visited);
                    }
                }
                if let Some(inner) = self.lookup_predicate_expr(name)
                    && inner != CExpr::Var(name.clone())
                {
                    return self.resolve_predicate_operand(&inner, depth + 1, visited);
                }

                let resolved = self
                    .lookup_predicate_expr(name)
                    .or_else(|| self.lookup_definition(name))
                    .or_else(|| self.formatted_defs_map().get(name).cloned())
                    .map(|inner| {
                        if let Some(stack_var) = self.stack_alias_from_deref_expr(&inner) {
                            CExpr::Var(stack_var)
                        } else if matches!(inner, CExpr::Call { .. }) {
                            inner
                        } else if (self.is_predicate_like_expr(&inner)
                            || matches!(
                                inner,
                                CExpr::Binary {
                                    op: BinaryOp::Add
                                        | BinaryOp::Sub
                                        | BinaryOp::Mul
                                        | BinaryOp::Div
                                        | BinaryOp::Mod
                                        | BinaryOp::Shl
                                        | BinaryOp::Shr
                                        | BinaryOp::BitAnd
                                        | BinaryOp::BitOr
                                        | BinaryOp::BitXor,
                                    ..
                                } | CExpr::Unary { .. }
                            ))
                            && !self.expr_is_address_artifact_in_scalar_context(&inner)
                        {
                            self.resolve_predicate_expr_tree_with_visited(&inner, visited)
                        } else if matches!(
                            inner,
                            CExpr::Var(_) | CExpr::Paren(_) | CExpr::Cast { .. } | CExpr::Deref(_)
                        ) {
                            self.resolve_predicate_operand(&inner, depth + 1, visited)
                        } else {
                            CExpr::Var(name.clone())
                        }
                    })
                    .unwrap_or_else(|| CExpr::Var(name.clone()));

                visited.remove(name);
                if let Some((_, ref alias @ CExpr::Var(ref alias_name))) = stack_alias_fallback {
                    if !allow_stack_alias_fallback(alias_name) {
                        return resolved;
                    }
                    if self.structured_predicate_candidate_should_win(alias, &resolved) {
                        resolved
                    } else {
                        self.choose_preferred_scalar_predicate_expr(
                            Some(alias.clone()),
                            Some(resolved.clone()),
                        )
                        .unwrap_or(resolved)
                    }
                } else {
                    resolved
                }
            }
            _ => expr.clone(),
        }
    }

    pub(super) fn is_literal_expr(&self, expr: &CExpr) -> bool {
        matches!(
            expr,
            CExpr::IntLit(_) | CExpr::UIntLit(_) | CExpr::FloatLit(_) | CExpr::CharLit(_)
        )
    }

    pub(super) fn is_opaque_temp_name(&self, name: &str) -> bool {
        if name.starts_with("var_") {
            return true;
        }
        if let Some(rest) = name.strip_prefix('t') {
            return rest
                .chars()
                .next()
                .map(|c| c.is_ascii_digit())
                .unwrap_or(false);
        }
        false
    }

    pub(super) fn is_semantic_binding_name(name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        lower.starts_with("local_")
            || lower.starts_with("arg")
            || lower.starts_with("field_")
            || lower.starts_with("var_")
            || lower.starts_with("sub_")
            || lower.starts_with("str.")
            || lower.starts_with("0x")
            || lower.contains('.')
    }

    pub(super) fn is_register_like_base_name(&self, name: &str) -> bool {
        self.inputs.arch.is_register_like_base_name(name)
    }

    pub(super) fn is_ephemeral_ssa_target(&self, name: &str) -> bool {
        if Self::is_semantic_binding_name(name) {
            return false;
        }

        if self.is_opaque_temp_name(name) {
            return true;
        }

        let lower = name.to_ascii_lowercase();
        let base = match lower.rsplit_once('_') {
            Some((base, suffix))
                if !base.is_empty() && suffix.chars().all(|ch| ch.is_ascii_digit()) =>
            {
                base
            }
            _ => lower.as_str(),
        };

        self.is_register_like_base_name(base)
    }

    pub(super) fn expr_contains_opaque_temp(&self, expr: &CExpr) -> bool {
        let mut found = false;
        expr.visit(&mut |node| {
            if let CExpr::Var(name) = node
                && self.is_opaque_temp_name(name)
            {
                found = true;
            }
        });
        found
    }

    pub(super) fn expr_contains_unresolved_memory(&self, expr: &CExpr) -> bool {
        let mut found = false;
        expr.visit(&mut |node| {
            if matches!(node, CExpr::Deref(_)) {
                found = true;
            }
        });
        found
    }

    pub(super) fn is_sf_like_expr(&self, expr: &CExpr) -> bool {
        self.extract_sf(expr).is_some() || self.is_sf_surrogate(expr)
    }

    pub(super) fn is_sf_surrogate(&self, expr: &CExpr) -> bool {
        let mut visited = HashSet::new();
        self.is_sf_surrogate_inner(expr, &mut visited, 0)
    }

    pub(super) fn is_sf_surrogate_inner(
        &self,
        expr: &CExpr,
        visited: &mut HashSet<String>,
        depth: usize,
    ) -> bool {
        // Guard against deeply nested/cyclic definitions from large CFGs.
        if depth > MAX_SF_SURROGATE_DEPTH {
            return false;
        }
        match expr {
            CExpr::Binary {
                op: BinaryOp::Lt,
                left,
                right,
            } if self.is_zero_expr(right) => self.is_sub_like_expr_inner(left, visited, depth + 1),
            CExpr::Paren(inner) => self.is_sf_surrogate_inner(inner, visited, depth + 1),
            CExpr::Cast { expr: inner, .. } => {
                self.is_sf_surrogate_inner(inner, visited, depth + 1)
            }
            CExpr::Var(name) => {
                if !visited.insert(name.clone()) {
                    return false;
                }
                let resolved = self
                    .lookup_definition(name)
                    .or_else(|| self.formatted_defs_map().get(name).cloned())
                    .map(|inner| self.is_sf_surrogate_inner(&inner, visited, depth + 1))
                    .unwrap_or(false);
                visited.remove(name);
                resolved
            }
            _ => false,
        }
    }

    pub(super) fn is_sub_like_expr_inner(
        &self,
        expr: &CExpr,
        visited: &mut HashSet<String>,
        depth: usize,
    ) -> bool {
        if depth > MAX_SUB_LIKE_DEPTH {
            return false;
        }
        match expr {
            CExpr::Binary {
                op: BinaryOp::Sub, ..
            } => true,
            CExpr::Paren(inner) => self.is_sub_like_expr_inner(inner, visited, depth + 1),
            CExpr::Cast { expr: inner, .. } => {
                self.is_sub_like_expr_inner(inner, visited, depth + 1)
            }
            CExpr::Var(name) => {
                if !visited.insert(name.clone()) {
                    return false;
                }
                let resolved = self
                    .lookup_definition(name)
                    .or_else(|| self.formatted_defs_map().get(name).cloned())
                    .map(|inner| self.is_sub_like_expr_inner(&inner, visited, depth + 1))
                    .unwrap_or(false);
                visited.remove(name);
                resolved
            }
            _ => false,
        }
    }

    /// Extract switch expression from an operation (for switch statement detection).
    pub fn extract_switch_expr(&self, op: &SSAOp) -> Option<CExpr> {
        // Look for indirect branch (BranchInd) which typically holds the switch variable
        if let SSAOp::BranchInd { target } = op {
            return Some(self.get_expr(target));
        }
        None
    }

    /// Look up the original comparison operands for a flag variable.
    pub(super) fn lookup_flag_origin(&self, flag_name: &str) -> Option<(String, String)> {
        if let Some(prov) = self.lookup_flag_compare_provenance(flag_name) {
            return Some((prov.lhs, prov.rhs));
        }

        let (flag_base, flag_version) = parse_flag_name(flag_name)?;

        let exact_matches = self.collect_matching_flag_origins(&flag_base, flag_version.as_deref());
        if let Some((_, origin)) = exact_matches.into_iter().next() {
            return Some(origin);
        }

        // Fallback by base-name only when there is exactly one candidate.
        // This avoids picking an arbitrary origin for unsuffixed flags.
        let candidates = self.collect_matching_flag_origins(&flag_base, None);

        if candidates.len() == 1 {
            return candidates.into_iter().next().map(|(_, origin)| origin);
        }

        None
    }

    pub(super) fn lookup_flag_compare_provenance(
        &self,
        flag_name: &str,
    ) -> Option<FlagCompareProvenance> {
        let (flag_base, flag_version) = parse_flag_name(flag_name)?;

        let exact_matches =
            self.collect_matching_flag_compare_provenance(&flag_base, flag_version.as_deref());
        if let Some((_, prov)) = exact_matches.into_iter().next() {
            return Some(prov);
        }

        let candidates = self.collect_matching_flag_compare_provenance(&flag_base, None);

        if candidates.len() == 1 {
            return candidates.into_iter().next().map(|(_, prov)| prov);
        }

        None
    }

    fn collect_matching_flag_origins(
        &self,
        flag_base: &str,
        version: Option<&str>,
    ) -> Vec<(String, (String, String))> {
        let mut candidates = self
            .flag_origins_map()
            .iter()
            .filter_map(|(key, origin)| {
                let (key_base, key_version) = parse_flag_name(key)?;
                (key_base == flag_base
                    && version.is_none_or(|expected| key_version.as_deref() == Some(expected)))
                .then_some((key.clone(), origin.clone()))
            })
            .collect::<Vec<_>>();
        candidates.sort_by(|a, b| {
            self.flag_origin_selection_key(&b.1)
                .cmp(&self.flag_origin_selection_key(&a.1))
                .then_with(|| a.0.cmp(&b.0))
        });
        candidates
    }

    fn collect_matching_flag_compare_provenance(
        &self,
        flag_base: &str,
        version: Option<&str>,
    ) -> Vec<(String, FlagCompareProvenance)> {
        let mut candidates = self
            .flag_compare_provenance_map()
            .iter()
            .filter_map(|(key, prov)| {
                let (key_base, key_version) = parse_flag_name(key)?;
                (key_base == flag_base
                    && version.is_none_or(|expected| key_version.as_deref() == Some(expected)))
                .then_some((key.clone(), prov.clone()))
            })
            .collect::<Vec<_>>();
        candidates.sort_by(|a, b| {
            self.flag_compare_provenance_selection_key(&b.1)
                .cmp(&self.flag_compare_provenance_selection_key(&a.1))
                .then_with(|| a.0.cmp(&b.0))
        });
        candidates
    }

    fn flag_origin_selection_key(&self, origin: &(String, String)) -> (i32, i32) {
        (
            self.flag_operand_quality(&origin.0) + self.flag_operand_quality(&origin.1),
            self.flag_operand_quality(&origin.0)
                .max(self.flag_operand_quality(&origin.1)),
        )
    }

    fn flag_compare_provenance_selection_key(
        &self,
        prov: &FlagCompareProvenance,
    ) -> (i32, i32, u8) {
        (
            self.flag_operand_quality(&prov.lhs) + self.flag_operand_quality(&prov.rhs),
            self.flag_operand_quality(&prov.lhs)
                .max(self.flag_operand_quality(&prov.rhs)),
            match prov.kind {
                FlagCompareKind::Equality => 3,
                FlagCompareKind::UnsignedLess => 2,
                FlagCompareKind::SignedNegative => 1,
                FlagCompareKind::Overflow => 0,
            },
        )
    }

    fn flag_operand_quality(&self, name: &str) -> i32 {
        if self.arg_alias_for_rendered_name(name).is_some() || name.starts_with("arg") {
            return 40;
        }
        if self.parse_expr_from_name(name).is_some() {
            return 30;
        }
        if self.is_low_signal_visible_name(name) {
            return 0;
        }
        if self.is_transient_visible_name(name) {
            return 10;
        }
        20
    }

    pub(super) fn compare_provenance_expr(&self, prov: &FlagCompareProvenance) -> Option<CExpr> {
        let lhs = self.resolve_predicate_operand(
            &self.origin_name_to_expr(&prov.lhs),
            0,
            &mut HashSet::new(),
        );
        let rhs = self.resolve_predicate_operand(
            &self.origin_name_to_expr(&prov.rhs),
            0,
            &mut HashSet::new(),
        );

        match prov.kind {
            FlagCompareKind::Equality => Some(CExpr::binary(BinaryOp::Eq, lhs, rhs)),
            FlagCompareKind::UnsignedLess => Some(CExpr::binary(BinaryOp::Lt, lhs, rhs)),
            FlagCompareKind::SignedNegative => Some(CExpr::binary(
                BinaryOp::Lt,
                CExpr::binary(BinaryOp::Sub, lhs, rhs),
                CExpr::IntLit(0),
            )),
            FlagCompareKind::Overflow => None,
        }
    }

    pub(super) fn compare_provenance_expr_for_branch(
        &self,
        prov: &FlagCompareProvenance,
    ) -> Option<CExpr> {
        let depth_seed = MAX_PREDICATE_OPERAND_DEPTH.saturating_sub(1);
        let lhs = self.resolve_predicate_operand(
            &self.origin_name_to_expr(&prov.lhs),
            depth_seed,
            &mut HashSet::new(),
        );
        let rhs = self.resolve_predicate_operand(
            &self.origin_name_to_expr(&prov.rhs),
            depth_seed,
            &mut HashSet::new(),
        );

        match prov.kind {
            FlagCompareKind::Equality => Some(CExpr::binary(BinaryOp::Eq, lhs, rhs)),
            FlagCompareKind::UnsignedLess => Some(CExpr::binary(BinaryOp::Lt, lhs, rhs)),
            FlagCompareKind::SignedNegative => Some(CExpr::binary(
                BinaryOp::Lt,
                CExpr::binary(BinaryOp::Sub, lhs, rhs),
                CExpr::IntLit(0),
            )),
            FlagCompareKind::Overflow => None,
        }
    }
}

fn parse_flag_name(name: &str) -> Option<(String, Option<String>)> {
    let lower = name.to_ascii_lowercase();
    if is_flag_base_name(&lower) {
        return Some((lower, None));
    }

    let (base, suffix) = lower.split_once('_')?;
    if is_flag_base_name(base) && !suffix.is_empty() && suffix.chars().all(|ch| ch.is_ascii_digit())
    {
        return Some((base.to_string(), Some(suffix.to_string())));
    }

    None
}

fn is_specific_flag_name(name: &str, flag: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    if flag_name_matches(&lower, flag) {
        return true;
    }

    let Some((base, suffix)) = lower.split_once('_') else {
        return false;
    };

    flag_name_matches(base, flag)
        && !suffix.is_empty()
        && suffix.chars().all(|ch| ch.is_ascii_digit())
}

fn flag_name_matches(base: &str, flag: &str) -> bool {
    if base == flag {
        return true;
    }

    matches!(
        (base, flag),
        ("cy" | "tmpcy", "cf")
            | ("zr" | "tmpzr", "zf")
            | ("ng" | "tmpng", "sf")
            | ("ov" | "tmpov", "of")
    )
}

fn is_flag_base_name(name: &str) -> bool {
    matches!(
        name,
        "cf" | "pf"
            | "af"
            | "zf"
            | "sf"
            | "of"
            | "cy"
            | "zr"
            | "ng"
            | "ov"
            | "nf"
            | "vf"
            | "df"
            | "tf"
            | "if"
            | "iopl"
            | "nt"
            | "rf"
            | "vm"
            | "tmpcy"
            | "tmpzr"
            | "tmpng"
            | "tmpov"
    )
}

/// Check if a name is a CPU flag that should be eliminated when unused.
pub(crate) fn is_cpu_flag(name: &str) -> bool {
    // Match exact flag names
    if matches!(
        name,
        "cf" | "pf"
            | "af"
            | "zf"
            | "sf"
            | "of"
            | "cy"
            | "zr"
            | "ng"
            | "ov"
            | "nf"
            | "vf"
            | "df"
            | "tf"
            | "if"
            | "iopl"
            | "nt"
            | "rf"
            | "vm"
            | "ac"
            | "vif"
            | "vip"
            | "id"
            | "tmpcy"
            | "tmpzr"
            | "tmpng"
            | "tmpov"
    ) {
        return true;
    }

    // Also match versioned flags (e.g., cf_1, zf_2)
    name.starts_with("cf_")
        || name.starts_with("pf_")
        || name.starts_with("af_")
        || name.starts_with("zf_")
        || name.starts_with("sf_")
        || name.starts_with("of_")
        || name.starts_with("cy_")
        || name.starts_with("zr_")
        || name.starts_with("ng_")
        || name.starts_with("ov_")
        || name.starts_with("nf_")
        || name.starts_with("vf_")
        || name.starts_with("tmpcy_")
        || name.starts_with("tmpzr_")
        || name.starts_with("tmpng_")
        || name.starts_with("tmpov_")
}

#[cfg(test)]
#[path = "tests/flags.rs"]
mod tests;
