//! C Abstract Syntax Tree representation.
//!
//! This module defines the AST types used to represent decompiled C code.

use serde::{Deserialize, Serialize};

/// The C type model.
///
/// This was a second type enum with its own renderer, and the two had already
/// disagreed once -- about how to spell a 128-bit integer -- with nothing to
/// catch it. It is now the shared model, so there is one set of variants and
/// one spelling for each of them.
pub use r2types::CTypeLike as CType;

/// A C expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum CExpr {
    /// Internal marker attached to one exact rendered expression occurrence.
    ///
    /// This is transparent to C rendering and must be stripped before a
    /// `CFunction` leaves the decompiler.
    #[doc(hidden)]
    #[serde(skip)]
    Observed {
        id: RenderObservationId,
        expr: Box<CExpr>,
    },
    /// Integer literal.
    IntLit(i64),
    /// Unsigned integer literal.
    UIntLit(u64),
    /// Float literal.
    FloatLit(f64),
    /// String literal.
    StringLit(String),
    /// Character literal.
    CharLit(char),
    /// Reference to a name this function declares.
    Var(crate::symbol::SymbolId),
    /// A name for something the function does not own, and what kind of thing it is.
    ///
    /// `Var` is for values this function has. An intrinsic the target defines, or
    /// a marker the lowering emits where it has nothing to say, is neither a value
    /// nor something a declaration could give it, and spelling it as a variable is
    /// what let a machine name look exactly like a local.
    External {
        name: String,
        kind: crate::symbol::ExternalKind,
    },
    /// Unary operation.
    Unary { op: UnaryOp, operand: Box<CExpr> },
    /// Binary operation.
    Binary {
        op: BinaryOp,
        left: Box<CExpr>,
        right: Box<CExpr>,
    },
    /// Ternary conditional: cond ? then : else.
    Ternary {
        cond: Box<CExpr>,
        then_expr: Box<CExpr>,
        else_expr: Box<CExpr>,
    },
    /// Type cast: (type)expr.
    Cast { ty: CType, expr: Box<CExpr> },
    /// Function call.
    /// A call, and the site that makes it when one is known.
    ///
    /// Two layers build an expression for one call and nothing downstream could
    /// tell they were the same call, because the only handle either offered was
    /// the shape of the expression and the shapes differ. The site is an
    /// identity that does not change when the rendering does.
    Call {
        func: Box<CExpr>,
        args: Vec<CExpr>,
        site: Option<(u64, usize)>,
    },
    /// Array/pointer subscript: `arr[index]`.
    Subscript { base: Box<CExpr>, index: Box<CExpr> },
    /// Member access: obj.member.
    Member { base: Box<CExpr>, member: String },
    /// Pointer member access: ptr->member.
    PtrMember { base: Box<CExpr>, member: String },
    /// Sizeof expression.
    Sizeof(Box<CExpr>),
    /// Sizeof type.
    SizeofType(CType),
    /// Address-of: &expr.
    AddrOf(Box<CExpr>),
    /// Dereference: *expr.
    Deref(Box<CExpr>),
    /// Comma expression: (a, b, c).
    Comma(Vec<CExpr>),
    /// Parenthesized expression.
    Paren(Box<CExpr>),
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnaryOp {
    /// Logical NOT: !x
    Not,
    /// Bitwise NOT: ~x
    BitNot,
    /// Negation: -x
    Neg,
    /// Pre-increment: ++x
    PreInc,
    /// Pre-decrement: --x
    PreDec,
    /// Post-increment: x++
    PostInc,
    /// Post-decrement: x--
    PostDec,
}

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinaryOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,

    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Logical
    And,
    Or,

    // Assignment
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ModAssign,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,
    ShlAssign,
    ShrAssign,
}

impl CExpr {
    /// Attach an internal observation marker to this exact occurrence.
    pub(crate) fn observed(id: RenderObservationId, expr: CExpr) -> Self {
        Self::Observed {
            id,
            expr: Box::new(expr),
        }
    }

    /// Borrow the semantic expression beneath any internal observation markers.
    pub(crate) fn unobserved(&self) -> &Self {
        let mut expr = self;
        while let Self::Observed { expr: inner, .. } = expr {
            expr = inner;
        }
        expr
    }

    /// Structural equality that treats observation wrappers as metadata at
    /// every depth, not only at the root.
    pub(crate) fn transparently_eq(&self, other: &Self) -> bool {
        let left = self.unobserved();
        let right = other.unobserved();
        match (left, right) {
            (Self::IntLit(left), Self::IntLit(right)) => left == right,
            (Self::UIntLit(left), Self::UIntLit(right)) => left == right,
            (Self::FloatLit(left), Self::FloatLit(right)) => left == right,
            (Self::StringLit(left), Self::StringLit(right)) => left == right,
            (Self::CharLit(left), Self::CharLit(right)) => left == right,
            (Self::Var(left), Self::Var(right)) => left == right,
            (
                Self::External {
                    name: left_name,
                    kind: left_kind,
                },
                Self::External {
                    name: right_name,
                    kind: right_kind,
                },
            ) => left_name == right_name && left_kind == right_kind,
            (
                Self::Unary {
                    op: left_op,
                    operand: left_operand,
                },
                Self::Unary {
                    op: right_op,
                    operand: right_operand,
                },
            ) => left_op == right_op && left_operand.transparently_eq(right_operand),
            (
                Self::Binary {
                    op: left_op,
                    left: left_left,
                    right: left_right,
                },
                Self::Binary {
                    op: right_op,
                    left: right_left,
                    right: right_right,
                },
            ) => {
                left_op == right_op
                    && left_left.transparently_eq(right_left)
                    && left_right.transparently_eq(right_right)
            }
            (
                Self::Ternary {
                    cond: left_cond,
                    then_expr: left_then,
                    else_expr: left_else,
                },
                Self::Ternary {
                    cond: right_cond,
                    then_expr: right_then,
                    else_expr: right_else,
                },
            ) => {
                left_cond.transparently_eq(right_cond)
                    && left_then.transparently_eq(right_then)
                    && left_else.transparently_eq(right_else)
            }
            (
                Self::Cast {
                    ty: left_ty,
                    expr: left_expr,
                },
                Self::Cast {
                    ty: right_ty,
                    expr: right_expr,
                },
            ) => left_ty == right_ty && left_expr.transparently_eq(right_expr),
            (
                Self::Call {
                    func: left_func,
                    args: left_args,
                    site: left_site,
                },
                Self::Call {
                    func: right_func,
                    args: right_args,
                    site: right_site,
                },
            ) => {
                left_site == right_site
                    && left_func.transparently_eq(right_func)
                    && transparent_expr_slices_eq(left_args, right_args)
            }
            (
                Self::Subscript {
                    base: left_base,
                    index: left_index,
                },
                Self::Subscript {
                    base: right_base,
                    index: right_index,
                },
            ) => left_base.transparently_eq(right_base) && left_index.transparently_eq(right_index),
            (
                Self::Member {
                    base: left_base,
                    member: left_member,
                },
                Self::Member {
                    base: right_base,
                    member: right_member,
                },
            )
            | (
                Self::PtrMember {
                    base: left_base,
                    member: left_member,
                },
                Self::PtrMember {
                    base: right_base,
                    member: right_member,
                },
            ) => left_member == right_member && left_base.transparently_eq(right_base),
            (Self::Sizeof(left), Self::Sizeof(right))
            | (Self::AddrOf(left), Self::AddrOf(right))
            | (Self::Deref(left), Self::Deref(right))
            | (Self::Paren(left), Self::Paren(right)) => left.transparently_eq(right),
            (Self::SizeofType(left), Self::SizeofType(right)) => left == right,
            (Self::Comma(left), Self::Comma(right)) => transparent_expr_slices_eq(left, right),
            _ => false,
        }
    }

    /// Clone semantic expression structure without copying occurrence-owned
    /// observation IDs into a second location.
    pub(crate) fn clone_without_render_observations(&self) -> Self {
        fn strip(expr: CExpr) -> CExpr {
            match expr {
                CExpr::Observed { expr, .. } => strip(*expr),
                other => other.map_children(&mut strip),
            }
        }

        strip(self.clone())
    }

    /// Create an integer literal.
    pub fn int(value: i64) -> Self {
        Self::IntLit(value)
    }

    /// Create an unsigned integer literal.
    pub fn uint(value: u64) -> Self {
        Self::UIntLit(value)
    }

    /// Create a variable reference to an already declared name.
    pub fn var(name: crate::symbol::SymbolId) -> Self {
        Self::Var(name)
    }

    /// Create a binary operation.
    pub fn binary(op: BinaryOp, left: CExpr, right: CExpr) -> Self {
        Self::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Create a unary operation.
    pub fn unary(op: UnaryOp, operand: CExpr) -> Self {
        Self::Unary {
            op,
            operand: Box::new(operand),
        }
    }

    /// Create a function call.
    pub fn call(func: CExpr, args: Vec<CExpr>) -> Self {
        Self::Call {
            func: Box::new(func),
            args,
            site: None,
        }
    }

    /// A call that knows which site makes it.
    pub fn call_at(site: (u64, usize), func: CExpr, args: Vec<CExpr>) -> Self {
        Self::Call {
            func: Box::new(func),
            args,
            site: Some(site),
        }
    }

    /// Create a cast expression.
    pub fn cast(ty: CType, expr: CExpr) -> Self {
        Self::Cast {
            ty,
            expr: Box::new(expr),
        }
    }

    /// Create an assignment.
    pub fn assign(target: CExpr, value: CExpr) -> Self {
        Self::binary(BinaryOp::Assign, target, value)
    }

    /// Create a dereference.
    pub fn deref(expr: CExpr) -> Self {
        Self::Deref(Box::new(expr))
    }

    /// Create an address-of.
    pub fn addr_of(expr: CExpr) -> Self {
        Self::AddrOf(Box::new(expr))
    }

    /// Create a subscript.
    pub fn subscript(base: CExpr, index: CExpr) -> Self {
        Self::Subscript {
            base: Box::new(base),
            index: Box::new(index),
        }
    }

    /// Get operator precedence (higher = binds tighter).
    pub fn precedence(&self) -> u8 {
        match self {
            Self::Observed { expr, .. } => expr.precedence(),
            Self::Comma(_) => 1,
            Self::Binary {
                op:
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
                    | BinaryOp::ShrAssign,
                ..
            } => 2,
            Self::Ternary { .. } => 3,
            Self::Binary {
                op: BinaryOp::Or, ..
            } => 4,
            Self::Binary {
                op: BinaryOp::And, ..
            } => 5,
            Self::Binary {
                op: BinaryOp::BitOr,
                ..
            } => 6,
            Self::Binary {
                op: BinaryOp::BitXor,
                ..
            } => 7,
            Self::Binary {
                op: BinaryOp::BitAnd,
                ..
            } => 8,
            Self::Binary {
                op: BinaryOp::Eq | BinaryOp::Ne,
                ..
            } => 9,
            Self::Binary {
                op: BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge,
                ..
            } => 10,
            Self::Binary {
                op: BinaryOp::Shl | BinaryOp::Shr,
                ..
            } => 11,
            Self::Binary {
                op: BinaryOp::Add | BinaryOp::Sub,
                ..
            } => 12,
            Self::Binary {
                op: BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod,
                ..
            } => 13,
            Self::Unary { .. }
            | Self::Cast { .. }
            | Self::Sizeof(_)
            | Self::SizeofType(_)
            | Self::AddrOf(_)
            | Self::Deref(_) => 14,
            Self::Subscript { .. }
            | Self::Member { .. }
            | Self::PtrMember { .. }
            | Self::Call { .. } => 15,
            _ => 16, // Literals, variables, parenthesized
        }
    }

    /// Apply a transformation to immediate child expressions.
    pub fn map_children(self, f: &mut impl FnMut(CExpr) -> CExpr) -> Self {
        match self {
            Self::Observed { id, expr } => Self::Observed {
                id,
                expr: Box::new(f(*expr)),
            },
            Self::Unary { op, operand } => Self::Unary {
                op,
                operand: Box::new(f(*operand)),
            },
            Self::Binary { op, left, right } => Self::Binary {
                op,
                left: Box::new(f(*left)),
                right: Box::new(f(*right)),
            },
            Self::Ternary {
                cond,
                then_expr,
                else_expr,
            } => Self::Ternary {
                cond: Box::new(f(*cond)),
                then_expr: Box::new(f(*then_expr)),
                else_expr: Box::new(f(*else_expr)),
            },
            Self::Cast { ty, expr } => Self::Cast {
                ty,
                expr: Box::new(f(*expr)),
            },
            Self::Call { func, args, site } => Self::Call {
                func: Box::new(f(*func)),
                args: args.into_iter().map(f).collect(),
                site,
            },
            Self::Subscript { base, index } => Self::Subscript {
                base: Box::new(f(*base)),
                index: Box::new(f(*index)),
            },
            Self::Member { base, member } => Self::Member {
                base: Box::new(f(*base)),
                member,
            },
            Self::PtrMember { base, member } => Self::PtrMember {
                base: Box::new(f(*base)),
                member,
            },
            Self::Sizeof(inner) => Self::Sizeof(Box::new(f(*inner))),
            Self::AddrOf(inner) => Self::AddrOf(Box::new(f(*inner))),
            Self::Deref(inner) => Self::Deref(Box::new(f(*inner))),
            Self::Comma(items) => Self::Comma(items.into_iter().map(f).collect()),
            Self::Paren(inner) => Self::Paren(Box::new(f(*inner))),
            leaf => leaf,
        }
    }

    /// Visit this expression and all descendants in pre-order.
    pub fn visit(&self, f: &mut impl FnMut(&CExpr)) {
        if let Self::Observed { expr, .. } = self {
            expr.visit(f);
            return;
        }
        f(self);
        match self {
            Self::Unary { operand, .. }
            | Self::Cast { expr: operand, .. }
            | Self::Sizeof(operand)
            | Self::AddrOf(operand)
            | Self::Deref(operand)
            | Self::Paren(operand) => operand.visit(f),
            Self::Binary { left, right, .. } => {
                left.visit(f);
                right.visit(f);
            }
            Self::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.visit(f);
                then_expr.visit(f);
                else_expr.visit(f);
            }
            Self::Call { func, args, .. } => {
                func.visit(f);
                for arg in args {
                    arg.visit(f);
                }
            }
            Self::Subscript { base, index } => {
                base.visit(f);
                index.visit(f);
            }
            Self::Member { base, .. } | Self::PtrMember { base, .. } => base.visit(f),
            Self::Comma(items) => {
                for item in items {
                    item.visit(f);
                }
            }
            Self::IntLit(_)
            | Self::UIntLit(_)
            | Self::FloatLit(_)
            | Self::StringLit(_)
            | Self::CharLit(_)
            | Self::Var(_)
            | Self::External { .. }
            | Self::SizeofType(_) => {}
            Self::Observed { .. } => unreachable!("handled before visiting semantic nodes"),
        }
    }
}

fn transparent_expr_slices_eq(left: &[CExpr], right: &[CExpr]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| left.transparently_eq(right))
}

pub use crate::observation_journal::RenderObservationId;

/// Test-only marker allocator. Production IDs are owned by the sealed journal.
#[cfg(test)]
#[derive(Debug, Default)]
pub(crate) struct RenderObservationOwner {
    next: u32,
}

/// Allocation failed before an observation could be attached.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RenderObservationAllocationError {
    IdSpaceExhausted,
}

#[cfg(test)]
impl RenderObservationOwner {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    fn allocate(&mut self) -> Result<RenderObservationId, RenderObservationAllocationError> {
        let next = self
            .next
            .checked_add(1)
            .ok_or(RenderObservationAllocationError::IdSpaceExhausted)?;
        let id = crate::observation_journal::test_render_observation_id(self.next);
        self.next = next;
        Ok(id)
    }

    pub(crate) fn observe_expr(
        &mut self,
        expr: CExpr,
    ) -> Result<(RenderObservationId, CExpr), RenderObservationAllocationError> {
        let id = self.allocate()?;
        Ok((id, CExpr::observed(id, expr)))
    }

    pub(crate) fn observe_stmt(
        &mut self,
        stmt: CStmt,
    ) -> Result<(RenderObservationId, CStmt), RenderObservationAllocationError> {
        let id = self.allocate()?;
        Ok((id, CStmt::observed(id, stmt)))
    }

    pub(crate) fn expected_count(&self) -> usize {
        usize::try_from(self.next).unwrap_or(usize::MAX)
    }
}

impl BinaryOp {
    /// True for the operators whose left operand is written, not read.
    pub const fn writes_left_operand(self) -> bool {
        matches!(
            self,
            Self::Assign
                | Self::AddAssign
                | Self::SubAssign
                | Self::MulAssign
                | Self::DivAssign
                | Self::ModAssign
                | Self::BitAndAssign
                | Self::BitOrAssign
                | Self::BitXorAssign
                | Self::ShlAssign
                | Self::ShrAssign
        )
    }

    /// Get the C operator string.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::BitAnd => "&",
            Self::BitOr => "|",
            Self::BitXor => "^",
            Self::Shl => "<<",
            Self::Shr => ">>",
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::And => "&&",
            Self::Or => "||",
            Self::Assign => "=",
            Self::AddAssign => "+=",
            Self::SubAssign => "-=",
            Self::MulAssign => "*=",
            Self::DivAssign => "/=",
            Self::ModAssign => "%=",
            Self::BitAndAssign => "&=",
            Self::BitOrAssign => "|=",
            Self::BitXorAssign => "^=",
            Self::ShlAssign => "<<=",
            Self::ShrAssign => ">>=",
        }
    }
}

impl UnaryOp {
    /// Get the C operator string.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Not => "!",
            Self::BitNot => "~",
            Self::Neg => "-",
            Self::PreInc => "++",
            Self::PreDec => "--",
            Self::PostInc => "++",
            Self::PostDec => "--",
        }
    }

    /// Check if this is a postfix operator.
    pub fn is_postfix(&self) -> bool {
        matches!(self, Self::PostInc | Self::PostDec)
    }
}

/// A C statement.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum CStmt {
    /// Internal lexical-region marker attached to one exact statement occurrence.
    ///
    /// The marker is transparent to C semantics.  It is minted and sealed by
    /// the control-flow structurer so later lowering phases can recover exact
    /// lexical ancestry without rebuilding it from block addresses.
    #[doc(hidden)]
    #[serde(skip)]
    StructuredRegion {
        marker: crate::structured_region::StructuredRegionMarker,
        stmt: Box<CStmt>,
    },
    /// Internal marker attached to one exact rendered statement occurrence.
    ///
    /// This is transparent to C rendering and must be stripped before a
    /// `CFunction` leaves the decompiler.
    #[doc(hidden)]
    #[serde(skip)]
    Observed {
        id: RenderObservationId,
        stmt: Box<CStmt>,
    },
    /// Empty statement.
    Empty,
    /// Expression statement.
    Expr(CExpr),
    /// Variable declaration.
    Decl {
        ty: CType,
        name: crate::symbol::SymbolId,
        init: Option<CExpr>,
    },
    /// Block of statements.
    Block(Vec<CStmt>),
    /// If statement.
    If {
        cond: CExpr,
        then_body: Box<CStmt>,
        else_body: Option<Box<CStmt>>,
    },
    /// While loop.
    While { cond: CExpr, body: Box<CStmt> },
    /// Do-while loop.
    DoWhile { body: Box<CStmt>, cond: CExpr },
    /// For loop.
    For {
        init: Option<Box<CStmt>>,
        cond: Option<CExpr>,
        update: Option<CExpr>,
        body: Box<CStmt>,
    },
    /// Switch statement.
    Switch {
        expr: CExpr,
        cases: Vec<SwitchCase>,
        default: Option<Vec<CStmt>>,
    },
    /// Return statement.
    Return(Option<CExpr>),
    /// Break statement.
    Break,
    /// Continue statement.
    Continue,
    /// Goto statement.
    Goto(String),
    /// Label.
    Label(String),
    /// Comment.
    Comment(String),
}

/// Ordered observation metadata peeled from the outside of one statement.
///
/// Shape-changing passes may need to inspect or decompose the semantic
/// statement, but the observation IDs still belong to the same source
/// position. This chain is the single owner of that temporary separation: IDs
/// are stored outermost-to-innermost and reapplied in reverse construction
/// order, so neither their nesting order nor their cardinality can drift.
#[derive(Debug, Default)]
pub(crate) struct StmtObservationChain {
    outer_to_inner: Vec<RenderObservationId>,
}

impl StmtObservationChain {
    /// Reattach this chain to the semantic statement at the same position.
    pub(crate) fn reapply(self, mut stmt: CStmt) -> CStmt {
        for id in self.outer_to_inner.into_iter().rev() {
            stmt = CStmt::observed(id, stmt);
        }
        stmt
    }

    /// Reattach this chain when decomposition has one exact surviving statement.
    ///
    /// Returning `false` means the semantic position was deleted or split into
    /// multiple statements, so no single final occurrence owns the IDs.
    /// Callers must leave that coverage unaccounted rather than choosing a
    /// child merely to keep the chain reachable.
    pub(crate) fn reapply_to_unique(self, stmts: &mut [CStmt]) -> bool {
        if stmts.len() != 1 {
            return false;
        }
        let semantic = std::mem::replace(&mut stmts[0], CStmt::Empty);
        stmts[0] = self.reapply(semantic);
        true
    }
}

/// A case in a switch statement.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SwitchCase {
    /// Case value.
    pub value: CExpr,
    /// Case body.
    pub body: Vec<CStmt>,
}

impl CStmt {
    /// Attach an unsealed lexical-region marker to this statement occurrence.
    pub(crate) fn structured_region(
        marker: crate::structured_region::StructuredRegionMarker,
        stmt: CStmt,
    ) -> Self {
        Self::StructuredRegion {
            marker,
            stmt: Box::new(stmt),
        }
    }

    /// Attach an internal observation marker to this exact occurrence.
    pub(crate) fn observed(id: RenderObservationId, stmt: CStmt) -> Self {
        Self::Observed {
            id,
            stmt: Box::new(stmt),
        }
    }

    /// Separate only the leading statement-observation chain from its semantic
    /// node. Nested child observations remain in place.
    pub(crate) fn into_semantic_with_observations(self) -> (Self, StmtObservationChain) {
        let mut semantic = self;
        let mut outer_to_inner = Vec::new();
        loop {
            match semantic {
                Self::Observed { id, stmt } => {
                    outer_to_inner.push(id);
                    semantic = *stmt;
                }
                semantic => {
                    return (semantic, StmtObservationChain { outer_to_inner });
                }
            }
        }
    }

    /// Borrow the semantic statement beneath any internal observation markers.
    pub(crate) fn unobserved(&self) -> &Self {
        let mut stmt = self;
        while let Self::Observed { stmt: inner, .. } = stmt {
            stmt = inner;
        }
        stmt
    }

    /// Mutably borrow the semantic statement beneath leading observation metadata.
    pub(crate) fn unobserved_mut(&mut self) -> &mut Self {
        let mut stmt = self;
        loop {
            match stmt {
                Self::Observed { stmt: inner, .. } => stmt = inner,
                semantic => return semantic,
            }
        }
    }

    /// Clone semantic statement data while omitting every observation wrapper.
    pub(crate) fn clone_without_render_observations(&self) -> Self {
        let mut clone = self.clone();
        strip_stmt_observations(&mut clone);
        clone
    }

    /// Create an expression statement.
    pub fn expr(e: CExpr) -> Self {
        Self::Expr(e)
    }

    /// Create a return statement.
    pub fn ret(value: Option<CExpr>) -> Self {
        Self::Return(value)
    }

    /// Create an if statement.
    pub fn if_stmt(cond: CExpr, then_body: CStmt, else_body: Option<CStmt>) -> Self {
        Self::If {
            cond,
            then_body: Box::new(then_body),
            else_body: else_body.map(Box::new),
        }
    }

    /// Create a while loop.
    pub fn while_loop(cond: CExpr, body: CStmt) -> Self {
        Self::While {
            cond,
            body: Box::new(body),
        }
    }

    /// Create a block.
    pub fn block(stmts: Vec<CStmt>) -> Self {
        Self::Block(stmts)
    }

    /// Create a declaration.
    pub fn decl(ty: CType, name: crate::symbol::SymbolId, init: Option<CExpr>) -> Self {
        Self::Decl { ty, name, init }
    }

    /// Create a comment.
    pub fn comment(text: impl Into<String>) -> Self {
        Self::Comment(text.into())
    }
}

/// A C function definition.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CFunction {
    /// Every name this function declares.
    ///
    /// Owned here because every pass that runs after folding already takes
    /// `&mut CFunction`, so none of them needs the table threaded to it.
    /// The names this function declares, shared with everything that renders
    /// it. Handing a copy over instead would give the renderer identifiers the
    /// copy never issued.
    pub symbols: std::rc::Rc<std::cell::RefCell<crate::symbol::SymbolTable>>,
    /// Function name.
    pub name: String,
    /// Return type.
    pub ret_type: CType,
    /// Parameters.
    pub params: Vec<CParam>,
    /// Local variables.
    pub locals: Vec<CLocal>,
    /// Function body.
    pub body: Vec<CStmt>,
    /// False when the parameter list was never recovered, as opposed to being
    /// recovered and found empty. An empty list prints as `(void)`, which
    /// asserts the function takes no arguments; a function whose interface is
    /// unknown must not make that claim.
    pub params_known: bool,
    /// The functions this one calls, in the order their names sort.
    ///
    /// C requires a declaration before a call, and a decompiled function that
    /// calls another is not readable, compilable or checkable without one.
    /// These are emitted above the definition.
    pub externs: Vec<CExternDecl>,
}

/// A machine symbol spelled as a C identifier.
///
/// radare2 names a symbol `sym._rotl32`, and a decompiler that puts that in its
/// output has written something no C compiler will parse -- it reads as a
/// member access on an undeclared `sym`. The name still has to be recognisable,
/// so every character C does not allow becomes an underscore and nothing else
/// changes.
pub fn c_identifier(name: &str) -> String {
    let mut identifier = String::with_capacity(name.len());
    for character in name.chars() {
        if character.is_ascii_alphanumeric() || character == '_' {
            identifier.push(character);
        } else {
            identifier.push('_');
        }
    }
    if identifier.is_empty() {
        return "_".to_string();
    }
    if identifier.starts_with(|character: char| character.is_ascii_digit()) {
        identifier.insert(0, '_');
    }
    identifier
}

/// A prototype for a function this one calls.
///
/// Only what the call needs to be well formed: the name, what it returns, and
/// the types of the arguments the call passes. Where the callee's interface is
/// not recovered the parameter list is left unspecified rather than asserted
/// empty, for the same reason `params_known` exists.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CExternDecl {
    /// The callee's name, as the call spells it.
    pub name: String,
    /// What the callee returns.
    pub ret_type: CType,
    /// The callee's parameter types, or `None` when they are unknown.
    pub params: Option<Vec<CType>>,
}

/// A function parameter.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CParam {
    /// Parameter type.
    pub ty: CType,
    /// Parameter name.
    pub name: crate::symbol::SymbolId,
}

/// A local variable.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CLocal {
    /// Variable type.
    pub ty: CType,
    /// Variable name.
    pub name: crate::symbol::SymbolId,
    /// Stack offset (if known).
    pub stack_offset: Option<i64>,
}

impl CFunction {
    /// Create a new function.
    pub fn new(name: impl Into<String>, ret_type: CType) -> Self {
        Self {
            symbols: std::rc::Rc::new(std::cell::RefCell::new(crate::symbol::SymbolTable::new())),
            name: name.into(),
            ret_type,
            externs: Vec::new(),
            params: Vec::new(),
            locals: Vec::new(),
            body: Vec::new(),
            params_known: true,
        }
    }

    /// Mark the parameter list as unrecovered, so it is not rendered as a
    /// proven-empty `(void)` list.
    pub fn with_unknown_params(mut self) -> Self {
        self.params_known = false;
        self
    }

    /// Add a parameter.
    pub fn with_param(mut self, ty: CType, name: crate::symbol::SymbolId) -> Self {
        self.params.push(CParam { ty, name });
        self
    }

    /// Set the body.
    pub fn with_body(mut self, body: Vec<CStmt>) -> Self {
        self.body = body;
        self
    }
}

/// Validated reachability for one owner's fixed observation-ID domain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReachableObservations {
    reachable: Vec<bool>,
}

impl ReachableObservations {
    #[cfg(test)]
    pub(crate) fn contains(&self, id: RenderObservationId) -> bool {
        usize::try_from(id.index())
            .ok()
            .and_then(|index| self.reachable.get(index))
            .copied()
            .unwrap_or(false)
    }

    #[cfg(test)]
    pub(crate) fn ids(&self) -> impl Iterator<Item = RenderObservationId> + '_ {
        self.reachable
            .iter()
            .enumerate()
            .filter_map(|(index, reachable)| {
                if *reachable {
                    u32::try_from(index)
                        .ok()
                        .map(crate::observation_journal::test_render_observation_id)
                } else {
                    None
                }
            })
    }
}

/// A marked AST did not belong to the supplied dense observation-ID domain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RenderObservationStripError {
    DomainTooLarge {
        expected_count: usize,
    },
    CapacityUnavailable {
        expected_count: usize,
    },
    OutOfRange {
        id: RenderObservationId,
        expected_count: usize,
    },
    Duplicate {
        id: RenderObservationId,
    },
}

impl std::fmt::Display for RenderObservationStripError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DomainTooLarge { expected_count } => write!(
                f,
                "observation domain of size {expected_count} exceeds the ID space"
            ),
            Self::CapacityUnavailable { expected_count } => {
                write!(
                    f,
                    "cannot allocate observation domain of size {expected_count}"
                )
            }
            Self::OutOfRange { id, expected_count } => write!(
                f,
                "observation {} is outside expected domain 0..{expected_count}",
                id.index()
            ),
            Self::Duplicate { id } => {
                write!(f, "observation {} occurs more than once", id.index())
            }
        }
    }
}

impl std::error::Error for RenderObservationStripError {}

/// Final AST node carried by one validated observation marker.
///
/// The node is borrowed from inside the wrapper, after every render rewrite
/// has completed.  Consumers therefore inspect what survived, rather than
/// treating marker reachability as a proxy for the final disposition.
#[derive(Debug, Clone, Copy)]
pub(crate) enum RenderObservationNode<'a> {
    Expr(&'a CExpr),
    Stmt(&'a CStmt),
}

/// Failure while transactionally inspecting a fixed observation domain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RenderObservationInspectError<E> {
    Markers(RenderObservationStripError),
    Observer(E),
}

fn validate_render_observations(
    function: &CFunction,
    expected_count: usize,
) -> Result<ReachableObservations, RenderObservationStripError> {
    if expected_count > usize::try_from(u32::MAX).unwrap_or(usize::MAX) {
        return Err(RenderObservationStripError::DomainTooLarge { expected_count });
    }
    let mut reachable = Vec::new();
    reachable
        .try_reserve_exact(expected_count)
        .map_err(|_| RenderObservationStripError::CapacityUnavailable { expected_count })?;
    reachable.resize(expected_count, false);
    let mut observations = ReachableObservations { reachable };
    for stmt in &function.body {
        visit_stmt_observations(stmt, &mut |id| observations.record(id))?;
    }
    Ok(observations)
}

/// Whether a function still contains any internal render observation marker.
pub(crate) fn has_render_observations(function: &CFunction) -> bool {
    validate_render_observations(function, 0).is_err()
}

/// Whether one expression subtree contains any render observation marker.
pub(crate) fn expr_has_render_observations(expr: &CExpr) -> bool {
    let mut found = false;
    let never = visit_expr_observations(expr, &mut |_| {
        found = true;
        Ok::<_, std::convert::Infallible>(())
    });
    match never {
        Ok(()) => found,
        Err(never) => match never {},
    }
}

/// Whether one statement subtree contains any render observation marker.
pub(crate) fn stmt_has_render_observations(stmt: &CStmt) -> bool {
    let mut found = false;
    let never = visit_stmt_observations(stmt, &mut |_| {
        found = true;
        Ok::<_, std::convert::Infallible>(())
    });
    match never {
        Ok(()) => found,
        Err(never) => match never {},
    }
}

/// Validate every marker before exposing any final wrapped node to `inspect`.
///
/// Marker-domain errors invoke no callback.  Callers can likewise accumulate
/// observations in temporary storage and commit it only after this function
/// succeeds, making conflict handling transactional as well.
pub(crate) fn inspect_render_observations<E>(
    function: &CFunction,
    expected_count: usize,
    mut inspect: impl FnMut(RenderObservationId, RenderObservationNode<'_>) -> Result<(), E>,
) -> Result<ReachableObservations, RenderObservationInspectError<E>> {
    let observations = validate_render_observations(function, expected_count)
        .map_err(RenderObservationInspectError::Markers)?;
    for stmt in &function.body {
        inspect_stmt_observations(stmt, &mut inspect)
            .map_err(RenderObservationInspectError::Observer)?;
    }
    Ok(observations)
}

/// Transactionally inspect final wrapped nodes and then remove all markers.
///
/// Marker validation and observer callbacks both complete before mutation.
/// On success the already-validated AST is stripped without a redundant
/// validation pass.
#[cfg(test)]
pub(crate) fn inspect_and_strip_render_observations<E>(
    function: &mut CFunction,
    expected_count: usize,
    inspect: impl FnMut(RenderObservationId, RenderObservationNode<'_>) -> Result<(), E>,
) -> Result<ReachableObservations, RenderObservationInspectError<E>> {
    let observations = inspect_render_observations(function, expected_count, inspect)?;
    for stmt in &mut function.body {
        strip_stmt_observations(stmt);
    }
    Ok(observations)
}

/// Validate and remove every internal render observation before a `CFunction`
/// is exposed or serialized.
///
/// Validation is a read-only linear pass over a fixed-size dense bitset. The
/// AST is stripped only after every reachable marker is proven unique and in
/// range, so an error leaves the input unchanged.
#[cfg(test)]
pub(crate) fn strip_render_observations(
    function: &mut CFunction,
    expected_count: usize,
) -> Result<ReachableObservations, RenderObservationStripError> {
    let observations = validate_render_observations(function, expected_count)?;
    for stmt in &mut function.body {
        strip_stmt_observations(stmt);
    }
    Ok(observations)
}

/// Remove every internal observation wrapper after the audit path has failed.
///
/// This deliberately performs no validation: the observation journal owns the
/// authority to report that failure, while native rendering must still emit the
/// same marker-free AST it would have emitted without the shadow audit.
pub(crate) fn discard_render_observations(function: &mut CFunction) {
    for stmt in &mut function.body {
        strip_stmt_observations(stmt);
    }
}

/// Give every marker in a cloned statement tree a fresh occurrence identity.
///
/// A semantic block may be emitted in more than one certified region. Its
/// cached AST is the authoritative fold result, but observation IDs belong to
/// concrete AST occurrences and therefore cannot be copied with that cache.
pub(crate) fn remap_render_observation_ids<E>(
    stmts: &mut [CStmt],
    remap: &mut impl FnMut(RenderObservationId) -> Result<RenderObservationId, E>,
) -> Result<(), E> {
    fn remap_expr<E>(
        expr: &mut CExpr,
        remap: &mut impl FnMut(RenderObservationId) -> Result<RenderObservationId, E>,
    ) -> Result<(), E> {
        if let CExpr::Observed { id, expr } = expr {
            *id = remap(*id)?;
            return remap_expr(expr, remap);
        }
        match expr {
            CExpr::Observed { .. } => unreachable!("handled before semantic expression"),
            CExpr::Unary { operand, .. }
            | CExpr::Cast { expr: operand, .. }
            | CExpr::Sizeof(operand)
            | CExpr::AddrOf(operand)
            | CExpr::Deref(operand)
            | CExpr::Paren(operand) => remap_expr(operand, remap)?,
            CExpr::Binary { left, right, .. } => {
                remap_expr(left, remap)?;
                remap_expr(right, remap)?;
            }
            CExpr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                remap_expr(cond, remap)?;
                remap_expr(then_expr, remap)?;
                remap_expr(else_expr, remap)?;
            }
            CExpr::Call { func, args, .. } => {
                remap_expr(func, remap)?;
                for arg in args {
                    remap_expr(arg, remap)?;
                }
            }
            CExpr::Subscript { base, index } => {
                remap_expr(base, remap)?;
                remap_expr(index, remap)?;
            }
            CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                remap_expr(base, remap)?;
            }
            CExpr::Comma(items) => {
                for item in items {
                    remap_expr(item, remap)?;
                }
            }
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::Var(_)
            | CExpr::External { .. }
            | CExpr::SizeofType(_) => {}
        }
        Ok(())
    }

    fn remap_stmt<E>(
        stmt: &mut CStmt,
        remap: &mut impl FnMut(RenderObservationId) -> Result<RenderObservationId, E>,
    ) -> Result<(), E> {
        if let CStmt::Observed { id, stmt } = stmt {
            *id = remap(*id)?;
            return remap_stmt(stmt, remap);
        }
        match stmt {
            CStmt::StructuredRegion { stmt, .. } => remap_stmt(stmt, remap)?,
            CStmt::Observed { .. } => unreachable!("handled before semantic statement"),
            CStmt::Expr(expr) => remap_expr(expr, remap)?,
            CStmt::Decl { init, .. } | CStmt::Return(init) => {
                if let Some(expr) = init {
                    remap_expr(expr, remap)?;
                }
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    remap_stmt(stmt, remap)?;
                }
            }
            CStmt::If {
                cond,
                then_body,
                else_body,
            } => {
                remap_expr(cond, remap)?;
                remap_stmt(then_body, remap)?;
                if let Some(else_body) = else_body {
                    remap_stmt(else_body, remap)?;
                }
            }
            CStmt::While { cond, body } => {
                remap_expr(cond, remap)?;
                remap_stmt(body, remap)?;
            }
            CStmt::DoWhile { body, cond } => {
                remap_stmt(body, remap)?;
                remap_expr(cond, remap)?;
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                if let Some(init) = init {
                    remap_stmt(init, remap)?;
                }
                if let Some(cond) = cond {
                    remap_expr(cond, remap)?;
                }
                if let Some(update) = update {
                    remap_expr(update, remap)?;
                }
                remap_stmt(body, remap)?;
            }
            CStmt::Switch {
                expr,
                cases,
                default,
            } => {
                remap_expr(expr, remap)?;
                for case in cases {
                    remap_expr(&mut case.value, remap)?;
                    for stmt in &mut case.body {
                        remap_stmt(stmt, remap)?;
                    }
                }
                if let Some(default) = default {
                    for stmt in default {
                        remap_stmt(stmt, remap)?;
                    }
                }
            }
            CStmt::Empty
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Goto(_)
            | CStmt::Label(_)
            | CStmt::Comment(_) => {}
        }
        Ok(())
    }

    for stmt in stmts {
        remap_stmt(stmt, remap)?;
    }
    Ok(())
}

fn inspect_expr_observations<E>(
    expr: &CExpr,
    inspect: &mut impl FnMut(RenderObservationId, RenderObservationNode<'_>) -> Result<(), E>,
) -> Result<(), E> {
    if let CExpr::Observed { id, expr } = expr {
        inspect(*id, RenderObservationNode::Expr(expr))?;
        return inspect_expr_observations(expr, inspect);
    }
    match expr {
        CExpr::Observed { .. } => unreachable!("handled before semantic expression"),
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Sizeof(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Deref(operand)
        | CExpr::Paren(operand) => inspect_expr_observations(operand, inspect)?,
        CExpr::Binary { left, right, .. } => {
            inspect_expr_observations(left, inspect)?;
            inspect_expr_observations(right, inspect)?;
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            inspect_expr_observations(cond, inspect)?;
            inspect_expr_observations(then_expr, inspect)?;
            inspect_expr_observations(else_expr, inspect)?;
        }
        CExpr::Call { func, args, .. } => {
            inspect_expr_observations(func, inspect)?;
            for arg in args {
                inspect_expr_observations(arg, inspect)?;
            }
        }
        CExpr::Subscript { base, index } => {
            inspect_expr_observations(base, inspect)?;
            inspect_expr_observations(index, inspect)?;
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            inspect_expr_observations(base, inspect)?;
        }
        CExpr::Comma(items) => {
            for item in items {
                inspect_expr_observations(item, inspect)?;
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => {}
    }
    Ok(())
}

impl ReachableObservations {
    fn record(&mut self, id: RenderObservationId) -> Result<(), RenderObservationStripError> {
        let Ok(index) = usize::try_from(id.index()) else {
            return Err(RenderObservationStripError::OutOfRange {
                id,
                expected_count: self.reachable.len(),
            });
        };
        let Some(reachable) = self.reachable.get_mut(index) else {
            return Err(RenderObservationStripError::OutOfRange {
                id,
                expected_count: self.reachable.len(),
            });
        };
        if *reachable {
            return Err(RenderObservationStripError::Duplicate { id });
        }
        *reachable = true;
        Ok(())
    }
}

fn visit_expr_observations<E>(
    expr: &CExpr,
    visit: &mut impl FnMut(RenderObservationId) -> Result<(), E>,
) -> Result<(), E> {
    if let CExpr::Observed { id, expr } = expr {
        visit(*id)?;
        return visit_expr_observations(expr, visit);
    }
    match expr {
        CExpr::Observed { .. } => unreachable!("handled before semantic expression"),
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Sizeof(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Deref(operand)
        | CExpr::Paren(operand) => visit_expr_observations(operand, visit)?,
        CExpr::Binary { left, right, .. } => {
            visit_expr_observations(left, visit)?;
            visit_expr_observations(right, visit)?;
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            visit_expr_observations(cond, visit)?;
            visit_expr_observations(then_expr, visit)?;
            visit_expr_observations(else_expr, visit)?;
        }
        CExpr::Call { func, args, .. } => {
            visit_expr_observations(func, visit)?;
            for arg in args {
                visit_expr_observations(arg, visit)?;
            }
        }
        CExpr::Subscript { base, index } => {
            visit_expr_observations(base, visit)?;
            visit_expr_observations(index, visit)?;
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            visit_expr_observations(base, visit)?;
        }
        CExpr::Comma(items) => {
            for item in items {
                visit_expr_observations(item, visit)?;
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => {}
    }
    Ok(())
}

fn strip_expr_observations(expr: &mut CExpr) {
    while let CExpr::Observed { id, expr: inner } = expr {
        let _ = id;
        *expr = std::mem::replace(inner.as_mut(), CExpr::IntLit(0));
    }
    match expr {
        CExpr::Observed { .. } => unreachable!("all leading observations were stripped"),
        CExpr::Unary { operand, .. }
        | CExpr::Cast { expr: operand, .. }
        | CExpr::Sizeof(operand)
        | CExpr::AddrOf(operand)
        | CExpr::Deref(operand)
        | CExpr::Paren(operand) => strip_expr_observations(operand),
        CExpr::Binary { left, right, .. } => {
            strip_expr_observations(left);
            strip_expr_observations(right);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            strip_expr_observations(cond);
            strip_expr_observations(then_expr);
            strip_expr_observations(else_expr);
        }
        CExpr::Call { func, args, .. } => {
            strip_expr_observations(func);
            for arg in args {
                strip_expr_observations(arg);
            }
        }
        CExpr::Subscript { base, index } => {
            strip_expr_observations(base);
            strip_expr_observations(index);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            strip_expr_observations(base);
        }
        CExpr::Comma(items) => {
            for item in items {
                strip_expr_observations(item);
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_)
        | CExpr::External { .. }
        | CExpr::SizeofType(_) => {}
    }
}

fn visit_stmt_observations<E>(
    stmt: &CStmt,
    visit: &mut impl FnMut(RenderObservationId) -> Result<(), E>,
) -> Result<(), E> {
    if let CStmt::Observed { id, stmt } = stmt {
        visit(*id)?;
        return visit_stmt_observations(stmt, visit);
    }
    match stmt {
        CStmt::StructuredRegion { stmt, .. } => visit_stmt_observations(stmt, visit)?,
        CStmt::Observed { .. } => unreachable!("handled before semantic statement"),
        CStmt::Expr(expr) => visit_expr_observations(expr, visit)?,
        CStmt::Decl { init, .. } | CStmt::Return(init) => {
            if let Some(expr) = init {
                visit_expr_observations(expr, visit)?;
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                visit_stmt_observations(stmt, visit)?;
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            visit_expr_observations(cond, visit)?;
            visit_stmt_observations(then_body, visit)?;
            if let Some(else_body) = else_body {
                visit_stmt_observations(else_body, visit)?;
            }
        }
        CStmt::While { cond, body } => {
            visit_expr_observations(cond, visit)?;
            visit_stmt_observations(body, visit)?;
        }
        CStmt::DoWhile { body, cond } => {
            visit_stmt_observations(body, visit)?;
            visit_expr_observations(cond, visit)?;
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                visit_stmt_observations(init, visit)?;
            }
            if let Some(cond) = cond {
                visit_expr_observations(cond, visit)?;
            }
            if let Some(update) = update {
                visit_expr_observations(update, visit)?;
            }
            visit_stmt_observations(body, visit)?;
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            visit_expr_observations(expr, visit)?;
            for case in cases {
                visit_expr_observations(&case.value, visit)?;
                for stmt in &case.body {
                    visit_stmt_observations(stmt, visit)?;
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    visit_stmt_observations(stmt, visit)?;
                }
            }
        }
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
    Ok(())
}

fn inspect_stmt_observations<E>(
    stmt: &CStmt,
    inspect: &mut impl FnMut(RenderObservationId, RenderObservationNode<'_>) -> Result<(), E>,
) -> Result<(), E> {
    if let CStmt::Observed { id, stmt } = stmt {
        inspect(*id, RenderObservationNode::Stmt(stmt))?;
        return inspect_stmt_observations(stmt, inspect);
    }
    match stmt {
        CStmt::StructuredRegion { stmt, .. } => inspect_stmt_observations(stmt, inspect)?,
        CStmt::Observed { .. } => unreachable!("handled before semantic statement"),
        CStmt::Expr(expr) => inspect_expr_observations(expr, inspect)?,
        CStmt::Decl { init, .. } | CStmt::Return(init) => {
            if let Some(expr) = init {
                inspect_expr_observations(expr, inspect)?;
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                inspect_stmt_observations(stmt, inspect)?;
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            inspect_expr_observations(cond, inspect)?;
            inspect_stmt_observations(then_body, inspect)?;
            if let Some(else_body) = else_body {
                inspect_stmt_observations(else_body, inspect)?;
            }
        }
        CStmt::While { cond, body } => {
            inspect_expr_observations(cond, inspect)?;
            inspect_stmt_observations(body, inspect)?;
        }
        CStmt::DoWhile { body, cond } => {
            inspect_stmt_observations(body, inspect)?;
            inspect_expr_observations(cond, inspect)?;
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                inspect_stmt_observations(init, inspect)?;
            }
            if let Some(cond) = cond {
                inspect_expr_observations(cond, inspect)?;
            }
            if let Some(update) = update {
                inspect_expr_observations(update, inspect)?;
            }
            inspect_stmt_observations(body, inspect)?;
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            inspect_expr_observations(expr, inspect)?;
            for case in cases {
                inspect_expr_observations(&case.value, inspect)?;
                for stmt in &case.body {
                    inspect_stmt_observations(stmt, inspect)?;
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    inspect_stmt_observations(stmt, inspect)?;
                }
            }
        }
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
    Ok(())
}

/// Move only a source expression's leading observation wrappers onto a
/// replacement for that same occurrence.
pub(crate) fn carry_outer_expr_observations(source: &CExpr, mut replacement: CExpr) -> CExpr {
    let mut ids = Vec::new();
    let mut source = source;
    while let CExpr::Observed { id, expr } = source {
        ids.push(*id);
        source = expr;
    }
    for id in ids.into_iter().rev() {
        replacement = CExpr::observed(id, replacement);
    }
    replacement
}

fn strip_stmt_observations(stmt: &mut CStmt) {
    while let CStmt::Observed { id, stmt: inner } = stmt {
        let _ = id;
        *stmt = std::mem::replace(inner.as_mut(), CStmt::Empty);
    }
    match stmt {
        CStmt::StructuredRegion { stmt, .. } => strip_stmt_observations(stmt),
        CStmt::Observed { .. } => unreachable!("all leading observations were stripped"),
        CStmt::Expr(expr) => strip_expr_observations(expr),
        CStmt::Decl { init, .. } | CStmt::Return(init) => {
            if let Some(expr) = init {
                strip_expr_observations(expr);
            }
        }
        CStmt::Block(stmts) => {
            for stmt in stmts {
                strip_stmt_observations(stmt);
            }
        }
        CStmt::If {
            cond,
            then_body,
            else_body,
        } => {
            strip_expr_observations(cond);
            strip_stmt_observations(then_body);
            if let Some(else_body) = else_body {
                strip_stmt_observations(else_body);
            }
        }
        CStmt::While { cond, body } => {
            strip_expr_observations(cond);
            strip_stmt_observations(body);
        }
        CStmt::DoWhile { body, cond } => {
            strip_stmt_observations(body);
            strip_expr_observations(cond);
        }
        CStmt::For {
            init,
            cond,
            update,
            body,
        } => {
            if let Some(init) = init {
                strip_stmt_observations(init);
            }
            if let Some(cond) = cond {
                strip_expr_observations(cond);
            }
            if let Some(update) = update {
                strip_expr_observations(update);
            }
            strip_stmt_observations(body);
        }
        CStmt::Switch {
            expr,
            cases,
            default,
        } => {
            strip_expr_observations(expr);
            for case in cases {
                strip_expr_observations(&mut case.value);
                for stmt in &mut case.body {
                    strip_stmt_observations(stmt);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    strip_stmt_observations(stmt);
                }
            }
        }
        CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    #[test]
    fn test_type_display() {
        assert_eq!(CType::Void.to_string(), "void");
        assert_eq!(CType::i32().to_string(), "int32_t");
        assert_eq!(CType::u64().to_string(), "uint64_t");
        assert_eq!(CType::ptr(CType::i32()).to_string(), "int32_t*");
    }

    #[test]
    fn test_expr_creation() {
        let symbols = test_table();
        let a = CExpr::var(crate::symbol::declare(&symbols, "a"));
        let b = CExpr::var(crate::symbol::declare(&symbols, "b"));
        let sum = CExpr::binary(BinaryOp::Add, a, b);

        if let CExpr::Binary { op, left, right } = sum {
            assert_eq!(op, BinaryOp::Add);
            assert_eq!(*left, CExpr::var(crate::symbol::declare(&symbols, "a")));
            assert_eq!(*right, CExpr::var(crate::symbol::declare(&symbols, "b")));
        } else {
            panic!("Expected Binary expression");
        }
    }

    #[test]
    fn test_stmt_creation() {
        let symbols = test_table();
        let stmt = CStmt::if_stmt(
            CExpr::var(crate::symbol::declare(&symbols, "x")),
            CStmt::ret(Some(CExpr::int(1))),
            Some(CStmt::ret(Some(CExpr::int(0)))),
        );

        if let CStmt::If {
            cond,
            then_body: _,
            else_body,
        } = stmt
        {
            assert_eq!(cond, CExpr::var(crate::symbol::declare(&symbols, "x")));
            assert!(else_body.is_some());
        } else {
            panic!("Expected If statement");
        }
    }

    #[test]
    fn test_expr_visit_traverses_all_nodes() {
        let symbols = test_table();
        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::var(crate::symbol::declare(&symbols, "a")),
            CExpr::call(
                CExpr::var(crate::symbol::declare(&symbols, "f")),
                vec![
                    CExpr::int(1),
                    CExpr::var(crate::symbol::declare(&symbols, "b")),
                ],
            ),
        );
        let mut vars = Vec::new();
        expr.visit(&mut |node| {
            if let CExpr::Var(name) = node {
                vars.push(*name);
            }
        });
        assert!(vars.iter().any(|v| symbols.borrow().name(*v) == "a"));
        assert!(vars.iter().any(|v| symbols.borrow().name(*v) == "f"));
        assert!(vars.iter().any(|v| symbols.borrow().name(*v) == "b"));
    }

    #[test]
    fn test_expr_map_children_updates_direct_children() {
        let symbols = test_table();
        let expr = CExpr::binary(
            BinaryOp::Add,
            CExpr::var(crate::symbol::declare(&symbols, "a")),
            CExpr::int(1),
        );
        let mut mapper = |child: CExpr| match child {
            CExpr::Var(name) if name == crate::symbol::declare(&symbols, "a") => {
                CExpr::var(crate::symbol::declare(&symbols, "x"))
            }
            other => other,
        };
        let rewritten = expr.map_children(&mut mapper);
        let CExpr::Binary { left, .. } = rewritten else {
            panic!("expected binary expression");
        };
        assert_eq!(*left, CExpr::var(crate::symbol::declare(&symbols, "x")));
    }

    #[test]
    fn observations_survive_recursive_expression_rewrites() {
        fn rewrite(expr: CExpr) -> CExpr {
            let expr = expr.map_children(&mut rewrite);
            match expr {
                CExpr::IntLit(1) => CExpr::IntLit(2),
                other => other,
            }
        }

        let mut owner = RenderObservationOwner::new();
        let (id, observed_one) = owner
            .observe_expr(CExpr::IntLit(1))
            .expect("allocate observation");
        let rewritten = rewrite(CExpr::binary(BinaryOp::Add, observed_one, CExpr::IntLit(1)));
        assert_eq!(
            rewritten,
            CExpr::binary(
                BinaryOp::Add,
                CExpr::observed(id, CExpr::IntLit(2)),
                CExpr::IntLit(2),
            )
        );
    }

    #[test]
    fn statement_observation_chain_round_trips_in_nesting_order_once() {
        let semantic = CStmt::Expr(CExpr::IntLit(7));
        let mut owner = RenderObservationOwner::new();
        let (inner_id, inner) = owner
            .observe_stmt(semantic.clone())
            .expect("inner statement observation");
        let (outer_id, wrapped) = owner
            .observe_stmt(inner)
            .expect("outer statement observation");

        let (peeled, observations) = wrapped.clone().into_semantic_with_observations();
        assert_eq!(peeled, semantic);
        let rebuilt = observations.reapply(peeled);
        assert_eq!(rebuilt, wrapped, "outer and inner IDs must not reorder");

        let mut function = CFunction::new("stmt_chain", CType::Void).with_body(vec![rebuilt]);
        let reachable = strip_render_observations(&mut function, owner.expected_count())
            .expect("recomposition must retain every ID exactly once");
        assert!(reachable.contains(inner_id));
        assert!(reachable.contains(outer_id));
        assert_eq!(function.body, vec![semantic]);
    }

    #[test]
    fn final_node_inspection_visits_subscript_markers_once() {
        let mut owner = RenderObservationOwner::new();
        let (base_id, base) = owner
            .observe_expr(CExpr::IntLit(1))
            .expect("base observation");
        let (index_id, index) = owner
            .observe_expr(CExpr::IntLit(2))
            .expect("index observation");
        let function =
            CFunction::new("inspect", CType::Void).with_body(vec![CStmt::Expr(CExpr::Subscript {
                base: Box::new(base),
                index: Box::new(index),
            })]);
        let mut visited = Vec::new();
        inspect_render_observations(
            &function,
            owner.expected_count(),
            |id, node| -> Result<(), std::convert::Infallible> {
                assert!(matches!(
                    node,
                    RenderObservationNode::Expr(CExpr::IntLit(_))
                ));
                visited.push(id);
                Ok(())
            },
        )
        .expect("valid marker inspection");
        assert_eq!(visited, vec![base_id, index_id]);
    }

    #[test]
    fn semantic_clones_drop_occurrence_owned_observations() {
        let mut owner = RenderObservationOwner::new();
        let (_, left) = owner
            .observe_expr(CExpr::IntLit(1))
            .expect("left observation");
        let (_, right) = owner
            .observe_expr(CExpr::IntLit(2))
            .expect("right observation");
        let source = CExpr::binary(BinaryOp::Add, left, right);
        assert_eq!(
            source.clone_without_render_observations(),
            CExpr::binary(BinaryOp::Add, CExpr::IntLit(1), CExpr::IntLit(2))
        );
        let mut function =
            CFunction::new("fold", CType::Void).with_body(vec![CStmt::Expr(CExpr::IntLit(3))]);
        let reachable = strip_render_observations(&mut function, owner.expected_count())
            .expect("eliminated observations remain unaccounted");
        assert_eq!(reachable.ids().count(), 0);
        assert_eq!(function.body, vec![CStmt::Expr(CExpr::IntLit(3))]);
    }

    #[test]
    fn stripping_reports_only_reachable_observations_and_restores_the_ast() {
        let mut plain = CFunction::new(
            "observed",
            CType::Int {
                bits: 32,
                signedness: r2types::Signedness::Signed,
            },
        )
        .with_body(vec![CStmt::Block(vec![CStmt::Expr(CExpr::binary(
            BinaryOp::Add,
            CExpr::IntLit(1),
            CExpr::IntLit(2),
        ))])]);
        let expected = plain.clone();
        let mut owner = RenderObservationOwner::new();
        let (nested_expr_id, nested_expr) = owner
            .observe_expr(CExpr::IntLit(1))
            .expect("allocate nested expression observation");
        let (expr_id, expr) = owner
            .observe_expr(CExpr::binary(BinaryOp::Add, nested_expr, CExpr::IntLit(2)))
            .expect("allocate expression observation");
        let (stmt_id, stmt) = owner
            .observe_stmt(CStmt::Block(vec![CStmt::Expr(expr)]))
            .expect("allocate statement observation");
        let (dropped_id, dropped_stmt) = owner
            .observe_stmt(CStmt::Expr(CExpr::IntLit(99)))
            .expect("allocate dropped observation");
        plain.body = vec![stmt, dropped_stmt];

        plain.body.pop();
        let reachable = strip_render_observations(&mut plain, owner.expected_count())
            .expect("valid observation domain");

        assert_eq!(
            reachable.ids().collect::<Vec<_>>(),
            vec![nested_expr_id, expr_id, stmt_id],
            "dense-ID order is independent of AST traversal order"
        );
        assert!(!reachable.contains(dropped_id));
        assert_eq!(plain, expected);
        assert_eq!(expr_id.index(), 1);
    }

    #[test]
    fn observations_are_rejected_by_serde_until_the_boundary_strips_them() {
        let mut owner = RenderObservationOwner::new();
        let (id, stmt) = owner
            .observe_stmt(CStmt::Expr(CExpr::IntLit(1)))
            .expect("allocate observation");
        let mut function = CFunction::new("observed", CType::Void).with_body(vec![stmt]);

        assert!(serde_json::to_string(&function).is_err());
        assert!(
            serde_json::from_str::<CStmt>(r#"{"Observed":{"id":0,"stmt":{"Expr":{"IntLit":1}}}}"#,)
                .is_err()
        );

        let reachable = strip_render_observations(&mut function, owner.expected_count())
            .expect("valid observation domain");
        assert_eq!(reachable.ids().collect::<Vec<_>>(), vec![id]);
        let stripped = serde_json::to_string(&function).expect("serialize stripped AST");
        assert!(!stripped.contains("Observed"));
    }

    #[test]
    fn stripping_rejects_duplicate_and_out_of_range_observations_without_mutation() {
        let duplicate = RenderObservationId::from_index(0);
        let mut duplicate_function =
            CFunction::new("duplicate", CType::Void).with_body(vec![CStmt::observed(
                duplicate,
                CStmt::Expr(CExpr::observed(duplicate, CExpr::IntLit(1))),
            )]);
        let duplicate_before = duplicate_function.clone();
        assert_eq!(
            strip_render_observations(&mut duplicate_function, 1),
            Err(RenderObservationStripError::Duplicate { id: duplicate })
        );
        assert_eq!(duplicate_function, duplicate_before);

        let out_of_range = RenderObservationId::from_index(1);
        let mut out_of_range_function = CFunction::new("range", CType::Void)
            .with_body(vec![CStmt::observed(out_of_range, CStmt::Empty)]);
        let out_of_range_before = out_of_range_function.clone();
        assert_eq!(
            strip_render_observations(&mut out_of_range_function, 1),
            Err(RenderObservationStripError::OutOfRange {
                id: out_of_range,
                expected_count: 1,
            })
        );
        assert_eq!(out_of_range_function, out_of_range_before);

        #[cfg(target_pointer_width = "64")]
        {
            let mut empty = CFunction::new("large", CType::Void);
            let expected_count = usize::try_from(u64::from(u32::MAX) + 1).unwrap();
            assert_eq!(
                strip_render_observations(&mut empty, expected_count),
                Err(RenderObservationStripError::DomainTooLarge { expected_count })
            );
        }
    }

    #[test]
    fn transparent_equality_ignores_nested_observations() {
        let mut owner = RenderObservationOwner::new();
        let (_, nested) = owner
            .observe_expr(CExpr::IntLit(1))
            .expect("allocate nested observation");
        let plain = CExpr::binary(BinaryOp::Add, CExpr::IntLit(1), CExpr::IntLit(2));
        let wrapped = CExpr::binary(BinaryOp::Add, nested, CExpr::IntLit(2));
        assert!(plain.transparently_eq(&wrapped));
        assert!(wrapped.transparently_eq(&plain));
    }
}
