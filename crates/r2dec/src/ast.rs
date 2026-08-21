//! C Abstract Syntax Tree representation.
//!
//! This module defines the AST types used to represent decompiled C code.

use serde::{Deserialize, Serialize};

/// A C type.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CType {
    /// Void type.
    Void,
    /// Boolean type.
    Bool,
    /// Signed integer with bit width.
    Int(u32),
    /// Unsigned integer with bit width.
    UInt(u32),
    /// Floating point with bit width.
    Float(u32),
    /// Pointer to another type.
    Pointer(Box<CType>),
    /// Array of elements.
    Array(Box<CType>, Option<usize>),
    /// Function type.
    Function { ret: Box<CType>, params: Vec<CType> },
    /// Struct type.
    Struct(String),
    /// Union type.
    Union(String),
    /// Enum type.
    Enum(String),
    /// Typedef alias.
    Typedef(String),
    /// Unknown type (will be rendered as a comment).
    Unknown,
}

impl CType {
    /// Create an 8-bit signed integer type.
    pub fn i8() -> Self {
        Self::Int(8)
    }

    /// Create a 16-bit signed integer type.
    pub fn i16() -> Self {
        Self::Int(16)
    }

    /// Create a 32-bit signed integer type.
    pub fn i32() -> Self {
        Self::Int(32)
    }

    /// Create a 64-bit signed integer type.
    pub fn i64() -> Self {
        Self::Int(64)
    }

    /// Create an 8-bit unsigned integer type.
    pub fn u8() -> Self {
        Self::UInt(8)
    }

    /// Create a 16-bit unsigned integer type.
    pub fn u16() -> Self {
        Self::UInt(16)
    }

    /// Create a 32-bit unsigned integer type.
    pub fn u32() -> Self {
        Self::UInt(32)
    }

    /// Create a 64-bit unsigned integer type.
    pub fn u64() -> Self {
        Self::UInt(64)
    }

    /// Create a pointer type.
    pub fn ptr(inner: CType) -> Self {
        Self::Pointer(Box::new(inner))
    }

    /// Create a void pointer type.
    pub fn void_ptr() -> Self {
        Self::ptr(Self::Void)
    }

    /// Get the size in bits (if known).
    pub fn bits(&self) -> Option<u32> {
        match self {
            Self::Bool => Some(1),
            Self::Int(bits) | Self::UInt(bits) | Self::Float(bits) => Some(*bits),
            Self::Pointer(_) => Some(64), // Assume 64-bit pointers
            _ => None,
        }
    }

    /// Check if this is a signed type.
    pub fn is_signed(&self) -> bool {
        matches!(self, Self::Int(_))
    }

    /// Check if this is an integer type.
    pub fn is_integer(&self) -> bool {
        matches!(self, Self::Int(_) | Self::UInt(_) | Self::Bool)
    }

    /// Check if this is a pointer type.
    pub fn is_pointer(&self) -> bool {
        matches!(self, Self::Pointer(_))
    }
}

impl std::fmt::Display for CType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Void => write!(f, "void"),
            Self::Bool => write!(f, "bool"),
            Self::Int(8) => write!(f, "int8_t"),
            Self::Int(16) => write!(f, "int16_t"),
            Self::Int(32) => write!(f, "int32_t"),
            Self::Int(64) => write!(f, "int64_t"),
            Self::Int(bits) => write!(f, "int{}_t", bits),
            Self::UInt(8) => write!(f, "uint8_t"),
            Self::UInt(16) => write!(f, "uint16_t"),
            Self::UInt(32) => write!(f, "uint32_t"),
            Self::UInt(64) => write!(f, "uint64_t"),
            Self::UInt(bits) => write!(f, "uint{}_t", bits),
            Self::Float(32) => write!(f, "float"),
            Self::Float(64) => write!(f, "double"),
            Self::Float(bits) => write!(f, "float{}", bits),
            Self::Pointer(inner) => write!(f, "{}*", inner),
            Self::Array(inner, Some(size)) => write!(f, "{}[{}]", inner, size),
            Self::Array(inner, None) => write!(f, "{}[]", inner),
            Self::Function { ret, params } => {
                write!(f, "{}(*)(", ret)?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ")")
            }
            Self::Struct(name) => write!(f, "struct {}", name),
            Self::Union(name) => write!(f, "union {}", name),
            Self::Enum(name) => write!(f, "enum {}", name),
            Self::Typedef(name) => write!(f, "{}", name),
            Self::Unknown => write!(f, "/* unknown */"),
        }
    }
}

/// A C expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum CExpr {
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
    Call { func: Box<CExpr>, args: Vec<CExpr> },
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
            Self::Call { func, args } => Self::Call {
                func: Box::new(f(*func)),
                args: args.into_iter().map(f).collect(),
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
            Self::Call { func, args } => {
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
        }
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

/// A case in a switch statement.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SwitchCase {
    /// Case value.
    pub value: CExpr,
    /// Case body.
    pub body: Vec<CStmt>,
}

impl CStmt {
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
    pub symbols: std::cell::RefCell<crate::symbol::SymbolTable>,
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
            symbols: std::cell::RefCell::new(crate::symbol::SymbolTable::new()),
            name: name.into(),
            ret_type,
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
        let a = CExpr::var(symbols.borrow_mut().declare_or_reuse("a"));
        let b = CExpr::var(symbols.borrow_mut().declare_or_reuse("b"));
        let sum = CExpr::binary(BinaryOp::Add, a, b);

        if let CExpr::Binary { op, left, right } = sum {
            assert_eq!(op, BinaryOp::Add);
            assert_eq!(*left, CExpr::var(symbols.borrow_mut().declare_or_reuse("a")));
            assert_eq!(*right, CExpr::var(symbols.borrow_mut().declare_or_reuse("b")));
        } else {
            panic!("Expected Binary expression");
        }
    }

    #[test]
    fn test_stmt_creation() {
        let symbols = test_table();
        let stmt = CStmt::if_stmt(
            CExpr::var(symbols.borrow_mut().declare_or_reuse("x")),
            CStmt::ret(Some(CExpr::int(1))),
            Some(CStmt::ret(Some(CExpr::int(0)))),
        );

        if let CStmt::If {
            cond,
            then_body: _,
            else_body,
        } = stmt
        {
            assert_eq!(cond, CExpr::var(symbols.borrow_mut().declare_or_reuse("x")));
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
            CExpr::var(symbols.borrow_mut().declare_or_reuse("a")),
            CExpr::call(CExpr::var(symbols.borrow_mut().declare_or_reuse("f")), vec![CExpr::int(1), CExpr::var(symbols.borrow_mut().declare_or_reuse("b"))]),
        );
        let mut vars = Vec::new();
        expr.visit(&mut |node| {
            if let CExpr::Var(name) = node {
                vars.push(name.clone());
            }
        });
        assert!(vars.iter().any(|v| &*symbols.borrow().name(*v) == "a"));
        assert!(vars.iter().any(|v| &*symbols.borrow().name(*v) == "f"));
        assert!(vars.iter().any(|v| &*symbols.borrow().name(*v) == "b"));
    }

    #[test]
    fn test_expr_map_children_updates_direct_children() {
        let symbols = test_table();
        let expr = CExpr::binary(BinaryOp::Add, CExpr::var(symbols.borrow_mut().declare_or_reuse("a")), CExpr::int(1));
        let mut mapper = |child: CExpr| match child {
            CExpr::Var(name) if name == symbols.borrow_mut().declare_or_reuse("a") => CExpr::var(symbols.borrow_mut().declare_or_reuse("x")),
            other => other,
        };
        let rewritten = expr.map_children(&mut mapper);
        let CExpr::Binary { left, .. } = rewritten else {
            panic!("expected binary expression");
        };
        assert_eq!(*left, CExpr::var(symbols.borrow_mut().declare_or_reuse("x")));
    }
}
