//! Hash-consed terms over the machine expression arena.
//!
//! A term is a node of a second arena that `r2rewrite` owns. Its leaves point
//! at nodes of the base [`r2ssa::MachineExprArena`], which is never mutated:
//! the base arena is validated structurally against the SSA graph, and a
//! rewritten root would break that validation. Equal terms share one id, so
//! structural equality is id equality and every rule that asks "are these the
//! same operand" asks it exactly.

use std::collections::HashMap;

use r2ssa::{
    MachineArithmeticFlagOp, MachineArithmeticOp, MachineBitVector, MachineBitwiseOp,
    MachineBooleanOp, MachineCastKind, MachineComparisonOp, MachineExprId,
    MachineOvershiftBehavior, MachineShiftKind, MachineSignedness, MachineType,
};
use serde::Serialize;

/// Handle into a [`TermArena`]. Ids are issued in creation order and a term's
/// children always have smaller ids than the term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct TermId(u32);

impl TermId {
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) const fn from_index(index: usize) -> Self {
        Self(index as u32)
    }
}

/// The widest term the rewriter models. Wider machine nodes stay opaque.
pub const MAX_TERM_WIDTH_BITS: u32 = MachineBitVector::MAX_LITERAL_BITS;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum TermKind {
    /// A read of one prepared value: a `Source` or `Constant` node of the base
    /// arena, rendered by the binding plan's answer for that value.
    Leaf(MachineExprId),
    /// An instruction root the rewriter does not model -- a memory read, a
    /// merge, a division, a population count, checked arithmetic, or anything
    /// wider than [`MAX_TERM_WIDTH_BITS`] -- rendered by the base path.
    Opaque(MachineExprId),
    /// A constant the rewriter introduced or folded; it names no value.
    Literal(MachineBitVector),
    Arithmetic {
        op: MachineArithmeticOp,
        left: TermId,
        right: TermId,
    },
    Negate(TermId),
    Bitwise {
        op: MachineBitwiseOp,
        left: TermId,
        right: TermId,
    },
    BitwiseNot(TermId),
    Boolean {
        op: MachineBooleanOp,
        left: TermId,
        right: TermId,
    },
    BooleanNot(TermId),
    Shift {
        kind: MachineShiftKind,
        overshift: MachineOvershiftBehavior,
        value: TermId,
        count: TermId,
    },
    Compare {
        op: MachineComparisonOp,
        interpretation: MachineSignedness,
        left: TermId,
        right: TermId,
    },
    Flag {
        op: MachineArithmeticFlagOp,
        left: TermId,
        right: TermId,
    },
    Cast {
        kind: MachineCastKind,
        input: TermId,
    },
    Extract {
        input: TermId,
        lsb_bits: u32,
    },
    Concat {
        high: TermId,
        low: TermId,
    },
    Select {
        condition: TermId,
        if_true: TermId,
        if_false: TermId,
    },
}

/// The children of one term, in operand order.
#[derive(Debug, Clone, Copy)]
pub struct Children {
    items: [TermId; 3],
    len: u8,
    next: u8,
}

impl Iterator for Children {
    type Item = TermId;

    fn next(&mut self) -> Option<TermId> {
        if self.next >= self.len {
            return None;
        }
        let item = self.items[self.next as usize];
        self.next += 1;
        Some(item)
    }
}

impl TermKind {
    pub fn children(&self) -> Children {
        let placeholder = TermId(0);
        let (items, len) = match *self {
            Self::Leaf(_) | Self::Opaque(_) | Self::Literal(_) => {
                ([placeholder, placeholder, placeholder], 0)
            }
            Self::Negate(input)
            | Self::BitwiseNot(input)
            | Self::BooleanNot(input)
            | Self::Cast { input, .. }
            | Self::Extract { input, .. } => ([input, placeholder, placeholder], 1),
            Self::Arithmetic { left, right, .. }
            | Self::Bitwise { left, right, .. }
            | Self::Boolean { left, right, .. }
            | Self::Compare { left, right, .. }
            | Self::Flag { left, right, .. } => ([left, right, placeholder], 2),
            Self::Shift { value, count, .. } => ([value, count, placeholder], 2),
            Self::Concat { high, low } => ([high, low, placeholder], 2),
            Self::Select {
                condition,
                if_true,
                if_false,
            } => ([condition, if_true, if_false], 3),
        };
        Children {
            items,
            len,
            next: 0,
        }
    }

    /// Whether this term has no children.
    pub const fn is_nullary(&self) -> bool {
        matches!(self, Self::Leaf(_) | Self::Opaque(_) | Self::Literal(_))
    }

    /// Rebuild this term over new children, given in operand order.
    pub fn with_children(&self, new: &[TermId]) -> Self {
        match *self {
            Self::Leaf(_) | Self::Opaque(_) | Self::Literal(_) => *self,
            Self::Negate(_) => Self::Negate(new[0]),
            Self::BitwiseNot(_) => Self::BitwiseNot(new[0]),
            Self::BooleanNot(_) => Self::BooleanNot(new[0]),
            Self::Cast { kind, .. } => Self::Cast {
                kind,
                input: new[0],
            },
            Self::Extract { lsb_bits, .. } => Self::Extract {
                input: new[0],
                lsb_bits,
            },
            Self::Arithmetic { op, .. } => Self::Arithmetic {
                op,
                left: new[0],
                right: new[1],
            },
            Self::Bitwise { op, .. } => Self::Bitwise {
                op,
                left: new[0],
                right: new[1],
            },
            Self::Boolean { op, .. } => Self::Boolean {
                op,
                left: new[0],
                right: new[1],
            },
            Self::Compare {
                op, interpretation, ..
            } => Self::Compare {
                op,
                interpretation,
                left: new[0],
                right: new[1],
            },
            Self::Flag { op, .. } => Self::Flag {
                op,
                left: new[0],
                right: new[1],
            },
            Self::Shift {
                kind, overshift, ..
            } => Self::Shift {
                kind,
                overshift,
                value: new[0],
                count: new[1],
            },
            Self::Concat { .. } => Self::Concat {
                high: new[0],
                low: new[1],
            },
            Self::Select { .. } => Self::Select {
                condition: new[0],
                if_true: new[1],
                if_false: new[2],
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub struct Term {
    pub ty: MachineType,
    pub kind: TermKind,
}

impl Term {
    pub const fn width_bits(&self) -> u32 {
        self.ty.width_bits()
    }

    pub const fn is_bool(&self) -> bool {
        matches!(self.ty, MachineType::Bool { .. })
    }
}

/// Owner of every term for one function. Equal terms intern to one id; the
/// intern map is looked up and never iterated, so nothing observable depends
/// on hash order.
#[derive(Debug, Clone, Default)]
pub struct TermArena {
    nodes: Vec<Term>,
    interned: HashMap<Term, TermId>,
}

impl TermArena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, ty: MachineType, kind: TermKind) -> TermId {
        let term = Term { ty, kind };
        if let Some(id) = self.interned.get(&term) {
            return *id;
        }
        let id = TermId(self.nodes.len() as u32);
        self.nodes.push(term);
        self.interned.insert(term, id);
        id
    }

    pub fn term(&self, id: TermId) -> Term {
        self.nodes[id.index()]
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = (TermId, Term)> + '_ {
        self.nodes
            .iter()
            .enumerate()
            .map(|(index, term)| (TermId(index as u32), *term))
    }

    /// Every base-arena node this term reads, each once, in first-visit order.
    /// Covers both `Leaf` and `Opaque` terms.
    pub fn leaves(&self, root: TermId) -> Vec<MachineExprId> {
        let mut out = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            match self.term(id).kind {
                TermKind::Leaf(expr) | TermKind::Opaque(expr) => {
                    if !out.contains(&expr) {
                        out.push(expr);
                    }
                }
                kind => {
                    let children: Vec<TermId> = kind.children().collect();
                    stack.extend(children.into_iter().rev());
                }
            }
        }
        out
    }

    /// Whether `needle` occurs anywhere in the term rooted at `root`.
    pub fn contains(&self, root: TermId, needle: TermId) -> bool {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if id == needle {
                return true;
            }
            if !seen.insert(id) {
                continue;
            }
            stack.extend(self.term(id).kind.children());
        }
        false
    }

    /// The size of the term as a tree, counting shared subterms once per
    /// occurrence. Saturates rather than overflows. Every rule strictly
    /// decreases this for the term it rewrites, so it bounds how often rules
    /// can fire at one node; the driver derives its budget from it.
    pub fn tree_measure(&self, root: TermId) -> u64 {
        let mut memo: HashMap<TermId, u64> = HashMap::new();
        self.tree_measure_memo(root, &mut memo)
    }

    fn tree_measure_memo(&self, id: TermId, memo: &mut HashMap<TermId, u64>) -> u64 {
        if let Some(size) = memo.get(&id) {
            return *size;
        }
        let kind = self.term(id).kind;
        let size = if kind.is_nullary() {
            1
        } else {
            kind.children().fold(1u64, |acc, child| {
                acc.saturating_add(self.tree_measure_memo(child, memo))
            })
        };
        memo.insert(id, size);
        size
    }
}
