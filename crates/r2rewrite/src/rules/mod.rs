//! The rule table.
//!
//! A rule is a proven equivalence: `apply` rewrites a term whose shape it
//! recognises into an equal term with a strictly smaller measure, and the
//! proof test (`tests/rule_proofs.rs`) builds every template the rule lists,
//! checks that the rule fires on it, that the declared measure component
//! drops, and that the two sides are equal for every input at every proof
//! width. A rule that is not in [`RULES`] never fires; a rule in [`RULES`]
//! without a template fails the suite. The table is the catalogue.

use serde::Serialize;

use crate::term::{TermArena, TermId, TermKind};

/// Stable name of one rule, used in rewrite records and test names.
pub type RuleId = &'static str;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum RuleGroup {
    /// Folding over literals.
    Literal,
    /// Identities and absorption.
    Identity,
    /// Casts and slices.
    Cast,
    /// Boolean and comparison normal form.
    Boolean,
    /// Flag arithmetic to comparison.
    Flag,
    /// Shifts.
    Shift,
    /// Affine normal form lemmas.
    Affine,
    /// Masks.
    Mask,
}

/// The component of the termination measure a rule strictly decreases.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum Measure {
    /// Non-leaf nodes of the term, counted as a tree.
    NonLeafNodes,
    /// Sum of the widths of every cast and extract in the term.
    CastWidth,
    /// Commutative nodes whose literal operand is not the last one.
    LiteralPosition,
}

/// Lexicographic measure of a term as a tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct MeasureVector {
    pub non_leaf_nodes: u64,
    pub cast_width: u64,
    pub literals_not_last: u64,
}

impl MeasureVector {
    pub fn component(&self, measure: Measure) -> u64 {
        match measure {
            Measure::NonLeafNodes => self.non_leaf_nodes,
            Measure::CastWidth => self.cast_width,
            Measure::LiteralPosition => self.literals_not_last,
        }
    }
}

pub fn measure(arena: &TermArena, root: TermId) -> MeasureVector {
    let mut memo = std::collections::HashMap::new();
    measure_memo(arena, root, &mut memo)
}

fn measure_memo(
    arena: &TermArena,
    id: TermId,
    memo: &mut std::collections::HashMap<TermId, MeasureVector>,
) -> MeasureVector {
    if let Some(m) = memo.get(&id) {
        return *m;
    }
    let term = arena.term(id);
    let mut m = MeasureVector {
        non_leaf_nodes: 0,
        cast_width: 0,
        literals_not_last: 0,
    };
    if !term.kind.is_nullary() {
        m.non_leaf_nodes = 1;
        if matches!(term.kind, TermKind::Cast { .. } | TermKind::Extract { .. }) {
            m.cast_width = u64::from(term.width_bits());
        }
        let children: Vec<TermId> = term.kind.children().collect();
        if children.len() >= 2
            && crate::canon::is_commutative(&term.kind)
            && matches!(arena.term(children[0]).kind, TermKind::Literal(_))
            && !matches!(arena.term(children[1]).kind, TermKind::Literal(_))
        {
            m.literals_not_last = 1;
        }
        for child in children {
            let c = measure_memo(arena, child, memo);
            m.non_leaf_nodes = m.non_leaf_nodes.saturating_add(c.non_leaf_nodes);
            m.cast_width = m.cast_width.saturating_add(c.cast_width);
            m.literals_not_last = m.literals_not_last.saturating_add(c.literals_not_last);
        }
    }
    memo.insert(id, m);
    m
}

/// Rewrite one term, or decline.
pub type Apply = fn(&mut TermArena, TermId) -> Option<TermId>;

/// Build an instance of the shape a rule recognises, at `width` bits, over
/// the given fresh leaves. The proof test asserts the rule fires on it.
pub type Template = fn(&mut TermArena, u32, &[TermId]) -> TermId;

pub struct Rule {
    pub id: RuleId,
    pub group: RuleGroup,
    pub decreases: Measure,
    pub apply: Apply,
    pub templates: &'static [Template],
    /// Widths the equivalence is proven at. Must contain 64 unless
    /// `proof_note` says why not.
    pub proof_widths: &'static [u32],
    pub proof_note: Option<&'static str>,
}

pub const DEFAULT_PROOF_WIDTHS: &[u32] = &[8, 16, 32, 64];

pub mod identity;
pub mod literal;

/// Every rule, in the order the driver tries them. Literal folding first, so
/// a term over literals is a literal before any identity looks at it.
pub static RULES: &[&Rule] = &[
    &literal::ADD,
    &literal::SUB,
    &literal::MUL,
    &literal::NEG,
    &literal::AND,
    &literal::OR,
    &literal::XOR,
    &literal::NOT,
    &literal::SHIFT,
    &literal::COMPARE,
    &literal::FLAG,
    &literal::BOOL,
    &literal::BOOL_NOT,
    &literal::CAST,
    &literal::EXTRACT,
    &literal::CONCAT,
    &literal::SELECT,
    &identity::ADD_ZERO,
    &identity::SUB_ZERO,
    &identity::SUB_SELF,
    &identity::MUL_ONE,
    &identity::MUL_ZERO,
    &identity::AND_ZERO,
    &identity::AND_ONES,
    &identity::AND_SELF,
    &identity::OR_ZERO,
    &identity::OR_SELF,
    &identity::OR_ONES,
    &identity::XOR_ZERO,
    &identity::XOR_SELF,
    &identity::NOT_NOT,
    &identity::NEG_NEG,
    &identity::SHL_ZERO,
    &identity::LSHR_ZERO,
    &identity::ASHR_ZERO,
    &identity::BOOLNOT_BOOLNOT,
    &identity::BOOLAND_SELF,
    &identity::BOOLOR_SELF,
    &identity::BOOLAND_TRUE,
    &identity::BOOLOR_FALSE,
];

pub fn rule(id: RuleId) -> Option<&'static Rule> {
    RULES.iter().copied().find(|rule| rule.id == id)
}
