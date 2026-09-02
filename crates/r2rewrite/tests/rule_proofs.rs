//! Every rule is a proven equivalence, and the table is the catalogue.
//!
//! For each rule and each of its templates, at each width the rule lists:
//! the rule fires on the template (a proof that never exercises its rule is
//! vacuous and fails), the declared measure component strictly drops and the
//! whole measure drops lexicographically, the two sides agree on every input
//! at width 8 when the template has at most two variables, and Z3 finds no
//! input on which they differ at every width.

mod proof;

use std::collections::{BTreeSet, HashMap};

use proof::Encoder;
use r2rewrite::{LeafRef, RULES, TermArena, TermKind, canon, eval, mask, measure};
use r2ssa::{MachineSignedness, MachineType};
use z3::{SatResult, Solver};

fn unsigned(width: u32) -> MachineType {
    MachineType::Integer {
        width_bits: width,
        signedness: MachineSignedness::Unsigned,
    }
}

fn fresh_leaves(arena: &mut TermArena, width: u32) -> Vec<r2rewrite::TermId> {
    (0..3)
        .map(|index| arena.intern(unsigned(width), TermKind::Variable(index)))
        .collect()
}

#[test]
fn rule_ids_are_unique_and_named_by_group() {
    let mut seen = BTreeSet::new();
    for rule in RULES.iter().copied() {
        assert!(seen.insert(rule.id), "duplicate rule id {}", rule.id);
        assert!(
            rule.id.contains('.'),
            "rule id {} is not group.name",
            rule.id
        );
    }
}

#[test]
fn every_rule_has_a_template() {
    for rule in RULES.iter().copied() {
        assert!(
            !rule.templates.is_empty(),
            "rule {} has no template, so nothing proves it",
            rule.id
        );
    }
}

#[test]
fn every_rule_proves_at_sixty_four_bits_or_explains() {
    for rule in RULES.iter().copied() {
        assert!(
            rule.proof_widths.contains(&64) || rule.proof_note.is_some(),
            "rule {} is not proven at 64 bits and does not say why",
            rule.id
        );
        assert!(
            !rule.proof_widths.is_empty(),
            "rule {} lists no proof width",
            rule.id
        );
    }
}

/// Exhaustively evaluate both sides over every assignment when the term has
/// at most two variables of at most eight bits each.
fn exhaustive_agrees(
    arena: &TermArena,
    before: r2rewrite::TermId,
    after: r2rewrite::TermId,
) -> Option<bool> {
    let mut variables = arena.variables(before);
    for variable in arena.variables(after) {
        if !variables.contains(&variable) {
            variables.push(variable);
        }
    }
    if variables.len() > 2 || variables.iter().any(|(_, ty)| ty.width_bits() > 8) {
        return None;
    }
    let domains: Vec<Vec<u128>> = variables
        .iter()
        .map(|(_, ty)| match ty {
            MachineType::Bool { .. } => vec![0, 1],
            ty => (0..=mask(ty.width_bits())).collect(),
        })
        .collect();
    let mut assignment: HashMap<(u32, MachineType), u128> = HashMap::new();
    let total: usize = domains.iter().map(Vec::len).product();
    for index in 0..total {
        let mut rest = index;
        for (position, (variable, domain)) in variables.iter().zip(&domains).enumerate() {
            let _ = position;
            assignment.insert(*variable, domain[rest % domain.len()]);
            rest /= domain.len();
        }
        let mut leaf = |leaf: LeafRef, ty: &MachineType| match leaf {
            LeafRef::Variable(index) => assignment[&(index, *ty)],
            LeafRef::Expr(_) => panic!("templates have no base leaves"),
        };
        let l = eval(arena, before, &mut leaf);
        let r = eval(arena, after, &mut leaf);
        if l != r {
            return Some(false);
        }
    }
    Some(true)
}

#[test]
fn every_rule_is_a_proven_equivalence() {
    for rule in RULES.iter().copied() {
        for (template_index, template) in rule.templates.iter().enumerate() {
            for &width in rule.proof_widths {
                let mut arena = TermArena::new();
                let leaves = fresh_leaves(&mut arena, width);
                let before = template(&mut arena, width, &leaves);
                let after = (rule.apply)(&mut arena, before).unwrap_or_else(|| {
                    panic!(
                        "rule {} does not fire on its template {} at width {}: {:?}",
                        rule.id,
                        template_index,
                        width,
                        arena.term(before)
                    )
                });
                assert_ne!(
                    before, after,
                    "rule {} rewrote template {} to itself at width {}",
                    rule.id, template_index, width
                );
                let measure_before = measure(&arena, before);
                let measure_after = measure(&arena, after);
                assert!(
                    measure_after.component(rule.decreases)
                        < measure_before.component(rule.decreases),
                    "rule {} template {} width {}: declared measure {:?} does not drop ({:?} -> {:?})",
                    rule.id,
                    template_index,
                    width,
                    rule.decreases,
                    measure_before,
                    measure_after
                );
                assert!(
                    measure_after < measure_before,
                    "rule {} template {} width {}: measure does not drop lexicographically ({:?} -> {:?})",
                    rule.id,
                    template_index,
                    width,
                    measure_before,
                    measure_after
                );
                if let Some(agrees) = exhaustive_agrees(&arena, before, after) {
                    assert!(
                        agrees,
                        "rule {} template {} width {}: the evaluator disagrees on some input",
                        rule.id, template_index, width
                    );
                }
                let mut encoder = Encoder::new(&arena);
                let lhs = encoder.encode(before);
                let rhs = encoder.encode(after);
                let solver = Solver::new();
                solver.assert(lhs.eq(rhs.clone()).not());
                let verdict = solver.check();
                if verdict != SatResult::Unsat {
                    let mut witness = String::new();
                    if let Some(model) = solver.get_model() {
                        for ((index, ty), bv) in encoder.variables() {
                            let value = model.eval(bv, true).and_then(|v| v.as_u64());
                            witness.push_str(&format!(" v{index}@{ty:?}={value:?}"));
                        }
                    }
                    panic!(
                        "rule {} template {} width {}: not an equivalence ({verdict:?}); before {:?} after {:?};{witness}",
                        rule.id,
                        template_index,
                        width,
                        arena.term(before),
                        arena.term(after)
                    );
                }
            }
        }
    }
}

/// Normalisers are equivalences too, and idempotent, and never add a node.
#[test]
fn operand_ordering_is_an_idempotent_equivalence() {
    use r2ssa::{MachineArithmeticOp, MachineBitwiseOp, MachineComparisonOp};
    let shapes: &[r2rewrite::rules::Template] = &[
        |arena, w, l| {
            let five = arena.intern(
                unsigned(w),
                TermKind::Literal(r2ssa::MachineBitVector::new(w, 5).unwrap()),
            );
            arena.intern(
                unsigned(w),
                TermKind::Arithmetic {
                    op: MachineArithmeticOp::Add,
                    left: five,
                    right: l[0],
                },
            )
        },
        |arena, w, l| {
            arena.intern(
                unsigned(w),
                TermKind::Arithmetic {
                    op: MachineArithmeticOp::Multiply,
                    left: l[1],
                    right: l[0],
                },
            )
        },
        |arena, w, l| {
            arena.intern(
                unsigned(w),
                TermKind::Bitwise {
                    op: MachineBitwiseOp::Xor,
                    left: l[2],
                    right: l[0],
                },
            )
        },
        |arena, w, l| {
            let _ = w;
            let seven = arena.intern(
                unsigned(w),
                TermKind::Literal(r2ssa::MachineBitVector::new(w, 7).unwrap()),
            );
            arena.intern(
                MachineType::Bool { storage_bits: 8 },
                TermKind::Compare {
                    op: MachineComparisonOp::Equal,
                    interpretation: MachineSignedness::Unsigned,
                    left: seven,
                    right: l[0],
                },
            )
        },
        |arena, _w, l| {
            arena.intern(
                MachineType::Bool { storage_bits: 8 },
                TermKind::Compare {
                    op: MachineComparisonOp::NotEqual,
                    interpretation: MachineSignedness::Unsigned,
                    left: l[1],
                    right: l[0],
                },
            )
        },
    ];
    check_normaliser(shapes, canon::order_operands);
}

/// A truncation is an extract at offset zero; an arithmetic right shift by a
/// literal count at or past the width shifts by the width minus one.
#[test]
fn truncation_and_shift_clamp_are_idempotent_equivalences() {
    use r2ssa::{MachineCastKind, MachineOvershiftBehavior, MachineShiftKind};
    let shapes: &[r2rewrite::rules::Template] = &[
        |arena, w, _| {
            let wide = arena.intern(unsigned((w * 2).min(64).max(w + 4)), TermKind::Variable(7));
            arena.intern(
                unsigned(w),
                TermKind::Cast {
                    kind: MachineCastKind::Truncate,
                    input: wide,
                },
            )
        },
        |arena, w, l| {
            let count = arena.intern(
                unsigned(8),
                TermKind::Literal(r2ssa::MachineBitVector::new(8, u64::from(w) + 5).unwrap()),
            );
            arena.intern(
                unsigned(w),
                TermKind::Shift {
                    kind: MachineShiftKind::ArithmeticRight,
                    overshift: MachineOvershiftBehavior::SignFill,
                    value: l[0],
                    count,
                },
            )
        },
    ];
    check_normaliser(shapes, canon::normalize);
}

fn check_normaliser(
    shapes: &[r2rewrite::rules::Template],
    normaliser: fn(&mut TermArena, r2rewrite::TermId) -> r2rewrite::TermId,
) {
    for (index, shape) in shapes.iter().enumerate() {
        for width in [8u32, 16, 32, 64] {
            let mut arena = TermArena::new();
            let leaves = fresh_leaves(&mut arena, width);
            let before = shape(&mut arena, width, &leaves);
            let once = normaliser(&mut arena, before);
            assert_ne!(before, once, "shape {index} at {width} was already ordered");
            let twice = normaliser(&mut arena, once);
            assert_eq!(once, twice, "shape {index} at {width}: not idempotent");
            assert!(measure(&arena, once) <= measure(&arena, before));
            if let Some(agrees) = exhaustive_agrees(&arena, before, once) {
                assert!(agrees, "shape {index} at {width}: evaluator disagrees");
            }
            let mut encoder = Encoder::new(&arena);
            let lhs = encoder.encode(before);
            let rhs = encoder.encode(once);
            let solver = Solver::new();
            solver.assert(lhs.eq(rhs).not());
            assert_eq!(solver.check(), SatResult::Unsat, "shape {index} at {width}");
        }
    }
}
