use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use r2ssa::{SSAOp, SSAVar};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ScalarSignednessEvidence {
    Signed,
    Unsigned,
}

/// Recover signedness only from operations whose machine semantics distinguish
/// signed from unsigned values, then flow that evidence backward through exact
/// same-width aliases. Width alone remains deliberately neutral.
pub(crate) fn infer_scalar_signedness<'a>(
    operations: impl IntoIterator<Item = &'a SSAOp>,
    aliases: impl IntoIterator<Item = (&'a SSAVar, &'a SSAVar)>,
    arch_name: Option<&str>,
) -> HashMap<SSAVar, BTreeSet<ScalarSignednessEvidence>> {
    let operations = operations.into_iter().collect::<Vec<_>>();
    let condition_values = control_condition_values(&operations);
    let mut reverse_edges = HashMap::<SSAVar, BTreeSet<SSAVar>>::new();
    let mut signedness = HashMap::<SSAVar, BTreeSet<ScalarSignednessEvidence>>::new();

    for (source, derived) in aliases {
        link_same_width(&mut reverse_edges, source, derived);
    }
    for op in operations {
        match op {
            SSAOp::Copy { dst, src } | SSAOp::Cast { dst, src } | SSAOp::New { dst, src } => {
                link_same_width(&mut reverse_edges, src, dst);
            }
            SSAOp::Phi { dst, sources } => {
                for source in sources {
                    link_same_width(&mut reverse_edges, source, dst);
                }
            }
            SSAOp::IntZExt { dst, src } => {
                if !is_implicit_register_zero_extension(arch_name, dst, src) {
                    seed_signedness(&mut signedness, src, ScalarSignednessEvidence::Unsigned);
                }
            }
            SSAOp::IntSExt { src, .. } => {
                seed_signedness(&mut signedness, src, ScalarSignednessEvidence::Signed);
            }
            SSAOp::IntLess { dst, a, b } | SSAOp::IntLessEqual { dst, a, b }
                if condition_values.contains(dst) =>
            {
                seed_signedness(&mut signedness, a, ScalarSignednessEvidence::Unsigned);
                seed_signedness(&mut signedness, b, ScalarSignednessEvidence::Unsigned);
            }
            SSAOp::IntSLess { dst, a, b } | SSAOp::IntSLessEqual { dst, a, b }
                if condition_values.contains(dst) =>
            {
                seed_signedness(&mut signedness, a, ScalarSignednessEvidence::Signed);
                seed_signedness(&mut signedness, b, ScalarSignednessEvidence::Signed);
            }
            SSAOp::IntDiv { a, b, .. } | SSAOp::IntRem { a, b, .. } => {
                seed_signedness(&mut signedness, a, ScalarSignednessEvidence::Unsigned);
                seed_signedness(&mut signedness, b, ScalarSignednessEvidence::Unsigned);
            }
            SSAOp::IntSDiv { a, b, .. } | SSAOp::IntSRem { a, b, .. } => {
                seed_signedness(&mut signedness, a, ScalarSignednessEvidence::Signed);
                seed_signedness(&mut signedness, b, ScalarSignednessEvidence::Signed);
            }
            SSAOp::IntRight { a, .. } => {
                seed_signedness(&mut signedness, a, ScalarSignednessEvidence::Unsigned);
            }
            SSAOp::IntSRight { a, .. } => {
                seed_signedness(&mut signedness, a, ScalarSignednessEvidence::Signed);
            }
            _ => {}
        }
    }

    let mut ready = signedness.keys().cloned().collect::<VecDeque<_>>();
    while let Some(derived) = ready.pop_front() {
        let Some(observed) = signedness.get(&derived).cloned() else {
            continue;
        };
        let Some(sources) = reverse_edges.get(&derived) else {
            continue;
        };
        for source in sources {
            let entry = signedness.entry(source.clone()).or_default();
            let before = entry.len();
            entry.extend(observed.iter().copied());
            if entry.len() != before {
                ready.push_back(source.clone());
            }
        }
    }
    signedness
}

fn control_condition_values(operations: &[&SSAOp]) -> HashSet<SSAVar> {
    let mut values = operations
        .iter()
        .filter_map(|op| match op {
            SSAOp::CBranch { cond, .. } => Some(cond.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut changed = true;
    while changed {
        changed = false;
        for op in operations {
            let Some(dst) = op.dst() else {
                continue;
            };
            if !values.contains(dst) || !condition_carrier_op(op) {
                continue;
            }
            op.for_each_source(|source| {
                if !source.is_const() {
                    changed |= values.insert(source.clone());
                }
            });
        }
    }
    values
}

fn condition_carrier_op(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Copy { .. }
            | SSAOp::Cast { .. }
            | SSAOp::New { .. }
            | SSAOp::Phi { .. }
            | SSAOp::BoolNot { .. }
            | SSAOp::BoolAnd { .. }
            | SSAOp::BoolOr { .. }
            | SSAOp::BoolXor { .. }
            | SSAOp::IntEqual { .. }
            | SSAOp::IntNotEqual { .. }
    ) || matches!(
        op,
        SSAOp::IntAnd { dst, .. } | SSAOp::IntOr { dst, .. } | SSAOp::IntXor { dst, .. }
            if dst.size == 1
    )
}

/// Some ISAs define a narrow register write by zeroing its wider architectural
/// parent. Lifters expose that state update as `IntZExt`, but it says nothing
/// about the source-language signedness of the narrow value.
fn is_implicit_register_zero_extension(
    arch_name: Option<&str>,
    dst: &SSAVar,
    src: &SSAVar,
) -> bool {
    if dst.size != 8 || src.size != 4 {
        return false;
    }
    let arch = arch_name.unwrap_or_default().to_ascii_lowercase();
    let dst = dst.name.to_ascii_lowercase();
    if arch == "x86-64"
        || arch == "x86_64"
        || arch == "x64"
        || arch == "amd64"
        || arch.starts_with("x86:64")
    {
        return matches!(
            dst.as_str(),
            "rax" | "rbx" | "rcx" | "rdx" | "rsi" | "rdi" | "rbp" | "rsp"
        ) || dst
            .strip_prefix('r')
            .and_then(|index| index.parse::<u8>().ok())
            .is_some_and(|index| (8..=15).contains(&index));
    }
    if arch == "aarch64" || arch == "arm64" || arch.starts_with("aarch64:") {
        return dst == "sp"
            || dst
                .strip_prefix('x')
                .and_then(|index| index.parse::<u8>().ok())
                .is_some_and(|index| index <= 30);
    }
    false
}

fn link_same_width(
    reverse_edges: &mut HashMap<SSAVar, BTreeSet<SSAVar>>,
    source: &SSAVar,
    derived: &SSAVar,
) {
    if source.size == derived.size {
        reverse_edges
            .entry(derived.clone())
            .or_default()
            .insert(source.clone());
    }
}

fn seed_signedness(
    signedness: &mut HashMap<SSAVar, BTreeSet<ScalarSignednessEvidence>>,
    var: &SSAVar,
    evidence: ScalarSignednessEvidence,
) {
    if !var.is_const() {
        signedness.entry(var.clone()).or_default().insert(evidence);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_alias_propagates_extension_signedness_to_source() {
        let source = SSAVar::new("source", 1, 1);
        let reload = SSAVar::new("reload", 1, 1);
        let operations = [SSAOp::IntZExt {
            dst: SSAVar::new("wide", 1, 4),
            src: reload.clone(),
        }];

        let inferred = infer_scalar_signedness(&operations, [(&source, &reload)], None);

        assert_eq!(
            inferred.get(&source),
            Some(&BTreeSet::from([ScalarSignednessEvidence::Unsigned]))
        );
    }

    #[test]
    fn conflicting_machine_semantics_remain_explicit() {
        let value = SSAVar::new("value", 1, 1);
        let operations = [
            SSAOp::IntZExt {
                dst: SSAVar::new("unsigned_wide", 1, 4),
                src: value.clone(),
            },
            SSAOp::IntSExt {
                dst: SSAVar::new("signed_wide", 1, 4),
                src: value.clone(),
            },
        ];

        let inferred = infer_scalar_signedness(&operations, std::iter::empty(), None);

        assert_eq!(
            inferred.get(&value),
            Some(&BTreeSet::from([
                ScalarSignednessEvidence::Signed,
                ScalarSignednessEvidence::Unsigned,
            ]))
        );
    }

    #[test]
    fn x86_parent_register_zeroing_is_not_unsigned_evidence() {
        let value = SSAVar::new("loaded", 1, 4);
        let operations = [SSAOp::IntZExt {
            dst: SSAVar::new("RAX", 1, 8),
            src: value.clone(),
        }];

        let inferred = infer_scalar_signedness(&operations, std::iter::empty(), Some("x86-64"));

        assert!(!inferred.contains_key(&value));
    }

    #[test]
    fn unsigned_compare_reaching_branch_types_its_operands() {
        let value = SSAVar::new("value", 1, 8);
        let carry = SSAVar::new("carry", 1, 1);
        let condition = SSAVar::new("condition", 1, 1);
        let operations = [
            SSAOp::IntLessEqual {
                dst: carry.clone(),
                a: value.clone(),
                b: SSAVar::new("bound", 1, 8),
            },
            SSAOp::Copy {
                dst: condition.clone(),
                src: carry,
            },
            SSAOp::CBranch {
                target: SSAVar::constant(0x2000, 8),
                cond: condition,
            },
        ];

        let inferred = infer_scalar_signedness(&operations, std::iter::empty(), None);

        assert_eq!(
            inferred.get(&value),
            Some(&BTreeSet::from([ScalarSignednessEvidence::Unsigned]))
        );
    }

    #[test]
    fn dead_unsigned_flag_does_not_type_signed_branch_operands() {
        let value = SSAVar::new("value", 1, 8);
        let operations = [
            SSAOp::IntLessEqual {
                dst: SSAVar::new("dead_carry", 1, 1),
                a: value.clone(),
                b: SSAVar::new("bound", 1, 8),
            },
            SSAOp::IntSLess {
                dst: SSAVar::new("negative", 1, 1),
                a: SSAVar::new("difference", 1, 8),
                b: SSAVar::constant(0, 8),
            },
            SSAOp::CBranch {
                target: SSAVar::constant(0x2000, 8),
                cond: SSAVar::new("negative", 1, 1),
            },
        ];

        let inferred = infer_scalar_signedness(&operations, std::iter::empty(), None);

        assert!(!inferred.contains_key(&value));
    }
}
