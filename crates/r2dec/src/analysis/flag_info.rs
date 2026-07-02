use std::collections::{HashMap, HashSet};

use r2ssa::SSAOp;

use super::lower::LowerCtx;
use super::{FlagCompareKind, FlagCompareProvenance, FlagInfo, PassEnv, SSABlock, UseInfo, utils};
use crate::ast::{BinaryOp, CExpr, UnaryOp};

#[derive(Debug, Default)]
pub(crate) struct FlagScratch {
    pub(crate) info: FlagInfo,
}

pub(crate) fn analyze(blocks: &[SSABlock], use_info: &UseInfo, env: &PassEnv<'_>) -> FlagInfo {
    let mut scratch = FlagScratch::default();
    let lower = LowerCtx {
        use_info: Some(use_info),
        definitions: &use_info.definitions,
        semantic_values: &use_info.semantic_values,
        use_counts: &use_info.use_counts,
        condition_vars: &use_info.condition_vars,
        pinned: &use_info.pinned,
        var_aliases: &use_info.var_aliases,
        param_register_aliases: env.param_register_aliases,
        type_hints: &use_info.type_hints,
        ptr_arith: &use_info.ptr_arith,
        stack_slots: &use_info.stack_slots,
        forwarded_values: &use_info.forwarded_values,
        type_oracle: env.type_oracle,
    };

    for block in blocks {
        analyze_comparison_patterns(&mut scratch, block, use_info, &lower);
    }
    recompute_flag_only_values(&mut scratch, blocks);

    scratch.info
}

fn format_compare_operand(var: &r2ssa::SSAVar, compare_width: u32) -> String {
    if let Some(val) = utils::parse_compare_const_value_with_width(var, compare_width) {
        if (val > 255 && val % 10 != 0) || val > 0xffff {
            format!("0x{:x}", val)
        } else {
            format!("{}", val)
        }
    } else {
        var.name.clone()
    }
}

fn analyze_comparison_patterns(
    scratch: &mut FlagScratch,
    block: &SSABlock,
    use_info: &UseInfo,
    lower: &LowerCtx<'_>,
) {
    for op in &block.ops {
        if let SSAOp::IntSub { dst, a, b } = op {
            let dst_key = dst.display_name();
            let (a_name, b_name) = trace_compare_operands(a, b, use_info);
            scratch.info.sub_results.insert(dst_key, (a_name, b_name));
        }

        if let SSAOp::IntEqual { dst, a, b } = op {
            let dst_name = dst.name.to_lowercase();
            if dst_name.contains("zf")
                && b.is_const()
                && utils::parse_const_value(&b.name) == Some(0)
            {
                let a_key = a.display_name();
                if let Some((orig_a, orig_b)) = scratch.info.sub_results.get(&a_key).cloned() {
                    record_flag_compare_provenance(
                        scratch,
                        dst.display_name(),
                        orig_a,
                        orig_b,
                        FlagCompareKind::Equality,
                    );
                }
            }
        }

        if let SSAOp::IntSLess { dst, a, b } = op {
            let dst_name = dst.name.to_lowercase();
            if dst_name.contains("sf")
                && b.is_const()
                && utils::parse_const_value(&b.name) == Some(0)
            {
                let a_key = a.display_name();
                if let Some((orig_a, orig_b)) = scratch.info.sub_results.get(&a_key).cloned() {
                    record_flag_compare_provenance(
                        scratch,
                        dst.display_name(),
                        orig_a,
                        orig_b,
                        FlagCompareKind::SignedNegative,
                    );
                }
            }
        }

        if let SSAOp::IntSBorrow { dst, a, b } = op {
            let dst_name = dst.name.to_lowercase();
            if dst_name.contains("of") {
                let (a_name, b_name) = trace_compare_operands(a, b, use_info);
                record_flag_compare_provenance(
                    scratch,
                    dst.display_name(),
                    a_name,
                    b_name,
                    FlagCompareKind::Overflow,
                );
            }
        }

        if let SSAOp::IntLess { dst, a, b } = op {
            let dst_name = dst.name.to_lowercase();
            if dst_name.contains("cf") {
                let (a_name, b_name) = trace_compare_operands(a, b, use_info);
                record_flag_compare_provenance(
                    scratch,
                    dst.display_name(),
                    a_name,
                    b_name,
                    FlagCompareKind::UnsignedLess,
                );
            }
        }

        let predicate_expr = match op {
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Cast { src, .. } => predicate_passthrough_expr(src, scratch),
            SSAOp::BoolNot { src, .. } => Some(CExpr::unary(
                UnaryOp::Not,
                predicate_operand_expr(src, scratch, use_info, lower),
            )),
            SSAOp::BoolAnd { a, b, .. } => Some(CExpr::binary(
                BinaryOp::And,
                predicate_operand_expr(a, scratch, use_info, lower),
                predicate_operand_expr(b, scratch, use_info, lower),
            )),
            SSAOp::BoolOr { a, b, .. } => Some(CExpr::binary(
                BinaryOp::Or,
                predicate_operand_expr(a, scratch, use_info, lower),
                predicate_operand_expr(b, scratch, use_info, lower),
            )),
            SSAOp::BoolXor { a, b, .. } => Some(CExpr::binary(
                BinaryOp::BitXor,
                predicate_operand_expr(a, scratch, use_info, lower),
                predicate_operand_expr(b, scratch, use_info, lower),
            )),
            SSAOp::IntEqual { dst, a, b } => {
                predicate_expr_for_compare_flag(dst.display_name(), scratch).or_else(|| {
                    Some(CExpr::binary(
                        BinaryOp::Eq,
                        predicate_operand_expr(a, scratch, use_info, lower),
                        predicate_operand_expr(b, scratch, use_info, lower),
                    ))
                })
            }
            SSAOp::IntNotEqual { a, b, .. } => Some(CExpr::binary(
                BinaryOp::Ne,
                predicate_operand_expr(a, scratch, use_info, lower),
                predicate_operand_expr(b, scratch, use_info, lower),
            )),
            SSAOp::IntLess { dst, a, b } | SSAOp::IntSLess { dst, a, b } => {
                predicate_expr_for_compare_flag(dst.display_name(), scratch).or_else(|| {
                    Some(CExpr::binary(
                        BinaryOp::Lt,
                        predicate_operand_expr(a, scratch, use_info, lower),
                        predicate_operand_expr(b, scratch, use_info, lower),
                    ))
                })
            }
            SSAOp::IntLessEqual { a, b, .. } | SSAOp::IntSLessEqual { a, b, .. } => {
                Some(CExpr::binary(
                    BinaryOp::Le,
                    predicate_operand_expr(a, scratch, use_info, lower),
                    predicate_operand_expr(b, scratch, use_info, lower),
                ))
            }
            _ => None,
        };

        if let (Some(dst), Some(expr)) = (op.dst(), predicate_expr) {
            record_predicate_expr(scratch, dst.display_name(), expr, use_info);
        }
    }
}

fn const_expr_from_var(var: &r2ssa::SSAVar) -> Option<CExpr> {
    Some(utils::compare_const_to_expr(var))
}

fn predicate_passthrough_expr(src: &r2ssa::SSAVar, scratch: &FlagScratch) -> Option<CExpr> {
    if let Some(expr) = scratch.info.predicate_exprs.get(&src.display_name()) {
        return Some(expr.clone());
    }
    if src.is_const() {
        return const_expr_from_var(src);
    }
    if utils::is_cpu_flag(&src.name.to_lowercase()) {
        return Some(CExpr::Var(src.display_name()));
    }
    None
}

fn trace_compare_operands(
    a: &r2ssa::SSAVar,
    b: &r2ssa::SSAVar,
    use_info: &UseInfo,
) -> (String, String) {
    let a_name = traced_compare_operand_name(a, use_info);
    let compare_width = a.size.max(b.size);
    let b_name = if b.is_const() {
        format_compare_operand(b, compare_width)
    } else {
        traced_compare_operand_name(b, use_info)
    };
    (a_name, b_name)
}

fn traced_compare_operand_name(var: &r2ssa::SSAVar, use_info: &UseInfo) -> String {
    let key = var.display_name();
    if use_info.call_result_source_by_alias.contains_key(&key)
        || matches!(use_info.definitions.get(&key), Some(CExpr::Call { .. }))
    {
        return key;
    }
    utils::trace_ssa_var_to_source(var, &use_info.copy_sources, &use_info.var_aliases)
}

fn record_flag_compare_provenance(
    scratch: &mut FlagScratch,
    dst_key: String,
    lhs: String,
    rhs: String,
    kind: FlagCompareKind,
) {
    scratch
        .info
        .flag_origins
        .insert(dst_key.clone(), (lhs.clone(), rhs.clone()));
    scratch
        .info
        .compare_provenance
        .insert(dst_key, FlagCompareProvenance { lhs, rhs, kind });
}

fn predicate_expr_for_compare_flag(dst_key: String, scratch: &FlagScratch) -> Option<CExpr> {
    scratch
        .info
        .compare_provenance
        .contains_key(&dst_key)
        .then_some(CExpr::Var(dst_key))
}

fn predicate_operand_expr(
    src: &r2ssa::SSAVar,
    scratch: &FlagScratch,
    use_info: &UseInfo,
    lower: &LowerCtx<'_>,
) -> CExpr {
    predicate_passthrough_expr(src, scratch).unwrap_or_else(|| {
        if src.is_const() {
            const_expr_from_var(src).unwrap_or_else(|| CExpr::Var(src.display_name()))
        } else {
            let lowered = lower.get_expr(src);
            if matches!(lowered, CExpr::Call { .. })
                && (use_info
                    .call_result_source_by_alias
                    .contains_key(&src.display_name())
                    || matches!(
                        use_info.definitions.get(&src.display_name()),
                        Some(CExpr::Call { .. })
                    ))
            {
                CExpr::Var(utils::format_traced_name(
                    &src.display_name(),
                    &use_info.var_aliases,
                ))
            } else {
                lowered
            }
        }
    })
}

fn record_predicate_expr(
    scratch: &mut FlagScratch,
    dst_key: String,
    expr: CExpr,
    use_info: &UseInfo,
) {
    let formatted = utils::format_traced_name(&dst_key, &use_info.var_aliases);
    scratch.info.predicate_exprs.insert(dst_key, expr.clone());
    scratch.info.predicate_exprs.insert(formatted, expr);
}

fn op_can_be_flag_glue(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Copy { .. }
            | SSAOp::BoolAnd { .. }
            | SSAOp::BoolOr { .. }
            | SSAOp::BoolXor { .. }
            | SSAOp::BoolNot { .. }
            | SSAOp::IntEqual { .. }
            | SSAOp::IntNotEqual { .. }
            | SSAOp::IntLess { .. }
            | SSAOp::IntSLess { .. }
            | SSAOp::IntLessEqual { .. }
            | SSAOp::IntSLessEqual { .. }
            | SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. }
            | SSAOp::Trunc { .. }
            | SSAOp::Cast { .. }
    )
}

fn consumer_is_flag_context(op: &SSAOp, flag_context_dsts: &HashSet<String>) -> bool {
    if matches!(op, SSAOp::CBranch { .. }) {
        return true;
    }

    if let Some(dst) = op.dst() {
        let dst_key = dst.display_name();
        return utils::is_cpu_flag(&dst.name.to_lowercase())
            || flag_context_dsts.contains(&dst_key);
    }

    false
}

fn recompute_flag_only_values(scratch: &mut FlagScratch, blocks: &[SSABlock]) {
    scratch.info.flag_only_values.clear();

    let mut consumers: HashMap<String, Vec<(usize, usize)>> = HashMap::new();
    let mut defs: HashMap<String, (usize, usize)> = HashMap::new();

    for (block_idx, block) in blocks.iter().enumerate() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            for src in op.sources() {
                consumers
                    .entry(src.display_name())
                    .or_default()
                    .push((block_idx, op_idx));
            }
            if let Some(dst) = op.dst() {
                defs.insert(dst.display_name(), (block_idx, op_idx));
            }
        }
    }

    let mut flag_context_dsts: HashSet<String> = defs
        .keys()
        .filter(|name| utils::is_cpu_flag(&name.to_lowercase()))
        .cloned()
        .collect();

    loop {
        let mut changed = false;
        for (dst_key, (block_idx, op_idx)) in &defs {
            if flag_context_dsts.contains(dst_key) {
                continue;
            }

            let op = &blocks[*block_idx].ops[*op_idx];
            if !op_can_be_flag_glue(op) {
                continue;
            }

            let srcs = op.sources();
            if srcs.is_empty() {
                continue;
            }

            if !srcs.iter().all(|src| {
                src.is_const()
                    || utils::is_cpu_flag(&src.name.to_lowercase())
                    || flag_context_dsts.contains(&src.display_name())
            }) {
                continue;
            }

            let Some(op_consumers) = consumers.get(dst_key) else {
                continue;
            };
            if op_consumers.is_empty() {
                continue;
            }

            if op_consumers.iter().all(|(consumer_block, consumer_op)| {
                consumer_is_flag_context(
                    &blocks[*consumer_block].ops[*consumer_op],
                    &flag_context_dsts,
                )
            }) {
                flag_context_dsts.insert(dst_key.clone());
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    for (src_key, src_consumers) in consumers {
        if src_consumers.is_empty() || utils::is_cpu_flag(&src_key.to_lowercase()) {
            continue;
        }

        if src_consumers.iter().all(|(consumer_block, consumer_op)| {
            consumer_is_flag_context(
                &blocks[*consumer_block].ops[*consumer_op],
                &flag_context_dsts,
            )
        }) {
            scratch.info.flag_only_values.insert(src_key);
        }
    }
}
