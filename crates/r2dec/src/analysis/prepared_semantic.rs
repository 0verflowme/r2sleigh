use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use r2ssa::function::DefLocation;
use r2ssa::{
    CompareKind, MemoryLocation, ObjectKind, ReturnCarrier, SSAOp, SSAVar, SSAVarNameKind,
    SsaArtifact, ValueId, ValueOwner,
};
use r2types::{
    CalleeIdentity, CalleeResolutionFacts, CalleeTargetIdentityRequest, CallsiteKey,
    ExternalStackBase, ExternalStackSlotRole, ExternalStackSlotSpec, FunctionCallResultFacts,
    FunctionCallsiteFacts, FunctionFacts, StackSlotKey, VisibleBinding, VisibleBindingKind,
};

use super::lower::LowerCtx;
use super::{
    BaseRef, CallArgBinding, DecompilerFacts, FlagInfo, NormalizedAddr, PassEnv, SSABlock,
    ScalarValue, SemanticCallArg, SemanticOwnershipFacts, SemanticValue, StackInfo,
    StackSlotProvenance, StackSlotValueKind, UseInfo, ValueProvenance, ValueRef,
};
use crate::analysis::utils::{
    compare_const_to_expr, compare_const_to_expr_with_width, is_cpu_flag,
    is_temporary_constant_or_memory_name, is_temporary_or_memory_name, parse_const_value,
};
use crate::ast::{BinaryOp, CExpr, UnaryOp};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StackAliasView {
    pub(crate) visible_name: String,
    pub(crate) arg_alias: Option<String>,
    pub(crate) binding_kind: Option<VisibleBindingKind>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct PreparedCallView {
    pub(crate) direct_target: Option<u64>,
    pub(crate) callee_identity: Option<CalleeIdentity>,
    pub(crate) authoritative_args: Vec<CExpr>,
    pub(crate) authoritative_arg_values: Vec<ValueId>,
    pub(crate) result_owner: Option<CExpr>,
    pub(crate) render_fact: Option<r2types::CallsiteRenderFact>,
}

#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct PreparedSemanticView {
    pub(crate) stack_aliases_by_offset: BTreeMap<i64, StackAliasView>,
    pub(crate) param_alias_by_reg: HashMap<String, String>,
    pub(crate) param_rank_by_alias: HashMap<String, usize>,
    pub(crate) value_id_by_var: HashMap<SSAVar, ValueId>,
    pub(crate) var_by_value_id: HashMap<ValueId, SSAVar>,
    pub(crate) owner_expr_by_value: HashMap<ValueId, CExpr>,
    pub(crate) owner_expr_by_name: HashMap<String, CExpr>,
    pub(crate) stack_offset_by_value: HashMap<ValueId, i64>,
    pub(crate) predicate_expr_by_value: HashMap<ValueId, CExpr>,
    pub(crate) predicate_expr_by_name: HashMap<String, CExpr>,
    pub(crate) branch_predicate_expr_by_block: BTreeMap<u64, CExpr>,
    pub(crate) call_view_by_site: BTreeMap<(u64, usize), PreparedCallView>,
    pub(crate) call_result_facts_by_value: BTreeMap<ValueId, r2types::CallResultFact>,
    pub(crate) call_result_source_by_value: HashMap<ValueId, (u64, usize)>,
    pub(crate) call_result_source_by_name: HashMap<String, (u64, usize)>,
    pub(crate) switch_selector_value_by_block: BTreeMap<u64, ValueId>,
    pub(crate) switch_selector_expr_by_block: BTreeMap<u64, CExpr>,
    pub(crate) certified_rendering_required: bool,
    pub(crate) authorized_stack_owner_names: BTreeMap<i64, BTreeSet<String>>,
    pub(crate) authorized_stack_owner_names_by_object:
        BTreeMap<(r2ssa::ObjectId, i64), BTreeSet<String>>,
    pub(crate) certified_loop_carrier_values: BTreeSet<ValueId>,
}

pub(crate) struct PreparedSemanticViewInputs<'a> {
    pub(crate) prepared: &'a SsaArtifact,
    pub(crate) abi_arg_regs: &'a [String],
    pub(crate) stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub(crate) visible_bindings: &'a [VisibleBinding],
    pub(crate) param_register_aliases: &'a HashMap<String, String>,
    pub(crate) function_facts: &'a FunctionFacts,
    #[cfg(test)]
    pub(crate) certified_rendering_required: bool,
}

impl<'a> PreparedSemanticViewInputs<'a> {
    fn callee_resolution(&self) -> Option<&'a CalleeResolutionFacts> {
        self.function_facts.callee_resolution()
    }

    fn callsite_facts(&self) -> Option<&'a FunctionCallsiteFacts> {
        self.function_facts.callsites()
    }

    fn call_result_facts(&self) -> Option<&'a FunctionCallResultFacts> {
        self.function_facts.call_results()
    }

    fn call_render_facts(&self) -> Option<&'a r2types::FunctionCallRenderFacts> {
        self.function_facts.call_render()
    }

    fn control_facts(&self) -> Option<&'a r2types::FunctionControlFacts> {
        self.function_facts.control()
    }
}

impl PreparedSemanticView {
    pub(crate) fn build(inputs: PreparedSemanticViewInputs<'_>) -> Self {
        #[cfg(test)]
        let certified_rendering_required = inputs.certified_rendering_required;
        #[cfg(not(test))]
        let certified_rendering_required = false;
        let mut view = Self {
            param_alias_by_reg: inputs.param_register_aliases.clone(),
            certified_rendering_required,
            certified_loop_carrier_values: inputs
                .function_facts
                .render()
                .into_iter()
                .flat_map(r2types::FunctionRenderFacts::loop_carriers)
                .flat_map(|entity| match entity {
                    r2types::CertifiedEntity::LoopCarrier {
                        phi,
                        identity_values,
                        entries,
                        updates,
                        dominating_initializers,
                        ..
                    } => std::iter::once(*phi)
                        .chain(identity_values.iter().copied())
                        .chain(entries.iter().map(|edge| edge.value))
                        .chain(updates.iter().flat_map(|update| {
                            std::iter::once(update.value)
                                .chain(update.identity_values.iter().copied())
                        }))
                        .chain(dominating_initializers.iter().map(|edge| edge.value))
                        .collect::<Vec<_>>(),
                    _ => Vec::new(),
                })
                .collect(),
            ..Self::default()
        };
        for (rank, reg) in inputs.abi_arg_regs.iter().enumerate() {
            if let Some(alias) = inputs.param_register_aliases.get(reg) {
                view.param_rank_by_alias.insert(alias.clone(), rank);
                view.param_rank_by_alias
                    .insert(alias.to_ascii_lowercase(), rank);
            }
        }
        view.init_value_indexes(inputs.prepared);

        populate_stack_aliases(&mut view, &inputs);
        populate_stack_offsets(&mut view, inputs.prepared);
        overlay_param_home_stack_aliases(&mut view, &inputs);
        populate_authorized_stack_owner_names(&mut view, &inputs);
        populate_owner_exprs(&mut view, &inputs);
        populate_call_result_sources(&mut view, inputs.call_result_facts());
        populate_calls(&mut view, &inputs);
        populate_predicates(&mut view, &inputs);
        populate_switches(&mut view, &inputs);
        refresh_name_indexes(&mut view);

        view
    }

    pub(crate) fn stack_alias_for_offset(&self, offset: i64) -> Option<&StackAliasView> {
        self.stack_aliases_by_offset.get(&offset)
    }

    pub(crate) fn value_id_for_var(&self, var: &SSAVar) -> Option<ValueId> {
        self.value_id_by_var.get(var).copied()
    }

    pub(crate) fn var_for_value_id(&self, value_id: ValueId) -> Option<&SSAVar> {
        self.var_by_value_id.get(&value_id)
    }

    pub(crate) fn stack_offset_for_var(&self, var: &SSAVar) -> Option<i64> {
        self.value_id_for_var(var)
            .and_then(|value_id| self.stack_offset_by_value.get(&value_id).copied())
    }

    pub(crate) fn owner_expr_for_var(&self, var: &SSAVar) -> Option<&CExpr> {
        self.value_id_for_var(var)
            .and_then(|value_id| self.owner_expr_by_value.get(&value_id))
            .or_else(|| self.owner_expr_by_name.get(&var.display_name()))
    }

    #[cfg(test)]
    pub(crate) fn owner_expr_for_value_id(&self, value_id: ValueId) -> Option<&CExpr> {
        self.owner_expr_by_value.get(&value_id)
    }

    pub(crate) fn owner_expr_for_name(&self, name: &str) -> Option<&CExpr> {
        self.owner_expr_by_name.get(name)
    }

    pub(crate) fn predicate_expr_for_cond(&self, var: &SSAVar) -> Option<&CExpr> {
        self.value_id_for_var(var)
            .and_then(|value_id| self.predicate_expr_by_value.get(&value_id))
            .or_else(|| self.predicate_expr_by_name.get(&var.display_name()))
            .or_else(|| self.predicate_expr_by_name.get(&var.name))
    }

    #[allow(dead_code)]
    pub(crate) fn predicate_expr_for_value_id(&self, value_id: ValueId) -> Option<&CExpr> {
        self.predicate_expr_by_value.get(&value_id)
    }

    pub(crate) fn predicate_expr_for_name(&self, name: &str) -> Option<&CExpr> {
        self.predicate_expr_by_name.get(name)
    }

    pub(crate) fn branch_expr_for_block(&self, block_addr: u64) -> Option<&CExpr> {
        self.branch_predicate_expr_by_block.get(&block_addr)
    }

    pub(crate) fn switch_selector_expr_for_block(&self, block_addr: u64) -> Option<&CExpr> {
        self.switch_selector_expr_by_block.get(&block_addr)
    }

    pub(crate) fn call_view_for_site(&self, site: (u64, usize)) -> Option<&PreparedCallView> {
        self.call_view_by_site.get(&site)
    }

    pub(crate) fn authoritative_call_arg_expr_for_value(
        &self,
        site: (u64, usize),
        value: ValueId,
    ) -> Option<CExpr> {
        let call_view = self.call_view_for_site(site)?;
        call_view
            .authoritative_arg_values
            .iter()
            .position(|candidate| *candidate == value)
            .and_then(|index| call_view.authoritative_args.get(index).cloned())
    }

    pub(crate) fn call_result_source_for_var(&self, var: &SSAVar) -> Option<(u64, usize)> {
        self.value_id_for_var(var)
            .and_then(|value_id| self.call_result_source_by_value.get(&value_id).copied())
            .or_else(|| {
                self.call_result_source_by_name
                    .get(&var.display_name())
                    .copied()
            })
            .or_else(|| self.call_result_source_by_name.get(&var.name).copied())
    }

    pub(crate) fn call_result_source_for_name(&self, name: &str) -> Option<(u64, usize)> {
        self.call_result_source_by_name.get(name).copied()
    }

    #[allow(dead_code)]
    pub(crate) fn call_result_source_for_value_id(
        &self,
        value_id: ValueId,
    ) -> Option<(u64, usize)> {
        self.call_result_source_by_value.get(&value_id).copied()
    }

    fn init_value_indexes(&mut self, prepared: &SsaArtifact) {
        self.value_id_by_var.clear();
        self.var_by_value_id.clear();
        for value in &prepared.graph().values {
            self.value_id_by_var.insert(value.var.clone(), value.id);
            self.var_by_value_id.insert(value.id, value.var.clone());
        }
    }

    fn insert_stack_offset(&mut self, var: &SSAVar, offset: i64) {
        if let Some(value_id) = self.value_id_for_var(var) {
            self.stack_offset_by_value.insert(value_id, offset);
        }
    }

    fn insert_owner_expr(&mut self, var: &SSAVar, expr: CExpr) {
        if let Some(value_id) = self.value_id_for_var(var) {
            self.owner_expr_by_value.insert(value_id, expr);
        }
    }

    fn insert_predicate_expr(&mut self, var: &SSAVar, expr: CExpr) {
        if let Some(value_id) = self.value_id_for_var(var) {
            self.predicate_expr_by_value.insert(value_id, expr);
        }
    }

    fn stack_offset_entries(&self) -> Vec<(SSAVar, i64)> {
        self.stack_offset_by_value
            .iter()
            .filter_map(|(value_id, offset)| {
                self.var_for_value_id(*value_id)
                    .cloned()
                    .map(|var| (var, *offset))
            })
            .collect()
    }
}

fn prepared_var(prepared: &SsaArtifact, value_id: ValueId) -> Option<&SSAVar> {
    prepared.value_var(value_id)
}

fn bind_prepared_value_id(
    use_info: &mut UseInfo,
    view: &PreparedSemanticView,
    var: &SSAVar,
) -> Option<ValueId> {
    let value_id = view.value_id_for_var(var)?;
    use_info.bind_value_id(var, value_id)
}

fn bind_prepared_copy_ids(
    use_info: &mut UseInfo,
    view: &PreparedSemanticView,
    dst: &SSAVar,
    src: &SSAVar,
) -> Option<(ValueId, ValueId)> {
    let _ = bind_prepared_value_id(use_info, view, dst);
    let _ = bind_prepared_value_id(use_info, view, src);
    Some((
        use_info.exact_value_id_for_var(dst)?,
        use_info.exact_value_id_for_var(src)?,
    ))
}

fn exact_prepared_copy_provenance(
    src: &SSAVar,
    src_id: ValueId,
    stack_slot: Option<i64>,
) -> ValueProvenance {
    ValueProvenance {
        source: src.display_name(),
        source_value_id: Some(src_id),
        source_var: Some(src.clone()),
        stack_slot,
    }
}

fn prepared_call_site_tuple(
    prepared: &SsaArtifact,
    inst_id: r2ssa::InstId,
) -> Option<(u64, usize)> {
    prepared.inst_op_site(inst_id)
}

#[allow(dead_code)]
pub(crate) fn build_prepared_runtime_facts(
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) -> DecompilerFacts {
    let execution = r2ssa::SsaExecutionControl::default();
    let control =
        crate::DecompileWorkControl::new(&execution, crate::DecompileWorkPhase::Structuring);
    build_prepared_runtime_facts_with_control(blocks, env, prepared, view, control)
        .expect("default decompiler work control cannot stop")
}

pub(crate) fn build_prepared_runtime_facts_with_control(
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    control: crate::DecompileWorkControl<'_>,
) -> Result<DecompilerFacts, crate::DecompileExecutionStop> {
    control.poll()?;
    let mut use_info = UseInfo {
        type_hints: env.type_hints.clone(),
        ..UseInfo::default()
    };
    let mut flag_info = FlagInfo::default();
    let mut stack_info = StackInfo::default();

    seed_prepared_param_aliases(&mut use_info, blocks, env);
    seed_prepared_stack_facts(&mut use_info, &mut stack_info, prepared, view);
    collect_prepared_runtime_facts(&mut use_info, &mut flag_info, blocks, env, prepared, view);
    pin_prepared_loop_carried_phi_values(&mut use_info, prepared, view);
    pin_aliases_for_prepared_pinned_values(&mut use_info);
    populate_prepared_call_runtime_facts(&mut use_info, blocks, env, prepared, view);
    overlay_local_struct_semantics(&mut use_info, blocks, env, control)?;
    overlay_prepared_switch_roots(&mut use_info, prepared, view);
    populate_prepared_render_definitions(&mut use_info, blocks, env);

    control.poll()?;
    Ok(DecompilerFacts {
        use_info,
        ownership: SemanticOwnershipFacts::default(),
        flag_info,
        stack_info,
    })
}

fn pin_prepared_loop_carried_phi_values(
    use_info: &mut UseInfo,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) {
    for value in &view.certified_loop_carrier_values {
        if let Some(var) = prepared.value_var(*value) {
            pin_prepared_phi_materialized_var(use_info, var);
        }
    }
}

fn pin_prepared_phi_materialized_var(use_info: &mut UseInfo, var: &SSAVar) {
    if var.is_const() || var.is_temp() || is_cpu_flag(&var.name.to_ascii_lowercase()) {
        return;
    }
    let display = var.display_name();
    use_info.pinned.insert(display.clone());
    use_info.pinned.insert(display.to_ascii_lowercase());
}

fn pin_aliases_for_prepared_pinned_values(use_info: &mut UseInfo) {
    let mut aliases = Vec::new();
    for pinned in &use_info.pinned {
        if let Some(alias) = use_info.var_aliases.get(pinned)
            && !alias.trim().is_empty()
        {
            aliases.push(alias.clone());
        }
    }
    for alias in aliases {
        use_info.pinned.insert(alias);
    }
}

fn populate_prepared_render_definitions(
    use_info: &mut UseInfo,
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
) {
    for block in blocks {
        for op in &block.ops {
            let Some(dst) = op.dst() else {
                continue;
            };
            if !prepared_op_has_render_definition(op) {
                continue;
            }
            let expr = {
                let lower = LowerCtx {
                    string_literals: crate::analysis::lower::no_string_literals(),
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
                lower.op_to_expr(op)
            };
            if is_self_render_definition(dst, &expr) {
                continue;
            }
            if !prepared_render_definition_is_safe(&expr, env) {
                continue;
            }
            let key = dst.display_name();
            use_info
                .definitions
                .entry(key.clone())
                .or_insert_with(|| expr.clone());
            if let Some(value_id) = use_info.value_id_for_var(dst) {
                use_info
                    .definitions_by_value
                    .entry(value_id)
                    .or_insert_with(|| expr.clone());
            }
            use_info.formatted_defs.entry(key).or_insert(expr);
        }
    }
}

fn prepared_op_has_render_definition(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Copy { .. }
            | SSAOp::Load { .. }
            | SSAOp::IntAdd { .. }
            | SSAOp::IntSub { .. }
            | SSAOp::IntMult { .. }
            | SSAOp::IntDiv { .. }
            | SSAOp::IntSDiv { .. }
            | SSAOp::IntRem { .. }
            | SSAOp::IntSRem { .. }
            | SSAOp::IntAnd { .. }
            | SSAOp::IntOr { .. }
            | SSAOp::IntXor { .. }
            | SSAOp::IntLeft { .. }
            | SSAOp::IntRight { .. }
            | SSAOp::IntSRight { .. }
            | SSAOp::IntEqual { .. }
            | SSAOp::IntNotEqual { .. }
            | SSAOp::IntLess { .. }
            | SSAOp::IntLessEqual { .. }
            | SSAOp::IntSLess { .. }
            | SSAOp::IntSLessEqual { .. }
            | SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. }
            | SSAOp::IntCarry { .. }
            | SSAOp::IntSCarry { .. }
            | SSAOp::IntSBorrow { .. }
            | SSAOp::IntNegate { .. }
            | SSAOp::IntNot { .. }
            | SSAOp::BoolNot { .. }
            | SSAOp::BoolAnd { .. }
            | SSAOp::BoolOr { .. }
            | SSAOp::BoolXor { .. }
            | SSAOp::Piece { .. }
            | SSAOp::FloatAdd { .. }
            | SSAOp::FloatSub { .. }
            | SSAOp::FloatMult { .. }
            | SSAOp::FloatDiv { .. }
            | SSAOp::FloatNeg { .. }
            | SSAOp::FloatAbs { .. }
            | SSAOp::FloatSqrt { .. }
            | SSAOp::FloatEqual { .. }
            | SSAOp::FloatNotEqual { .. }
            | SSAOp::FloatLess { .. }
            | SSAOp::FloatLessEqual { .. }
            | SSAOp::Trunc { .. }
            | SSAOp::Int2Float { .. }
            | SSAOp::Float2Int { .. }
            | SSAOp::FloatCeil { .. }
            | SSAOp::FloatFloor { .. }
            | SSAOp::FloatRound { .. }
            | SSAOp::FloatNaN { .. }
            | SSAOp::Subpiece { .. }
            | SSAOp::FloatFloat { .. }
            | SSAOp::Cast { .. }
            | SSAOp::Select { .. }
            | SSAOp::PtrAdd { .. }
            | SSAOp::PtrSub { .. }
            | SSAOp::CallOther {
                output: Some(_),
                ..
            }
            | SSAOp::CpuId { .. }
    )
}

fn prepared_render_definition_is_safe(expr: &CExpr, env: &PassEnv<'_>) -> bool {
    let arg_regs = env
        .arg_regs
        .iter()
        .map(|reg| reg.to_ascii_lowercase())
        .collect::<HashSet<_>>();
    let caller_saved = env
        .caller_saved_regs
        .iter()
        .map(|reg| reg.to_ascii_lowercase())
        .collect::<HashSet<_>>();
    let sp = env.sp_name.to_ascii_lowercase();
    let fp = env.fp_name.to_ascii_lowercase();
    let ret = env.ret_reg_name.to_ascii_lowercase();
    let mut safe = true;
    expr.visit(&mut |node| {
        if matches!(
            node,
            CExpr::Deref(_)
                | CExpr::Subscript { .. }
                | CExpr::Member { .. }
                | CExpr::PtrMember { .. }
        ) {
            safe = false;
            return;
        }
        let CExpr::Var(name) = node else {
            return;
        };
        let lower = name.to_ascii_lowercase();
        let base = lower.split('_').next().unwrap_or(lower.as_str());
        if base == sp
            || base == fp
            || base == ret
            || arg_regs.contains(base)
            || caller_saved.contains(base)
            || is_temporary_or_memory_name(name)
        {
            safe = false;
        }
    });
    safe
}

fn is_self_render_definition(dst: &SSAVar, expr: &CExpr) -> bool {
    let dst_display = dst.display_name();
    let dst_rendered = if let Some(tmp_name) = SSAVarNameKind::strip_temporary_prefix(&dst.name) {
        let suffix = if dst.version > 0 {
            format!("_{}", dst.version)
        } else {
            String::new()
        };
        format!("t{}{}", tmp_name, suffix)
    } else if dst.version > 0 {
        format!("{}_{}", dst.name.to_ascii_lowercase(), dst.version)
    } else {
        dst.name.to_ascii_lowercase()
    };
    matches!(expr, CExpr::Var(name) if name == &dst_display || name.eq_ignore_ascii_case(&dst_rendered))
}

fn overlay_local_struct_semantics(
    use_info: &mut UseInfo,
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    control: crate::DecompileWorkControl<'_>,
) -> Result<(), crate::DecompileExecutionStop> {
    let semantic = UseInfo::analyze_for_local_struct_accesses_with_control(blocks, env, control)?;
    for (name, value) in semantic.semantic_values {
        control.poll()?;
        // Prepared ValueId-bound facts are canonical; local struct inference is heuristic.
        if use_info.value_ids_by_name.contains_key(&name) {
            continue;
        }
        let should_replace = match use_info.semantic_values.get(&name) {
            None => true,
            Some(SemanticValue::Address(_) | SemanticValue::Load { .. }) => false,
            Some(_) => matches!(
                value,
                SemanticValue::Address(_) | SemanticValue::Load { .. }
            ),
        };
        if should_replace {
            use_info.semantic_values.insert(name, value);
        }
    }
    for (name, fact) in semantic.ptr_members {
        control.poll()?;
        use_info.ptr_members.entry(name).or_insert(fact);
    }
    Ok(())
}

fn populate_stack_aliases(
    view: &mut PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
) {
    for binding in inputs.visible_bindings {
        let Some(slot) = binding.stack_slot.as_ref() else {
            continue;
        };
        let name = binding.name.trim();
        if name.is_empty() {
            continue;
        }
        let binding_arg_alias = prepared_binding_arg_alias(
            binding,
            inputs.visible_bindings,
            inputs.param_register_aliases,
        );
        let offset = prepared_stack_slot_offset(slot);
        let entry = view
            .stack_aliases_by_offset
            .entry(offset)
            .or_insert_with(|| StackAliasView {
                visible_name: name.to_string(),
                arg_alias: binding_arg_alias.clone(),
                binding_kind: Some(binding.kind),
            });
        if entry.visible_name.is_empty() {
            entry.visible_name = name.to_string();
        }
        if entry.arg_alias.is_none() {
            entry.arg_alias = binding_arg_alias;
        }
        if entry.binding_kind.is_none() {
            entry.binding_kind = Some(binding.kind);
        }
    }

    for (slot_key, slot) in inputs.stack_slots {
        let offset = prepared_stack_slot_offset(slot_key);
        let name = prepared_stack_visible_name(slot);
        let visible_name = name.clone().unwrap_or_else(|| synthetic_stack_name(offset));
        let entry = view
            .stack_aliases_by_offset
            .entry(offset)
            .or_insert_with(|| StackAliasView {
                visible_name: visible_name.clone(),
                arg_alias: prepared_stack_arg_alias(slot),
                binding_kind: None,
            });
        if entry.visible_name.is_empty() {
            entry.visible_name = visible_name;
        }
        if entry.arg_alias.is_none() {
            entry.arg_alias = prepared_stack_arg_alias(slot);
        }
    }
}

fn prepared_stack_slot_offset(slot: &StackSlotKey) -> i64 {
    match slot.base {
        ExternalStackBase::FramePointer => slot.offset.saturating_abs().saturating_neg(),
        _ => slot.offset,
    }
}

fn record_authorized_stack_owner_name(
    view: &mut PreparedSemanticView,
    function_facts: &FunctionFacts,
    offset: i64,
    name: &str,
) {
    let name = name.trim();
    for object in function_facts
        .render_facts()
        .stack_slots()
        .filter_map(|(object, _, slot_offset, _)| (slot_offset == offset).then_some(object))
    {
        if let Some(authorization) =
            function_facts.authorized_stack_slot_owner_render(object, offset, name)
        {
            view.authorized_stack_owner_names_by_object
                .entry((authorization.object, authorization.offset))
                .or_default()
                .insert(name.to_ascii_lowercase());
        }
    }
    if function_facts
        .authorized_stack_slot_owner_render_by_offset(offset, name)
        .is_some()
    {
        view.authorized_stack_owner_names
            .entry(offset)
            .or_default()
            .insert(name.to_ascii_lowercase());
    }
}

fn populate_authorized_stack_owner_names(
    view: &mut PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
) {
    let function_facts = inputs.function_facts;
    let alias_candidates: Vec<_> = view
        .stack_aliases_by_offset
        .iter()
        .map(|(offset, alias)| (*offset, alias.visible_name.clone()))
        .collect();
    for (offset, name) in alias_candidates {
        record_authorized_stack_owner_name(view, function_facts, offset, &name);
    }
    for binding in inputs.visible_bindings {
        let Some(slot) = binding.stack_slot.as_ref() else {
            continue;
        };
        if !matches!(
            binding.kind,
            VisibleBindingKind::Param | VisibleBindingKind::Local | VisibleBindingKind::StackObject
        ) {
            continue;
        }
        record_authorized_stack_owner_name(
            view,
            function_facts,
            prepared_stack_slot_offset(slot),
            &binding.name,
        );
    }
    for (slot_key, slot) in inputs.stack_slots {
        if !matches!(
            slot.role,
            ExternalStackSlotRole::Local | ExternalStackSlotRole::StackArg
        ) {
            continue;
        }
        record_authorized_stack_owner_name(
            view,
            function_facts,
            prepared_stack_slot_offset(slot_key),
            &slot.name,
        );
    }
}

fn prepared_binding_arg_alias(
    binding: &VisibleBinding,
    visible_bindings: &[VisibleBinding],
    param_register_aliases: &HashMap<String, String>,
) -> Option<String> {
    match binding.kind {
        VisibleBindingKind::Param => binding
            .source_reg
            .as_deref()
            .and_then(|reg| param_register_aliases.get(&reg.to_ascii_lowercase()))
            .cloned()
            .or_else(|| {
                let name = binding.name.trim();
                (!name.is_empty()).then(|| name.to_string())
            }),
        VisibleBindingKind::HiddenHome => binding
            .source_reg
            .as_deref()
            .and_then(|reg| param_register_aliases.get(&reg.to_ascii_lowercase()))
            .cloned()
            .or_else(|| {
                binding.param_index.and_then(|idx| {
                    visible_bindings.iter().find_map(|candidate| {
                        (candidate.kind == VisibleBindingKind::Param
                            && candidate.param_index == Some(idx)
                            && !candidate.name.trim().is_empty())
                        .then(|| candidate.name.trim().to_string())
                    })
                })
            }),
        _ => None,
    }
}

fn refresh_name_indexes(view: &mut PreparedSemanticView) {
    view.owner_expr_by_name = view
        .owner_expr_by_value
        .iter()
        .filter_map(|(value_id, expr)| {
            view.var_for_value_id(*value_id)
                .map(|var| (var.display_name(), expr.clone()))
        })
        .collect();
    view.predicate_expr_by_name = view
        .predicate_expr_by_value
        .iter()
        .filter_map(|(value_id, expr)| {
            view.var_for_value_id(*value_id)
                .map(|var| (var.display_name(), expr.clone()))
        })
        .collect();
    let mut call_result_source_by_name = HashMap::new();
    for (value_id, site) in &view.call_result_source_by_value {
        let Some(var) = view.var_for_value_id(*value_id) else {
            continue;
        };
        call_result_source_by_name.insert(var.display_name(), *site);
        call_result_source_by_name.insert(var.name.clone(), *site);
    }
    view.call_result_source_by_name = call_result_source_by_name;
}

fn overlay_param_home_stack_aliases(
    view: &mut PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
) {
    for block in inputs.prepared.function().blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            let SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr,
                val,
            } = op
            else {
                continue;
            };
            let Some(offset) = view
                .stack_offset_for_var(addr)
                .or_else(|| stack_offset_for_value(inputs.prepared, addr))
            else {
                continue;
            };
            let Some(arg_alias) =
                param_alias_for_store_value(inputs.param_register_aliases, block, op_idx, val)
            else {
                continue;
            };
            let entry = view
                .stack_aliases_by_offset
                .entry(offset)
                .or_insert_with(|| StackAliasView {
                    visible_name: synthetic_stack_name(offset),
                    arg_alias: Some(arg_alias.clone()),
                    binding_kind: None,
                });
            if entry.arg_alias.is_none() {
                entry.arg_alias = Some(arg_alias);
            }
        }
    }
}

fn param_alias_for_store_value(
    param_register_aliases: &HashMap<String, String>,
    block: &r2ssa::FunctionSSABlock,
    before_idx: usize,
    value: &SSAVar,
) -> Option<String> {
    let mut current = value;
    for _ in 0..8 {
        if let Some(alias) = param_alias_for_var(param_register_aliases, current) {
            return Some(alias);
        }
        let next = block.ops[..before_idx]
            .iter()
            .rev()
            .find_map(|op| match op {
                SSAOp::Copy { dst, src }
                | SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src }
                | SSAOp::Trunc { dst, src }
                | SSAOp::Cast { dst, src }
                | SSAOp::Subpiece { dst, src, .. }
                    if dst == current =>
                {
                    Some(src)
                }
                _ => None,
            })?;
        if next == current {
            return None;
        }
        current = next;
    }
    None
}

fn populate_stack_offsets(view: &mut PreparedSemanticView, prepared: &SsaArtifact) {
    let Some(prep) = prepared.function().decompile_prep_facts() else {
        return;
    };
    for var in prep.stack_address_roots.keys() {
        if let Some(offset) = prep.stack_address_root_of(var).map(|root| root.offset) {
            view.insert_stack_offset(var, offset);
        }
    }
    for (key, object_id) in &prepared.objects().value_objects {
        if key.space != r2il::SpaceId::Ram {
            continue;
        }
        if let Some(object) = prepared.objects().object(*object_id)
            && let Some(offset) = stack_offset_for_object_kind(&object.kind)
            && let Some(value) = prepared_var(prepared, key.value)
        {
            view.insert_stack_offset(value, offset);
        }
    }
}

fn populate_owner_exprs(view: &mut PreparedSemanticView, inputs: &PreparedSemanticViewInputs<'_>) {
    let prepared = inputs.prepared;
    let mut producer_by_dst = HashMap::<SSAVar, &SSAOp>::new();
    for block in prepared.function().blocks() {
        for op in &block.ops {
            if let Some(dst) = op.dst() {
                producer_by_dst.insert(dst.clone(), op);
            }
        }
    }

    for (value, offset) in view.stack_offset_entries() {
        if !is_prepared_stack_address_carrier(prepared, &value) {
            continue;
        }
        let Some(alias) = preferred_stack_alias_name(view, offset) else {
            continue;
        };
        if !alias.is_empty() && prepared_stack_owner_recovery_allowed(view, offset, &alias) {
            view.insert_owner_expr(&value, CExpr::AddrOf(Box::new(CExpr::Var(alias.clone()))));
        }
    }

    for block in prepared.function().blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            if let SSAOp::Load {
                dst,
                space: r2il::SpaceId::Ram,
                addr,
            } = op
            {
                let derived = prepared_direct_stack_load_offset(prepared, view, addr)
                    .and_then(|offset| {
                        local_store_owner_expr_for_offset(view, prepared, block, op_idx, offset)
                            .map(|expr| (expr, Some(offset)))
                            .or_else(|| {
                                prepared_stack_alias_expr_for_offset(view, offset)
                                    .map(|expr| (expr, Some(offset)))
                            })
                    })
                    .or_else(|| {
                        prepared
                            .memory_uses_for_op_site(block.addr, op_idx)
                            .and_then(|facts| {
                                let mut ram = facts
                                    .iter()
                                    .filter(|fact| fact.location.space == r2il::SpaceId::Ram);
                                let first = ram.next()?;
                                ram.next().is_none().then_some(first)
                            })
                            .and_then(|fact| {
                                let offset = fact.location.address.exact_offset()?;
                                alias_for_memory_location(view, &fact.location)
                                    .map(|alias| (CExpr::Var(alias), Some(offset)))
                            })
                    })
                    .or_else(|| {
                        prepared_load_access_expr_for_addr(block, view, addr, dst.size)
                            .map(|expr| (expr, None))
                    });
                let Some((expr, offset)) = derived else {
                    continue;
                };
                view.insert_owner_expr(dst, expr);
                if let Some(offset) = offset
                    && view.stack_offset_for_var(dst) != Some(offset)
                {
                    view.insert_stack_offset(dst, offset);
                }
            }
        }
    }

    for _ in 0..4 {
        let mut changed = false;

        for block in prepared.function().blocks() {
            for op in &block.ops {
                match op {
                    SSAOp::Copy { dst, src }
                    | SSAOp::IntZExt { dst, src }
                    | SSAOp::IntSExt { dst, src }
                    | SSAOp::Trunc { dst, src }
                    | SSAOp::Cast { dst, src, .. }
                    | SSAOp::Subpiece { dst, src, .. } => {
                        if let Some(expr) = view
                            .owner_expr_for_var(src)
                            .cloned()
                            .or_else(|| scalar_owner_expr_for_value(view, src, src.size))
                            && view.owner_expr_for_var(dst) != Some(&expr)
                        {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                        if let Some(offset) = view.stack_offset_for_var(src)
                            && view.stack_offset_for_var(dst) != Some(offset)
                        {
                            view.insert_stack_offset(dst, offset);
                            changed = true;
                        }
                    }
                    SSAOp::IntSub { dst, a, b } => {
                        let compare_width = a.size.max(b.size);
                        let derived =
                            prepared_binary_owner_expr(view, BinaryOp::Sub, a, b, compare_width)
                                .or_else(|| {
                                    prepared_address_owner_expr_for_value(view, a, compare_width)
                                        .zip(prepared_address_owner_expr_for_value(
                                            view,
                                            b,
                                            compare_width,
                                        ))
                                        .map(|(lhs, rhs)| {
                                            prepared_simplify_binary_expr(
                                                view,
                                                BinaryOp::Sub,
                                                lhs,
                                                rhs,
                                            )
                                        })
                                });
                        if let Some(expr) = derived
                            && view.owner_expr_for_var(dst) != Some(&expr)
                        {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                    }
                    SSAOp::IntLeft { dst, a, b } => {
                        let compare_width = a.size.max(b.size);
                        let derived =
                            prepared_binary_owner_expr(view, BinaryOp::Shl, a, b, compare_width)
                                .or_else(|| {
                                    prepared_scaled_index_owner_expr(view, a, compare_width)
                                        .zip(scalar_owner_expr_for_value(view, b, compare_width))
                                        .map(|(lhs, rhs)| {
                                            prepared_simplify_binary_expr(
                                                view,
                                                BinaryOp::Shl,
                                                lhs,
                                                rhs,
                                            )
                                        })
                                });
                        if let Some(expr) = derived
                            && view.owner_expr_for_var(dst) != Some(&expr)
                        {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                    }
                    SSAOp::IntMult { dst, a, b } => {
                        let compare_width = a.size.max(b.size);
                        let derived =
                            prepared_binary_owner_expr(view, BinaryOp::Mul, a, b, compare_width)
                                .or_else(|| {
                                    prepared_scaled_index_owner_expr(view, a, compare_width)
                                        .zip(prepared_scaled_index_owner_expr(
                                            view,
                                            b,
                                            compare_width,
                                        ))
                                        .map(|(lhs, rhs)| {
                                            prepared_simplify_binary_expr(
                                                view,
                                                BinaryOp::Mul,
                                                lhs,
                                                rhs,
                                            )
                                        })
                                });
                        if let Some(expr) = derived
                            && view.owner_expr_for_var(dst) != Some(&expr)
                        {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                    }
                    SSAOp::IntAdd { dst, a, b } => {
                        let compare_width = a.size.max(b.size);
                        let derived =
                            prepared_binary_owner_expr(view, BinaryOp::Add, a, b, compare_width)
                                .or_else(|| {
                                    prepared_address_owner_expr_for_value(view, a, compare_width)
                                        .zip(prepared_address_owner_expr_for_value(
                                            view,
                                            b,
                                            compare_width,
                                        ))
                                        .map(|(lhs, rhs)| {
                                            prepared_simplify_binary_expr(
                                                view,
                                                BinaryOp::Add,
                                                lhs,
                                                rhs,
                                            )
                                        })
                                });
                        if let Some(expr) = derived
                            && view.owner_expr_for_var(dst) != Some(&expr)
                        {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                    }
                    SSAOp::IntDiv { dst, a, b } | SSAOp::IntRem { dst, a, b } => {
                        let op = if matches!(op, SSAOp::IntDiv { .. }) {
                            BinaryOp::Div
                        } else {
                            BinaryOp::Mod
                        };
                        let compare_width = a.size.max(b.size);
                        if let Some(expr) =
                            prepared_binary_owner_expr(view, op, a, b, compare_width)
                            && view.owner_expr_for_var(dst) != Some(&expr)
                        {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                    }
                    SSAOp::IntSDiv { dst, a, b } | SSAOp::IntSRem { dst, a, b } => {
                        let op = if matches!(op, SSAOp::IntSDiv { .. }) {
                            BinaryOp::Div
                        } else {
                            BinaryOp::Mod
                        };
                        let compare_width = a.size.max(b.size);
                        let derived = prepared_signed_dividend_expr(view, &producer_by_dst, a)
                            .zip(scalar_owner_expr_for_value(view, b, compare_width))
                            .map(|(lhs, rhs)| prepared_simplify_binary_expr(view, op, lhs, rhs))
                            .or_else(|| prepared_binary_owner_expr(view, op, a, b, compare_width));
                        if let Some(expr) = derived
                            && view.owner_expr_for_var(dst) != Some(&expr)
                        {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                    }
                    SSAOp::IntAnd { dst, a, b }
                    | SSAOp::IntOr { dst, a, b }
                    | SSAOp::IntXor { dst, a, b } => {
                        let op = match op {
                            SSAOp::IntAnd { .. } => BinaryOp::BitAnd,
                            SSAOp::IntOr { .. } => BinaryOp::BitOr,
                            SSAOp::IntXor { .. } => BinaryOp::BitXor,
                            _ => unreachable!(),
                        };
                        let compare_width = a.size.max(b.size);
                        if let Some(expr) =
                            prepared_binary_owner_expr(view, op, a, b, compare_width)
                            && view.owner_expr_for_var(dst) != Some(&expr)
                        {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        if !changed {
            break;
        }
    }

    refine_load_owner_exprs(view, inputs);
}

fn refine_load_owner_exprs(
    view: &mut PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
) {
    let prepared = inputs.prepared;
    for block in prepared.function().blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            let SSAOp::Load {
                dst,
                space: r2il::SpaceId::Ram,
                addr,
            } = op
            else {
                continue;
            };
            let candidate = prepared_direct_stack_load_offset(prepared, view, addr)
                .and_then(|offset| {
                    local_store_owner_expr_for_offset(view, prepared, block, op_idx, offset)
                        .map(|expr| (expr, Some(offset)))
                        .or_else(|| {
                            prepared_stack_alias_expr_for_offset(view, offset)
                                .map(|expr| (expr, Some(offset)))
                        })
                })
                .or_else(|| {
                    prepared
                        .memory_uses_for_op_site(block.addr, op_idx)
                        .and_then(|facts| {
                            let mut ram = facts
                                .iter()
                                .filter(|fact| fact.location.space == r2il::SpaceId::Ram);
                            let first = ram.next()?;
                            ram.next().is_none().then_some(first)
                        })
                        .and_then(|fact| {
                            let offset = fact.location.address.exact_offset()?;
                            alias_for_memory_location(view, &fact.location)
                                .map(|alias| (CExpr::Var(alias), Some(offset)))
                        })
                })
                .or_else(|| {
                    prepared_load_access_expr_for_addr(block, view, addr, dst.size)
                        .map(|expr| (expr, None))
                });
            let Some((candidate_expr, candidate_offset)) = candidate else {
                continue;
            };
            let should_replace = view.owner_expr_for_var(dst).is_none_or(|current| {
                prepared_load_owner_candidate_should_replace(current, &candidate_expr)
            });
            if should_replace {
                view.insert_owner_expr(dst, candidate_expr);
                if let Some(candidate_offset) = candidate_offset
                    && view.stack_offset_for_var(dst) != Some(candidate_offset)
                {
                    view.insert_stack_offset(dst, candidate_offset);
                }
            }
        }
    }
}

fn prepared_load_owner_candidate_should_replace(current: &CExpr, candidate: &CExpr) -> bool {
    current != candidate
        && ((prepared_expr_is_generic_scalar_alias(current)
            && !prepared_expr_is_generic_scalar_alias(candidate))
            || (prepared_expr_is_plain_visible_alias(current)
                && prepared_expr_is_structured_load_access(candidate)))
}

fn prepared_expr_is_generic_scalar_alias(expr: &CExpr) -> bool {
    match expr {
        CExpr::Var(name) => is_generic_prepared_stack_alias(name) || name.ends_with("_home"),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            prepared_expr_is_generic_scalar_alias(inner)
        }
        CExpr::Binary { left, right, .. } => {
            prepared_expr_is_generic_scalar_alias(left)
                && prepared_expr_is_generic_scalar_alias(right)
        }
        _ => false,
    }
}

fn prepared_expr_is_plain_visible_alias(expr: &CExpr) -> bool {
    matches!(prepared_strip_expr_wrappers(expr), CExpr::Var(_))
}

fn prepared_expr_is_structured_load_access(expr: &CExpr) -> bool {
    matches!(
        prepared_strip_expr_wrappers(expr),
        CExpr::Deref(_) | CExpr::Subscript { .. } | CExpr::Member { .. } | CExpr::PtrMember { .. }
    )
}

fn prepared_strip_expr_wrappers(mut expr: &CExpr) -> &CExpr {
    loop {
        match expr {
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => expr = inner,
            _ => return expr,
        }
    }
}

fn prepared_expr_is_direct_stack_address(expr: &CExpr) -> bool {
    matches!(prepared_strip_expr_wrappers(expr), CExpr::AddrOf(_))
}

fn prepared_direct_stack_load_offset(
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    addr: &SSAVar,
) -> Option<i64> {
    let offset = view
        .stack_offset_for_var(addr)
        .or_else(|| stack_offset_for_value(prepared, addr))?;
    prepared
        .function()
        .decompile_prep_facts()
        .and_then(|facts| facts.stack_address_root_of(addr))
        .map(|_| offset)
        .or_else(|| {
            view.owner_expr_for_var(addr)
                .is_some_and(prepared_expr_is_direct_stack_address)
                .then_some(offset)
        })
}

fn prepared_load_access_expr_for_addr(
    block: &r2ssa::FunctionSSABlock,
    view: &PreparedSemanticView,
    addr: &SSAVar,
    elem_size: u32,
) -> Option<CExpr> {
    let addr_expr = authoritative_scalar_expr_for_value(block, view, addr, 0)
        .or_else(|| scalar_owner_expr_for_value(view, addr, addr.size))
        .or_else(|| view.owner_expr_for_var(addr).cloned())?;
    prepared_load_access_expr_from_visible_addr(addr_expr, elem_size)
}

fn prepared_load_access_expr_from_visible_addr(expr: CExpr, elem_size: u32) -> Option<CExpr> {
    let elem_size = i64::from(elem_size.max(1));

    fn literal_i64(expr: &CExpr) -> Option<i64> {
        match expr {
            CExpr::IntLit(value) => Some(*value),
            CExpr::UIntLit(value) => (*value <= i64::MAX as u64).then_some(*value as i64),
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => literal_i64(inner),
            _ => None,
        }
    }

    match expr {
        CExpr::AddrOf(inner) => Some(*inner),
        CExpr::Paren(inner) => {
            prepared_load_access_expr_from_visible_addr(*inner, elem_size as u32)
        }
        CExpr::Cast { expr: inner, .. } => {
            prepared_load_access_expr_from_visible_addr(*inner, elem_size as u32)
        }
        CExpr::Binary {
            op: BinaryOp::Add,
            left,
            right,
        } => {
            if let Some(offset) = literal_i64(right.as_ref())
                && offset % elem_size == 0
            {
                let index = offset / elem_size;
                return Some(if index == 0 {
                    CExpr::deref(*left)
                } else {
                    CExpr::subscript(*left, CExpr::IntLit(index))
                });
            }
            if let Some(offset) = literal_i64(left.as_ref())
                && offset % elem_size == 0
            {
                let index = offset / elem_size;
                return Some(if index == 0 {
                    CExpr::deref(*right)
                } else {
                    CExpr::subscript(*right, CExpr::IntLit(index))
                });
            }
            Some(CExpr::deref(CExpr::binary(BinaryOp::Add, *left, *right)))
        }
        CExpr::Binary {
            op: BinaryOp::Sub,
            left,
            right,
        } => {
            if let Some(offset) = literal_i64(right.as_ref())
                && offset % elem_size == 0
            {
                let index = -(offset / elem_size);
                return Some(if index == 0 {
                    CExpr::deref(*left)
                } else {
                    CExpr::subscript(*left, CExpr::IntLit(index))
                });
            }
            Some(CExpr::deref(CExpr::binary(BinaryOp::Sub, *left, *right)))
        }
        other => Some(CExpr::deref(other)),
    }
}

fn populate_call_result_sources(
    view: &mut PreparedSemanticView,
    call_result_facts: Option<&FunctionCallResultFacts>,
) {
    let Some(call_result_facts) = call_result_facts else {
        return;
    };
    for cert in call_result_facts.by_value.values() {
        view.call_result_facts_by_value
            .insert(cert.value, cert.clone());
        view.call_result_source_by_value.insert(
            cert.value,
            (cert.callsite.block_addr, cert.callsite.op_index),
        );
    }
}

fn populate_predicates(view: &mut PreparedSemanticView, inputs: &PreparedSemanticViewInputs<'_>) {
    view.predicate_expr_by_value.clear();
    view.branch_predicate_expr_by_block.clear();

    let Some(control_facts) = inputs.control_facts() else {
        return;
    };

    for predicate in control_facts.branch_predicates.values() {
        let Some(compare) = predicate.comparison.as_ref() else {
            continue;
        };
        let Some(lhs_var) = prepared_var(inputs.prepared, compare.lhs) else {
            continue;
        };
        let Some(rhs_var) = prepared_var(inputs.prepared, compare.rhs) else {
            continue;
        };
        let compare_width = lhs_var.size.max(rhs_var.size);
        let lhs = expr_for_compare_operand_with_width(inputs, lhs_var.clone(), view, compare_width);
        let rhs = expr_for_compare_operand_with_width(inputs, rhs_var.clone(), view, compare_width);
        let expr = CExpr::binary(binary_op_for_compare(compare.kind), lhs, rhs);
        let Some(cond_var) = prepared_var(inputs.prepared, predicate.condition) else {
            continue;
        };
        view.insert_predicate_expr(cond_var, expr.clone());
        view.branch_predicate_expr_by_block
            .insert(predicate.block_addr, expr);
    }

    populate_derived_predicates(view, inputs);
}

fn populate_derived_predicates(
    view: &mut PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
) {
    for _ in 0..4 {
        let mut changed = false;

        for block in inputs.prepared.function().blocks() {
            for op in &block.ops {
                let Some(dst) = op.dst() else {
                    continue;
                };
                if view.predicate_expr_for_cond(dst).is_some() {
                    continue;
                }

                let derived = match op {
                    SSAOp::Copy { src, .. }
                    | SSAOp::IntZExt { src, .. }
                    | SSAOp::IntSExt { src, .. }
                    | SSAOp::Trunc { src, .. }
                    | SSAOp::Cast { src, .. }
                    | SSAOp::Subpiece { src, .. } => view.predicate_expr_for_cond(src).cloned(),
                    SSAOp::BoolNot { src, .. } => view
                        .predicate_expr_for_cond(src)
                        .cloned()
                        .map(|expr| CExpr::unary(UnaryOp::Not, expr)),
                    SSAOp::BoolAnd { a, b, .. } => {
                        boolean_expr_for_sources(view, inputs, a, b, BinaryOp::And)
                    }
                    SSAOp::BoolOr { a, b, .. } => {
                        boolean_expr_for_sources(view, inputs, a, b, BinaryOp::Or)
                    }
                    SSAOp::BoolXor { a, b, .. } => {
                        boolean_expr_for_sources(view, inputs, a, b, BinaryOp::BitXor)
                    }
                    SSAOp::IntEqual { a, b, .. } => {
                        compare_expr_for_sources(view, inputs, a, b, BinaryOp::Eq)
                    }
                    SSAOp::IntNotEqual { a, b, .. } => {
                        compare_expr_for_sources(view, inputs, a, b, BinaryOp::Ne)
                    }
                    SSAOp::IntLess { a, b, .. } | SSAOp::IntSLess { a, b, .. } => {
                        compare_expr_for_sources(view, inputs, a, b, BinaryOp::Lt)
                    }
                    SSAOp::IntLessEqual { a, b, .. } | SSAOp::IntSLessEqual { a, b, .. } => {
                        compare_expr_for_sources(view, inputs, a, b, BinaryOp::Le)
                    }
                    _ => None,
                };

                if let Some(expr) = derived {
                    view.insert_predicate_expr(dst, expr);
                    changed = true;
                }
            }
        }

        if !changed {
            break;
        }
    }

    for block in inputs.prepared.function().blocks() {
        let Some(cond) = block.ops.iter().rev().find_map(|op| match op {
            SSAOp::CBranch { cond, .. } => Some(cond),
            _ => None,
        }) else {
            continue;
        };
        if let Some(expr) = view.predicate_expr_for_cond(cond).cloned() {
            view.branch_predicate_expr_by_block.insert(block.addr, expr);
        }
    }
}

fn boolean_expr_for_sources(
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    lhs: &SSAVar,
    rhs: &SSAVar,
    op: BinaryOp,
) -> Option<CExpr> {
    let lhs = predicate_expr_for_operand(view, inputs, lhs)?;
    let rhs = predicate_expr_for_operand(view, inputs, rhs)?;
    Some(CExpr::binary(op, lhs, rhs))
}

fn compare_expr_for_sources(
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    lhs: &SSAVar,
    rhs: &SSAVar,
    op: BinaryOp,
) -> Option<CExpr> {
    if let Some(expr) = reconstruct_zero_compare_from_def(view, inputs, lhs, rhs, op, 0) {
        return Some(expr);
    }
    if let Some(expr) = reconstruct_zero_compare_from_def(view, inputs, rhs, lhs, op, 0) {
        return Some(expr);
    }

    let compare_width = lhs.size.max(rhs.size);
    let lhs = expr_for_compare_operand_with_width(inputs, lhs.clone(), view, compare_width);
    let rhs = expr_for_compare_operand_with_width(inputs, rhs.clone(), view, compare_width);
    Some(CExpr::binary(op, lhs, rhs))
}

fn reconstruct_zero_compare_from_def(
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    candidate: &SSAVar,
    zero: &SSAVar,
    op: BinaryOp,
    depth: u32,
) -> Option<CExpr> {
    if depth > 8 || !matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
        return None;
    }

    let zero = compare_style_operand_expr(zero, candidate.size.max(zero.size))?;
    if !matches!(zero, CExpr::IntLit(0) | CExpr::UIntLit(0)) {
        return None;
    }

    reconstruct_zero_compare_from_nonzero_def(view, inputs, candidate, op, depth)
}

fn reconstruct_zero_compare_from_nonzero_def(
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    candidate: &SSAVar,
    op: BinaryOp,
    depth: u32,
) -> Option<CExpr> {
    if depth > 8 || !matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
        return None;
    }

    let (block_addr, DefLocation::Op(op_idx)) = inputs.prepared.function().find_def(candidate)?
    else {
        return None;
    };
    let block = inputs.prepared.function().get_block(block_addr)?;
    let def = block.ops.get(op_idx)?;

    match def {
        SSAOp::Copy { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::Subpiece { src, .. } => {
            reconstruct_zero_compare_from_nonzero_def(view, inputs, src, op, depth + 1)
        }
        SSAOp::IntSub { a, b, .. } => {
            let compare_width = a.size.max(b.size);
            let lhs = expr_for_compare_operand_with_width(inputs, a.clone(), view, compare_width);
            let rhs = expr_for_compare_operand_with_width(inputs, b.clone(), view, compare_width);
            Some(CExpr::binary(op, lhs, rhs))
        }
        SSAOp::IntAnd { a, b, .. } if a == b => {
            let lhs = expr_for_compare_operand_with_width(inputs, a.clone(), view, a.size);
            Some(CExpr::binary(op, lhs, CExpr::IntLit(0)))
        }
        _ => None,
    }
}

fn predicate_expr_for_operand(
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    var: &SSAVar,
) -> Option<CExpr> {
    predicate_expr_for_operand_with_depth(view, inputs, var, 0)
}

fn predicate_expr_for_operand_with_depth(
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    var: &SSAVar,
    depth: u32,
) -> Option<CExpr> {
    fn is_flag_name(name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        matches!(
            lower.split('_').next(),
            Some("cf" | "zf" | "sf" | "of" | "pf")
        )
    }

    if depth > 8 {
        return None;
    }

    if let Some(expr) = view.predicate_expr_for_cond(var).cloned() {
        return Some(expr);
    }
    if var.is_const() {
        return Some(compare_const_to_expr(var));
    }
    if is_flag_name(&var.name) {
        if let Some(expr) = compare_def_expr_for_flag_operand(view, inputs, var, depth + 1) {
            return Some(expr);
        }
        return Some(CExpr::Var(var.display_name()));
    }
    let expr = expr_for_compare_operand(inputs, var.clone(), view);
    (!matches!(expr, CExpr::Var(ref name) if name == &var.display_name())).then_some(expr)
}

fn compare_def_expr_for_flag_operand(
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    var: &SSAVar,
    depth: u32,
) -> Option<CExpr> {
    if depth > 8 {
        return None;
    }

    let (block_addr, DefLocation::Op(op_idx)) = inputs.prepared.function().find_def(var)? else {
        return None;
    };
    let block = inputs.prepared.function().get_block(block_addr)?;
    let op = block.ops.get(op_idx)?;

    match op {
        SSAOp::Copy { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::Subpiece { src, .. } => {
            predicate_expr_for_operand_with_depth(view, inputs, src, depth + 1)
        }
        SSAOp::BoolNot { src, .. } => {
            predicate_expr_for_operand_with_depth(view, inputs, src, depth + 1)
                .map(|expr| CExpr::unary(UnaryOp::Not, expr))
        }
        SSAOp::BoolAnd { a, b, .. } => {
            let lhs = predicate_expr_for_operand_with_depth(view, inputs, a, depth + 1)?;
            let rhs = predicate_expr_for_operand_with_depth(view, inputs, b, depth + 1)?;
            Some(CExpr::binary(BinaryOp::And, lhs, rhs))
        }
        SSAOp::BoolOr { a, b, .. } => {
            let lhs = predicate_expr_for_operand_with_depth(view, inputs, a, depth + 1)?;
            let rhs = predicate_expr_for_operand_with_depth(view, inputs, b, depth + 1)?;
            Some(CExpr::binary(BinaryOp::Or, lhs, rhs))
        }
        SSAOp::BoolXor { a, b, .. } => {
            let lhs = predicate_expr_for_operand_with_depth(view, inputs, a, depth + 1)?;
            let rhs = predicate_expr_for_operand_with_depth(view, inputs, b, depth + 1)?;
            Some(CExpr::binary(BinaryOp::BitXor, lhs, rhs))
        }
        SSAOp::IntEqual { a, b, .. } => compare_expr_for_sources(view, inputs, a, b, BinaryOp::Eq),
        SSAOp::IntNotEqual { a, b, .. } => {
            compare_expr_for_sources(view, inputs, a, b, BinaryOp::Ne)
        }
        SSAOp::IntLess { a, b, .. } | SSAOp::IntSLess { a, b, .. } => {
            compare_expr_for_sources(view, inputs, a, b, BinaryOp::Lt)
        }
        SSAOp::IntLessEqual { a, b, .. } | SSAOp::IntSLessEqual { a, b, .. } => {
            compare_expr_for_sources(view, inputs, a, b, BinaryOp::Le)
        }
        _ => {
            let _ = block;
            None
        }
    }
}

fn populate_switches(view: &mut PreparedSemanticView, inputs: &PreparedSemanticViewInputs<'_>) {
    let Some(control_facts) = inputs.control_facts() else {
        return;
    };

    for (block_addr, switch) in &control_facts.switches {
        if let Some(selector_value) = switch.selector
            && let Some(selector) = prepared_var(inputs.prepared, selector_value).cloned()
        {
            let expr = expr_for_compare_operand(inputs, selector, view);
            view.switch_selector_value_by_block
                .insert(*block_addr, selector_value);
            view.switch_selector_expr_by_block.insert(*block_addr, expr);
        }
    }
}

fn populate_calls(view: &mut PreparedSemanticView, inputs: &PreparedSemanticViewInputs<'_>) {
    for call_site in inputs.prepared.call_sites().by_id.values() {
        let Some(site) = prepared_call_site_tuple(inputs.prepared, call_site.at) else {
            continue;
        };
        let direct_target = callsite_direct_target(inputs.callsite_facts(), site);
        let mut callee_identity = lookup_callee_identity_for_site(inputs, site, direct_target);
        if inputs
            .prepared
            .structured()
            .recursive_calls
            .contains_key(&call_site.id)
            && let Some(identity) = callee_identity.as_mut()
        {
            identity.is_recursive = true;
        }
        let mut call_view = PreparedCallView {
            direct_target,
            callee_identity,
            authoritative_args: Vec::new(),
            authoritative_arg_values: Vec::new(),
            result_owner: None,
            render_fact: inputs
                .call_render_facts()
                .and_then(|facts| {
                    facts.fact_for_site(CallsiteKey {
                        block_addr: site.0,
                        op_index: site.1,
                    })
                })
                .cloned(),
        };
        call_view.result_owner =
            certified_call_result_owner(site, inputs.prepared, view, inputs.call_result_facts());
        if let Some(owner) = call_view.result_owner.clone() {
            assign_certified_call_result_owner(
                site,
                inputs.prepared,
                view,
                inputs.call_result_facts(),
                &owner,
            );
        }
        let max_arity = prepared_call_max_arity(inputs, &call_view);
        let authoritative_args = canonical_call_authoritative_args(
            site,
            inputs.prepared.function(),
            inputs.prepared,
            view,
            inputs.callsite_facts(),
            max_arity,
        );
        call_view.authoritative_arg_values =
            authoritative_args.iter().map(|(value, _)| *value).collect();
        call_view.authoritative_args = authoritative_args
            .into_iter()
            .map(|(_, expr)| expr)
            .collect();
        view.call_view_by_site.insert(site, call_view);
    }
}

fn callsite_direct_target(
    callsite_facts: Option<&FunctionCallsiteFacts>,
    site: (u64, usize),
) -> Option<u64> {
    callsite_facts?
        .arguments_for_site(CallsiteKey {
            block_addr: site.0,
            op_index: site.1,
        })?
        .direct_target
}

fn canonical_call_authoritative_args(
    site: (u64, usize),
    function: &r2ssa::SSAFunction,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    callsite_facts: Option<&FunctionCallsiteFacts>,
    max_arity: Option<usize>,
) -> Vec<(ValueId, CExpr)> {
    let Some(callsite_facts) = callsite_facts else {
        return Vec::new();
    };
    let Some(call_facts) = callsite_facts.arguments_for_site(CallsiteKey {
        block_addr: site.0,
        op_index: site.1,
    }) else {
        return Vec::new();
    };
    let Some(block) = function.get_block(site.0) else {
        return Vec::new();
    };

    let mut args = Vec::new();
    let limit = max_arity.unwrap_or(usize::MAX);
    for argument in &call_facts.argument_values {
        if argument.index != args.len() || args.len() >= limit {
            break;
        }
        if !call_arg_value_has_location_certificate(call_facts, argument.index, argument.value) {
            break;
        }
        if let Some(expr) =
            authoritative_expr_for_prepared_value(block, prepared, view, argument.value)
        {
            args.push((argument.value, expr));
        } else {
            break;
        }
    }

    for stack_arg in &call_facts.stack_argument_locations {
        if args.len() >= limit {
            break;
        }
        if let Some(expr) =
            authoritative_expr_for_prepared_value(block, prepared, view, stack_arg.value)
        {
            args.push((stack_arg.value, expr));
        } else {
            break;
        }
    }

    args
}

fn call_arg_value_has_location_certificate(
    call_facts: &r2types::CallsiteArgumentFacts,
    index: usize,
    value: ValueId,
) -> bool {
    call_facts
        .register_argument_locations
        .iter()
        .any(|location| location.index == index && location.value == value)
        || call_facts
            .stack_argument_locations
            .iter()
            .any(|location| location.index == index && location.value == value)
}

fn authoritative_expr_for_prepared_value(
    block: &r2ssa::FunctionSSABlock,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    value: ValueId,
) -> Option<CExpr> {
    let var = prepared.value_var(value)?;
    authoritative_scalar_expr_for_value(block, view, var, 0)
        .or_else(|| scalar_owner_expr_for_value(view, var, var.size))
        .or_else(|| view.owner_expr_for_var(var).cloned())
        .or_else(|| Some(CExpr::Var(var.display_name())))
}

fn prepared_call_max_arity(
    _inputs: &PreparedSemanticViewInputs<'_>,
    call_view: &PreparedCallView,
) -> Option<usize> {
    call_view
        .callee_identity
        .as_ref()
        .and_then(CalleeIdentity::non_variadic_known_arity)
}

fn authoritative_scalar_expr_for_value(
    block: &r2ssa::FunctionSSABlock,
    view: &PreparedSemanticView,
    var: &SSAVar,
    depth: u32,
) -> Option<CExpr> {
    if depth > 8 {
        return None;
    }

    if let Some(expr) = compare_style_operand_expr(var, var.size) {
        return Some(expr);
    }
    if let Some(expr) = view.predicate_expr_for_cond(var).cloned() {
        return Some(expr);
    }
    if let Some(offset) = view.stack_offset_for_var(var)
        && let Some(alias) = preferred_stack_alias_name(view, offset)
    {
        return Some(CExpr::Var(alias));
    }
    if let Some(expr) = prepared_result_expr_for_var(view, var) {
        return Some(expr);
    }

    let (_, op) = block
        .ops
        .iter()
        .enumerate()
        .find(|(_, op)| op.dst() == Some(var))?;

    match op {
        SSAOp::Copy { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::Subpiece { src, .. } => {
            authoritative_scalar_expr_for_value(block, view, src, depth + 1)
                .or_else(|| scalar_owner_expr_for_value(view, src, src.size))
        }
        SSAOp::Load {
            space: r2il::SpaceId::Ram,
            addr,
            ..
        } => view
            .stack_offset_for_var(addr)
            .and_then(|offset| preferred_stack_alias_name(view, offset))
            .map(CExpr::Var)
            .or_else(|| prepared_load_access_expr_for_addr(block, view, addr, var.size)),
        SSAOp::IntAdd { a, b, .. } => {
            authoritative_scalar_expr_for_value(block, view, a, depth + 1)
                .or_else(|| scalar_owner_expr_for_value(view, a, a.size))
                .zip(
                    authoritative_scalar_expr_for_value(block, view, b, depth + 1)
                        .or_else(|| scalar_owner_expr_for_value(view, b, b.size)),
                )
                .map(|(lhs, rhs)| CExpr::binary(BinaryOp::Add, lhs, rhs))
        }
        SSAOp::IntSub { a, b, .. } => {
            authoritative_scalar_expr_for_value(block, view, a, depth + 1)
                .or_else(|| scalar_owner_expr_for_value(view, a, a.size))
                .zip(
                    authoritative_scalar_expr_for_value(block, view, b, depth + 1)
                        .or_else(|| scalar_owner_expr_for_value(view, b, b.size)),
                )
                .map(|(lhs, rhs)| CExpr::binary(BinaryOp::Sub, lhs, rhs))
        }
        SSAOp::IntEqual { a, b, .. } => {
            authoritative_scalar_expr_for_value(block, view, a, depth + 1)
                .or_else(|| scalar_owner_expr_for_value(view, a, a.size))
                .zip(
                    authoritative_scalar_expr_for_value(block, view, b, depth + 1)
                        .or_else(|| scalar_owner_expr_for_value(view, b, b.size)),
                )
                .map(|(lhs, rhs)| CExpr::binary(BinaryOp::Eq, lhs, rhs))
        }
        SSAOp::IntNotEqual { a, b, .. } => {
            authoritative_scalar_expr_for_value(block, view, a, depth + 1)
                .or_else(|| scalar_owner_expr_for_value(view, a, a.size))
                .zip(
                    authoritative_scalar_expr_for_value(block, view, b, depth + 1)
                        .or_else(|| scalar_owner_expr_for_value(view, b, b.size)),
                )
                .map(|(lhs, rhs)| CExpr::binary(BinaryOp::Ne, lhs, rhs))
        }
        _ => None,
    }
}

fn prepared_result_expr_for_var(view: &PreparedSemanticView, var: &SSAVar) -> Option<CExpr> {
    let site = view.call_result_source_for_var(var)?;
    let call_view = view.call_view_for_site(site)?;
    call_view
        .result_owner
        .clone()
        .or_else(|| prepared_call_expr_from_view(call_view))
}

fn certified_call_result_owner(
    site: (u64, usize),
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    call_result_facts: Option<&FunctionCallResultFacts>,
) -> Option<CExpr> {
    call_result_facts?
        .results_for_site(CallsiteKey {
            block_addr: site.0,
            op_index: site.1,
        })
        .filter_map(|cert| certified_call_result_owner_expr(cert, prepared, view))
        .next()
}

fn certified_call_result_owner_expr(
    cert: &r2types::CallResultFact,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) -> Option<CExpr> {
    match cert.owner.as_ref() {
        Some(ValueOwner::StackSlot { object, offset })
            if prepared
                .objects()
                .object(*object)
                .is_some_and(|fact| fact.kind.space() == r2il::SpaceId::Ram) =>
        {
            prepared_stack_alias_name_for_object_offset(view, *object, *offset).map(CExpr::Var)
        }
        Some(ValueOwner::Value(value)) if *value != cert.value => {
            let var = prepared.value_var(*value)?;
            (!var.is_register()).then(|| CExpr::Var(var.display_name()))
        }
        Some(ValueOwner::StackSlot { .. }) | Some(ValueOwner::Value(_)) | None => None,
    }
}

fn assign_certified_call_result_owner(
    site: (u64, usize),
    prepared: &SsaArtifact,
    view: &mut PreparedSemanticView,
    call_result_facts: Option<&FunctionCallResultFacts>,
    owner: &CExpr,
) {
    let Some(call_result_facts) = call_result_facts else {
        return;
    };
    for cert in call_result_facts.results_for_site(CallsiteKey {
        block_addr: site.0,
        op_index: site.1,
    }) {
        let Some(ValueOwner::StackSlot { object, .. }) = cert.owner.as_ref() else {
            continue;
        };
        if prepared
            .objects()
            .object(*object)
            .is_none_or(|fact| fact.kind.space() != r2il::SpaceId::Ram)
        {
            continue;
        }
        let Some(var) = prepared.value_var(cert.value) else {
            continue;
        };
        if view.owner_expr_for_var(var).is_none() {
            view.insert_owner_expr(var, owner.clone());
        }
    }
}

fn alias_for_memory_location(
    view: &PreparedSemanticView,
    location: &MemoryLocation,
) -> Option<String> {
    prepared_stack_alias_name_for_offset(view, location.address.exact_offset()?)
}

fn prepared_stack_owner_recovery_allowed(
    view: &PreparedSemanticView,
    offset: i64,
    name: &str,
) -> bool {
    !view.certified_rendering_required
        || view
            .authorized_stack_owner_names
            .get(&offset)
            .is_some_and(|names| names.contains(&name.to_ascii_lowercase()))
}

fn prepared_stack_owner_offset_authorized(view: &PreparedSemanticView, offset: i64) -> bool {
    !view.certified_rendering_required
        || view
            .authorized_stack_owner_names
            .get(&offset)
            .is_some_and(|names| !names.is_empty())
}

fn prepared_stack_alias_name_for_object_offset(
    view: &PreparedSemanticView,
    object: r2ssa::ObjectId,
    offset: i64,
) -> Option<String> {
    let authorized = view
        .authorized_stack_owner_names_by_object
        .get(&(object, offset))?;
    preferred_stack_alias_name(view, offset)
        .filter(|alias| authorized.contains(&alias.to_ascii_lowercase()))
        .or_else(|| authorized.iter().next().cloned())
}

fn prepared_stack_alias_name_for_offset(
    view: &PreparedSemanticView,
    offset: i64,
) -> Option<String> {
    preferred_stack_alias_name(view, offset)
        .filter(|alias| !alias.is_empty())
        .filter(|alias| prepared_stack_owner_recovery_allowed(view, offset, alias))
}

fn prepared_stack_alias_expr_for_offset(view: &PreparedSemanticView, offset: i64) -> Option<CExpr> {
    prepared_stack_alias_name_for_offset(view, offset).map(CExpr::Var)
}

fn stack_offset_for_value(prepared: &SsaArtifact, value: &SSAVar) -> Option<i64> {
    let object = prepared
        .object_for_var(value, r2il::SpaceId::Ram)
        .or_else(|| {
            prepared
                .function()
                .decompile_prep_facts()
                .and_then(|facts| facts.canonical_root_of(value))
                .and_then(|root| prepared.object_for_var(root, r2il::SpaceId::Ram))
        })?;
    let fact = prepared.objects().object(object)?;
    stack_offset_for_object_kind(&fact.kind)
}

fn stack_offset_for_object_kind(kind: &ObjectKind) -> Option<i64> {
    match kind {
        ObjectKind::StackSlot {
            space: r2il::SpaceId::Ram,
            offset,
            ..
        }
        | ObjectKind::FrameObject {
            space: r2il::SpaceId::Ram,
            offset,
            ..
        } => Some(*offset),
        _ => None,
    }
}

fn prepared_stack_reload_param_alias_expr(
    prepared: &SsaArtifact,
    env: &PassEnv<'_>,
    value_id: ValueId,
) -> Option<CExpr> {
    let cert = prepared.stack_reload_certificate_for_value(value_id)?;
    if prepared
        .objects()
        .object(cert.object)
        .is_none_or(|fact| fact.kind.space() != r2il::SpaceId::Ram)
    {
        return None;
    }
    [cert.canonical_source, cert.source]
        .into_iter()
        .filter_map(|source| prepared.value_var(source))
        .find_map(|var| param_alias_for_var(env.param_register_aliases, var))
        .map(CExpr::Var)
}

fn expr_for_compare_operand(
    inputs: &PreparedSemanticViewInputs<'_>,
    var: SSAVar,
    view: &PreparedSemanticView,
) -> CExpr {
    expr_for_compare_operand_with_width(inputs, var, view, 0)
}

fn expr_for_compare_operand_with_width(
    inputs: &PreparedSemanticViewInputs<'_>,
    var: SSAVar,
    view: &PreparedSemanticView,
    compare_width: u32,
) -> CExpr {
    if let Some(expr) = compare_style_operand_expr(&var, compare_width) {
        return expr;
    }

    let root = inputs
        .prepared
        .function()
        .decompile_prep_facts()
        .and_then(|facts| facts.canonical_root_of(&var))
        .cloned()
        .unwrap_or_else(|| var.clone());
    if let Some(expr) = compare_style_operand_expr(&root, compare_width) {
        return expr;
    }

    if let Some(alias) = param_alias_for_var(inputs.param_register_aliases, &root)
        .or_else(|| param_alias_for_var(inputs.param_register_aliases, &var))
    {
        return CExpr::Var(alias);
    }

    if let Some(expr) = non_generic_prepared_owner_expr(view, &var)
        .or_else(|| non_generic_prepared_predicate_expr(view, &var))
        .or_else(|| non_generic_prepared_owner_expr(view, &root))
        .or_else(|| non_generic_prepared_predicate_expr(view, &root))
    {
        return expr;
    }

    if let Some(alias) = preferred_non_generic_stack_alias(view, &var)
        .or_else(|| preferred_non_generic_stack_alias(view, &root))
    {
        return CExpr::Var(alias);
    }

    if let Some(expr) =
        generic_prepared_owner_expr(view, &var).or_else(|| generic_prepared_owner_expr(view, &root))
    {
        return expr;
    }

    if let Some(offset) = view.stack_offset_for_var(&var)
        && let Some(alias) = preferred_stack_alias_name(view, offset)
    {
        return CExpr::Var(alias);
    }
    if let Some(offset) = view.stack_offset_for_var(&root)
        && let Some(alias) = preferred_stack_alias_name(view, offset)
    {
        return CExpr::Var(alias);
    }

    if let Some(expr) =
        prepared_fallback_visible_expr(&root).or_else(|| prepared_fallback_visible_expr(&var))
    {
        return expr;
    }

    CExpr::Var(var.display_name())
}

fn compare_style_operand_expr(var: &SSAVar, compare_width: u32) -> Option<CExpr> {
    fn lit_for_u64(value: u64) -> CExpr {
        if value > 0x7fff_ffff {
            CExpr::UIntLit(value)
        } else {
            CExpr::IntLit(value as i64)
        }
    }

    if var.is_const() {
        let width = if compare_width == 0 {
            var.size
        } else {
            compare_width
        };
        return Some(compare_const_to_expr_with_width(var, width));
    }

    let raw = var.name.split('_').next().unwrap_or(&var.name);
    if let Some(dec) = raw.strip_prefix("0d").or_else(|| raw.strip_prefix("0D")) {
        return dec.parse::<u64>().ok().map(lit_for_u64);
    }

    if let Some(hex) = raw.strip_prefix("0x").or_else(|| raw.strip_prefix("0X")) {
        return u64::from_str_radix(hex, 16).ok().map(lit_for_u64);
    }

    if raw.chars().all(|c| c.is_ascii_hexdigit()) {
        let has_alpha = raw.chars().any(|c| c.is_ascii_alphabetic());
        let has_digit = raw.chars().any(|c| c.is_ascii_digit());
        if has_alpha && (has_digit || raw.len() > 4) {
            return u64::from_str_radix(raw, 16).ok().map(lit_for_u64);
        }
    }

    None
}

fn binary_op_for_compare(kind: CompareKind) -> BinaryOp {
    match kind {
        CompareKind::Equal => BinaryOp::Eq,
        CompareKind::NotEqual => BinaryOp::Ne,
        CompareKind::Less | CompareKind::SignedLess => BinaryOp::Lt,
        CompareKind::LessEqual | CompareKind::SignedLessEqual => BinaryOp::Le,
    }
}

fn param_alias_for_var(
    param_register_aliases: &HashMap<String, String>,
    var: &SSAVar,
) -> Option<String> {
    if var.version == 0 {
        let name = var.name.to_ascii_lowercase();
        if let Some(alias) = param_register_aliases.get(&name) {
            return Some(alias.clone());
        }
    }
    var.name
        .to_ascii_lowercase()
        .rsplit_once('_')
        .filter(|(_, version)| *version == "0")
        .and_then(|(base, _)| param_register_aliases.get(base))
        .cloned()
}

fn lookup_callee_identity_for_site(
    inputs: &PreparedSemanticViewInputs<'_>,
    site: (u64, usize),
    direct_target: Option<u64>,
) -> Option<CalleeIdentity> {
    CalleeResolutionFacts::resolve_target_identity(CalleeTargetIdentityRequest {
        resolution: inputs.callee_resolution(),
        callsite: Some(CallsiteKey {
            block_addr: site.0,
            op_index: site.1,
        }),
        prepared_identity: None,
        prepared_direct_target: direct_target,
        direct_target_context: None,
    })
    .map(|target| target.identity)
}

fn scalar_owner_expr_for_value(
    view: &PreparedSemanticView,
    var: &SSAVar,
    compare_width: u32,
) -> Option<CExpr> {
    compare_style_operand_expr(var, compare_width)
        .or_else(|| prepared_param_alias_for_var(view, var).map(CExpr::Var))
        .or_else(|| non_generic_prepared_predicate_expr(view, var))
        .or_else(|| non_generic_prepared_owner_expr(view, var))
        .or_else(|| {
            // A value that *is* the address of a stack slot is not named by
            // that slot. `buf` reads what the slot holds; the address is
            // `&buf`. The owner lookup above already refuses an `AddrOf`
            // owner for exactly that reason, so re-deriving the same address
            // from the slot's offset here would put the name back where the
            // address belongs -- and any arithmetic built on it then reads as
            // arithmetic on the variable, which is a different location. A
            // frame base sitting at offset zero is how that shows: `sp + 32`
            // becomes `buf + 32`.
            if matches!(view.owner_expr_for_var(var), Some(CExpr::AddrOf(_))) {
                return None;
            }
            view.stack_offset_for_var(var)
                .and_then(|offset| preferred_stack_alias_name(view, offset))
                .filter(|alias| {
                    !is_generic_prepared_stack_alias(alias) && !alias.ends_with("_home")
                })
                .map(CExpr::Var)
        })
        .or_else(|| view.predicate_expr_for_cond(var).cloned())
        .or_else(|| generic_prepared_owner_expr(view, var))
}

fn prepared_binary_owner_expr(
    view: &PreparedSemanticView,
    op: BinaryOp,
    a: &SSAVar,
    b: &SSAVar,
    compare_width: u32,
) -> Option<CExpr> {
    let lhs = scalar_owner_expr_for_value(view, a, compare_width)?;
    let rhs = scalar_owner_expr_for_value(view, b, compare_width)?;
    Some(prepared_simplify_binary_expr(view, op, lhs, rhs))
}

fn prepared_simplify_binary_expr(
    view: &PreparedSemanticView,
    op: BinaryOp,
    mut lhs: CExpr,
    mut rhs: CExpr,
) -> CExpr {
    if prepared_binary_op_is_commutative(op)
        && prepared_expr_order_key(view, &rhs) < prepared_expr_order_key(view, &lhs)
    {
        std::mem::swap(&mut lhs, &mut rhs);
    }

    match op {
        BinaryOp::Add => {
            if prepared_expr_is_zero(&lhs) {
                rhs
            } else if prepared_expr_is_zero(&rhs) {
                lhs
            } else if let Some(expr) = prepared_simplify_linear_addition(view, &lhs, &rhs) {
                expr
            } else {
                CExpr::binary(op, lhs, rhs)
            }
        }
        BinaryOp::Sub => {
            if prepared_expr_is_zero(&rhs) {
                lhs
            } else {
                CExpr::binary(op, lhs, rhs)
            }
        }
        BinaryOp::Mul => {
            if prepared_expr_is_one(&lhs) {
                rhs
            } else if prepared_expr_is_one(&rhs) {
                lhs
            } else {
                CExpr::binary(op, lhs, rhs)
            }
        }
        BinaryOp::Div => {
            if prepared_expr_is_one(&rhs) {
                lhs
            } else {
                CExpr::binary(op, lhs, rhs)
            }
        }
        BinaryOp::BitOr | BinaryOp::BitXor => {
            if matches!(op, BinaryOp::BitXor) && lhs == rhs {
                CExpr::IntLit(0)
            } else if prepared_expr_is_zero(&lhs) {
                rhs
            } else if prepared_expr_is_zero(&rhs) {
                lhs
            } else {
                CExpr::binary(op, lhs, rhs)
            }
        }
        _ => CExpr::binary(op, lhs, rhs),
    }
}

fn prepared_simplify_linear_addition(
    view: &PreparedSemanticView,
    left: &CExpr,
    right: &CExpr,
) -> Option<CExpr> {
    let mut terms = Vec::new();
    let mut constant = 0i64;
    prepared_collect_linear_add_terms(view, left, 1, &mut terms, &mut constant)?;
    prepared_collect_linear_add_terms(view, right, 1, &mut terms, &mut constant)?;
    terms.retain(|(_, coeff)| *coeff != 0);
    terms.sort_by_key(|(term, _)| prepared_expr_order_key(view, term));

    let mut pieces: Vec<CExpr> = terms
        .into_iter()
        .map(|(term, coeff)| prepared_linear_coeff_expr(term, coeff))
        .collect::<Option<Vec<_>>>()?;
    if constant != 0 {
        pieces.push(CExpr::IntLit(constant));
    }

    let mut iter = pieces.into_iter();
    let first = iter.next().unwrap_or(CExpr::IntLit(0));
    Some(iter.fold(first, |acc, expr| CExpr::binary(BinaryOp::Add, acc, expr)))
}

fn prepared_collect_linear_add_terms(
    view: &PreparedSemanticView,
    expr: &CExpr,
    scale: i64,
    terms: &mut Vec<(CExpr, i64)>,
    constant: &mut i64,
) -> Option<()> {
    match expr {
        CExpr::Binary {
            op: BinaryOp::Add,
            left,
            right,
        } => {
            prepared_collect_linear_add_terms(view, left, scale, terms, constant)?;
            prepared_collect_linear_add_terms(view, right, scale, terms, constant)
        }
        CExpr::Binary {
            op: BinaryOp::Mul,
            left,
            right,
        } => {
            if let Some(coeff) = prepared_literal_i64(right)
                && let Some(term) = prepared_linear_atom_expr(view, left)
            {
                return prepared_push_linear_term(terms, term, scale.checked_mul(coeff)?);
            }
            if let Some(coeff) = prepared_literal_i64(left)
                && let Some(term) = prepared_linear_atom_expr(view, right)
            {
                return prepared_push_linear_term(terms, term, scale.checked_mul(coeff)?);
            }
            None
        }
        CExpr::IntLit(value) => {
            *constant = constant.checked_add(scale.checked_mul(*value)?)?;
            Some(())
        }
        CExpr::UIntLit(value) => {
            let value = i64::try_from(*value).ok()?;
            *constant = constant.checked_add(scale.checked_mul(value)?)?;
            Some(())
        }
        CExpr::Paren(inner) => {
            prepared_collect_linear_add_terms(view, inner, scale, terms, constant)
        }
        _ => {
            let term = prepared_linear_atom_expr(view, expr)?;
            prepared_push_linear_term(terms, term, scale)
        }
    }
}

fn prepared_linear_atom_expr(view: &PreparedSemanticView, expr: &CExpr) -> Option<CExpr> {
    match expr {
        CExpr::Var(name)
            if view.param_rank_by_alias.contains_key(name)
                || view
                    .param_rank_by_alias
                    .contains_key(&name.to_ascii_lowercase()) =>
        {
            Some(expr.clone())
        }
        CExpr::Paren(inner) => prepared_linear_atom_expr(view, inner),
        CExpr::Cast { ty, expr: inner }
            if ty.is_integer() && prepared_linear_atom_expr(view, inner).is_some() =>
        {
            Some(expr.clone())
        }
        _ => None,
    }
}

fn prepared_push_linear_term(terms: &mut Vec<(CExpr, i64)>, term: CExpr, coeff: i64) -> Option<()> {
    if coeff == 0 {
        return Some(());
    }
    if let Some((_, existing)) = terms.iter_mut().find(|(existing, _)| *existing == term) {
        *existing = existing.checked_add(coeff)?;
    } else {
        terms.push((term, coeff));
    }
    Some(())
}

fn prepared_linear_coeff_expr(term: CExpr, coeff: i64) -> Option<CExpr> {
    match coeff {
        0 => Some(CExpr::IntLit(0)),
        1 => Some(term),
        _ => Some(CExpr::binary(BinaryOp::Mul, term, CExpr::IntLit(coeff))),
    }
}

fn prepared_literal_i64(expr: &CExpr) -> Option<i64> {
    match expr {
        CExpr::IntLit(value) => Some(*value),
        CExpr::UIntLit(value) => i64::try_from(*value).ok(),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => prepared_literal_i64(inner),
        _ => None,
    }
}

fn prepared_binary_op_is_commutative(op: BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::Add | BinaryOp::Mul | BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor
    )
}

fn prepared_expr_order_key(view: &PreparedSemanticView, expr: &CExpr) -> (u8, usize, String) {
    match expr {
        CExpr::Var(name) => view
            .param_rank_by_alias
            .get(name)
            .or_else(|| view.param_rank_by_alias.get(&name.to_ascii_lowercase()))
            .map(|rank| (0, *rank, name.clone()))
            .unwrap_or_else(|| (1, usize::MAX, name.clone())),
        CExpr::IntLit(value) => (2, usize::MAX, format!("{value:020}")),
        CExpr::UIntLit(value) => (2, usize::MAX, format!("{value:020}")),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            prepared_expr_order_key(view, inner)
        }
        _ => (1, usize::MAX, format!("{expr:?}")),
    }
}

fn prepared_expr_is_zero(expr: &CExpr) -> bool {
    match expr {
        CExpr::IntLit(value) => *value == 0,
        CExpr::UIntLit(value) => *value == 0,
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => prepared_expr_is_zero(inner),
        _ => false,
    }
}

fn prepared_expr_is_one(expr: &CExpr) -> bool {
    match expr {
        CExpr::IntLit(value) => *value == 1,
        CExpr::UIntLit(value) => *value == 1,
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => prepared_expr_is_one(inner),
        _ => false,
    }
}

fn prepared_signed_dividend_expr(
    view: &PreparedSemanticView,
    producer_by_dst: &HashMap<SSAVar, &SSAOp>,
    dividend: &SSAVar,
) -> Option<CExpr> {
    let SSAOp::IntOr {
        a: high_part,
        b: low_part,
        ..
    } = producer_by_dst.get(dividend).copied()?
    else {
        return None;
    };
    prepared_sign_extended_pair_low_root(producer_by_dst, high_part, low_part)
        .or_else(|| prepared_sign_extended_pair_low_root(producer_by_dst, low_part, high_part))
        .and_then(|root| scalar_owner_expr_for_value(view, root, root.size))
}

fn prepared_sign_extended_pair_low_root<'a>(
    producer_by_dst: &'a HashMap<SSAVar, &SSAOp>,
    shifted_high: &'a SSAVar,
    low_zext: &'a SSAVar,
) -> Option<&'a SSAVar> {
    let SSAOp::IntLeft {
        a: high_zext,
        b: shift,
        ..
    } = producer_by_dst.get(shifted_high).copied()?
    else {
        return None;
    };
    let SSAOp::IntZExt { src: high, .. } = producer_by_dst.get(high_zext).copied()? else {
        return None;
    };
    let low_root = prepared_signed_high_limb_low_root(producer_by_dst, high)?;
    let SSAOp::IntZExt { src: low, .. } = producer_by_dst.get(low_zext).copied()? else {
        return None;
    };
    if low == low_root
        && prepared_shift_matches_signed_concat_width(&shift.name, high, low, low_root)
    {
        Some(low_root)
    } else {
        None
    }
}

fn prepared_signed_high_limb_low_root<'a>(
    producer_by_dst: &'a HashMap<SSAVar, &SSAOp>,
    high: &'a SSAVar,
) -> Option<&'a SSAVar> {
    match producer_by_dst.get(high).copied()? {
        SSAOp::Subpiece { src: sext, .. } => match producer_by_dst.get(sext).copied()? {
            SSAOp::IntSExt { src, .. } => Some(src),
            _ => None,
        },
        SSAOp::IntSExt { src, .. } => Some(src),
        _ => None,
    }
}

fn prepared_shift_matches_signed_concat_width(
    shift_name: &str,
    high: &SSAVar,
    low: &SSAVar,
    low_root: &SSAVar,
) -> bool {
    [low.size, low_root.size, high.size]
        .into_iter()
        .filter(|size| *size > 0)
        .any(|size| prepared_const_may_equal(shift_name, u64::from(size.saturating_mul(8))))
}

fn prepared_const_may_equal(name: &str, expected: u64) -> bool {
    if parse_const_value(name) == Some(expected) {
        return true;
    }
    let Some(raw) = name.strip_prefix("const:") else {
        return false;
    };
    let raw = raw.split('_').next().unwrap_or(raw);
    u64::from_str_radix(raw.trim_start_matches("0x"), 16) == Ok(expected)
}

fn prepared_param_alias_for_var(view: &PreparedSemanticView, var: &SSAVar) -> Option<String> {
    param_alias_for_var(&view.param_alias_by_reg, var)
}

fn prepared_address_owner_expr_for_value(
    view: &PreparedSemanticView,
    var: &SSAVar,
    compare_width: u32,
) -> Option<CExpr> {
    scalar_owner_expr_for_value(view, var, compare_width).or_else(|| {
        prepared_fallback_visible_expr(var).filter(|expr| {
            matches!(
                expr,
                CExpr::Var(name) if crate::registers::register_family_name(name).is_some()
            )
        })
    })
}

fn prepared_scaled_index_owner_expr(
    view: &PreparedSemanticView,
    var: &SSAVar,
    compare_width: u32,
) -> Option<CExpr> {
    scalar_owner_expr_for_value(view, var, compare_width)
        .or_else(|| generic_prepared_owner_expr(view, var))
        .or_else(|| prepared_fallback_visible_expr(var))
}

fn is_prepared_stack_address_carrier(prepared: &SsaArtifact, value: &SSAVar) -> bool {
    if prepared
        .function()
        .decompile_prep_facts()
        .and_then(|facts| facts.stack_address_root_of(value))
        .is_some()
    {
        return true;
    }

    prepared
        .object_for_var(value, r2il::SpaceId::Ram)
        .and_then(|object_id| prepared.objects().object(object_id))
        .is_some_and(|object| stack_offset_for_object_kind(&object.kind).is_some())
}

fn preferred_non_generic_stack_alias(view: &PreparedSemanticView, var: &SSAVar) -> Option<String> {
    view.stack_offset_for_var(var)
        .and_then(|offset| preferred_stack_alias_name(view, offset))
        .filter(|alias| !is_generic_prepared_stack_alias(alias) && !alias.ends_with("_home"))
}

fn non_generic_prepared_owner_expr(view: &PreparedSemanticView, var: &SSAVar) -> Option<CExpr> {
    view.owner_expr_for_var(var)
        .cloned()
        .filter(|expr| !matches!(expr, CExpr::AddrOf(_)))
        .filter(|expr| !prepared_expr_is_generic_scalar_alias(expr))
}

fn generic_prepared_owner_expr(view: &PreparedSemanticView, var: &SSAVar) -> Option<CExpr> {
    view.owner_expr_for_var(var)
        .cloned()
        .filter(|expr| !matches!(expr, CExpr::AddrOf(_)))
}

fn non_generic_prepared_predicate_expr(view: &PreparedSemanticView, var: &SSAVar) -> Option<CExpr> {
    view.predicate_expr_for_cond(var)
        .cloned()
        .filter(|expr| !prepared_expr_is_generic_scalar_alias(expr))
}

fn prepared_fallback_visible_expr(var: &SSAVar) -> Option<CExpr> {
    if var.is_const() {
        return None;
    }

    if is_temporary_constant_or_memory_name(&var.name) {
        return None;
    }

    // The version is part of which value this is, and the definition side spells
    // it that way. Naming the storage alone made a use of `x19_3` print as
    // `x19`, which no longer matched the definition of `x19_3` -- so a
    // definition with eleven readers looked unread and was deleted, leaving the
    // readers naming nothing. Version zero stays bare, as it does everywhere:
    // that is the value the function was entered with.
    Some(CExpr::Var(if var.version > 0 {
        format!("{}_{}", var.name, var.version)
    } else {
        var.name.clone()
    }))
}

fn local_store_owner_expr_for_offset(
    view: &PreparedSemanticView,
    prepared: &SsaArtifact,
    block: &r2ssa::FunctionSSABlock,
    before_idx: usize,
    offset: i64,
) -> Option<CExpr> {
    if !prepared_stack_owner_offset_authorized(view, offset) {
        return None;
    }
    let alias = prepared_stack_alias_name_for_offset(view, offset);
    let prefer_alias = alias
        .as_deref()
        .is_some_and(|name| !is_generic_prepared_stack_alias(name));

    for op in block.ops[..before_idx].iter().rev() {
        let SSAOp::Store {
            space: r2il::SpaceId::Ram,
            addr,
            val,
        } = op
        else {
            continue;
        };
        let store_offset = view
            .stack_offset_for_var(addr)
            .or_else(|| stack_offset_for_value(prepared, addr));
        if store_offset != Some(offset) {
            continue;
        }
        if let Some(expr) = scalar_owner_expr_for_value(view, val, val.size) {
            if prefer_alias {
                return alias.map(CExpr::Var);
            }
            if matches!(&expr, CExpr::Var(name) if !is_generic_prepared_stack_alias(name)) {
                return Some(expr);
            }
            return Some(expr);
        }
    }
    alias.map(CExpr::Var)
}

fn preferred_stack_alias_name(view: &PreparedSemanticView, offset: i64) -> Option<String> {
    let alias = view.stack_alias_for_offset(offset)?;
    let visible = alias.visible_name.trim();
    let prefer_arg_alias = alias.arg_alias.as_ref().filter(|arg_alias| {
        !arg_alias.is_empty()
            && (visible.is_empty()
                || is_generic_prepared_stack_alias(visible)
                || visible.ends_with("_home"))
    });
    prefer_arg_alias
        .cloned()
        .or_else(|| (!visible.is_empty()).then(|| visible.to_string()))
        .or_else(|| alias.arg_alias.clone())
}

fn is_generic_prepared_stack_alias(name: &str) -> bool {
    name.starts_with("var_")
        || name.starts_with("local_")
        || name.starts_with("stack_")
        || name.starts_with("arg_")
}

fn prepared_stack_visible_name(slot: &ExternalStackSlotSpec) -> Option<String> {
    (!slot.name.is_empty()
        && matches!(
            slot.role,
            ExternalStackSlotRole::Local
                | ExternalStackSlotRole::StackArg
                | ExternalStackSlotRole::Unknown
        ))
    .then(|| slot.name.clone())
}

fn prepared_stack_arg_alias(slot: &ExternalStackSlotSpec) -> Option<String> {
    match slot.role {
        ExternalStackSlotRole::StackArg => (!slot.name.is_empty()).then(|| slot.name.clone()),
        ExternalStackSlotRole::ParamHome => {
            slot.param_name.clone().or_else(|| slot.source_reg.clone())
        }
        _ => None,
    }
}

fn synthetic_stack_name(offset: i64) -> String {
    if offset < 0 {
        format!("local_{:x}", (-offset) as u64)
    } else {
        format!("stack_{:x}", offset as u64)
    }
}

fn seed_prepared_param_aliases(info: &mut UseInfo, blocks: &[SSABlock], env: &PassEnv<'_>) {
    let mut maybe_insert = |var: &SSAVar| {
        if var.version != 0 {
            return;
        }
        if let Some(alias) = env
            .param_register_aliases
            .get(&var.name.to_ascii_lowercase())
        {
            info.var_aliases
                .entry(var.display_name())
                .or_insert_with(|| alias.clone());
        }
    };

    for block in blocks {
        for phi in &block.phis {
            maybe_insert(&phi.dst);
            for (_, src) in &phi.sources {
                maybe_insert(src);
            }
        }
        for op in &block.ops {
            if let Some(dst) = op.dst() {
                maybe_insert(dst);
            }
            for src in op.sources() {
                maybe_insert(src);
            }
        }
    }
}

fn seed_prepared_stack_facts(
    use_info: &mut UseInfo,
    stack_info: &mut StackInfo,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) {
    for (offset, alias) in &view.stack_aliases_by_offset {
        if let Some(arg_alias) = alias.arg_alias.clone() {
            stack_info
                .stack_arg_aliases
                .entry(*offset)
                .or_insert(arg_alias);
        }
        if let Some(name) = preferred_stack_alias_name(view, *offset) {
            stack_info.stack_vars.entry(*offset).or_insert(name.clone());
            let provenance = StackSlotProvenance {
                offset: *offset,
                predicate_carrier: false,
                return_carrier: false,
                value_kind: if matches!(alias.binding_kind, Some(VisibleBindingKind::StackObject)) {
                    StackSlotValueKind::AddressLike
                } else {
                    StackSlotValueKind::Scalar
                },
            };
            merge_prepared_stack_slot(use_info, &name, None, provenance);
            if *offset < 0 {
                use_info
                    .stable_stack_values
                    .entry(*offset)
                    .or_insert_with(|| SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var(name))));
            }
        }
    }

    for (key, object_id) in &prepared.objects().value_objects {
        if key.space != r2il::SpaceId::Ram {
            continue;
        }
        let Some(object) = prepared.objects().object(*object_id) else {
            continue;
        };
        let Some(offset) = stack_offset_for_object_kind(&object.kind) else {
            continue;
        };
        let Some(value) = prepared_var(prepared, key.value) else {
            continue;
        };
        let value_id = key.value;
        if use_info.bind_value_id(value, value_id).is_none() {
            continue;
        }
        let key = value.display_name();
        let provenance = StackSlotProvenance {
            offset,
            predicate_carrier: false,
            return_carrier: false,
            value_kind: StackSlotValueKind::AddressLike,
        };
        merge_prepared_stack_slot(use_info, &key, Some(value_id), provenance);
        if let Some(alias) = preferred_stack_alias_name(view, offset) {
            stack_info
                .definition_overrides
                .entry(key.clone())
                .or_insert_with(|| CExpr::AddrOf(Box::new(CExpr::Var(alias.clone()))));
            if offset < 0 {
                use_info
                    .stable_stack_values
                    .entry(offset)
                    .or_insert_with(|| SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var(alias))));
            }
        }
    }
}

fn collect_prepared_runtime_facts(
    use_info: &mut UseInfo,
    flag_info: &mut FlagInfo,
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) {
    for block in blocks {
        for phi in &block.phis {
            let _ = bind_prepared_value_id(use_info, view, &phi.dst);
            let dst_key = phi.dst.display_name();
            use_info.phi_sources.insert(
                dst_key.clone(),
                phi.sources.iter().map(|(_, src)| src.clone()).collect(),
            );
            use_info.producers.insert(
                dst_key.clone(),
                SSAOp::Phi {
                    dst: phi.dst.clone(),
                    sources: phi.sources.iter().map(|(_, src)| src.clone()).collect(),
                },
            );
            for (_, src) in &phi.sources {
                *use_info.use_counts.entry(src.display_name()).or_insert(0) += 1;
                if let Some(value_id) = bind_prepared_value_id(use_info, view, src) {
                    *use_info.use_counts_by_value.entry(value_id).or_insert(0) += 1;
                }
            }
            seed_prepared_value_fact(use_info, &phi.dst, prepared, view);
        }

        for op in &block.ops {
            for src in op.sources() {
                *use_info.use_counts.entry(src.display_name()).or_insert(0) += 1;
                if let Some(value_id) = bind_prepared_value_id(use_info, view, src) {
                    *use_info.use_counts_by_value.entry(value_id).or_insert(0) += 1;
                }
            }
            if let SSAOp::CBranch { cond, .. } = op {
                use_info.condition_vars.insert(cond.display_name());
                if let Some(value_id) = bind_prepared_value_id(use_info, view, cond) {
                    use_info.condition_values.insert(value_id);
                }
            }

            if let Some(dst) = op.dst() {
                let dst_key = dst.display_name();
                let _ = bind_prepared_value_id(use_info, view, dst);
                use_info.producers.insert(dst_key.clone(), op.clone());
                if is_flag_like_name(&dst.name) || op_produces_predicate(op) {
                    flag_info.flag_only_values.insert(dst_key.clone());
                }
                seed_prepared_value_fact(use_info, dst, prepared, view);
            }

            match op {
                SSAOp::Copy { dst, src }
                | SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src }
                | SSAOp::Trunc { dst, src }
                | SSAOp::Cast { dst, src, .. }
                | SSAOp::Subpiece { dst, src, .. } => {
                    let dst_key = dst.display_name();
                    let src_key = src.display_name();
                    use_info
                        .copy_sources
                        .insert(dst_key.clone(), src_key.clone());
                    let bound_copy = bind_prepared_copy_ids(use_info, view, dst, src);
                    let bound_dst_id = bound_copy.map(|(dst_id, _)| dst_id);
                    let bound_src_id = bound_copy.map(|(_, src_id)| src_id);
                    if let Some((dst_id, src_id)) = bound_copy {
                        use_info.copy_sources_by_value.insert(dst_id, src_id);
                    }
                    let source_prov =
                        use_info
                            .forwarded_value_for_var(src)
                            .cloned()
                            .unwrap_or(ValueProvenance {
                                source: src_key.clone(),
                                source_value_id: bound_src_id,
                                source_var: Some(src.clone()),
                                stack_slot: view
                                    .stack_offset_for_var(src)
                                    .or_else(|| stack_offset_for_value(prepared, src)),
                            });
                    use_info.forwarded_values.insert(
                        dst_key.clone(),
                        ValueProvenance {
                            source: source_prov.source.clone(),
                            source_value_id: source_prov.source_value_id.or(bound_src_id),
                            source_var: source_prov
                                .source_var
                                .clone()
                                .or_else(|| Some(src.clone())),
                            stack_slot: source_prov
                                .stack_slot
                                .or_else(|| view.stack_offset_for_var(src))
                                .or_else(|| stack_offset_for_value(prepared, src)),
                        },
                    );
                    if let (Some(dst_id), Some(src_id)) = (bound_dst_id, bound_src_id) {
                        use_info.forwarded_values_by_value.insert(
                            dst_id,
                            exact_prepared_copy_provenance(
                                src,
                                src_id,
                                source_prov
                                    .stack_slot
                                    .or_else(|| view.stack_offset_for_var(src))
                                    .or_else(|| stack_offset_for_value(prepared, src)),
                            ),
                        );
                    }
                    if dst.version == 0
                        && let Some(alias) = env
                            .param_register_aliases
                            .get(&dst.name.to_ascii_lowercase())
                    {
                        use_info
                            .var_aliases
                            .entry(dst_key)
                            .or_insert_with(|| alias.clone());
                    }
                }
                SSAOp::Load {
                    dst,
                    space: r2il::SpaceId::Ram,
                    addr,
                } => {
                    let Some(offset) = prepared_direct_stack_load_offset(prepared, view, addr)
                    else {
                        continue;
                    };
                    let key = dst.display_name();
                    let reload_value = bind_prepared_value_id(use_info, view, dst);
                    let provenance = StackSlotProvenance {
                        offset,
                        predicate_carrier: false,
                        return_carrier: false,
                        value_kind: StackSlotValueKind::Scalar,
                    };
                    merge_prepared_stack_slot(use_info, &key, reload_value, provenance);
                    let reload_param_expr = prepared_stack_owner_offset_authorized(view, offset)
                        .then(|| {
                            reload_value.and_then(|value_id| {
                                prepared_stack_reload_param_alias_expr(prepared, env, value_id)
                            })
                        })
                        .flatten();
                    let stack_alias_expr = prepared_stack_alias_expr_for_offset(view, offset);
                    if let Some(expr) = reload_param_expr.or(stack_alias_expr) {
                        if let CExpr::Var(alias) = &expr {
                            use_info
                                .var_aliases
                                .entry(key.clone())
                                .or_insert_with(|| alias.clone());
                        }
                        use_info
                            .definitions
                            .entry(key.clone())
                            .or_insert_with(|| expr.clone());
                        if let Some(value_id) = reload_value {
                            use_info
                                .definitions_by_value
                                .entry(value_id)
                                .or_insert_with(|| expr.clone());
                        }
                        use_info
                            .formatted_defs
                            .entry(key.clone())
                            .or_insert_with(|| expr.clone());
                        use_info.semantic_values.entry(key).or_insert_with(|| {
                            SemanticValue::Scalar(ScalarValue::Expr(expr.clone()))
                        });
                        if let Some(value_id) = reload_value {
                            use_info
                                .semantic_values_by_value
                                .entry(value_id)
                                .or_insert_with(|| {
                                    SemanticValue::Scalar(ScalarValue::Expr(expr.clone()))
                                });
                        }
                        if offset < 0 {
                            use_info
                                .stable_stack_values
                                .entry(offset)
                                .or_insert_with(|| {
                                    SemanticValue::Scalar(ScalarValue::Expr(expr.clone()))
                                });
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

fn populate_prepared_call_runtime_facts(
    use_info: &mut UseInfo,
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) {
    for block in blocks {
        for (op_idx, op) in block.ops.iter().enumerate() {
            if !matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
                continue;
            }
            let site = (block.addr, op_idx);
            let Some(call_view) = view.call_view_for_site(site) else {
                continue;
            };
            if !prepared_call_render_authorized(call_view) {
                continue;
            }

            let args = call_view
                .authoritative_args
                .iter()
                .cloned()
                .zip(call_view.authoritative_arg_values.iter().copied())
                .map(|(expr, value)| {
                    CallArgBinding::input(SemanticCallArg::FallbackExpr(expr))
                        .with_source_value_id(value)
                })
                .collect::<Vec<_>>();
            if !args.is_empty() {
                use_info.call_args.insert(site, args);
            }

            if let Some(call_expr) = prepared_call_expr(call_view, view, env) {
                use_info.call_result_exprs.insert(site, call_expr.clone());
                record_prepared_consumed_by_call(use_info, block, op_idx, env, prepared, view);
                record_prepared_call_result_aliases(
                    use_info, block, op_idx, prepared, view, &call_expr,
                );
            }
        }
    }
}

fn overlay_prepared_switch_roots(
    use_info: &mut UseInfo,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) {
    for (block_addr, selector_value) in &view.switch_selector_value_by_block {
        let Some(selector) = prepared_var(prepared, *selector_value) else {
            continue;
        };
        use_info.switch_selector_roots.insert(
            *block_addr,
            SemanticValue::Scalar(ScalarValue::Root(
                use_info
                    .value_id_for_var(selector)
                    .map(|value_id| ValueRef::with_value_id(value_id, selector.clone()))
                    .unwrap_or_else(|| ValueRef::new(selector.clone())),
            )),
        );
    }
}

fn merge_prepared_stack_slot(
    use_info: &mut UseInfo,
    name: &str,
    value_id: Option<ValueId>,
    provenance: StackSlotProvenance,
) {
    use_info
        .stack_slots
        .entry(name.to_string())
        .and_modify(|existing| *existing = existing.merge(provenance))
        .or_insert(provenance);
    if let Some(value_id) = value_id {
        use_info
            .stack_slots_by_value
            .entry(value_id)
            .and_modify(|existing| *existing = existing.merge(provenance))
            .or_insert(provenance);
    }
}

fn seed_prepared_value_fact(
    use_info: &mut UseInfo,
    var: &SSAVar,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) {
    let bound_value_id = bind_prepared_value_id(use_info, view, var);
    let key = var.display_name();
    if let Some(expr) = view
        .predicate_expr_for_cond(var)
        .cloned()
        .or_else(|| view.owner_expr_for_var(var).cloned())
    {
        use_info
            .definitions
            .entry(key.clone())
            .or_insert_with(|| expr.clone());
        if let Some(value_id) = bound_value_id {
            use_info
                .definitions_by_value
                .entry(value_id)
                .or_insert_with(|| expr.clone());
        }
        use_info
            .formatted_defs
            .entry(key.clone())
            .or_insert_with(|| expr.clone());
        use_info
            .semantic_values
            .entry(key.clone())
            .or_insert_with(|| semantic_value_for_prepared_expr(view, var, expr.clone()));
        if let Some(value_id) = bound_value_id {
            use_info
                .semantic_values_by_value
                .entry(value_id)
                .or_insert_with(|| semantic_value_for_prepared_expr(view, var, expr.clone()));
        }
        if let Some(offset) = view
            .stack_offset_for_var(var)
            .or_else(|| stack_offset_for_value(prepared, var))
        {
            merge_prepared_stack_slot(
                use_info,
                &key,
                bound_value_id,
                StackSlotProvenance {
                    offset,
                    predicate_carrier: false,
                    return_carrier: false,
                    value_kind: stack_value_kind_for_prepared_expr(&expr),
                },
            );
            if offset < 0 {
                use_info
                    .stable_stack_values
                    .entry(offset)
                    .or_insert_with(|| SemanticValue::Scalar(ScalarValue::Expr(expr)));
            }
        }
    } else if let Some(offset) = view
        .stack_offset_for_var(var)
        .or_else(|| stack_offset_for_value(prepared, var))
    {
        merge_prepared_stack_slot(
            use_info,
            &key,
            bound_value_id,
            StackSlotProvenance {
                offset,
                predicate_carrier: false,
                return_carrier: false,
                value_kind: StackSlotValueKind::AddressLike,
            },
        );
        if let Some(alias) = preferred_stack_alias_name(view, offset)
            && offset < 0
        {
            use_info
                .stable_stack_values
                .entry(offset)
                .or_insert_with(|| SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var(alias))));
        }
    }
}

fn semantic_value_for_prepared_expr(
    view: &PreparedSemanticView,
    var: &SSAVar,
    expr: CExpr,
) -> SemanticValue {
    if let Some(offset) = view.stack_offset_for_var(var)
        && matches!(expr, CExpr::AddrOf(_))
    {
        return SemanticValue::Address(NormalizedAddr {
            base: BaseRef::StackSlot(offset),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        });
    }
    SemanticValue::Scalar(ScalarValue::Expr(expr))
}

fn stack_value_kind_for_prepared_expr(expr: &CExpr) -> StackSlotValueKind {
    match expr {
        CExpr::AddrOf(_) => StackSlotValueKind::AddressLike,
        _ => StackSlotValueKind::Scalar,
    }
}

fn prepared_call_expr(
    call_view: &PreparedCallView,
    view: &PreparedSemanticView,
    env: &PassEnv<'_>,
) -> Option<CExpr> {
    if !prepared_call_render_authorized(call_view) {
        return None;
    }
    if !prepared_call_args_have_value_bijection(call_view) {
        return None;
    }
    let callee = prepared_call_callee_expr(call_view)?;
    let args = call_view
        .authoritative_args
        .iter()
        .map(|arg| normalize_prepared_inline_expr(arg.clone(), view, env, 0, &mut HashSet::new()))
        .collect();
    Some(CExpr::Call {
        func: Box::new(callee),
        args,
    })
}

fn prepared_call_callee_expr(call_view: &PreparedCallView) -> Option<CExpr> {
    call_view
        .callee_identity
        .as_ref()
        .and_then(|identity| identity.display_name.clone())
        .map(CExpr::Var)
        .or_else(|| {
            call_view
                .callee_identity
                .as_ref()
                .map(|identity| CExpr::Var(identity.primary_key()))
        })
}

fn prepared_call_expr_from_view(call_view: &PreparedCallView) -> Option<CExpr> {
    if !prepared_call_render_authorized(call_view) {
        return None;
    }
    if !prepared_call_args_have_value_bijection(call_view) {
        return None;
    }
    let callee = prepared_call_callee_expr(call_view)?;
    Some(CExpr::Call {
        func: Box::new(callee),
        args: call_view.authoritative_args.clone(),
    })
}

fn prepared_call_args_have_value_bijection(call_view: &PreparedCallView) -> bool {
    call_view.authoritative_args.len() == call_view.authoritative_arg_values.len()
}

fn prepared_call_render_authorized(call_view: &PreparedCallView) -> bool {
    let Some(render_fact) = &call_view.render_fact else {
        return false;
    };
    if matches!(
        render_fact.disposition,
        r2types::CallsiteRenderDisposition::Suppressed
            | r2types::CallsiteRenderDisposition::Residualized
    ) {
        return false;
    }
    prepared_call_args_have_value_bijection(call_view)
        && render_fact.proof_values.len() >= call_view.authoritative_arg_values.len()
        && render_fact
            .proof_values
            .iter()
            .take(call_view.authoritative_arg_values.len())
            .copied()
            .eq(call_view.authoritative_arg_values.iter().copied())
}

fn record_prepared_consumed_by_call(
    use_info: &mut UseInfo,
    block: &SSABlock,
    call_idx: usize,
    env: &PassEnv<'_>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) {
    for op in block.ops[..call_idx].iter().rev() {
        match op {
            SSAOp::Call { .. } | SSAOp::CallInd { .. } => break,
            SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::Return { .. } => break,
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr,
                val,
            } => {
                if view
                    .stack_offset_for_var(addr)
                    .or_else(|| stack_offset_for_value(prepared, addr))
                    .is_some()
                {
                    use_info.consumed_by_call.insert(addr.display_name());
                    use_info.consumed_by_call.insert(val.display_name());
                }
            }
            SSAOp::Copy { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Cast { dst, src, .. }
            | SSAOp::Subpiece { dst, src, .. } => {
                if env
                    .arg_regs
                    .iter()
                    .any(|reg| dst.name.eq_ignore_ascii_case(reg))
                {
                    use_info.consumed_by_call.insert(dst.display_name());
                    use_info.consumed_by_call.insert(src.display_name());
                }
            }
            other => {
                if let Some(dst) = other.dst()
                    && env
                        .arg_regs
                        .iter()
                        .any(|reg| dst.name.eq_ignore_ascii_case(reg))
                {
                    use_info.consumed_by_call.insert(dst.display_name());
                }
            }
        }
    }
}

fn record_prepared_call_result_aliases(
    use_info: &mut UseInfo,
    block: &SSABlock,
    call_idx: usize,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    call_expr: &CExpr,
) {
    let site = (block.addr, call_idx);
    for cert in view
        .call_result_facts_by_value
        .values()
        .filter(|cert| cert.callsite.block_addr == block.addr && cert.callsite.op_index == call_idx)
    {
        let Some(var) = prepared.value_var(cert.value) else {
            continue;
        };
        let direct = matches!(cert.owner.as_ref(), Some(ValueOwner::Value(_)))
            && matches!(&cert.carrier, ReturnCarrier::Register { .. });
        let alias = var.display_name();
        let visible_aliases = prepared_visible_aliases_for_call_result(use_info, &alias);
        record_prepared_call_alias(use_info, site, &alias, direct);
        for visible_alias in visible_aliases {
            record_prepared_call_alias(use_info, site, &visible_alias, false);
        }
        if direct {
            use_info
                .definitions
                .entry(alias.clone())
                .or_insert_with(|| call_expr.clone());
            use_info
                .formatted_defs
                .entry(alias)
                .or_insert_with(|| call_expr.clone());
        }
        if let Some(ValueOwner::StackSlot { object, offset }) = cert.owner.as_ref()
            && let Some(alias) = prepared_stack_alias_name_for_object_offset(view, *object, *offset)
        {
            record_prepared_call_alias(use_info, site, &alias, false);
            if *offset < 0 {
                use_info
                    .stable_stack_values
                    .entry(*offset)
                    .or_insert_with(|| {
                        SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var(alias.clone())))
                    });
            }
        }
    }
}

fn prepared_visible_aliases_for_call_result(use_info: &UseInfo, alias: &str) -> Vec<String> {
    let mut aliases = Vec::new();
    for key in [
        alias,
        &alias.to_ascii_lowercase(),
        &alias.to_ascii_uppercase(),
    ] {
        if let Some(visible) = use_info.var_aliases.get(key)
            && visible != alias
            && !aliases.iter().any(|existing| existing == visible)
        {
            aliases.push(visible.clone());
        }
    }
    aliases
}

fn record_prepared_call_alias(
    use_info: &mut UseInfo,
    site: (u64, usize),
    alias: &str,
    direct: bool,
) {
    if alias.is_empty() {
        return;
    }
    use_info
        .call_result_aliases
        .entry(site)
        .or_default()
        .insert(alias.to_string());
    use_info
        .call_result_source_by_alias
        .insert(alias.to_string(), site);
    if direct {
        use_info
            .direct_call_result_aliases
            .insert(alias.to_string());
    }
}

fn is_flag_like_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    matches!(
        lower.split('_').next(),
        Some("cf" | "zf" | "sf" | "of" | "pf")
    )
}

fn op_produces_predicate(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::BoolNot { .. }
            | SSAOp::BoolAnd { .. }
            | SSAOp::BoolOr { .. }
            | SSAOp::BoolXor { .. }
            | SSAOp::IntEqual { .. }
            | SSAOp::IntNotEqual { .. }
            | SSAOp::IntLess { .. }
            | SSAOp::IntSLess { .. }
            | SSAOp::IntLessEqual { .. }
            | SSAOp::IntSLessEqual { .. }
    )
}

fn normalize_prepared_inline_expr(
    expr: CExpr,
    view: &PreparedSemanticView,
    env: &PassEnv<'_>,
    depth: u32,
    visited: &mut HashSet<String>,
) -> CExpr {
    if depth > 8 {
        return expr;
    }

    match expr {
        CExpr::Var(name) => {
            if let Some(alias) = param_alias_for_name(&name, env) {
                return CExpr::Var(alias);
            }

            if !visited.insert(name.clone()) {
                return CExpr::Var(name);
            }

            let resolved = view
                .owner_expr_for_name(&name)
                .cloned()
                .or_else(|| view.predicate_expr_for_name(&name).cloned())
                .filter(|candidate| !matches!(candidate, CExpr::Var(candidate_name) if candidate_name.eq_ignore_ascii_case(&name)))
                .map(|candidate| {
                    normalize_prepared_inline_expr(candidate, view, env, depth + 1, visited)
                })
                .unwrap_or(CExpr::Var(name.clone()));
            visited.remove(&name);
            resolved
        }
        CExpr::Paren(inner) => CExpr::Paren(Box::new(normalize_prepared_inline_expr(
            *inner,
            view,
            env,
            depth + 1,
            visited,
        ))),
        CExpr::Cast { ty, expr } => CExpr::cast(
            ty,
            normalize_prepared_inline_expr(*expr, view, env, depth + 1, visited),
        ),
        CExpr::AddrOf(inner) => CExpr::AddrOf(Box::new(normalize_prepared_inline_expr(
            *inner,
            view,
            env,
            depth + 1,
            visited,
        ))),
        CExpr::Deref(inner) => CExpr::Deref(Box::new(normalize_prepared_inline_expr(
            *inner,
            view,
            env,
            depth + 1,
            visited,
        ))),
        CExpr::Unary { op, operand } => CExpr::unary(
            op,
            normalize_prepared_inline_expr(*operand, view, env, depth + 1, visited),
        ),
        CExpr::Binary { op, left, right } => CExpr::binary(
            op,
            normalize_prepared_inline_expr(*left, view, env, depth + 1, visited),
            normalize_prepared_inline_expr(*right, view, env, depth + 1, visited),
        ),
        CExpr::Subscript { base, index } => CExpr::Subscript {
            base: Box::new(normalize_prepared_inline_expr(
                *base,
                view,
                env,
                depth + 1,
                visited,
            )),
            index: Box::new(normalize_prepared_inline_expr(
                *index,
                view,
                env,
                depth + 1,
                visited,
            )),
        },
        CExpr::Member { base, member } => CExpr::Member {
            base: Box::new(normalize_prepared_inline_expr(
                *base,
                view,
                env,
                depth + 1,
                visited,
            )),
            member,
        },
        CExpr::PtrMember { base, member } => CExpr::PtrMember {
            base: Box::new(normalize_prepared_inline_expr(
                *base,
                view,
                env,
                depth + 1,
                visited,
            )),
            member,
        },
        CExpr::Call { func, args } => CExpr::Call {
            func: Box::new(normalize_prepared_inline_expr(
                *func,
                view,
                env,
                depth + 1,
                visited,
            )),
            args: args
                .into_iter()
                .map(|arg| normalize_prepared_inline_expr(arg, view, env, depth + 1, visited))
                .collect(),
        },
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => CExpr::Ternary {
            cond: Box::new(normalize_prepared_inline_expr(
                *cond,
                view,
                env,
                depth + 1,
                visited,
            )),
            then_expr: Box::new(normalize_prepared_inline_expr(
                *then_expr,
                view,
                env,
                depth + 1,
                visited,
            )),
            else_expr: Box::new(normalize_prepared_inline_expr(
                *else_expr,
                view,
                env,
                depth + 1,
                visited,
            )),
        },
        CExpr::Comma(items) => CExpr::Comma(
            items
                .into_iter()
                .map(|item| normalize_prepared_inline_expr(item, view, env, depth + 1, visited))
                .collect(),
        ),
        other => other,
    }
}

fn param_alias_for_name(name: &str, env: &PassEnv<'_>) -> Option<String> {
    let lower = name.to_ascii_lowercase();
    if let Some(alias) = env.param_register_aliases.get(&lower) {
        return Some(alias.clone());
    }
    lower
        .rsplit_once('_')
        .filter(|(_, version)| *version == "0")
        .and_then(|(base, _)| env.param_register_aliases.get(base))
        .cloned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::InterprocSummarySet;

    #[test]
    fn prepared_copy_binding_rejects_shared_value_id_before_fact_seeding() {
        let dst = SSAVar::new("dst", 1, 8);
        let src = SSAVar::new("src", 1, 8);
        let mut view = PreparedSemanticView::default();
        view.value_id_by_var.insert(dst.clone(), ValueId(1));
        view.value_id_by_var.insert(src.clone(), ValueId(1));
        view.var_by_value_id.insert(ValueId(1), dst.clone());

        let mut info = UseInfo::default();
        let binding = bind_prepared_copy_ids(&mut info, &view, &dst, &src);
        if let Some((dst_id, src_id)) = binding {
            info.copy_sources_by_value.insert(dst_id, src_id);
            info.forwarded_values_by_value.insert(
                dst_id,
                ValueProvenance {
                    source: src.display_name(),
                    source_value_id: Some(src_id),
                    source_var: Some(src.clone()),
                    stack_slot: None,
                },
            );
        }

        assert_eq!(binding, None);
        assert!(info.copy_sources_by_value.is_empty());
        assert!(info.forwarded_values_by_value.is_empty());
        assert_eq!(info.value_id_for_var(&dst), None);
        assert_eq!(info.value_id_for_var(&src), None);
    }

    #[test]
    fn prepared_copy_provenance_ignores_colliding_display_fact() {
        let dst = SSAVar::new("dst", 1, 8);
        let mut src = SSAVar::constant(1, 8);
        let mut spoof = SSAVar::constant(2, 8);
        src.name = "same".to_string();
        spoof.name = "same".to_string();
        assert_eq!(src.display_name(), spoof.display_name());
        assert_ne!(src, spoof);

        let mut view = PreparedSemanticView::default();
        view.value_id_by_var.insert(dst.clone(), ValueId(1));
        view.value_id_by_var.insert(src.clone(), ValueId(2));
        view.var_by_value_id.insert(ValueId(1), dst.clone());
        view.var_by_value_id.insert(ValueId(2), src.clone());

        let mut info = UseInfo::default();
        assert_eq!(info.bind_value_id(&spoof, ValueId(3)), Some(ValueId(3)));
        info.forwarded_values.insert(
            src.display_name(),
            ValueProvenance {
                source: spoof.display_name(),
                source_value_id: Some(ValueId(3)),
                source_var: Some(spoof),
                stack_slot: Some(-8),
            },
        );

        let (dst_id, src_id) =
            bind_prepared_copy_ids(&mut info, &view, &dst, &src).expect("exact copy binding");
        assert_eq!((dst_id, src_id), (ValueId(1), ValueId(2)));
        assert_eq!(info.forwarded_value_for_var(&src), None);

        let provenance = exact_prepared_copy_provenance(&src, src_id, Some(-8));
        assert_eq!(provenance.source_value_id, Some(ValueId(2)));
        assert_eq!(provenance.source_var, Some(src));
    }

    #[test]
    fn canonical_param_home_uses_rendered_header_alias_and_runtime_offset() {
        let slot = StackSlotKey {
            base: ExternalStackBase::FramePointer,
            offset: 8,
        };
        let binding = VisibleBinding {
            name: "arg0_home".to_string(),
            ty: None,
            kind: VisibleBindingKind::HiddenHome,
            stack_slot: Some(slot.clone()),
            param_index: Some(0),
            source_reg: Some("RDI".to_string()),
        };
        let aliases = HashMap::from([("rdi".to_string(), "arg1".to_string())]);

        assert_eq!(prepared_stack_slot_offset(&slot), -8);
        assert_eq!(
            prepared_binding_arg_alias(&binding, &[], &aliases).as_deref(),
            Some("arg1")
        );

        let legacy_slot = StackSlotKey {
            base: ExternalStackBase::FramePointer,
            offset: -8,
        };
        assert_eq!(prepared_stack_slot_offset(&legacy_slot), -8);
    }

    fn test_var(name: &str, version: u32, size: u32) -> SSAVar {
        SSAVar::new(name, version, size)
    }

    fn test_prepared_artifact() -> SsaArtifact {
        let mut block = R2ILBlock::new(0x1000, 1);
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        SsaArtifact::from_blocks(&[block], None).expect("prepared SSA artifact")
    }

    fn test_prepared_call_artifact() -> SsaArtifact {
        let mut block = R2ILBlock::new(0x1000, 5);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x401000, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        SsaArtifact::from_blocks(&[block], None).expect("prepared call SSA artifact")
    }

    fn test_prepared_branch_artifact() -> SsaArtifact {
        let cond = Varnode::unique(0x2000, 1);
        let mut entry = R2ILBlock::new(0x2000, 4);
        entry.push(R2ILOp::IntEqual {
            dst: cond.clone(),
            a: Varnode::constant(7, 8),
            b: Varnode::constant(9, 8),
        });
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x2010, 8),
            cond,
        });
        let mut fallthrough = R2ILBlock::new(0x2004, 1);
        fallthrough.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut target = R2ILBlock::new(0x2010, 1);
        target.push(R2ILOp::Return {
            target: Varnode::constant(1, 8),
        });
        SsaArtifact::for_decompile(&[entry, fallthrough, target], None)
            .expect("prepared branch SSA artifact")
    }

    fn test_prepared_recursive_call_artifact() -> SsaArtifact {
        let mut block = R2ILBlock::new(0x1500, 8);
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x1500, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        SsaArtifact::raw(&[block], None)
            .expect("prepared recursive call SSA artifact")
            .with_name("sym.self")
    }

    fn test_x86_64_arg_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.add_register(RegisterDef::new("RDI", 0x10, 8));
        arch.add_register(RegisterDef::new("RSI", 0x18, 8));
        arch
    }

    fn test_x86_64_result_arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rsp", 16, 8));
        arch.add_register(RegisterDef::new("rbp", 24, 8));
        arch
    }

    fn test_prepared_two_arg_call_artifact() -> SsaArtifact {
        let arch = test_x86_64_arg_arch();
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0x10, 8),
            src: Varnode::constant(7, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0x18, 8),
            src: Varnode::constant(9, 8),
        });
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x401000, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        SsaArtifact::for_decompile(&[block], Some(&arch))
            .expect("prepared two-arg call SSA artifact")
    }

    fn test_prepared_stack_owned_call_result_artifact() -> SsaArtifact {
        let arch = test_x86_64_result_arch();
        let slot = Varnode::unique(0x1780, 8);
        let stored = Varnode::unique(0x1788, 8);
        let loaded = Varnode::unique(0x1790, 8);
        let alias = Varnode::unique(0x1798, 8);
        let mut block = R2ILBlock::new(0x1780, 6);
        block.push(R2ILOp::IntAdd {
            dst: slot.clone(),
            a: Varnode::register(16, 8),
            b: Varnode::constant(u64::MAX - 7, 8),
        });
        block.push(R2ILOp::Call {
            target: Varnode::constant(0x401000, 8),
        });
        block.push(R2ILOp::Copy {
            dst: stored.clone(),
            src: Varnode::register(0, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: slot.clone(),
            val: stored,
        });
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: slot,
        });
        block.push(R2ILOp::Copy {
            dst: alias,
            src: loaded,
        });
        SsaArtifact::for_decompile(&[block], Some(&arch))
            .expect("prepared stack-owned call result SSA artifact")
    }

    fn test_callsite_facts(prepared: &SsaArtifact) -> r2types::FunctionCallsiteFacts {
        let by_callsite = prepared
            .certificates()
            .callsites
            .values()
            .filter_map(|cert| {
                let (block_addr, op_index) = prepared.inst_op_site(cert.at)?;
                let callsite = CallsiteKey {
                    block_addr,
                    op_index,
                };
                let register_argument_locations = cert
                    .argument_certificates
                    .iter()
                    .filter_map(|argument| {
                        let r2ssa::CallArgumentLocation::Register { name } = &argument.location
                        else {
                            return None;
                        };
                        Some(r2types::RegisterCallArgumentLocationFact {
                            index: argument.index,
                            value: argument.value,
                            name: name.clone(),
                            source_inst: argument.source_inst,
                        })
                    })
                    .collect();
                let stack_argument_locations = cert
                    .argument_certificates
                    .iter()
                    .filter_map(|argument| {
                        let r2ssa::CallArgumentLocation::Stack {
                            object,
                            offset,
                            memory_access,
                        } = argument.location
                        else {
                            return None;
                        };
                        Some(r2types::StackCallArgumentLocationFact {
                            index: argument.index,
                            value: argument.value,
                            object,
                            offset,
                            memory_access,
                            source_inst: argument.source_inst,
                        })
                    })
                    .collect();
                Some((
                    callsite,
                    r2types::CallsiteArgumentFacts {
                        callsite,
                        call_site_id: cert.call_site,
                        at: cert.at,
                        target: cert.target,
                        direct_target: cert.direct_target,
                        argument_values: cert
                            .argument_values
                            .iter()
                            .copied()
                            .enumerate()
                            .map(|(index, value)| r2types::CallArgumentValueFact { index, value })
                            .collect(),
                        register_argument_locations,
                        stack_argument_locations,
                    },
                ))
            })
            .collect();
        r2types::FunctionCallsiteFacts { by_callsite }
    }

    fn leak_function_facts(facts: FunctionFacts) -> &'static FunctionFacts {
        Box::leak(Box::new(facts))
    }

    fn test_control_facts(prepared: &SsaArtifact) -> r2types::FunctionControlFacts {
        let predicates = prepared.predicates();
        let certificates = prepared.certificates();
        let sorted_u64s = |values: &[u64]| {
            let mut values = values.to_vec();
            values.sort_unstable();
            values
        };
        let branch_predicates = predicates
            .predicates
            .values()
            .map(|predicate| {
                (
                    predicate.block_addr,
                    r2types::BranchPredicateFact {
                        id: predicate.id,
                        block_addr: predicate.block_addr,
                        condition: predicate.condition,
                        comparison: predicate.comparison.as_ref().map(|comparison| {
                            r2types::PredicateComparisonFact {
                                kind: comparison.kind,
                                lhs: comparison.lhs,
                                rhs: comparison.rhs,
                            }
                        }),
                        evaluated_comparison: predicate.evaluated_comparison.as_ref().map(
                            |comparison| r2types::PredicateComparisonFact {
                                kind: comparison.kind,
                                lhs: comparison.lhs,
                                rhs: comparison.rhs,
                            },
                        ),
                        render_comparison: predicate.comparison.as_ref().map(|comparison| {
                            r2types::PredicateComparisonFact {
                                kind: comparison.kind,
                                lhs: comparison.lhs,
                                rhs: comparison.rhs,
                            }
                        }),
                        true_target: predicate.true_target,
                        false_target: predicate.false_target,
                    },
                )
            })
            .collect();
        let loops = certificates
            .loops
            .iter()
            .map(|(loop_id, cert)| {
                (
                    *loop_id,
                    r2types::LoopStructureFact {
                        loop_id: *loop_id,
                        proof_node: cert.proof_node.to_string(),
                        header: cert.header,
                        condition: cert.condition,
                        condition_value: cert
                            .condition
                            .and_then(|id| predicates.predicates.get(&id).map(|p| p.condition)),
                        body: sorted_u64s(&cert.body),
                        latches: sorted_u64s(&cert.latches),
                        exits: sorted_u64s(&cert.exits),
                    },
                )
            })
            .collect();
        let switches = prepared
            .predicates()
            .switches
            .iter()
            .map(|(block_addr, switch)| {
                (
                    *block_addr,
                    r2types::SwitchSelectorFact {
                        proof_node: r2ssa::ProofNodeId::switch_certificate(*block_addr).to_string(),
                        block_addr: switch.block_addr,
                        selector: switch.selector,
                        cases: switch.cases.clone(),
                        default: switch.default,
                    },
                )
            })
            .collect();
        let block_assumptions = prepared
            .predicates()
            .block_assumptions
            .iter()
            .map(|(block_addr, assumptions)| {
                (
                    *block_addr,
                    assumptions
                        .iter()
                        .map(|assumption| r2types::ControlBlockAssumptionFact {
                            predecessor: assumption.predecessor,
                            predicate: assumption.predicate,
                            truth: assumption.truth,
                        })
                        .collect(),
                )
            })
            .collect();
        r2types::FunctionControlFacts {
            branch_predicates,
            block_assumptions,
            loops,
            switches,
            control_domains: prepared.control_domains().clone(),
        }
    }

    #[test]
    fn prepared_call_expr_requires_argument_value_bijection() {
        let unproved = PreparedCallView {
            callee_identity: Some(CalleeIdentity::from_name("sym.helper")),
            authoritative_args: vec![CExpr::IntLit(7)],
            authoritative_arg_values: Vec::new(),
            ..PreparedCallView::default()
        };
        assert!(
            prepared_call_expr_from_view(&unproved).is_none(),
            "prepared call expressions must not carry rendered args without ValueId proof"
        );

        let missing_render_fact = PreparedCallView {
            callee_identity: Some(CalleeIdentity::from_name("sym.helper")),
            authoritative_args: vec![CExpr::IntLit(7)],
            authoritative_arg_values: vec![ValueId(7)],
            ..PreparedCallView::default()
        };
        assert!(
            prepared_call_expr_from_view(&missing_render_fact).is_none(),
            "prepared call expressions require FunctionFacts call-render authorization"
        );

        let proved = PreparedCallView {
            callee_identity: Some(CalleeIdentity::from_name("sym.helper")),
            authoritative_args: vec![CExpr::IntLit(7)],
            authoritative_arg_values: vec![ValueId(7)],
            render_fact: Some(r2types::CallsiteRenderFact {
                callsite: CallsiteKey {
                    block_addr: 0x1000,
                    op_index: 0,
                },
                target: None,
                disposition: r2types::CallsiteRenderDisposition::SideEffectStatement,
                proof_values: vec![ValueId(7)],
                residual_reason: None,
            }),
            ..PreparedCallView::default()
        };
        assert_eq!(
            prepared_call_expr_from_view(&proved),
            Some(CExpr::Call {
                func: Box::new(CExpr::Var("sym.helper".to_string())),
                args: vec![CExpr::IntLit(7)],
            })
        );
    }

    #[test]
    fn prepared_view_resolves_authoritative_call_arg_by_value() {
        let site = (0x1000, 2);
        let view = PreparedSemanticView {
            call_view_by_site: BTreeMap::from([(
                site,
                PreparedCallView {
                    authoritative_args: vec![CExpr::Var("n".to_string()), CExpr::IntLit(7)],
                    authoritative_arg_values: vec![ValueId(26), ValueId(27)],
                    ..PreparedCallView::default()
                },
            )]),
            ..PreparedSemanticView::default()
        };

        assert_eq!(
            view.authoritative_call_arg_expr_for_value(site, ValueId(26)),
            Some(CExpr::Var("n".to_string()))
        );
        assert_eq!(
            view.authoritative_call_arg_expr_for_value(site, ValueId(99)),
            None
        );
        assert_eq!(
            view.authoritative_call_arg_expr_for_value((0x2000, 0), ValueId(26)),
            None
        );
    }

    #[test]
    fn prepared_scalar_expr_orders_commutative_params_by_abi_rank() {
        let view = PreparedSemanticView {
            param_rank_by_alias: HashMap::from([
                ("op".to_string(), 0),
                ("a".to_string(), 1),
                ("b".to_string(), 2),
            ]),
            ..PreparedSemanticView::default()
        };

        let expr = prepared_simplify_binary_expr(
            &view,
            BinaryOp::BitXor,
            CExpr::Var("b".to_string()),
            CExpr::Var("a".to_string()),
        );

        assert_eq!(
            expr,
            CExpr::binary(
                BinaryOp::BitXor,
                CExpr::Var("a".to_string()),
                CExpr::Var("b".to_string())
            )
        );
    }

    #[test]
    fn prepared_scalar_expr_simplifies_repeated_scaled_add() {
        let view = PreparedSemanticView {
            param_rank_by_alias: HashMap::from([("a".to_string(), 1)]),
            ..PreparedSemanticView::default()
        };
        let expr = prepared_simplify_binary_expr(
            &view,
            BinaryOp::Add,
            CExpr::Var("a".to_string()),
            CExpr::binary(BinaryOp::Mul, CExpr::Var("a".to_string()), CExpr::IntLit(2)),
        );

        assert_eq!(
            expr,
            CExpr::binary(BinaryOp::Mul, CExpr::Var("a".to_string()), CExpr::IntLit(3))
        );
    }

    #[test]
    fn prepared_scalar_expr_collects_nested_linear_adds_by_param_rank() {
        let view = PreparedSemanticView {
            param_rank_by_alias: HashMap::from([("a".to_string(), 1), ("b".to_string(), 2)]),
            ..PreparedSemanticView::default()
        };
        let expr = prepared_simplify_binary_expr(
            &view,
            BinaryOp::Add,
            CExpr::Var("b".to_string()),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("a".to_string()),
                CExpr::binary(
                    BinaryOp::Add,
                    CExpr::Var("a".to_string()),
                    CExpr::Var("a".to_string()),
                ),
            ),
        );

        assert_eq!(
            expr,
            CExpr::binary(
                BinaryOp::Add,
                CExpr::binary(BinaryOp::Mul, CExpr::Var("a".to_string()), CExpr::IntLit(3)),
                CExpr::Var("b".to_string())
            )
        );
    }

    #[test]
    fn prepared_view_build_preserves_param_alias_contract() {
        let prepared = test_prepared_artifact();
        let abi_arg_regs = vec!["rdi".to_string(), "rsi".to_string()];
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::from([
            ("rdi".to_string(), "argc".to_string()),
            ("rsi".to_string(), "argv".to_string()),
        ]);

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: leak_function_facts(FunctionFacts::default()),
            certified_rendering_required: false,
        });

        assert_eq!(view.param_alias_by_reg, param_register_aliases);
        assert_eq!(view.param_rank_by_alias.get("argc"), Some(&0));
        assert_eq!(view.param_rank_by_alias.get("argv"), Some(&1));
    }

    #[test]
    fn prepared_view_prefers_typed_callee_resolution_over_raw_name_maps() {
        let prepared = test_prepared_call_artifact();
        let abi_arg_regs = vec!["rdi".to_string(), "rsi".to_string()];
        let resolution_function_names = HashMap::from([(0x401000, "sym.imp.printf".to_string())]);
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_function_signatures = HashMap::new();
        let resolution_ctx = r2types::CalleeIdentityContext {
            function_names: &resolution_function_names,
            symbols: &symbols,
            callee_facts: &callee_facts,
            known_function_signatures: &known_function_signatures,
        };
        let callee_resolution = CalleeResolutionFacts::from_direct_call_targets(
            [(
                CallsiteKey {
                    block_addr: 0x1000,
                    op_index: 0,
                },
                0x401000,
            )],
            &resolution_ctx,
        );
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();
        let function_facts =
            FunctionFacts::default().with_callee_resolution(callee_resolution.clone());

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: &function_facts,
            certified_rendering_required: false,
        });

        let call_view = view
            .call_view_for_site((0x1000, 0))
            .expect("direct callsite should have prepared call view");
        let identity = call_view
            .callee_identity
            .as_ref()
            .expect("direct callsite should have typed callee identity");
        assert_eq!(identity.display_name.as_deref(), Some("sym.imp.printf"));
        assert_eq!(identity.primary_key(), "printf");
        assert!(identity.is_imported_name_hint());
        let resolved =
            CalleeResolutionFacts::resolve_target_policy(r2types::CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: Some(&callee_resolution),
                    callsite: None,
                    prepared_identity: Some(identity),
                    prepared_direct_target: None,
                    direct_target_context: None,
                },
                callee_facts: &callee_facts,
            })
            .expect("typed callee identity should resolve policy");
        assert!(
            !resolved.policy.imported,
            "typed function names alone must not authorize imported-call policy"
        );
    }

    #[test]
    fn prepared_view_uses_typed_direct_addr_identity_through_callsite_facts() {
        let prepared = test_prepared_call_artifact();
        let abi_arg_regs = vec!["rdi".to_string(), "rsi".to_string()];
        let key = r2types::CalleeIdentityKey::DirectAddress(0x401000);
        let mut callee_resolution = CalleeResolutionFacts::default();
        callee_resolution
            .by_direct_addr
            .insert(0x401000, key.clone());
        callee_resolution
            .by_key
            .insert(key, CalleeIdentity::from_name("sym.imp.printf"));
        let callee_facts = BTreeMap::new();
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();
        let callsite_facts = test_callsite_facts(&prepared);
        let function_facts = FunctionFacts::default()
            .with_callee_resolution(callee_resolution.clone())
            .with_callsites(callsite_facts.clone());

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: &function_facts,
            certified_rendering_required: false,
        });

        let call_view = view
            .call_view_for_site((0x1000, 0))
            .expect("direct callsite should have prepared call view");
        assert_eq!(call_view.direct_target, Some(0x401000));
        let identity = call_view
            .callee_identity
            .as_ref()
            .expect("direct-address identity should be certified through callsite facts");
        assert_eq!(identity.display_name.as_deref(), Some("sym.imp.printf"));
        assert!(identity.is_imported_name_hint());
        let resolved =
            CalleeResolutionFacts::resolve_target_policy(r2types::CalleeTargetResolutionRequest {
                identity: CalleeTargetIdentityRequest {
                    resolution: Some(&callee_resolution),
                    callsite: None,
                    prepared_identity: Some(identity),
                    prepared_direct_target: None,
                    direct_target_context: None,
                },
                callee_facts: &callee_facts,
            })
            .expect("direct-address callee identity should resolve policy");
        assert!(
            !resolved.policy.imported,
            "direct-address identities built from raw names remain import hints only"
        );
    }

    #[test]
    fn prepared_view_requires_callsite_facts_for_direct_addr_identity() {
        let prepared = test_prepared_call_artifact();
        let abi_arg_regs = vec!["rdi".to_string(), "rsi".to_string()];
        let key = r2types::CalleeIdentityKey::DirectAddress(0x401000);
        let mut callee_resolution = CalleeResolutionFacts::default();
        callee_resolution
            .by_direct_addr
            .insert(0x401000, key.clone());
        callee_resolution
            .by_key
            .insert(key, CalleeIdentity::from_name("sym.imp.printf"));
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();
        let function_facts =
            FunctionFacts::default().with_callee_resolution(callee_resolution.clone());

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: &function_facts,
            certified_rendering_required: false,
        });

        let call_view = view
            .call_view_for_site((0x1000, 0))
            .expect("direct callsite should have prepared call view");
        assert_eq!(
            call_view.direct_target, None,
            "prepared semantic view must not reparse direct targets from SSA names"
        );
        assert!(
            call_view.callee_identity.is_none(),
            "direct-address callee identity requires FunctionFacts direct-target evidence"
        );
    }

    #[test]
    fn prepared_view_refuses_raw_callee_identity_without_typed_resolution() {
        let prepared = test_prepared_call_artifact();
        let abi_arg_regs = vec!["rdi".to_string(), "rsi".to_string()];
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: leak_function_facts(FunctionFacts::default()),
            certified_rendering_required: false,
        });

        let call_view = view
            .call_view_for_site((0x1000, 0))
            .expect("direct callsite should have prepared call view");
        assert!(
            call_view.callee_identity.is_none(),
            "prepared semantic view must not certify raw callee names without typed resolution"
        );
        assert!(
            prepared_call_expr_from_view(call_view).is_none(),
            "prepared calls must not fall back to fabricated sub_<addr> expressions"
        );
    }

    #[test]
    fn prepared_view_refuses_recursive_name_identity_without_typed_resolution() {
        let prepared = test_prepared_recursive_call_artifact();
        assert_eq!(
            prepared.structured().recursive_calls.len(),
            1,
            "fixture should expose a structural recursive call"
        );
        let abi_arg_regs = vec!["rdi".to_string(), "rsi".to_string()];
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: leak_function_facts(FunctionFacts::default()),
            certified_rendering_required: false,
        });

        let call_view = view
            .call_view_for_site((0x1500, 0))
            .expect("recursive direct callsite should have prepared call view");
        assert!(
            call_view.callee_identity.is_none(),
            "recursive function names are not callee identity evidence"
        );
    }

    #[test]
    fn prepared_call_arity_prefers_typed_callee_signature_over_summary_hint() {
        let prepared = test_prepared_two_arg_call_artifact();
        let abi_arg_regs = vec!["rdi".to_string(), "rsi".to_string()];
        let typed_function_names = HashMap::from([(0x401000, "sym.imp.one_arg".to_string())]);
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_function_signatures = HashMap::from([(
            "sym.imp.one_arg".to_string(),
            r2types::FunctionType {
                return_type: r2types::CTypeLike::Void,
                params: vec![r2types::CTypeLike::Int {
                    bits: 32,
                    signedness: r2types::Signedness::Signed,
                }],
                variadic: false,
            },
        )]);
        let resolution_ctx = r2types::CalleeIdentityContext {
            function_names: &typed_function_names,
            symbols: &symbols,
            callee_facts: &callee_facts,
            known_function_signatures: &known_function_signatures,
        };
        let callee_resolution = CalleeResolutionFacts::from_direct_call_targets(
            [(
                CallsiteKey {
                    block_addr: 0x1000,
                    op_index: 2,
                },
                0x401000,
            )],
            &resolution_ctx,
        );
        let mut summaries = InterprocSummarySet::default();
        let summary_id = r2ssa::InterprocFunctionId(0x401000);
        let mut summary =
            r2ssa::FunctionSemanticSummary::unknown(summary_id, Some("sym.local_two_arg".into()));
        summary.arg_count_hint = Some(2);
        summaries.summaries.insert(summary_id, summary);
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();
        let callsite_facts = test_callsite_facts(&prepared);
        let function_facts = FunctionFacts::default()
            .with_callee_resolution(callee_resolution.clone())
            .with_callsites(callsite_facts.clone());

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: &function_facts,
            certified_rendering_required: false,
        });

        let call_view = view
            .call_view_for_site((0x1000, 2))
            .expect("direct callsite should have prepared call view");
        assert_eq!(
            call_view
                .callee_identity
                .as_ref()
                .and_then(CalleeIdentity::non_variadic_known_arity),
            Some(1)
        );
        assert_eq!(call_view.authoritative_args, vec![CExpr::IntLit(7)]);
    }

    #[test]
    fn prepared_call_args_require_function_facts_callsite_contract() {
        let prepared = test_prepared_two_arg_call_artifact();
        let abi_arg_regs = vec!["rdi".to_string(), "rsi".to_string()];
        let mut summaries = InterprocSummarySet::default();
        let summary_id = r2ssa::InterprocFunctionId(0x401000);
        let mut summary =
            r2ssa::FunctionSemanticSummary::unknown(summary_id, Some("sym.local_two_arg".into()));
        summary.arg_count_hint = Some(1);
        summaries.summaries.insert(summary_id, summary);
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: leak_function_facts(FunctionFacts::default()),
            certified_rendering_required: false,
        });

        let call_view = view
            .call_view_for_site((0x1000, 2))
            .expect("direct callsite should have prepared call view");
        assert_eq!(
            call_view.authoritative_args,
            Vec::<CExpr>::new(),
            "prepared call rendering must not infer authoritative args without FunctionFacts callsite facts"
        );
    }

    #[test]
    fn prepared_call_args_require_function_facts_location_contract() {
        let prepared = test_prepared_two_arg_call_artifact();
        let abi_arg_regs = vec!["rdi".to_string(), "rsi".to_string()];
        let mut callsite_facts = test_callsite_facts(&prepared);
        let call_facts = callsite_facts
            .by_callsite
            .get_mut(&CallsiteKey {
                block_addr: 0x1000,
                op_index: 2,
            })
            .expect("fixture callsite facts");
        call_facts.register_argument_locations.clear();
        call_facts.stack_argument_locations.clear();
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();
        let function_facts = FunctionFacts::default().with_callsites(callsite_facts.clone());

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: &function_facts,
            certified_rendering_required: false,
        });

        let call_view = view
            .call_view_for_site((0x1000, 2))
            .expect("direct callsite should have prepared call view");
        assert_eq!(
            call_view.authoritative_args,
            Vec::<CExpr>::new(),
            "ordered values alone must not authorize executable call args without location proof"
        );
    }

    #[test]
    fn prepared_call_args_use_function_facts_callsite_contract() {
        let prepared = test_prepared_two_arg_call_artifact();
        let abi_arg_regs = vec!["rdi".to_string(), "rsi".to_string()];
        let callsite_facts = test_callsite_facts(&prepared);
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();
        let function_facts = FunctionFacts::default().with_callsites(callsite_facts.clone());

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: &function_facts,
            certified_rendering_required: false,
        });

        let call_view = view
            .call_view_for_site((0x1000, 2))
            .expect("direct callsite should have prepared call view");
        assert_eq!(
            call_view.authoritative_args,
            vec![CExpr::IntLit(7), CExpr::IntLit(9)]
        );
    }

    #[test]
    fn prepared_call_result_owner_requires_function_facts_contract() {
        let prepared = test_prepared_stack_owned_call_result_artifact();
        let abi_arg_regs = Vec::new();
        let stack_slots = BTreeMap::from([(
            StackSlotKey {
                base: r2types::ExternalStackBase::StackPointer,
                offset: -8,
            },
            ExternalStackSlotSpec {
                name: "call_result".to_string(),
                role: ExternalStackSlotRole::Local,
                ..ExternalStackSlotSpec::default()
            },
        )]);
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: leak_function_facts(FunctionFacts::default()),
            certified_rendering_required: false,
        });

        let call_view = view
            .call_view_for_site((0x1780, 1))
            .expect("direct callsite should have prepared call view");
        assert_eq!(
            call_view.result_owner, None,
            "prepared SSA call-result certificates must not bypass FunctionFacts"
        );
        assert!(
            view.call_result_source_by_value.is_empty(),
            "call-result source indexes must be populated from FunctionFacts, not local prepared SSA reads"
        );
    }

    #[test]
    fn prepared_branch_predicates_require_function_facts_control_contract() {
        let prepared = test_prepared_branch_artifact();
        assert!(
            !prepared.predicates().predicates.is_empty(),
            "fixture must expose raw prepared predicate facts"
        );
        let abi_arg_regs = Vec::new();
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: leak_function_facts(FunctionFacts::default()),
            certified_rendering_required: false,
        });

        assert!(
            view.branch_predicate_expr_by_block.is_empty(),
            "prepared semantic view must not render branch predicates from raw prepared SSA side channels"
        );
    }

    #[test]
    fn prepared_branch_predicates_use_function_facts_control_contract() {
        let prepared = test_prepared_branch_artifact();
        let control_facts = test_control_facts(&prepared);
        let abi_arg_regs = Vec::new();
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let param_register_aliases = HashMap::new();
        let function_facts = FunctionFacts::default().with_control(control_facts.clone());

        let view = PreparedSemanticView::build(PreparedSemanticViewInputs {
            prepared: &prepared,
            abi_arg_regs: &abi_arg_regs,
            stack_slots: &stack_slots,
            visible_bindings: &visible_bindings,
            param_register_aliases: &param_register_aliases,
            function_facts: &function_facts,
            certified_rendering_required: false,
        });

        assert_eq!(
            view.branch_expr_for_block(0x2000),
            Some(&CExpr::binary(
                BinaryOp::Eq,
                CExpr::IntLit(7),
                CExpr::IntLit(9)
            )),
            "branch predicate rendering must be authorized by FunctionFacts control evidence"
        );
    }

    #[test]
    fn prepared_runtime_facts_preserve_env_type_hints() {
        let prepared = test_prepared_artifact();
        let view = PreparedSemanticView::default();
        let blocks: Vec<SSABlock> = Vec::new();
        let function_names = HashMap::new();
        let strings = HashMap::new();
        let symbols = HashMap::new();
        let arg_regs = Vec::new();
        let param_register_aliases = HashMap::new();
        let caller_saved_regs = HashSet::new();
        let type_hints = HashMap::from([("result".to_string(), crate::ast::CType::u64())]);
        let env = PassEnv {
            string_literals: crate::analysis::lower::no_string_literals(),
            ptr_size: 8,
            sp_name: "rsp",
            fp_name: "rbp",
            ret_reg_name: "rax",
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            callee_facts: crate::analysis::empty_callee_facts(),
            callee_resolution: None,
            summary_view: None,
            arg_regs: &arg_regs,
            param_register_aliases: &param_register_aliases,
            caller_saved_regs: &caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };

        let facts = build_prepared_runtime_facts(&blocks, &env, &prepared, &view);

        assert_eq!(facts.use_info.type_hints, type_hints);
    }

    #[test]
    fn prepared_definition_safety_uses_typed_storage_classification() {
        let function_names = HashMap::new();
        let strings = HashMap::new();
        let symbols = HashMap::new();
        let arg_regs = vec!["RDI".to_string()];
        let param_register_aliases = HashMap::new();
        let caller_saved_regs = HashSet::from(["RCX".to_string()]);
        let type_hints: HashMap<String, crate::ast::CType> = HashMap::new();
        let env = PassEnv {
            string_literals: crate::analysis::lower::no_string_literals(),
            ptr_size: 8,
            sp_name: "RSP",
            fp_name: "RBP",
            ret_reg_name: "RAX",
            function_names: &function_names,
            strings: &strings,
            symbols: &symbols,
            callee_facts: crate::analysis::empty_callee_facts(),
            callee_resolution: None,
            summary_view: None,
            arg_regs: &arg_regs,
            param_register_aliases: &param_register_aliases,
            caller_saved_regs: &caller_saved_regs,
            type_hints: &type_hints,
            type_oracle: None,
        };

        assert!(!prepared_render_definition_is_safe(
            &CExpr::Var("tmp:1".to_string()),
            &env
        ));
        assert!(!prepared_render_definition_is_safe(
            &CExpr::Var("ram:401000".to_string()),
            &env
        ));
        assert!(!prepared_render_definition_is_safe(
            &CExpr::Var("unique:1".to_string()),
            &env
        ));
        assert!(!prepared_render_definition_is_safe(
            &CExpr::Var("RDI".to_string()),
            &env
        ));
        assert!(!prepared_render_definition_is_safe(
            &CExpr::Var("RBP".to_string()),
            &env
        ));
        assert!(!prepared_render_definition_is_safe(
            &CExpr::Var("RAX".to_string()),
            &env
        ));
        assert!(!prepared_render_definition_is_safe(
            &CExpr::Var("RCX".to_string()),
            &env
        ));
        assert!(prepared_render_definition_is_safe(
            &CExpr::Var("const:1".to_string()),
            &env
        ));
        assert!(prepared_render_definition_is_safe(
            &CExpr::Var("space1:20".to_string()),
            &env
        ));
        assert!(prepared_render_definition_is_safe(
            &CExpr::Var("value".to_string()),
            &env
        ));
    }

    #[test]
    fn prepared_fallback_visible_expr_rejects_only_unrenderable_storage_names() {
        assert_eq!(
            prepared_fallback_visible_expr(&SSAVar::constant(1, 8)),
            None
        );
        assert_eq!(
            prepared_fallback_visible_expr(&test_var("tmp:1", 0, 8)),
            None
        );
        assert_eq!(
            prepared_fallback_visible_expr(&test_var("ram:401000", 0, 8)),
            None
        );
        assert_eq!(
            prepared_fallback_visible_expr(&test_var("unique:1", 0, 8)),
            None
        );
        assert_eq!(
            prepared_fallback_visible_expr(&test_var("space1:20", 0, 8)),
            Some(CExpr::Var("space1:20".to_string()))
        );
        assert_eq!(
            prepared_fallback_visible_expr(&test_var("rax", 0, 8)),
            Some(CExpr::Var("rax".to_string()))
        );
    }

    #[test]
    fn self_render_definition_uses_typed_temporary_render_name() {
        let dst = test_var("tmp:11f80", 2, 8);
        assert!(is_self_render_definition(
            &dst,
            &CExpr::Var("t11f80_2".to_string())
        ));
        assert!(is_self_render_definition(
            &dst,
            &CExpr::Var(dst.display_name())
        ));
        assert!(!is_self_render_definition(
            &dst,
            &CExpr::Var("t11f80_3".to_string())
        ));

        let version_zero_temp = test_var("tmp:11f80", 0, 8);
        assert!(is_self_render_definition(
            &version_zero_temp,
            &CExpr::Var("t11f80".to_string())
        ));
        assert!(!is_self_render_definition(
            &version_zero_temp,
            &CExpr::Var("t11f80_0".to_string())
        ));

        let versioned_reg = test_var("rax", 2, 8);
        assert!(is_self_render_definition(
            &versioned_reg,
            &CExpr::Var("rax_2".to_string())
        ));
        assert!(!is_self_render_definition(
            &versioned_reg,
            &CExpr::Var("rax".to_string())
        ));

        let version_zero_reg = test_var("rbx", 0, 8);
        assert!(is_self_render_definition(
            &version_zero_reg,
            &CExpr::Var("rbx".to_string())
        ));
        assert!(!is_self_render_definition(
            &version_zero_reg,
            &CExpr::Var("rbx_0".to_string())
        ));
    }

    #[test]
    fn prepared_signed_dividend_expr_collapses_cdq_pair_to_low_root() {
        let eax = test_var("EAX", 1, 4);
        let edx = test_var("EDX", 1, 4);
        let sext = test_var("tmp:sext", 1, 8);
        let high_zext = test_var("tmp:high_zext", 1, 8);
        let shifted_high = test_var("tmp:shifted_high", 1, 8);
        let low_zext = test_var("tmp:low_zext", 1, 8);
        let dividend = test_var("tmp:dividend", 1, 8);
        let shift = SSAVar::constant(32, 8);

        let sext_op = SSAOp::IntSExt {
            dst: sext.clone(),
            src: eax.clone(),
        };
        let high_op = SSAOp::Subpiece {
            dst: edx.clone(),
            src: sext.clone(),
            offset: 4,
        };
        let high_zext_op = SSAOp::IntZExt {
            dst: high_zext.clone(),
            src: edx.clone(),
        };
        let shift_op = SSAOp::IntLeft {
            dst: shifted_high.clone(),
            a: high_zext.clone(),
            b: shift,
        };
        let low_zext_op = SSAOp::IntZExt {
            dst: low_zext.clone(),
            src: eax.clone(),
        };
        let dividend_op = SSAOp::IntOr {
            dst: dividend.clone(),
            a: shifted_high.clone(),
            b: low_zext.clone(),
        };

        let producers = HashMap::from([
            (sext.clone(), &sext_op),
            (edx, &high_op),
            (high_zext, &high_zext_op),
            (shifted_high, &shift_op),
            (low_zext, &low_zext_op),
            (dividend.clone(), &dividend_op),
        ]);
        let view = PreparedSemanticView {
            owner_expr_by_name: HashMap::from([(eax.display_name(), CExpr::Var("a".to_string()))]),
            ..PreparedSemanticView::default()
        };

        assert_eq!(
            prepared_signed_dividend_expr(&view, &producers, &dividend),
            Some(CExpr::Var("a".to_string()))
        );
    }

    #[test]
    fn prepared_signed_dividend_expr_accepts_direct_sign_extended_high_limb() {
        let eax = test_var("EAX", 1, 4);
        let sext = test_var("tmp:sext", 1, 8);
        let high_zext = test_var("tmp:high_zext", 1, 8);
        let shifted_high = test_var("tmp:shifted_high", 1, 8);
        let low_zext = test_var("tmp:low_zext", 1, 8);
        let dividend = test_var("tmp:dividend", 1, 8);
        let shift = SSAVar::constant(32, 8);

        let sext_op = SSAOp::IntSExt {
            dst: sext.clone(),
            src: eax.clone(),
        };
        let high_zext_op = SSAOp::IntZExt {
            dst: high_zext.clone(),
            src: sext.clone(),
        };
        let shift_op = SSAOp::IntLeft {
            dst: shifted_high.clone(),
            a: high_zext.clone(),
            b: shift,
        };
        let low_zext_op = SSAOp::IntZExt {
            dst: low_zext.clone(),
            src: eax.clone(),
        };
        let dividend_op = SSAOp::IntOr {
            dst: dividend.clone(),
            a: shifted_high.clone(),
            b: low_zext.clone(),
        };

        let producers = HashMap::from([
            (sext.clone(), &sext_op),
            (high_zext, &high_zext_op),
            (shifted_high, &shift_op),
            (low_zext, &low_zext_op),
            (dividend.clone(), &dividend_op),
        ]);
        let view = PreparedSemanticView {
            owner_expr_by_name: HashMap::from([(eax.display_name(), CExpr::Var("a".to_string()))]),
            ..PreparedSemanticView::default()
        };

        assert_eq!(
            prepared_signed_dividend_expr(&view, &producers, &dividend),
            Some(CExpr::Var("a".to_string()))
        );
    }

    #[test]
    fn prepared_select_has_render_definition() {
        assert!(prepared_op_has_render_definition(&SSAOp::Select {
            dst: test_var("tmp:result", 1, 4),
            cond: test_var("tmp:cond", 1, 1),
            if_true: test_var("W0", 1, 4),
            if_false: test_var("W1", 1, 4),
        }));
    }
}
