use std::collections::{BTreeMap, HashMap, HashSet};

use r2ssa::function::DefLocation;
use r2ssa::{
    CompareKind, InterprocSummarySet, MemoryLocation, ObjectKind, SSAOp, SSAVar, SsaArtifact,
    ValueId,
};
use r2types::{
    CalleeFact, ExternalStackSlotRole, ExternalStackSlotSpec, StackSlotKey, VisibleBinding,
    VisibleBindingKind,
};

use super::{
    BaseRef, CallArgBinding, DecompilerFacts, FlagInfo, NormalizedAddr, PassEnv, ScalarValue,
    SemanticCallArg, SemanticOwnershipFacts, SemanticValue, StackInfo, StackSlotProvenance,
    StackSlotValueKind, UseInfo, ValueProvenance, ValueRef,
};
use crate::analysis::utils::{compare_const_to_expr, compare_const_to_expr_with_width};
use crate::ast::{BinaryOp, CExpr, UnaryOp};
use crate::fold::SSABlock;
use crate::fold::op_lower::is_generic_stack_placeholder_alias;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StackAliasView {
    pub(crate) visible_name: String,
    pub(crate) arg_alias: Option<String>,
    pub(crate) binding_kind: Option<VisibleBindingKind>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub(crate) struct PreparedCallView {
    pub(crate) direct_target: Option<u64>,
    pub(crate) callee_name: Option<String>,
    pub(crate) authoritative_args: Vec<CExpr>,
    pub(crate) result_owner: Option<CExpr>,
}

#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct PreparedSemanticView {
    pub(crate) stack_aliases_by_offset: BTreeMap<i64, StackAliasView>,
    pub(crate) param_alias_by_reg: HashMap<String, String>,
    pub(crate) value_id_by_var: HashMap<SSAVar, ValueId>,
    pub(crate) var_by_value_id: HashMap<ValueId, SSAVar>,
    pub(crate) owner_expr_by_value: HashMap<ValueId, CExpr>,
    pub(crate) owner_expr_by_name: HashMap<String, CExpr>,
    pub(crate) stack_offset_by_value: HashMap<ValueId, i64>,
    pub(crate) predicate_expr_by_value: HashMap<ValueId, CExpr>,
    pub(crate) predicate_expr_by_name: HashMap<String, CExpr>,
    pub(crate) branch_predicate_expr_by_block: BTreeMap<u64, CExpr>,
    pub(crate) call_view_by_site: BTreeMap<(u64, usize), PreparedCallView>,
    pub(crate) call_result_source_by_value: HashMap<ValueId, (u64, usize)>,
    pub(crate) call_result_source_by_name: HashMap<String, (u64, usize)>,
    pub(crate) switch_selector_expr_by_block: BTreeMap<u64, CExpr>,
}

pub(crate) struct PreparedSemanticViewInputs<'a> {
    pub(crate) prepared: &'a SsaArtifact,
    pub(crate) interproc_summary_set: Option<&'a InterprocSummarySet>,
    pub(crate) abi_arg_regs: &'a [String],
    pub(crate) ret_reg_name: &'a str,
    pub(crate) function_names: &'a HashMap<u64, String>,
    pub(crate) symbols: &'a HashMap<u64, String>,
    pub(crate) callee_facts: &'a BTreeMap<u64, CalleeFact>,
    pub(crate) stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    pub(crate) visible_bindings: &'a [VisibleBinding],
    pub(crate) param_register_aliases: &'a HashMap<String, String>,
}

impl PreparedSemanticView {
    pub(crate) fn build(inputs: PreparedSemanticViewInputs<'_>) -> Self {
        let mut view = Self {
            param_alias_by_reg: inputs.param_register_aliases.clone(),
            ..Self::default()
        };
        view.init_value_indexes(inputs.prepared);

        populate_stack_aliases(&mut view, &inputs);
        populate_stack_offsets(&mut view, inputs.prepared);
        overlay_param_home_stack_aliases(&mut view, &inputs);
        populate_owner_exprs(&mut view, inputs.prepared);
        populate_call_result_sources(&mut view, inputs.prepared, inputs.ret_reg_name);
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
            .or_else(|| self.owner_expr_by_name.get(&var.name))
    }

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

    fn insert_call_result_source(&mut self, var: &SSAVar, site: (u64, usize)) {
        if let Some(value_id) = self.value_id_for_var(var) {
            self.call_result_source_by_value.insert(value_id, site);
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

fn prepared_call_site_tuple(
    prepared: &SsaArtifact,
    inst_id: r2ssa::InstId,
) -> Option<(u64, usize)> {
    prepared.inst_op_site(inst_id)
}

pub(crate) fn build_prepared_runtime_facts(
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) -> DecompilerFacts {
    let mut use_info = UseInfo {
        type_hints: env.type_hints.clone(),
        ..UseInfo::default()
    };
    let mut flag_info = FlagInfo::default();
    let mut stack_info = StackInfo::default();

    seed_prepared_param_aliases(&mut use_info, blocks, env);
    seed_prepared_stack_facts(&mut use_info, &mut stack_info, prepared, view);
    collect_prepared_runtime_facts(&mut use_info, &mut flag_info, blocks, env, prepared, view);
    populate_prepared_call_runtime_facts(&mut use_info, blocks, env, prepared, view);
    overlay_local_struct_semantics(&mut use_info, blocks, env);
    overlay_prepared_switch_roots(&mut use_info, prepared);
    finalize_prepared_call_inlining(&mut use_info);

    DecompilerFacts {
        use_info,
        ownership: SemanticOwnershipFacts::default(),
        flag_info,
        stack_info,
    }
}

fn overlay_local_struct_semantics(use_info: &mut UseInfo, blocks: &[SSABlock], env: &PassEnv<'_>) {
    let semantic = UseInfo::analyze_for_local_struct_accesses(blocks, env);
    for (name, value) in semantic.semantic_values {
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
        use_info.ptr_members.entry(name).or_insert(fact);
    }
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
        let entry = view
            .stack_aliases_by_offset
            .entry(slot.offset)
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
        let name = prepared_stack_visible_name(slot);
        let visible_name = name
            .clone()
            .unwrap_or_else(|| synthetic_stack_name(slot_key.offset));
        let entry = view
            .stack_aliases_by_offset
            .entry(slot_key.offset)
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

fn prepared_binding_arg_alias(
    binding: &VisibleBinding,
    visible_bindings: &[VisibleBinding],
    param_register_aliases: &HashMap<String, String>,
) -> Option<String> {
    match binding.kind {
        VisibleBindingKind::Param => {
            let name = binding.name.trim();
            (!name.is_empty()).then(|| name.to_string())
        }
        VisibleBindingKind::HiddenHome => binding
            .param_index
            .and_then(|idx| {
                visible_bindings.iter().find_map(|candidate| {
                    (candidate.kind == VisibleBindingKind::Param
                        && candidate.param_index == Some(idx)
                        && !candidate.name.trim().is_empty())
                    .then(|| candidate.name.trim().to_string())
                })
            })
            .or_else(|| {
                binding
                    .source_reg
                    .as_deref()
                    .and_then(|reg| param_register_aliases.get(&reg.to_ascii_lowercase()))
                    .cloned()
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
        for op in &block.ops {
            let SSAOp::Store { addr, val, .. } = op else {
                continue;
            };
            let Some(offset) = view
                .stack_offset_for_var(addr)
                .or_else(|| stack_offset_for_value(inputs.prepared, addr))
            else {
                continue;
            };
            let Some(arg_alias) = param_alias_for_var(inputs.param_register_aliases, val) else {
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

fn populate_stack_offsets(view: &mut PreparedSemanticView, prepared: &SsaArtifact) {
    let Some(prep) = prepared.function().decompile_prep_facts() else {
        return;
    };
    for var in prep.stack_address_roots.keys() {
        if let Some(offset) = prep.stack_address_root_of(var).map(|root| root.offset) {
            view.insert_stack_offset(var, offset);
        }
    }
    for (&value_id, object_id) in &prepared.objects().value_objects {
        if let Some(object) = prepared.objects().object(*object_id)
            && let Some(offset) = stack_offset_for_object_kind(&object.kind)
            && let Some(value) = prepared_var(prepared, value_id)
        {
            view.insert_stack_offset(value, offset);
        }
    }
}

fn populate_owner_exprs(view: &mut PreparedSemanticView, prepared: &SsaArtifact) {
    for (value, offset) in view.stack_offset_entries() {
        if !is_prepared_stack_address_carrier(prepared, &value) {
            continue;
        }
        let Some(alias) = preferred_stack_alias_name(view, offset) else {
            continue;
        };
        if !alias.is_empty() {
            view.insert_owner_expr(&value, CExpr::AddrOf(Box::new(CExpr::Var(alias.clone()))));
        }
    }

    for block in prepared.function().blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            if let SSAOp::Load { dst, addr, .. } = op {
                let derived = prepared_direct_stack_load_offset(prepared, view, addr)
                    .and_then(|offset| {
                        local_store_owner_expr_for_offset(view, prepared, block, op_idx, offset)
                            .map(|expr| (expr, Some(offset)))
                            .or_else(|| {
                                preferred_stack_alias_name(view, offset)
                                    .filter(|alias| !alias.is_empty())
                                    .map(|alias| (CExpr::Var(alias), Some(offset)))
                            })
                    })
                    .or_else(|| {
                        prepared
                            .memory_uses_for_op_site(block.addr, op_idx)
                            .and_then(|facts| facts.first())
                            .and_then(|fact| {
                                alias_for_memory_location(view, fact.location)
                                    .map(|alias| (CExpr::Var(alias), Some(fact.location.offset)))
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
                        if let Some(expr) = view.owner_expr_for_var(src).cloned()
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
                        let Some(lhs) =
                            prepared_address_owner_expr_for_value(view, a, compare_width)
                        else {
                            continue;
                        };
                        let Some(rhs) =
                            prepared_address_owner_expr_for_value(view, b, compare_width)
                        else {
                            continue;
                        };
                        let expr = CExpr::binary(BinaryOp::Sub, lhs, rhs);
                        if view.owner_expr_for_var(dst) != Some(&expr) {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                    }
                    SSAOp::IntLeft { dst, a, b } => {
                        let compare_width = a.size.max(b.size);
                        let Some(lhs) = prepared_scaled_index_owner_expr(view, a, compare_width)
                        else {
                            continue;
                        };
                        let Some(rhs) = scalar_owner_expr_for_value(view, b, compare_width) else {
                            continue;
                        };
                        let expr = CExpr::binary(BinaryOp::Shl, lhs, rhs);
                        if view.owner_expr_for_var(dst) != Some(&expr) {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                    }
                    SSAOp::IntMult { dst, a, b } => {
                        let compare_width = a.size.max(b.size);
                        let Some(lhs) = prepared_scaled_index_owner_expr(view, a, compare_width)
                        else {
                            continue;
                        };
                        let Some(rhs) = prepared_scaled_index_owner_expr(view, b, compare_width)
                        else {
                            continue;
                        };
                        let expr = CExpr::binary(BinaryOp::Mul, lhs, rhs);
                        if view.owner_expr_for_var(dst) != Some(&expr) {
                            view.insert_owner_expr(dst, expr);
                            changed = true;
                        }
                    }
                    SSAOp::IntAdd { dst, a, b } => {
                        let compare_width = a.size.max(b.size);
                        let derived = prepared_address_owner_expr_for_value(view, a, compare_width)
                            .zip(prepared_address_owner_expr_for_value(
                                view,
                                b,
                                compare_width,
                            ))
                            .map(|(lhs, rhs)| CExpr::binary(BinaryOp::Add, lhs, rhs));
                        if let Some(expr) = derived
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

    refine_load_owner_exprs(view, prepared);
}

fn refine_load_owner_exprs(view: &mut PreparedSemanticView, prepared: &SsaArtifact) {
    for block in prepared.function().blocks() {
        for (op_idx, op) in block.ops.iter().enumerate() {
            let SSAOp::Load { dst, addr, .. } = op else {
                continue;
            };
            let candidate = prepared_direct_stack_load_offset(prepared, view, addr)
                .and_then(|offset| {
                    local_store_owner_expr_for_offset(view, prepared, block, op_idx, offset)
                        .map(|expr| (expr, Some(offset)))
                        .or_else(|| {
                            preferred_stack_alias_name(view, offset)
                                .filter(|alias| !alias.is_empty())
                                .map(|alias| (CExpr::Var(alias), Some(offset)))
                        })
                })
                .or_else(|| {
                    prepared
                        .memory_uses_for_op_site(block.addr, op_idx)
                        .and_then(|facts| facts.first())
                        .and_then(|fact| {
                            alias_for_memory_location(view, fact.location)
                                .map(|alias| (CExpr::Var(alias), Some(fact.location.offset)))
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

fn record_call_result_source_alias(
    view: &mut PreparedSemanticView,
    var: &SSAVar,
    site: (u64, usize),
) {
    view.insert_call_result_source(var, site);
}

fn var_matches_return_register_family(var: &SSAVar, ret_reg_name: &str) -> bool {
    let Some(ret_family) = crate::registers::register_family_name(ret_reg_name) else {
        return false;
    };
    crate::registers::register_family_name(&var.name).as_deref() == Some(ret_family.as_str())
}

fn populate_call_result_sources(
    view: &mut PreparedSemanticView,
    prepared: &SsaArtifact,
    ret_reg_name: &str,
) {
    for call_site in prepared.call_sites().by_id.values() {
        let Some((block_addr, op_idx)) = prepared_call_site_tuple(prepared, call_site.at) else {
            continue;
        };
        let Some(block) = prepared.function().get_block(block_addr) else {
            continue;
        };
        let site = (block_addr, op_idx);
        let mut tracked = HashSet::new();
        let mut saw_call_define = false;
        for op in block.ops.iter().skip(op_idx + 1) {
            match op {
                SSAOp::CallDefine { dst } => {
                    saw_call_define = true;
                    tracked.insert(dst.clone());
                    record_call_result_source_alias(view, dst, site);
                }
                SSAOp::Copy { dst, src }
                | SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src }
                | SSAOp::Trunc { dst, src }
                | SSAOp::Cast { dst, src, .. }
                | SSAOp::Subpiece { dst, src, .. } => {
                    if !saw_call_define
                        && tracked.is_empty()
                        && var_matches_return_register_family(src, ret_reg_name)
                    {
                        tracked.insert(src.clone());
                        record_call_result_source_alias(view, src, site);
                    }
                    if tracked.contains(src) {
                        tracked.insert(dst.clone());
                        record_call_result_source_alias(view, dst, site);
                    }
                }
                SSAOp::Store { val, .. }
                    if !saw_call_define
                        && tracked.is_empty()
                        && var_matches_return_register_family(val, ret_reg_name) =>
                {
                    tracked.insert(val.clone());
                    record_call_result_source_alias(view, val, site);
                }
                SSAOp::Call { .. } | SSAOp::CallInd { .. } if saw_call_define => break,
                SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::Return { .. }
                    if saw_call_define =>
                {
                    break;
                }
                _ => {}
            }
        }
    }
}

fn populate_predicates(view: &mut PreparedSemanticView, inputs: &PreparedSemanticViewInputs<'_>) {
    view.predicate_expr_by_value.clear();
    view.branch_predicate_expr_by_block.clear();

    for predicate in inputs.prepared.predicates().predicates.values() {
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
    for (block_addr, switch) in &inputs.prepared.predicates().switches {
        if let Some(selector) = switch
            .selector
            .and_then(|selector| prepared_var(inputs.prepared, selector).cloned())
        {
            let expr = expr_for_compare_operand(inputs, selector, view);
            view.switch_selector_expr_by_block.insert(*block_addr, expr);
        }
    }
}

fn populate_calls(view: &mut PreparedSemanticView, inputs: &PreparedSemanticViewInputs<'_>) {
    for call_site in inputs.prepared.call_sites().by_id.values() {
        let Some(site) = prepared_call_site_tuple(inputs.prepared, call_site.at) else {
            continue;
        };
        let mut call_view = PreparedCallView {
            direct_target: call_site.direct_target,
            callee_name: call_site
                .direct_target
                .and_then(|addr| lookup_callee_name(inputs, addr)),
            authoritative_args: Vec::new(),
            result_owner: None,
        };
        if call_view.callee_name.is_none()
            && let Some(addr) = call_site.direct_target
        {
            call_view.callee_name = lookup_callee_name(inputs, addr);
        }
        call_view.result_owner = infer_call_result_owner(
            site,
            inputs.prepared,
            inputs.prepared.function(),
            view,
            inputs.ret_reg_name,
        );
        if let Some(owner) = call_view.result_owner.clone() {
            assign_call_result_owner(
                site,
                inputs.prepared.function(),
                view,
                &owner,
                inputs.ret_reg_name,
            );
        }
        let max_arity = call_site.direct_target.and_then(|target| {
            inputs
                .interproc_summary_set
                .and_then(|set| set.summaries.get(&r2ssa::InterprocFunctionId(target)))
                .and_then(|summary| summary.arg_count_hint)
        });
        call_view.authoritative_args = infer_call_authoritative_args(
            site,
            inputs.prepared.function(),
            view,
            inputs.abi_arg_regs,
            max_arity,
        );
        view.call_view_by_site.insert(site, call_view);
    }
}

fn infer_call_authoritative_args(
    site: (u64, usize),
    function: &r2ssa::SSAFunction,
    view: &PreparedSemanticView,
    abi_arg_regs: &[String],
    max_arity: Option<usize>,
) -> Vec<CExpr> {
    let (block_addr, op_idx) = site;
    let Some(block) = function.get_block(block_addr) else {
        return Vec::new();
    };

    let mut args = Vec::new();
    let max_regs = max_arity.unwrap_or(abi_arg_regs.len());
    for reg_name in abi_arg_regs.iter().take(max_regs) {
        let Some(expr) = infer_call_authoritative_arg_expr(block, op_idx, reg_name, view) else {
            break;
        };
        args.push(expr);
    }

    args
}

fn infer_call_authoritative_arg_expr(
    block: &r2ssa::FunctionSSABlock,
    op_idx: usize,
    reg_name: &str,
    view: &PreparedSemanticView,
) -> Option<CExpr> {
    let reg_name = reg_name.to_ascii_lowercase();
    for op in block.ops[..op_idx].iter().rev() {
        match op {
            SSAOp::Copy { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Cast { dst, src, .. }
            | SSAOp::Subpiece { dst, src, .. }
                if dst.name.eq_ignore_ascii_case(&reg_name) =>
            {
                return authoritative_scalar_expr_for_value(block, view, src, 0)
                    .or_else(|| scalar_owner_expr_for_value(view, src, src.size))
                    .or_else(|| view.owner_expr_for_var(src).cloned())
                    .or_else(|| Some(CExpr::Var(src.display_name())));
            }
            other
                if other
                    .dst()
                    .is_some_and(|dst| dst.name.eq_ignore_ascii_case(&reg_name)) =>
            {
                let dst = other.dst().expect("checked above");
                return authoritative_scalar_expr_for_value(block, view, dst, 0)
                    .or_else(|| scalar_owner_expr_for_value(view, dst, dst.size))
                    .or_else(|| view.owner_expr_for_var(dst).cloned())
                    .or_else(|| Some(CExpr::Var(dst.display_name())));
            }
            SSAOp::Call { .. } | SSAOp::CallInd { .. } => break,
            _ => {}
        }
    }
    None
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
        SSAOp::Load { addr, .. } => view
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

fn infer_call_result_owner(
    site: (u64, usize),
    prepared: &SsaArtifact,
    function: &r2ssa::SSAFunction,
    view: &PreparedSemanticView,
    ret_reg_name: &str,
) -> Option<CExpr> {
    let (block_addr, op_idx) = site;
    let block = function.get_block(block_addr)?;
    let mut tracked = HashSet::new();
    let mut saw_call_define = false;
    let mut next_idx = op_idx + 1;
    while let Some(op) = block.ops.get(next_idx) {
        match op {
            SSAOp::CallDefine { dst } => {
                saw_call_define = true;
                tracked.insert(dst.clone());
                if let Some(owner) = view.owner_expr_for_var(dst) {
                    return Some(owner.clone());
                }
            }
            SSAOp::Copy { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Subpiece { dst, src, .. }
            | SSAOp::Cast { dst, src, .. } => {
                if !saw_call_define
                    && tracked.is_empty()
                    && var_matches_return_register_family(src, ret_reg_name)
                {
                    tracked.insert(src.clone());
                }
                if tracked.contains(src) {
                    tracked.insert(dst.clone());
                    if let Some(owner) = view.owner_expr_for_var(dst) {
                        return Some(owner.clone());
                    }
                }
            }
            SSAOp::Store { addr, val, .. } if tracked.contains(val) => {
                if let Some(offset) = view
                    .stack_offset_for_var(addr)
                    .or_else(|| stack_offset_for_value(prepared, addr))
                    && let Some(alias) = preferred_stack_alias_name(view, offset)
                {
                    return Some(CExpr::Var(alias));
                }
            }
            SSAOp::Call { .. } if saw_call_define => break,
            SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::Return { .. } => break,
            _ if saw_call_define => {}
            _ => {}
        }
        next_idx += 1;
    }
    None
}

fn assign_call_result_owner(
    site: (u64, usize),
    function: &r2ssa::SSAFunction,
    view: &mut PreparedSemanticView,
    owner: &CExpr,
    ret_reg_name: &str,
) {
    let (block_addr, op_idx) = site;
    let Some(block) = function.get_block(block_addr) else {
        return;
    };
    let mut tracked = HashSet::new();
    let mut saw_call_define = false;
    let mut next_idx = op_idx + 1;
    while let Some(op) = block.ops.get(next_idx) {
        match op {
            SSAOp::CallDefine { dst } => {
                saw_call_define = true;
                tracked.insert(dst.clone());
                if view.owner_expr_for_var(dst).is_none() {
                    view.insert_owner_expr(dst, owner.clone());
                }
            }
            SSAOp::Copy { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Subpiece { dst, src, .. }
            | SSAOp::Cast { dst, src, .. } => {
                if !saw_call_define
                    && tracked.is_empty()
                    && var_matches_return_register_family(src, ret_reg_name)
                {
                    tracked.insert(src.clone());
                    if view.owner_expr_for_var(src).is_none() {
                        view.insert_owner_expr(src, owner.clone());
                    }
                }
                if tracked.contains(src) {
                    tracked.insert(dst.clone());
                    if view.owner_expr_for_var(dst).is_none() {
                        view.insert_owner_expr(dst, owner.clone());
                    }
                }
            }
            SSAOp::Call { .. } if saw_call_define => break,
            SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::Return { .. } => break,
            _ if saw_call_define => {}
            _ => {}
        }
        next_idx += 1;
    }
}

fn alias_for_memory_location(
    view: &PreparedSemanticView,
    location: MemoryLocation,
) -> Option<String> {
    preferred_stack_alias_name(view, location.offset)
}

fn stack_offset_for_value(prepared: &SsaArtifact, value: &SSAVar) -> Option<i64> {
    let object = prepared.object_for_var(value).or_else(|| {
        prepared
            .function()
            .decompile_prep_facts()
            .and_then(|facts| facts.canonical_root_of(value))
            .and_then(|root| prepared.object_for_var(root))
    })?;
    let fact = prepared.objects().object(object)?;
    stack_offset_for_object_kind(&fact.kind)
}

fn stack_offset_for_object_kind(kind: &ObjectKind) -> Option<i64> {
    match kind {
        ObjectKind::StackSlot { offset, .. } | ObjectKind::FrameObject { offset, .. } => {
            Some(*offset)
        }
        _ => None,
    }
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

fn lookup_callee_name(inputs: &PreparedSemanticViewInputs<'_>, addr: u64) -> Option<String> {
    inputs
        .callee_facts
        .get(&addr)
        .and_then(|fact| fact.name.clone())
        .or_else(|| inputs.function_names.get(&addr).cloned())
        .or_else(|| inputs.symbols.get(&addr).cloned())
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
        .object_for_var(value)
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

    let lower = var.name.to_ascii_lowercase();
    if lower.starts_with("tmp:")
        || lower.starts_with("const:")
        || lower.starts_with("ram:")
        || lower.starts_with("unique:")
    {
        return None;
    }

    Some(CExpr::Var(var.name.clone()))
}

fn local_store_owner_expr_for_offset(
    view: &PreparedSemanticView,
    prepared: &SsaArtifact,
    block: &r2ssa::FunctionSSABlock,
    before_idx: usize,
    offset: i64,
) -> Option<CExpr> {
    let alias = preferred_stack_alias_name(view, offset).filter(|alias| !alias.is_empty());
    let prefer_alias = alias
        .as_deref()
        .is_some_and(|name| !is_generic_prepared_stack_alias(name));

    for op in block.ops[..before_idx].iter().rev() {
        let SSAOp::Store { addr, val, .. } = op else {
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

    for (&value_id, object_id) in &prepared.objects().value_objects {
        let Some(object) = prepared.objects().object(*object_id) else {
            continue;
        };
        let Some(offset) = stack_offset_for_object_kind(&object.kind) else {
            continue;
        };
        let Some(value) = prepared_var(prepared, value_id) else {
            continue;
        };
        use_info.bind_value_id(value, value_id);
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
            if let Some(value_id) = view.value_id_for_var(&phi.dst) {
                use_info.bind_value_id(&phi.dst, value_id);
            }
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
                if let Some(value_id) = view.value_id_for_var(src) {
                    use_info.bind_value_id(src, value_id);
                    *use_info.use_counts_by_value.entry(value_id).or_insert(0) += 1;
                }
            }
            seed_prepared_value_fact(use_info, &phi.dst, prepared, view);
        }

        for op in &block.ops {
            for src in op.sources() {
                *use_info.use_counts.entry(src.display_name()).or_insert(0) += 1;
                if let Some(value_id) = view.value_id_for_var(src) {
                    use_info.bind_value_id(src, value_id);
                    *use_info.use_counts_by_value.entry(value_id).or_insert(0) += 1;
                }
            }
            if let SSAOp::CBranch { cond, .. } = op {
                use_info.condition_vars.insert(cond.display_name());
                if let Some(value_id) = view.value_id_for_var(cond) {
                    use_info.bind_value_id(cond, value_id);
                    use_info.condition_values.insert(value_id);
                }
            }

            if let Some(dst) = op.dst() {
                let dst_key = dst.display_name();
                if let Some(value_id) = view.value_id_for_var(dst) {
                    use_info.bind_value_id(dst, value_id);
                }
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
                    if let (Some(dst_id), Some(src_id)) =
                        (view.value_id_for_var(dst), view.value_id_for_var(src))
                    {
                        use_info.bind_value_id(dst, dst_id);
                        use_info.bind_value_id(src, src_id);
                        use_info.copy_sources_by_value.insert(dst_id, src_id);
                    }
                    let source_prov = use_info.forwarded_values.get(&src_key).cloned().unwrap_or(
                        ValueProvenance {
                            source: src_key.clone(),
                            source_value_id: view.value_id_for_var(src),
                            source_var: Some(src.clone()),
                            stack_slot: view
                                .stack_offset_for_var(src)
                                .or_else(|| stack_offset_for_value(prepared, src)),
                        },
                    );
                    use_info.forwarded_values.insert(
                        dst_key.clone(),
                        ValueProvenance {
                            source: source_prov.source.clone(),
                            source_value_id: source_prov
                                .source_value_id
                                .or_else(|| view.value_id_for_var(src)),
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
                    if let Some(dst_id) = view.value_id_for_var(dst) {
                        use_info.forwarded_values_by_value.insert(
                            dst_id,
                            ValueProvenance {
                                source: source_prov.source,
                                source_value_id: source_prov
                                    .source_value_id
                                    .or_else(|| view.value_id_for_var(src)),
                                source_var: source_prov.source_var.or_else(|| Some(src.clone())),
                                stack_slot: source_prov
                                    .stack_slot
                                    .or_else(|| view.stack_offset_for_var(src))
                                    .or_else(|| stack_offset_for_value(prepared, src)),
                            },
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
                SSAOp::Load { dst, addr, .. } => {
                    let Some(offset) = prepared_direct_stack_load_offset(prepared, view, addr)
                    else {
                        continue;
                    };
                    let key = dst.display_name();
                    let provenance = StackSlotProvenance {
                        offset,
                        predicate_carrier: false,
                        return_carrier: false,
                        value_kind: StackSlotValueKind::Scalar,
                    };
                    merge_prepared_stack_slot(
                        use_info,
                        &key,
                        view.value_id_for_var(dst),
                        provenance,
                    );
                    if let Some(alias) = preferred_stack_alias_name(view, offset) {
                        let expr = CExpr::Var(alias.clone());
                        use_info
                            .definitions
                            .entry(key.clone())
                            .or_insert_with(|| expr.clone());
                        if let Some(value_id) = view.value_id_for_var(dst) {
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
                        if let Some(value_id) = view.value_id_for_var(dst) {
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
                                    SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var(alias)))
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

            let args = call_view
                .authoritative_args
                .iter()
                .cloned()
                .map(SemanticCallArg::FallbackExpr)
                .map(CallArgBinding::input)
                .collect::<Vec<_>>();
            if !args.is_empty() {
                use_info.call_args.insert(site, args);
            }

            if let Some(call_expr) = prepared_call_expr(call_view, view, env) {
                use_info.call_result_exprs.insert(site, call_expr.clone());
                record_prepared_consumed_by_call(use_info, block, op_idx, env, prepared, view);
                record_prepared_call_result_aliases(
                    use_info, block, op_idx, prepared, view, env, &call_expr,
                );
            }
        }
    }
}

fn overlay_prepared_switch_roots(use_info: &mut UseInfo, prepared: &SsaArtifact) {
    for switch in prepared.predicates().switches.values() {
        let Some(selector) = switch
            .selector
            .and_then(|selector| prepared_var(prepared, selector))
        else {
            continue;
        };
        use_info.switch_selector_roots.insert(
            switch.block_addr,
            SemanticValue::Scalar(ScalarValue::Root(
                use_info
                    .value_id_for_var(selector)
                    .map(|value_id| ValueRef::with_value_id(value_id, selector.clone()))
                    .unwrap_or_else(|| ValueRef::new(selector.clone())),
            )),
        );
    }
}

fn finalize_prepared_call_inlining(use_info: &mut UseInfo) {
    for (site, aliases) in &use_info.call_result_aliases {
        if aliases.iter().any(|alias| {
            !use_info.direct_call_result_aliases.contains(alias)
                && !is_generic_stack_placeholder_alias(alias)
                && use_info
                    .call_result_exprs
                    .get(site)
                    .is_some_and(|_| use_info.use_counts.get(alias).copied().unwrap_or(0) <= 1)
        }) {
            use_info.inlined_call_results.insert(*site);
            continue;
        }

        if aliases.iter().any(|alias| {
            use_info.call_result_exprs.get(site).is_some_and(|_| {
                !use_info.direct_call_result_aliases.contains(alias)
                    && use_info.use_counts.get(alias).copied().unwrap_or(0) <= 1
            })
        }) {
            use_info.inlined_call_results.insert(*site);
        }
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
    if let Some(value_id) = view.value_id_for_var(var) {
        use_info.bind_value_id(var, value_id);
    }
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
        if let Some(value_id) = view.value_id_for_var(var) {
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
        if let Some(value_id) = view.value_id_for_var(var) {
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
                view.value_id_for_var(var),
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
            view.value_id_for_var(var),
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
        .callee_name
        .as_ref()
        .map(|name| CExpr::Var(name.clone()))
        .or_else(|| {
            call_view
                .direct_target
                .map(|addr| CExpr::Var(format!("sub_{addr:x}")))
        })
}

fn prepared_call_expr_from_view(call_view: &PreparedCallView) -> Option<CExpr> {
    let callee = prepared_call_callee_expr(call_view)?;
    Some(CExpr::Call {
        func: Box::new(callee),
        args: call_view.authoritative_args.clone(),
    })
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
            SSAOp::Store { addr, val, .. } => {
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
    env: &PassEnv<'_>,
    call_expr: &CExpr,
) {
    let mut tracked = HashSet::new();
    let mut saw_call_define = false;
    let site = (block.addr, call_idx);
    let mut next_idx = call_idx + 1;

    while let Some(op) = block.ops.get(next_idx) {
        match op {
            SSAOp::CallDefine { dst } => {
                saw_call_define = true;
                tracked.insert(dst.clone());
                record_prepared_call_alias(use_info, site, &dst.display_name(), true);
                use_info
                    .definitions
                    .insert(dst.display_name(), call_expr.clone());
                use_info
                    .formatted_defs
                    .insert(dst.display_name(), call_expr.clone());
            }
            SSAOp::Copy { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Subpiece { dst, src, .. }
            | SSAOp::Cast { dst, src, .. } => {
                if !saw_call_define
                    && tracked.is_empty()
                    && var_matches_return_register_family(src, env.ret_reg_name)
                {
                    tracked.insert(src.clone());
                    record_prepared_call_alias(use_info, site, &src.display_name(), true);
                    use_info
                        .definitions
                        .entry(src.display_name())
                        .or_insert_with(|| call_expr.clone());
                    use_info
                        .formatted_defs
                        .entry(src.display_name())
                        .or_insert_with(|| call_expr.clone());
                }
                if tracked.contains(src) {
                    tracked.insert(dst.clone());
                    record_prepared_call_alias(use_info, site, &dst.display_name(), true);
                    use_info
                        .definitions
                        .entry(dst.display_name())
                        .or_insert_with(|| call_expr.clone());
                    use_info
                        .formatted_defs
                        .entry(dst.display_name())
                        .or_insert_with(|| call_expr.clone());
                }
            }
            SSAOp::Store { val, .. }
                if !saw_call_define
                    && tracked.is_empty()
                    && var_matches_return_register_family(val, env.ret_reg_name) =>
            {
                tracked.insert(val.clone());
                record_prepared_call_alias(use_info, site, &val.display_name(), true);
                use_info
                    .definitions
                    .entry(val.display_name())
                    .or_insert_with(|| call_expr.clone());
                use_info
                    .formatted_defs
                    .entry(val.display_name())
                    .or_insert_with(|| call_expr.clone());
            }
            SSAOp::Store { addr, val, .. } if tracked.contains(val) => {
                if let Some(offset) = view
                    .stack_offset_for_var(addr)
                    .or_else(|| stack_offset_for_value(prepared, addr))
                    && let Some(alias) = preferred_stack_alias_name(view, offset)
                {
                    record_prepared_call_alias(use_info, site, &alias, false);
                    if offset < 0 {
                        use_info
                            .stable_stack_values
                            .entry(offset)
                            .or_insert_with(|| {
                                SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var(alias.clone())))
                            });
                    }
                }
            }
            SSAOp::Call { .. } | SSAOp::CallInd { .. } if saw_call_define => break,
            SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::Return { .. } => break,
            _ if saw_call_define => {}
            _ => {}
        }
        next_idx += 1;
    }
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
