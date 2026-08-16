use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::Hash;

use r2il::SpaceId;
use r2ssa::{
    ObjectKind, SSAFunction, SSAOp, SSAVar, SSAVarNameKind, SsaArtifact, SsaExecutionControl,
    ValueId,
};
use r2types::{
    CalleeCallArgPolicy, CalleeResolutionFacts, CalleeTargetIdentityRequest,
    CalleeTargetPolicyDecision, CalleeTargetResolutionRequest, CallsiteKey,
};

use super::{
    BaseRef, CallArgBinding, CallArgRole, FrameObjectFieldKey, FrameSlotMergeSummary,
    NormalizedAddr, PassEnv, PtrArith, SSABlock, ScalarValue, SemanticCallArg, SemanticValue,
    StackSlotProvenance, StackSlotValueKind, UseInfo, UseInfoAnalysisMode, ValueProvenance,
    ValueRef, lower::LowerCtx, utils,
};
use crate::ast::{BinaryOp, CExpr, CType};
use crate::control::{DecompileExecutionStop, DecompileWorkControl, DecompileWorkPhase};
use crate::registers::register_family_name;

#[derive(Debug, Default)]
pub(crate) struct UseScratch {
    pub(crate) info: UseInfo,
    producers: HashMap<String, SSAOp>,
}

#[derive(Debug, Default)]
struct SemanticTypeHintCache {
    names_by_var: HashMap<String, Vec<String>>,
    stack_slot_names_by_offset: HashMap<i64, Vec<String>>,
}

impl SemanticTypeHintCache {
    fn from_info(info: &UseInfo) -> Self {
        let mut stack_slot_names_by_offset: HashMap<i64, Vec<String>> = HashMap::new();
        for (slot_name, slot) in &info.stack_slots {
            let entry = stack_slot_names_by_offset.entry(slot.offset).or_default();
            push_unique_casefold(entry, slot_name.clone());
            push_unique_casefold(entry, slot_name.to_ascii_lowercase());
        }
        Self {
            names_by_var: HashMap::new(),
            stack_slot_names_by_offset,
        }
    }
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LocalStructFieldAccessProfile {
    pub(crate) arg_index: usize,
    pub(crate) field_offset: u64,
    pub(crate) access_size: u32,
    pub(crate) is_write: bool,
}

#[allow(dead_code)]
pub(crate) fn analyze(blocks: &[SSABlock], env: &PassEnv<'_>) -> UseInfo {
    let execution = SsaExecutionControl::default();
    let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Structuring);
    analyze_with_control(blocks, env, control).expect("default decompiler work control cannot stop")
}

pub(crate) fn analyze_with_control(
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    control: DecompileWorkControl<'_>,
) -> Result<UseInfo, DecompileExecutionStop> {
    analyze_with_definition_overrides_mode(
        blocks,
        env,
        &HashMap::new(),
        UseInfoAnalysisMode::Full,
        control,
    )
}

#[cfg(test)]
pub(crate) fn analyze_for_local_struct_accesses(blocks: &[SSABlock], env: &PassEnv<'_>) -> UseInfo {
    let execution = SsaExecutionControl::default();
    let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Structuring);
    analyze_for_local_struct_accesses_with_control(blocks, env, control)
        .expect("default decompiler work control cannot stop")
}

pub(crate) fn analyze_for_local_struct_accesses_with_control(
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    control: DecompileWorkControl<'_>,
) -> Result<UseInfo, DecompileExecutionStop> {
    analyze_with_definition_overrides_mode(
        blocks,
        env,
        &HashMap::new(),
        UseInfoAnalysisMode::LocalStructAccesses,
        control,
    )
}

#[allow(dead_code)]
pub(crate) fn analyze_with_definition_overrides(
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    definition_overrides: &HashMap<String, CExpr>,
) -> UseInfo {
    let execution = SsaExecutionControl::default();
    let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Structuring);
    analyze_with_definition_overrides_with_control(blocks, env, definition_overrides, control)
        .expect("default decompiler work control cannot stop")
}

pub(crate) fn analyze_with_definition_overrides_with_control(
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    definition_overrides: &HashMap<String, CExpr>,
    control: DecompileWorkControl<'_>,
) -> Result<UseInfo, DecompileExecutionStop> {
    analyze_with_definition_overrides_mode(
        blocks,
        env,
        definition_overrides,
        UseInfoAnalysisMode::Full,
        control,
    )
}

fn analyze_with_definition_overrides_mode(
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    definition_overrides: &HashMap<String, CExpr>,
    mode: UseInfoAnalysisMode,
    control: DecompileWorkControl<'_>,
) -> Result<UseInfo, DecompileExecutionStop> {
    control.poll()?;
    let mut scratch = UseScratch::default();
    scratch.info.type_hints = env.type_hints.clone();
    seed_local_value_ids(&mut scratch, blocks);
    seed_entry_param_aliases(&mut scratch, blocks, env);

    for block in blocks {
        control.poll()?;
        count_uses_and_conditions(&mut scratch, block);
    }
    pin_loop_carried_phi_values(&mut scratch, blocks);
    for block in blocks {
        control.poll()?;
        collect_definitions(&mut scratch, block, env, definition_overrides);
    }
    refresh_semantic_values(&mut scratch, blocks, env);
    populate_stable_stack_values(&mut scratch, blocks, env);
    populate_frame_object_field_roots(&mut scratch, blocks, env);
    populate_stable_memory_values(&mut scratch, blocks, env);
    refresh_semantic_values(&mut scratch, blocks, env);
    rebuild_definitions(&mut scratch, blocks, env, definition_overrides);

    analyze_call_args(&mut scratch, blocks, env);
    bind_single_use_call_result_definitions(&mut scratch, blocks, env);
    propagate_call_result_aliases(&mut scratch.info, control)?;
    rerun_semantic_call_analysis_after_result_binding(&mut scratch, blocks, env, control)?;
    if matches!(mode, UseInfoAnalysisMode::Full) {
        coalesce_variables(&mut scratch, blocks, env, control)?;
        pin_aliases_for_pinned_values(&mut scratch.info);
        build_formatted_defs(&mut scratch, env);
    }
    rebuild_id_mirrors_from_name_maps(&mut scratch.info);
    scratch.info.producers = scratch.producers.clone();

    control.poll()?;
    Ok(scratch.info)
}

fn seed_local_value_ids(scratch: &mut UseScratch, blocks: &[SSABlock]) {
    let mut next_value = scratch
        .info
        .vars_by_value_id
        .keys()
        .next_back()
        .map(|value_id| value_id.0 + 1)
        .unwrap_or(0);
    let mut maybe_bind = |var: &SSAVar, info: &mut UseInfo| {
        if info.value_id_for_var(var).is_some() {
            return;
        }
        let value_id = ValueId(next_value);
        next_value += 1;
        let _ = info.bind_value_id(var, value_id);
    };

    for block in blocks {
        for phi in &block.phis {
            maybe_bind(&phi.dst, &mut scratch.info);
            for (_, src) in &phi.sources {
                maybe_bind(src, &mut scratch.info);
            }
        }
        for op in &block.ops {
            if let Some(dst) = op.dst() {
                maybe_bind(dst, &mut scratch.info);
            }
            for src in op.sources() {
                maybe_bind(src, &mut scratch.info);
            }
        }
    }
}

fn rebuild_id_mirrors_from_name_maps(info: &mut UseInfo) {
    info.use_counts_by_value.clear();
    for (name, count) in &info.use_counts {
        if let Some(value_id) = info.value_id_for_name(name) {
            info.use_counts_by_value.insert(value_id, *count);
        }
    }

    info.semantic_values_by_value.clear();
    for (value_id, var) in &info.vars_by_value_id {
        let display = var.display_name();
        if info.exact_value_id_for_var(var) == Some(*value_id)
            && info.value_id_for_name(&display) == Some(*value_id)
            && let Some(value) = info.semantic_values.get(&display)
        {
            info.semantic_values_by_value
                .insert(*value_id, value.clone());
        }
    }

    info.copy_sources_by_value.clear();
    for (dst, src) in &info.copy_sources {
        if let (Some(dst_id), Some(src_id)) =
            (info.value_id_for_name(dst), info.value_id_for_name(src))
        {
            info.copy_sources_by_value.insert(dst_id, src_id);
        }
    }

    info.ptr_arith_by_value.clear();
    for (name, ptr) in &info.ptr_arith {
        if let Some(value_id) = info.value_id_for_name(name) {
            info.ptr_arith_by_value.insert(value_id, ptr.clone());
        }
    }

    info.condition_values.clear();
    for name in &info.condition_vars {
        if let Some(value_id) = info.value_id_for_name(name) {
            info.condition_values.insert(value_id);
        }
    }

    info.stack_slots_by_value.clear();
    for (name, slot) in &info.stack_slots {
        if let Some(value_id) = info.value_id_for_name(name) {
            info.stack_slots_by_value.insert(value_id, *slot);
        }
    }

    info.stable_memory_values_by_value.clear();
    for (name, value) in &info.stable_memory_values {
        if let Some(value_id) = info.value_id_for_name(name) {
            info.stable_memory_values_by_value
                .insert(value_id, value.clone());
        }
    }

    info.forwarded_values_by_value.clear();
    for (name, provenance) in &info.forwarded_values {
        if let Some(value_id) = info.value_id_for_name(name) {
            info.forwarded_values_by_value
                .insert(value_id, provenance.clone());
        }
    }

    info.call_result_source_by_value.clear();
    for (name, site) in &info.call_result_source_by_alias {
        if let Some(value_id) = info.value_id_for_name(name) {
            info.call_result_source_by_value.insert(value_id, *site);
        }
    }
}

fn rerun_semantic_call_analysis_after_result_binding(
    scratch: &mut UseScratch,
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    control: DecompileWorkControl<'_>,
) -> Result<(), DecompileExecutionStop> {
    control.poll()?;
    scratch.info.call_args.clear();
    scratch.info.consumed_by_call.clear();
    scratch.info.inlined_call_results.clear();
    populate_stable_stack_values(scratch, blocks, env);
    populate_frame_object_field_roots(scratch, blocks, env);
    populate_stable_memory_values(scratch, blocks, env);
    refresh_semantic_values(scratch, blocks, env);
    analyze_call_args(scratch, blocks, env);
    bind_single_use_call_result_definitions(scratch, blocks, env);
    propagate_call_result_aliases(&mut scratch.info, control)?;
    Ok(())
}

#[derive(Debug, Clone)]
struct CallArgCandidate {
    binding: CallArgBinding,
    score: i32,
    producer_idx: usize,
    dst_key: String,
}

type StackCallArg = (i64, CallArgBinding, String, String);
type StackCallArgCollection = (Vec<StackCallArg>, HashSet<(u64, usize)>);

struct PostCallResultQuery<'a, 'b> {
    info: &'a UseInfo,
    lower: &'a LowerCtx<'b>,
    block_addr: u64,
    ops: &'a [SSAOp],
    producers: &'a HashMap<String, usize>,
    env: &'a PassEnv<'b>,
}

struct PostCallAliasQuery<'a, 'b> {
    info: &'a UseInfo,
    block: &'a SSABlock,
    producers: &'a HashMap<String, usize>,
    env: &'a PassEnv<'b>,
}

struct StackHomeQuery<'a, 'b> {
    ops: &'a [SSAOp],
    producers: &'a HashMap<String, usize>,
    info: &'a UseInfo,
    lower: &'a LowerCtx<'b>,
    env: &'a PassEnv<'b>,
}

fn bind_call_arg_source_var(
    info: &UseInfo,
    binding: CallArgBinding,
    source_var: &SSAVar,
) -> CallArgBinding {
    let binding = binding.with_source_var(source_var);
    if let Some(value_id) = exact_call_arg_source_value_id(info, source_var) {
        binding.with_source_value_id(value_id)
    } else {
        binding
    }
}

fn exact_call_arg_source_value_id(info: &UseInfo, source_var: &SSAVar) -> Option<ValueId> {
    info.exact_value_id_for_var(source_var)
}

fn same_register_family_call_arg_source(src: &SSAVar, dst: &SSAVar) -> bool {
    let Some(src_family) = register_family_name(&src.name) else {
        return false;
    };
    let Some(dst_family) = register_family_name(&dst.name) else {
        return false;
    };
    src_family == dst_family
}

fn push_unique_casefold(names: &mut Vec<String>, name: String) {
    if !names
        .iter()
        .any(|existing| existing.eq_ignore_ascii_case(&name))
    {
        names.push(name);
    }
}

fn lookup_type_hint<'a>(info: &'a UseInfo, env: &'a PassEnv<'_>, name: &str) -> Option<&'a CType> {
    let lower = name.to_ascii_lowercase();
    info.type_hints
        .get(name)
        .or_else(|| info.type_hints.get(&lower))
        .or_else(|| env.type_hints.get(name))
        .or_else(|| env.type_hints.get(&lower))
}

pub(crate) fn preserve_authoritative_facts(info: &mut UseInfo, baseline: &UseInfo) {
    preserve_semantic_fact_map(&mut info.semantic_values, &baseline.semantic_values);
    preserve_semantic_fact_map(
        &mut info.frame_object_field_roots,
        &baseline.frame_object_field_roots,
    );
    preserve_semantic_fact_map(&mut info.stable_stack_values, &baseline.stable_stack_values);
    preserve_semantic_fact_map(
        &mut info.stable_memory_values,
        &baseline.stable_memory_values,
    );
    for (key, value) in &baseline.switch_selector_roots {
        let should_replace = match info.switch_selector_roots.get(key) {
            None => true,
            Some(existing) => {
                switch_selector_candidate_score(info, value)
                    > switch_selector_candidate_score(info, existing)
            }
        };
        if should_replace {
            info.switch_selector_roots.insert(*key, value.clone());
        }
    }

    for (key, summary) in &baseline.frame_slot_merges {
        let should_replace = match info.frame_slot_merges.get(key) {
            None => true,
            Some(current) => {
                frame_slot_merge_preservation_score(summary)
                    > frame_slot_merge_preservation_score(current)
            }
        };
        if should_replace {
            info.frame_slot_merges.insert(key.clone(), summary.clone());
        }
    }

    for (key, expr) in &baseline.definitions {
        let should_replace = info
            .definitions
            .get(key)
            .is_some_and(|current| expr_contains_call(current) && !expr_contains_call(expr));
        if should_replace {
            info.definitions.insert(key.clone(), expr.clone());
            info.formatted_defs.insert(key.clone(), expr.clone());
            if let Some(value_id) = info.value_id_for_name(key) {
                info.definitions_by_value.insert(value_id, expr.clone());
            }
        }
    }

    for (key, args) in &baseline.call_args {
        let should_replace = match info.call_args.get(key) {
            None => true,
            Some(current) => {
                call_arg_vector_needs_authoritative_preservation(current)
                    && call_arg_vector_preservation_score(args)
                        > call_arg_vector_preservation_score(current)
            }
        };
        if should_replace {
            info.call_args.insert(*key, args.clone());
        }
    }
    for (source_call, aliases) in &baseline.call_result_aliases {
        info.call_result_aliases
            .entry(*source_call)
            .or_default()
            .extend(aliases.iter().cloned());
    }
    for (source_call, expr) in &baseline.call_result_exprs {
        info.call_result_exprs
            .entry(*source_call)
            .or_insert_with(|| expr.clone());
    }
    for (alias, source_call) in &baseline.call_result_source_by_alias {
        if !info.call_result_source_by_alias.contains_key(alias) {
            info.insert_call_result_source_alias(alias, *source_call);
        }
    }
    for aliases in baseline.call_result_aliases.values() {
        for alias in aliases {
            if baseline.direct_call_result_aliases.contains(alias) {
                continue;
            }
            info.direct_call_result_aliases.remove(alias);
            info.direct_call_result_aliases
                .remove(&alias.to_ascii_lowercase());
            info.direct_call_result_aliases
                .remove(&alias.to_ascii_uppercase());
            if let Some(expr) = baseline
                .definitions
                .get(alias)
                .or_else(|| baseline.definitions.get(&alias.to_ascii_lowercase()))
                .or_else(|| baseline.definitions.get(&alias.to_ascii_uppercase()))
                .cloned()
            {
                info.definitions.insert(alias.clone(), expr.clone());
                info.formatted_defs.insert(alias.clone(), expr.clone());
                if let Some(value_id) = info.value_id_for_name(alias) {
                    info.definitions_by_value.insert(value_id, expr);
                }
            }
        }
    }
    info.direct_call_result_aliases
        .extend(baseline.direct_call_result_aliases.iter().cloned());

    info.consumed_by_call
        .extend(baseline.consumed_by_call.iter().cloned());
    info.inlined_call_results
        .extend(baseline.inlined_call_results.iter().copied());

    for (key, value) in &baseline.forwarded_values {
        if !info.forwarded_values.contains_key(key) {
            if let Some(var) = info
                .value_id_for_name(key)
                .and_then(|value_id| info.var_for_value_id(value_id))
                .cloned()
            {
                info.insert_forwarded_value_for_var(&var, value.clone());
            } else {
                info.forwarded_values
                    .entry(key.clone())
                    .or_insert_with(|| value.clone());
            }
        }
    }
    for (key, value) in &baseline.type_hints {
        info.type_hints
            .entry(key.clone())
            .or_insert_with(|| value.clone());
    }
    for (key, value) in &baseline.var_aliases {
        info.var_aliases
            .entry(key.clone())
            .or_insert_with(|| value.clone());
    }
    for (key, value) in &baseline.stack_slots {
        if let Some(var) = info
            .value_id_for_name(key)
            .and_then(|value_id| info.var_for_value_id(value_id))
            .cloned()
        {
            let merged = info
                .stack_slot_for_var(&var)
                .map(|existing| existing.merge(*value))
                .unwrap_or(*value);
            info.insert_stack_slot_for_var(&var, merged);
        } else {
            info.stack_slots
                .entry(key.clone())
                .and_modify(|existing| *existing = existing.merge(*value))
                .or_insert(*value);
        }
    }
}

fn expr_contains_call(expr: &CExpr) -> bool {
    let mut contains = false;
    expr.visit(&mut |node| {
        if matches!(node, CExpr::Call { .. }) {
            contains = true;
        }
    });
    contains
}

fn semantic_value_contains_call(value: &SemanticValue) -> bool {
    match value {
        SemanticValue::Scalar(ScalarValue::Expr(expr)) => expr_contains_call(expr),
        SemanticValue::Address(addr) | SemanticValue::Load { addr, .. } => {
            normalized_addr_contains_call(addr)
        }
        SemanticValue::Scalar(ScalarValue::Root(_)) | SemanticValue::Unknown => false,
    }
}

fn normalized_addr_contains_call(addr: &NormalizedAddr) -> bool {
    matches!(&addr.base, BaseRef::Raw(expr) if expr_contains_call(expr))
}

fn record_call_result_alias(info: &mut UseInfo, source_call: (u64, usize), alias: &str) {
    if alias.is_empty() {
        return;
    }
    info.call_result_aliases
        .entry(source_call)
        .or_default()
        .insert(alias.to_string());
    info.insert_call_result_source_alias(alias, source_call);
}

fn record_direct_call_result_alias(info: &mut UseInfo, alias: &str) {
    if alias.is_empty() {
        return;
    }
    info.direct_call_result_aliases.insert(alias.to_string());
}

fn record_call_result_expr(info: &mut UseInfo, source_call: (u64, usize), expr: &CExpr) {
    info.call_result_exprs
        .entry(source_call)
        .or_insert_with(|| expr.clone());
}

fn preserve_semantic_fact_map<K>(
    current: &mut HashMap<K, SemanticValue>,
    baseline: &HashMap<K, SemanticValue>,
) where
    K: Clone + Eq + Hash,
{
    for (key, value) in baseline {
        let should_replace = match current.get(key) {
            None => true,
            Some(existing)
                if semantic_value_contains_call(existing)
                    && !semantic_value_contains_call(value) =>
            {
                true
            }
            Some(existing) => {
                semantic_value_preservation_score(value)
                    > semantic_value_preservation_score(existing)
            }
        };
        if should_replace {
            current.insert(key.clone(), value.clone());
        }
    }
}

fn frame_slot_merge_preservation_score(summary: &FrameSlotMergeSummary) -> i32 {
    40 + summary
        .incoming
        .values()
        .map(semantic_value_preservation_score)
        .sum::<i32>()
}

fn call_arg_vector_preservation_score(args: &[CallArgBinding]) -> i32 {
    (args.len() as i32) * 20
        + args
            .iter()
            .enumerate()
            .map(|(idx, arg)| call_arg_binding_preservation_score(arg) + (idx as i32 * 3))
            .sum::<i32>()
}

fn call_arg_vector_needs_authoritative_preservation(args: &[CallArgBinding]) -> bool {
    let imported_result_slot = matches!(
        args.first(),
        Some(CallArgBinding {
            arg: SemanticCallArg::StringAddr(_),
            ..
        })
    );
    let mut seen_negative_input_offsets = HashSet::new();

    for (idx, binding) in args.iter().enumerate() {
        if binding.role == CallArgRole::Result
            && !(imported_result_slot && idx + 1 == args.len() && binding.source_call.is_some())
        {
            return true;
        }

        if call_arg_binding_is_low_signal(binding) {
            return true;
        }

        if !binding.is_result()
            && let Some(offset) =
                call_arg_semantic_source_offset_for_binding(binding, 0, &mut HashSet::new())
            && offset < 0
            && !seen_negative_input_offsets.insert(offset)
        {
            return true;
        }
    }

    false
}

fn call_arg_binding_preservation_score(binding: &CallArgBinding) -> i32 {
    let role_score = match binding.role {
        CallArgRole::Input => 0,
        CallArgRole::Result => 120,
    };
    let stack_score = binding
        .stack_offset
        .map(|offset| if offset >= 0 { -20 } else { 20 })
        .unwrap_or(0);
    let source_score = call_arg_semantic_source_offset_for_binding(binding, 0, &mut HashSet::new())
        .map(|offset| if offset >= 0 { -60 } else { 140 })
        .unwrap_or(0);
    let low_signal_penalty = if call_arg_binding_is_low_signal(binding) {
        -180
    } else {
        0
    };
    role_score
        + stack_score
        + source_score
        + low_signal_penalty
        + semantic_call_arg_preservation_score(&binding.arg)
}

fn semantic_call_arg_preservation_score(arg: &SemanticCallArg) -> i32 {
    match arg {
        SemanticCallArg::StringAddr(_) => 450,
        SemanticCallArg::Semantic(value) => 200 + semantic_value_preservation_score(value),
        SemanticCallArg::FallbackExpr(expr) => call_arg_expr_preservation_score(expr, 0),
    }
}

fn call_arg_binding_is_low_signal(binding: &CallArgBinding) -> bool {
    match &binding.arg {
        SemanticCallArg::StringAddr(_) => false,
        SemanticCallArg::Semantic(value) => semantic_value_is_low_signal(value),
        SemanticCallArg::FallbackExpr(expr) => call_arg_expr_is_low_signal(expr, 0),
    }
}

fn semantic_value_is_low_signal(value: &SemanticValue) -> bool {
    match value {
        SemanticValue::Unknown => true,
        SemanticValue::Scalar(ScalarValue::Expr(expr)) => call_arg_expr_is_low_signal(expr, 0),
        SemanticValue::Scalar(ScalarValue::Root(root)) => {
            let name = root.display_name();
            is_call_arg_placeholder_name(&name)
                || is_call_arg_transient_name(&name)
                || is_generic_entry_arg_name(&name)
        }
        SemanticValue::Address(addr) | SemanticValue::Load { addr, .. } => {
            normalized_addr_is_low_signal(addr)
        }
    }
}

fn normalized_addr_is_low_signal(addr: &NormalizedAddr) -> bool {
    let low_signal_name = |name: &str| {
        let lower = name.to_ascii_lowercase();
        is_call_arg_placeholder_name(&lower)
            || is_call_arg_transient_name(&lower)
            || is_generic_entry_arg_name(&lower)
    };

    match &addr.base {
        BaseRef::Value(value) => low_signal_name(&value.display_name()),
        BaseRef::Raw(CExpr::Var(name)) => low_signal_name(name),
        BaseRef::Raw(CExpr::Paren(inner)) | BaseRef::Raw(CExpr::Cast { expr: inner, .. }) => {
            matches!(inner.as_ref(), CExpr::Var(name) if low_signal_name(name))
        }
        _ => false,
    }
}

fn call_arg_expr_is_low_signal(expr: &CExpr, depth: u32) -> bool {
    if depth > 8 {
        return false;
    }

    match expr {
        CExpr::Var(name) => {
            is_call_arg_placeholder_name(name)
                || is_call_arg_transient_name(name)
                || is_generic_entry_arg_name(name)
        }
        CExpr::Paren(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::AddrOf(inner)
        | CExpr::Deref(inner)
        | CExpr::Sizeof(inner) => call_arg_expr_is_low_signal(inner, depth + 1),
        CExpr::Unary { operand, .. } => call_arg_expr_is_low_signal(operand, depth + 1),
        CExpr::Binary { left, right, .. } => {
            call_arg_expr_is_low_signal(left, depth + 1)
                || call_arg_expr_is_low_signal(right, depth + 1)
        }
        CExpr::Subscript { base, index } => {
            call_arg_expr_is_low_signal(base, depth + 1)
                || call_arg_expr_is_low_signal(index, depth + 1)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            call_arg_expr_is_low_signal(base, depth + 1)
        }
        CExpr::Call { func, args } => {
            call_arg_expr_is_low_signal(func, depth + 1)
                || args
                    .iter()
                    .any(|arg| call_arg_expr_is_low_signal(arg, depth + 1))
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            call_arg_expr_is_low_signal(cond, depth + 1)
                || call_arg_expr_is_low_signal(then_expr, depth + 1)
                || call_arg_expr_is_low_signal(else_expr, depth + 1)
        }
        CExpr::Comma(items) => items
            .iter()
            .any(|item| call_arg_expr_is_low_signal(item, depth + 1)),
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::CharLit(_)
        | CExpr::StringLit(_)
        | CExpr::SizeofType(_) => false,
    }
}

fn is_generic_entry_arg_name(name: &str) -> bool {
    name.eq_ignore_ascii_case("argc")
        || name.eq_ignore_ascii_case("argv")
        || name.eq_ignore_ascii_case("envp")
        || name.strip_prefix("arg").is_some_and(|suffix| {
            !suffix.is_empty() && suffix.chars().all(|ch| ch.is_ascii_digit())
        })
}

fn call_arg_semantic_source_offset_for_binding(
    binding: &CallArgBinding,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<i64> {
    if depth > 8 {
        return None;
    }

    match &binding.arg {
        SemanticCallArg::Semantic(SemanticValue::Load {
            space: SpaceId::Ram,
            addr,
            ..
        })
        | SemanticCallArg::Semantic(SemanticValue::Address(addr)) => {
            normalized_stack_slot_offset(addr)
        }
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Root(root))) => {
            call_arg_semantic_source_offset_for_binding(
                &CallArgBinding::input(SemanticCallArg::FallbackExpr(CExpr::Var(
                    root.display_name(),
                ))),
                depth + 1,
                visited,
            )
        }
        SemanticCallArg::FallbackExpr(CExpr::Var(name)) => {
            if !visited.insert(name.clone()) {
                return None;
            }
            let offset = parse_negative_local_name(name);
            visited.remove(name);
            offset
        }
        SemanticCallArg::FallbackExpr(CExpr::Paren(inner))
        | SemanticCallArg::FallbackExpr(CExpr::Cast { expr: inner, .. }) => {
            call_arg_semantic_source_offset_for_binding(
                &CallArgBinding::input(SemanticCallArg::FallbackExpr((**inner).clone())),
                depth + 1,
                visited,
            )
        }
        _ => None,
    }
}

fn parse_negative_local_name(name: &str) -> Option<i64> {
    name.strip_prefix("local_")
        .and_then(|suffix| i64::from_str_radix(suffix, 16).ok())
        .map(|offset| -offset)
}

fn semantic_value_preservation_score(value: &SemanticValue) -> i32 {
    match value {
        SemanticValue::Unknown => 0,
        SemanticValue::Scalar(ScalarValue::Expr(expr)) => {
            40 + call_arg_expr_preservation_score(expr, 0)
        }
        SemanticValue::Scalar(ScalarValue::Root(root)) => {
            let mut score = 80;
            if root.var.version == 0 {
                score += 40;
            }
            score + call_arg_expr_preservation_score(&CExpr::Var(root.display_name()), 0)
        }
        SemanticValue::Address(addr) => 220 + normalized_addr_rank(addr),
        SemanticValue::Load { addr, .. } => 260 + normalized_addr_rank(addr),
    }
}

fn call_arg_expr_preservation_score(expr: &CExpr, depth: u32) -> i32 {
    if depth > 8 {
        return 0;
    }

    match expr {
        CExpr::StringLit(_) => 320,
        CExpr::IntLit(_) | CExpr::UIntLit(_) | CExpr::FloatLit(_) | CExpr::CharLit(_) => 80,
        CExpr::Var(name) => {
            if is_call_arg_placeholder_name(name) {
                -120
            } else if is_call_arg_transient_name(name) {
                -60
            } else if is_symbol_or_object_name(name)
                || name.eq_ignore_ascii_case("argc")
                || name.eq_ignore_ascii_case("argv")
                || name.eq_ignore_ascii_case("envp")
                || name.starts_with("arg")
            {
                180
            } else {
                70
            }
        }
        CExpr::Subscript { base, index } => {
            220 + call_arg_expr_preservation_score(base, depth + 1)
                + call_arg_expr_preservation_score(index, depth + 1)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            200 + call_arg_expr_preservation_score(base, depth + 1)
        }
        CExpr::Deref(inner) => 120 + call_arg_expr_preservation_score(inner, depth + 1),
        CExpr::AddrOf(inner) => 100 + call_arg_expr_preservation_score(inner, depth + 1),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } | CExpr::Sizeof(inner) => {
            call_arg_expr_preservation_score(inner, depth + 1)
        }
        CExpr::Unary { operand, .. } => 50 + call_arg_expr_preservation_score(operand, depth + 1),
        CExpr::Binary { left, right, .. } => {
            90 + call_arg_expr_preservation_score(left, depth + 1)
                + call_arg_expr_preservation_score(right, depth + 1)
        }
        CExpr::Call { func, args } => {
            30 + call_arg_expr_preservation_score(func, depth + 1)
                + args
                    .iter()
                    .map(|arg| call_arg_expr_preservation_score(arg, depth + 1))
                    .sum::<i32>()
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            20 + call_arg_expr_preservation_score(cond, depth + 1)
                + call_arg_expr_preservation_score(then_expr, depth + 1)
                + call_arg_expr_preservation_score(else_expr, depth + 1)
        }
        CExpr::Comma(items) => items
            .iter()
            .map(|item| call_arg_expr_preservation_score(item, depth + 1))
            .sum(),
        CExpr::SizeofType(_) => 0,
    }
}

fn populate_stable_stack_values(scratch: &mut UseScratch, blocks: &[SSABlock], env: &PassEnv<'_>) {
    scratch.info.stable_stack_values.clear();
    let Some(entry) = blocks.first() else {
        return;
    };

    let mut candidates: HashMap<i64, SemanticValue> = HashMap::new();
    let mut conflicts = HashSet::new();

    for op in &entry.ops {
        let SSAOp::Store {
            space: SpaceId::Ram,
            addr,
            val,
        } = op
        else {
            continue;
        };
        let Some(offset) = stack_slot_offset_for_addr(&scratch.info, addr, env).or_else(|| {
            semantic_addr_for_var(&scratch.info, addr, env)
                .and_then(|shape| normalized_stack_slot_offset(&shape))
        }) else {
            continue;
        };
        let Some(value) = semantic_stack_store_value(&scratch.info, val, env) else {
            conflicts.insert(offset);
            candidates.remove(&offset);
            continue;
        };
        match candidates.get(&offset) {
            Some(existing) if existing != &value => {
                conflicts.insert(offset);
                candidates.remove(&offset);
            }
            None if !conflicts.contains(&offset) => {
                candidates.insert(offset, value);
            }
            _ => {}
        }
    }

    if candidates.is_empty() {
        return;
    }

    for block in blocks {
        for op in &block.ops {
            let SSAOp::Store {
                space: SpaceId::Ram,
                addr,
                val,
            } = op
            else {
                continue;
            };
            let Some(offset) = stack_slot_offset_for_addr(&scratch.info, addr, env).or_else(|| {
                semantic_addr_for_var(&scratch.info, addr, env)
                    .and_then(|shape| normalized_stack_slot_offset(&shape))
            }) else {
                continue;
            };
            let Some(expected) = candidates.get(&offset).cloned() else {
                continue;
            };
            let actual = semantic_stack_store_value(&scratch.info, val, env);
            if actual.as_ref() != Some(&expected) {
                conflicts.insert(offset);
            }
        }
    }

    scratch.info.stable_stack_values = candidates
        .into_iter()
        .filter(|(offset, _)| !conflicts.contains(offset))
        .collect();
}

fn populate_frame_object_field_roots(
    scratch: &mut UseScratch,
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
) {
    scratch.info.frame_object_field_roots.clear();
    let Some(entry) = blocks.first() else {
        return;
    };

    let mut candidates: HashMap<FrameObjectFieldKey, SemanticValue> = HashMap::new();
    let mut conflicts = HashSet::new();

    for op in &entry.ops {
        let SSAOp::Store {
            space: SpaceId::Ram,
            addr,
            val,
        } = op
        else {
            continue;
        };
        let Some(shape) = semantic_addr_for_var(&scratch.info, addr, env) else {
            continue;
        };
        let Some(key) = frame_object_field_key(&scratch.info, &shape, env, 0) else {
            continue;
        };
        let Some(value) = semantic_stack_store_value(&scratch.info, val, env) else {
            conflicts.insert(key);
            candidates.remove(&key);
            continue;
        };
        match candidates.get(&key) {
            Some(existing) if existing != &value => {
                conflicts.insert(key);
                candidates.remove(&key);
            }
            None if !conflicts.contains(&key) => {
                candidates.insert(key, value);
            }
            _ => {}
        }
    }

    if candidates.is_empty() {
        return;
    }

    // Seed the entry-derived roots before validating later stores so loads
    // through the frame object can canonicalize back to the same semantic root
    // instead of looking like unrelated temporaries and conflicting.
    scratch.info.frame_object_field_roots = candidates.clone();
    refresh_semantic_values(scratch, blocks, env);

    for block in blocks {
        for op in &block.ops {
            let SSAOp::Store {
                space: SpaceId::Ram,
                addr,
                val,
            } = op
            else {
                continue;
            };
            let Some(shape) = semantic_addr_for_var(&scratch.info, addr, env) else {
                continue;
            };
            let Some(key) = frame_object_field_key(&scratch.info, &shape, env, 0) else {
                continue;
            };
            let Some(expected) = candidates.get(&key).cloned() else {
                continue;
            };
            let actual = semantic_stack_store_value(&scratch.info, val, env);
            if actual.as_ref() != Some(&expected) {
                conflicts.insert(key);
            }
        }
    }

    scratch.info.frame_object_field_roots = candidates
        .into_iter()
        .filter(|(key, _)| !conflicts.contains(key))
        .collect();
    refresh_semantic_values(scratch, blocks, env);
}

fn canonical_value_ref_key(
    info: &UseInfo,
    value: &ValueRef,
    env: &PassEnv<'_>,
    depth: u32,
) -> String {
    if depth > 8 {
        return value.display_name();
    }

    let key = value.display_name();
    if let Some(SemanticValue::Scalar(ScalarValue::Root(root))) = info.semantic_values.get(&key)
        && root.var != value.var
    {
        return canonical_value_ref_key(info, root, env, depth + 1);
    }
    if let Some(SemanticValue::Address(NormalizedAddr {
        base: BaseRef::Value(root),
        index: None,
        scale_bytes: 0,
        offset_bytes: 0,
    })) = info.semantic_values.get(&key)
        && root.var != value.var
    {
        return canonical_value_ref_key(info, root, env, depth + 1);
    }
    if let Some(prov) = info.forwarded_values.get(&key)
        && let Some(source_var) = &prov.source_var
        && *source_var != value.var
    {
        return canonical_value_ref_key(info, &ValueRef::from(source_var), env, depth + 1);
    }

    if value.var.version == 0
        && let Some(alias) = env
            .param_register_aliases
            .get(&value.var.name.to_ascii_lowercase())
    {
        return format!("param:{alias}");
    }

    key
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct MemoryStateKey {
    space: SpaceId,
    normalized_addr: String,
}

fn normalized_memory_key(
    info: &UseInfo,
    space: SpaceId,
    addr: &NormalizedAddr,
    env: &PassEnv<'_>,
) -> Option<MemoryStateKey> {
    let base = match &addr.base {
        BaseRef::Value(value) => format!("v:{}", canonical_value_ref_key(info, value, env, 0)),
        BaseRef::StackSlot(offset) => format!("s:{offset}"),
        BaseRef::Raw(_) => return None,
    };
    let index = addr
        .index
        .as_ref()
        .map(|value| canonical_value_ref_key(info, value, env, 0))
        .unwrap_or_default();
    Some(MemoryStateKey {
        space,
        normalized_addr: format!("{base}|{index}|{}|{}", addr.scale_bytes, addr.offset_bytes),
    })
}

fn stable_memory_map_key(key: &MemoryStateKey) -> String {
    let space = match key.space {
        SpaceId::Ram => "ram".to_string(),
        SpaceId::Register => "register".to_string(),
        SpaceId::Unique => "unique".to_string(),
        SpaceId::Const => "const".to_string(),
        SpaceId::Custom(id) => format!("custom:{id}"),
    };
    format!("{space}|{}", key.normalized_addr)
}

fn frame_object_field_key(
    info: &UseInfo,
    addr: &NormalizedAddr,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<FrameObjectFieldKey> {
    if depth > 8 || addr.index.is_some() {
        return None;
    }

    match &addr.base {
        BaseRef::StackSlot(base_slot_offset) if addr.offset_bytes != 0 => {
            Some(FrameObjectFieldKey {
                base_slot_offset: *base_slot_offset,
                field_offset: addr.offset_bytes,
            })
        }
        BaseRef::Value(value_ref) => {
            let base_addr = semantic_addr_for_var(info, &value_ref.var, env)?;
            let mut key = frame_object_field_key(info, &base_addr, env, depth + 1)?;
            key.field_offset += addr.offset_bytes;
            Some(key)
        }
        BaseRef::Raw(_) => None,
        BaseRef::StackSlot(_) => None,
    }
}

fn populate_stable_memory_values(scratch: &mut UseScratch, blocks: &[SSABlock], env: &PassEnv<'_>) {
    scratch.info.stable_memory_values.clear();
    let Some(entry) = blocks.first() else {
        return;
    };

    let mut candidates: HashMap<MemoryStateKey, SemanticValue> = HashMap::new();
    let mut conflicts = HashSet::new();

    for op in &entry.ops {
        let SSAOp::Store { space, addr, val } = op else {
            continue;
        };
        let Some(shape) = semantic_addr_for_var(&scratch.info, addr, env) else {
            continue;
        };
        if normalized_stack_slot_offset(&shape).is_some() || !is_authoritative_addr(&shape) {
            continue;
        }
        let Some(key) = normalized_memory_key(&scratch.info, *space, &shape, env) else {
            continue;
        };
        let Some(value) = semantic_stack_store_value(&scratch.info, val, env) else {
            conflicts.insert(key.clone());
            candidates.remove(&key);
            continue;
        };
        match candidates.get(&key) {
            Some(existing) if existing != &value => {
                conflicts.insert(key.clone());
                candidates.remove(&key);
            }
            None if !conflicts.contains(&key) => {
                candidates.insert(key, value);
            }
            _ => {}
        }
    }

    if candidates.is_empty() {
        return;
    }

    for block in blocks {
        for op in &block.ops {
            let SSAOp::Store { space, addr, val } = op else {
                continue;
            };
            let Some(shape) = semantic_addr_for_var(&scratch.info, addr, env) else {
                continue;
            };
            if normalized_stack_slot_offset(&shape).is_some() {
                continue;
            }
            let Some(key) = normalized_memory_key(&scratch.info, *space, &shape, env) else {
                continue;
            };
            let Some(expected) = candidates.get(&key).cloned() else {
                continue;
            };
            let actual = semantic_stack_store_value(&scratch.info, val, env);
            if actual.as_ref() != Some(&expected) {
                conflicts.insert(key);
            }
        }
    }

    scratch.info.stable_memory_values = candidates
        .into_iter()
        .filter(|(key, _)| !conflicts.contains(key))
        .map(|(key, value)| (stable_memory_map_key(&key), value))
        .collect();
}

fn refresh_semantic_values(scratch: &mut UseScratch, blocks: &[SSABlock], env: &PassEnv<'_>) {
    let mut cache = SemanticTypeHintCache::from_info(&scratch.info);
    for block in blocks {
        for phi in &block.phis {
            collect_semantic_values_with_cache(
                scratch,
                &SSAOp::Phi {
                    dst: phi.dst.clone(),
                    sources: phi.sources.iter().map(|(_, src)| src.clone()).collect(),
                },
                env,
                &mut cache,
            );
        }
        for op in &block.ops {
            collect_semantic_values_with_cache(scratch, op, env, &mut cache);
        }
    }
}

pub(crate) fn populate_frame_slot_merges(
    info: &mut UseInfo,
    func: &SSAFunction,
    env: &PassEnv<'_>,
    prepared: Option<&SsaArtifact>,
) {
    info.frame_slot_merges.clear();

    for block in func.blocks() {
        let preds = func.predecessors(block.addr);
        if preds.len() < 2 {
            continue;
        }

        for op in &block.ops {
            let SSAOp::Load {
                dst,
                space: SpaceId::Ram,
                addr,
            } = op
            else {
                continue;
            };
            let prepared_offset =
                prepared.and_then(|prepared| prepared_stack_offset_for_var(prepared, addr));
            let Some(slot_offset) = prepared_offset.or_else(|| {
                utils::extract_stack_offset_from_var(
                    addr,
                    &info.definitions,
                    env.fp_name,
                    env.sp_name,
                )
            }) else {
                continue;
            };

            let mut incoming = BTreeMap::new();
            let mut complete = true;
            for pred_addr in &preds {
                let Some(pred_block) = func.get_block(*pred_addr) else {
                    complete = false;
                    break;
                };
                let Some(value) =
                    merged_slot_store_value_for_pred(info, pred_block, slot_offset, env, prepared)
                else {
                    complete = false;
                    break;
                };
                incoming.insert(*pred_addr, value);
            }

            if !complete || incoming.len() != preds.len() {
                continue;
            }

            info.frame_slot_merges.insert(
                dst.display_name(),
                FrameSlotMergeSummary {
                    slot_offset,
                    merge_block_addr: block.addr,
                    load_name: dst.display_name(),
                    incoming,
                },
            );
        }
    }
}

fn prepared_stack_offset_for_var(prepared: &SsaArtifact, var: &SSAVar) -> Option<i64> {
    let object = prepared.object_for_var(var, r2il::SpaceId::Ram)?;
    let object = prepared.objects().object(object)?;
    match object.kind {
        ObjectKind::StackSlot { offset, .. } | ObjectKind::FrameObject { offset, .. } => {
            Some(offset)
        }
        _ => None,
    }
}

pub(crate) fn annotate_stack_slot_semantics(
    info: &mut UseInfo,
    func: &SSAFunction,
    return_slots: &HashSet<i64>,
    env: &PassEnv<'_>,
) {
    let mut offset_semantics: HashMap<i64, StackSlotProvenance> = HashMap::new();
    for slot in info.stack_slots.values().copied() {
        merge_stack_slot_semantics(&mut offset_semantics, slot);
    }

    for slot_offset in return_slots {
        merge_stack_slot_semantics(
            &mut offset_semantics,
            StackSlotProvenance {
                offset: *slot_offset,
                predicate_carrier: false,
                return_carrier: true,
                value_kind: StackSlotValueKind::Unknown,
            },
        );
        merge_stack_slot_semantics(
            &mut offset_semantics,
            StackSlotProvenance {
                offset: *slot_offset,
                predicate_carrier: false,
                return_carrier: true,
                value_kind: stack_slot_value_kind_from_return_slot_stores(
                    info,
                    func,
                    *slot_offset,
                    env,
                ),
            },
        );
    }

    for summary in info.frame_slot_merges.values() {
        merge_stack_slot_semantics(
            &mut offset_semantics,
            StackSlotProvenance {
                offset: summary.slot_offset,
                predicate_carrier: false,
                return_carrier: return_slots.contains(&summary.slot_offset),
                value_kind: stack_slot_value_kind_from_merge_summary(summary),
            },
        );
    }

    for block in func.blocks() {
        for (idx, op) in block.ops.iter().enumerate() {
            let SSAOp::CBranch { cond, .. } = op else {
                continue;
            };
            let Some(predicate_slot) =
                predicate_carrier_slot_for_branch(info, block, idx, cond, env, 0)
            else {
                continue;
            };

            let provenance = StackSlotProvenance {
                offset: predicate_slot.offset,
                predicate_carrier: true,
                return_carrier: return_slots.contains(&predicate_slot.offset),
                value_kind: StackSlotValueKind::Scalar,
            };
            merge_stack_slot_semantics(&mut offset_semantics, provenance);
            merge_named_stack_slot_semantics(info, predicate_slot.load_name, provenance);
            merge_named_stack_slot_semantics(info, predicate_slot.addr_name, provenance);
        }
    }

    for slot in info.stack_slots.values_mut() {
        if let Some(offset_fact) = offset_semantics.get(&slot.offset).copied() {
            *slot = slot.merge(offset_fact);
        }
    }
}

pub(crate) fn populate_switch_selector_roots(
    info: &mut UseInfo,
    func: &SSAFunction,
    env: &PassEnv<'_>,
) {
    info.switch_selector_roots.clear();

    for block in func.blocks() {
        if func.successors(block.addr).len() < 3 {
            continue;
        }
        let Some(candidate) = switch_selector_value_for_block(info, func, block, env) else {
            continue;
        };
        info.switch_selector_roots.insert(block.addr, candidate);
    }
}

fn switch_selector_value_for_block(
    info: &UseInfo,
    func: &SSAFunction,
    block: &SSABlock,
    env: &PassEnv<'_>,
) -> Option<SemanticValue> {
    let preds = func.predecessors(block.addr);
    let load_ctx = SwitchSelectorLoadCtx {
        func,
        block,
        preds: &preds,
        env,
    };
    let mut best = None;

    for (idx, op) in block.ops.iter().enumerate() {
        let candidate = match op {
            SSAOp::Load {
                dst,
                space: SpaceId::Ram,
                addr,
            } => switch_selector_value_for_load(info, &load_ctx, idx, dst, addr),
            SSAOp::Copy { dst, src }
            | SSAOp::IntZExt { dst, src }
            | SSAOp::IntSExt { dst, src }
            | SSAOp::Trunc { dst, src }
            | SSAOp::Cast { dst, src }
            | SSAOp::Subpiece { dst, src, .. } => switch_selector_value_for_var(info, dst, env)
                .or_else(|| switch_selector_value_for_var(info, src, env)),
            _ => None,
        };
        best = preferred_switch_selector_value(info, best, candidate);
    }

    best
}

#[derive(Debug)]
struct PredicateCarrierSlotMatch {
    offset: i64,
    load_name: String,
    addr_name: String,
}

const MAX_STACK_CARRIER_TRACE_DEPTH: u32 = 12;

fn merge_stack_slot_semantics(
    slots: &mut HashMap<i64, StackSlotProvenance>,
    candidate: StackSlotProvenance,
) {
    slots
        .entry(candidate.offset)
        .and_modify(|existing| *existing = existing.merge(candidate))
        .or_insert(candidate);
}

fn merge_named_stack_slot_semantics(
    info: &mut UseInfo,
    name: String,
    candidate: StackSlotProvenance,
) {
    info.stack_slots
        .entry(name)
        .and_modify(|existing| *existing = existing.merge(candidate))
        .or_insert(candidate);
}

fn stack_slot_value_kind_from_merge_summary(summary: &FrameSlotMergeSummary) -> StackSlotValueKind {
    let mut kinds = summary
        .incoming
        .values()
        .map(stack_slot_value_kind_from_semantic_value);
    let Some(first) = kinds.next() else {
        return StackSlotValueKind::Unknown;
    };
    if first == StackSlotValueKind::Unknown {
        return StackSlotValueKind::Unknown;
    }
    if kinds.all(|kind| kind == first) {
        first
    } else {
        StackSlotValueKind::Unknown
    }
}

fn stack_slot_value_kind_from_semantic_value(value: &SemanticValue) -> StackSlotValueKind {
    match value {
        SemanticValue::Scalar(_) => StackSlotValueKind::Scalar,
        SemanticValue::Address(_) => StackSlotValueKind::AddressLike,
        SemanticValue::Load { .. } | SemanticValue::Unknown => StackSlotValueKind::Unknown,
    }
}

fn predicate_carrier_slot_for_branch(
    info: &UseInfo,
    block: &SSABlock,
    branch_idx: usize,
    cond: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<PredicateCarrierSlotMatch> {
    if depth > MAX_STACK_CARRIER_TRACE_DEPTH || cond.is_const() {
        return None;
    }

    for (idx, op) in block.ops[..branch_idx].iter().enumerate().rev() {
        if op.dst() != Some(cond) {
            continue;
        }
        return match op {
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Subpiece { src, .. }
            | SSAOp::BoolNot { src, .. } => {
                predicate_carrier_slot_for_branch(info, block, idx, src, env, depth + 1)
            }
            SSAOp::IntSub { a, b, .. } if var_is_zero_constant(a) || var_is_zero_constant(b) => {
                let passthrough = if var_is_zero_constant(a) { b } else { a };
                predicate_carrier_slot_for_branch(info, block, idx, passthrough, env, depth + 1)
            }
            SSAOp::IntEqual { a, b, .. }
            | SSAOp::IntNotEqual { a, b, .. }
            | SSAOp::IntLess { a, b, .. }
            | SSAOp::IntSLess { a, b, .. }
            | SSAOp::IntLessEqual { a, b, .. }
            | SSAOp::IntSLessEqual { a, b, .. } => {
                compare_zero_predicate_carrier_slot_for_operands(
                    info,
                    block,
                    idx,
                    a,
                    b,
                    env,
                    depth + 1,
                )
            }
            SSAOp::Load {
                dst,
                space: SpaceId::Ram,
                addr,
            } => predicate_carrier_slot_for_load(info, block, idx, dst, addr, env, depth + 1),
            _ => None,
        };
    }

    None
}

fn compare_zero_predicate_carrier_slot_for_operands(
    info: &UseInfo,
    block: &SSABlock,
    before_idx: usize,
    a: &SSAVar,
    b: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<PredicateCarrierSlotMatch> {
    let a_zero = var_is_zero_constant(a);
    let b_zero = var_is_zero_constant(b);
    if a_zero == b_zero {
        return None;
    }

    let candidate = if a_zero { b } else { a };
    predicate_carrier_slot_for_branch(info, block, before_idx, candidate, env, depth + 1)
}

fn predicate_carrier_slot_for_load(
    info: &UseInfo,
    block: &SSABlock,
    load_idx: usize,
    dst: &SSAVar,
    addr: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<PredicateCarrierSlotMatch> {
    if depth > MAX_STACK_CARRIER_TRACE_DEPTH {
        return None;
    }

    let offset = stack_slot_offset_for_addr(info, addr, env)?;
    for (store_idx, op) in block.ops[..load_idx].iter().enumerate().rev() {
        let SSAOp::Store {
            space: SpaceId::Ram,
            addr: store_addr,
            val,
        } = op
        else {
            continue;
        };
        let Some(store_offset) = stack_slot_offset_for_addr(info, store_addr, env) else {
            continue;
        };
        if store_offset != offset {
            continue;
        }
        if block_value_is_scalar_or_predicate(info, block, store_idx, val, env, depth + 1) {
            return Some(PredicateCarrierSlotMatch {
                offset,
                load_name: dst.display_name(),
                addr_name: addr.display_name(),
            });
        }
    }
    None
}

fn block_value_is_scalar_or_predicate(
    info: &UseInfo,
    block: &SSABlock,
    before_idx: usize,
    var: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> bool {
    if depth > MAX_STACK_CARRIER_TRACE_DEPTH {
        return false;
    }

    if var.is_const() {
        return true;
    }

    if semantic_source_value_for_var(info, var).is_some_and(|value| {
        stack_slot_value_kind_from_semantic_value(&value) == StackSlotValueKind::Scalar
    }) {
        return true;
    }

    if semantic_var_is_pointer_like(info, var, env) {
        return false;
    }

    for (idx, op) in block.ops[..before_idx].iter().enumerate().rev() {
        if op.dst() != Some(var) {
            continue;
        }
        return match op {
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Subpiece { src, .. }
            | SSAOp::BoolNot { src, .. } => {
                block_value_is_scalar_or_predicate(info, block, idx, src, env, depth + 1)
            }
            SSAOp::IntEqual { .. }
            | SSAOp::IntNotEqual { .. }
            | SSAOp::IntLess { .. }
            | SSAOp::IntSLess { .. }
            | SSAOp::IntLessEqual { .. }
            | SSAOp::IntSLessEqual { .. } => true,
            SSAOp::IntSub { a, b, .. } if var_is_zero_constant(a) || var_is_zero_constant(b) => {
                let passthrough = if var_is_zero_constant(a) { b } else { a };
                block_value_is_scalar_or_predicate(info, block, idx, passthrough, env, depth + 1)
            }
            SSAOp::IntAnd { a, b, .. }
            | SSAOp::IntOr { a, b, .. }
            | SSAOp::IntXor { a, b, .. }
            | SSAOp::BoolAnd { a, b, .. }
            | SSAOp::BoolOr { a, b, .. } => {
                block_value_is_scalar_or_predicate(info, block, idx, a, env, depth + 1)
                    && block_value_is_scalar_or_predicate(info, block, idx, b, env, depth + 1)
            }
            SSAOp::Load {
                dst,
                space: SpaceId::Ram,
                addr,
            } => predicate_carrier_slot_for_load(info, block, idx, dst, addr, env, depth + 1)
                .is_some(),
            _ => false,
        };
    }

    false
}

fn var_is_zero_constant(var: &SSAVar) -> bool {
    utils::parse_const_value(&var.name).is_some_and(|value| value == 0)
}

fn stack_slot_value_kind_from_return_slot_stores(
    info: &UseInfo,
    func: &SSAFunction,
    slot_offset: i64,
    env: &PassEnv<'_>,
) -> StackSlotValueKind {
    let mut kinds = Vec::new();
    for exit_block in func.blocks().filter(|block| {
        block
            .ops
            .iter()
            .any(|op| matches!(op, SSAOp::Return { .. }))
    }) {
        if let Some(kind) =
            stack_slot_value_kind_from_return_exit(info, func, exit_block, slot_offset, env)
        {
            kinds.push(kind);
        }
    }

    let Some(first) = kinds.first().copied() else {
        return StackSlotValueKind::Unknown;
    };
    if first == StackSlotValueKind::Unknown {
        return StackSlotValueKind::Unknown;
    }
    if kinds.into_iter().all(|kind| kind == first) {
        first
    } else {
        StackSlotValueKind::Unknown
    }
}

fn stack_slot_value_kind_from_return_exit(
    info: &UseInfo,
    func: &SSAFunction,
    exit_block: &SSABlock,
    slot_offset: i64,
    env: &PassEnv<'_>,
) -> Option<StackSlotValueKind> {
    let mut kinds = Vec::new();

    if let Some(kind) = stack_slot_value_kind_from_block_store_to_exit(
        info,
        exit_block,
        exit_block.addr,
        slot_offset,
        env,
    ) {
        kinds.push(kind);
    }

    for pred_addr in func.predecessors(exit_block.addr) {
        let pred_block = func.get_block(pred_addr)?;
        if let Some(kind) = stack_slot_value_kind_from_block_store_to_exit(
            info,
            pred_block,
            exit_block.addr,
            slot_offset,
            env,
        ) {
            kinds.push(kind);
        }
    }

    let first = kinds.first().copied()?;
    if first == StackSlotValueKind::Unknown {
        return Some(StackSlotValueKind::Unknown);
    }
    if kinds.into_iter().all(|kind| kind == first) {
        Some(first)
    } else {
        Some(StackSlotValueKind::Unknown)
    }
}

fn stack_slot_value_kind_from_block_store_to_exit(
    info: &UseInfo,
    block: &SSABlock,
    exit_addr: u64,
    slot_offset: i64,
    env: &PassEnv<'_>,
) -> Option<StackSlotValueKind> {
    let mut exiting = false;

    for (idx, op) in block.ops.iter().enumerate().rev() {
        match op {
            SSAOp::Return { .. } => exiting = true,
            SSAOp::Branch { target } | SSAOp::CBranch { target, .. }
                if crate::address::parse_address_from_var_name(&target.name) == Some(exit_addr) =>
            {
                exiting = true;
            }
            SSAOp::Store {
                space: SpaceId::Ram,
                addr,
                val,
            } if exiting => {
                let Some(offset) = stack_slot_offset_for_addr(info, addr, env) else {
                    continue;
                };
                if offset != slot_offset {
                    continue;
                }
                return Some(value_kind_for_block_var(info, block, idx, val, env, 0));
            }
            _ => {}
        }
    }

    None
}

fn value_kind_for_block_var(
    info: &UseInfo,
    block: &SSABlock,
    before_idx: usize,
    var: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> StackSlotValueKind {
    if depth > 8 {
        return StackSlotValueKind::Unknown;
    }

    let stable_scalar_load_kind = info
        .semantic_values
        .get(&var.display_name())
        .and_then(|value| match value {
            SemanticValue::Load {
                space: SpaceId::Ram,
                addr,
                ..
            } => normalized_stack_slot_offset(addr)
                .filter(|offset| *offset < 0)
                .and_then(|offset| info.stable_stack_values.get(&offset))
                .map(stack_slot_value_kind_from_semantic_value),
            _ => None,
        })
        .unwrap_or(StackSlotValueKind::Unknown);
    if stable_scalar_load_kind == StackSlotValueKind::Scalar {
        return StackSlotValueKind::Scalar;
    }

    let semantic_kind = semantic_source_value_for_var(info, var)
        .map(|value| stack_slot_value_kind_from_semantic_value(&value))
        .unwrap_or(StackSlotValueKind::Unknown);
    if semantic_kind == StackSlotValueKind::Scalar {
        return StackSlotValueKind::Scalar;
    }

    if block_value_is_scalar_or_predicate(info, block, before_idx, var, env, depth + 1) {
        return StackSlotValueKind::Scalar;
    }

    if semantic_kind == StackSlotValueKind::AddressLike {
        return StackSlotValueKind::AddressLike;
    }

    if semantic_var_is_pointer_like(info, var, env) {
        return StackSlotValueKind::AddressLike;
    }

    semantic_kind
}

struct SwitchSelectorLoadCtx<'a, 'b> {
    func: &'a SSAFunction,
    block: &'a SSABlock,
    preds: &'b [u64],
    env: &'a PassEnv<'a>,
}

fn switch_selector_value_for_load(
    info: &UseInfo,
    ctx: &SwitchSelectorLoadCtx<'_, '_>,
    op_idx: usize,
    dst: &SSAVar,
    addr: &SSAVar,
) -> Option<SemanticValue> {
    let slot_offset = stack_slot_offset_for_addr(info, addr, ctx.env).or_else(|| {
        utils::extract_stack_offset_from_var(
            addr,
            &info.definitions,
            ctx.env.fp_name,
            ctx.env.sp_name,
        )
    });

    let from_preds = slot_offset.and_then(|offset| {
        let mut best = None;
        for pred_addr in ctx.preds {
            let pred_block = ctx.func.get_block(*pred_addr)?;
            let candidate =
                merged_slot_store_value_for_pred(info, pred_block, offset, ctx.env, None);
            best = preferred_switch_selector_value(info, best, candidate);
        }
        best
    });

    let from_same_family =
        same_register_family_semantic_value_before(info, &ctx.block.ops, op_idx, dst, ctx.env);

    preferred_switch_selector_value(
        info,
        preferred_switch_selector_value(info, from_preds, from_same_family),
        switch_selector_value_for_var(info, dst, ctx.env),
    )
    .or_else(|| slot_offset.and_then(|offset| info.stable_stack_values.get(&offset).cloned()))
    .filter(|candidate| switch_selector_candidate_score(info, candidate) > 0)
    .map(|candidate| {
        if let SemanticValue::Scalar(ScalarValue::Root(root)) = &candidate
            && root.var == *dst
            && let Some(forwarded) = info.forwarded_values.get(&dst.display_name())
            && let Some(source_var) = &forwarded.source_var
        {
            return SemanticValue::Scalar(ScalarValue::Root(ValueRef::from(source_var)));
        }
        candidate
    })
    .filter(|candidate| {
        !matches!(
                candidate,
                SemanticValue::Scalar(ScalarValue::Root(root))
                    if root.var.version == 0
                        && ctx.env
                            .param_register_aliases
                            .contains_key(&root.var.name.to_ascii_lowercase())
                        && ctx.block.addr != ctx.func.entry
        )
    })
}

fn switch_selector_value_for_var(
    info: &UseInfo,
    var: &SSAVar,
    env: &PassEnv<'_>,
) -> Option<SemanticValue> {
    let direct = info.semantic_values.get(&var.display_name()).cloned();
    let forwarded = info
        .forwarded_values
        .get(&var.display_name())
        .and_then(|prov| prov.source_var.as_ref())
        .map(|source_var| SemanticValue::Scalar(ScalarValue::Root(ValueRef::from(source_var))));

    preferred_switch_selector_value(info, direct, forwarded).filter(|candidate| {
        !matches!(candidate, SemanticValue::Unknown)
            && !matches!(
                candidate,
                SemanticValue::Scalar(ScalarValue::Root(root))
                    if root.var.version == 0
                        && env
                            .param_register_aliases
                            .contains_key(&root.var.name.to_ascii_lowercase())
            )
    })
}

fn preferred_switch_selector_value(
    info: &UseInfo,
    current: Option<SemanticValue>,
    candidate: Option<SemanticValue>,
) -> Option<SemanticValue> {
    match (current, candidate) {
        (None, other) => other,
        (some @ Some(_), None) => some,
        (Some(current), Some(candidate)) => {
            let current_score = switch_selector_candidate_score(info, &current);
            let candidate_score = switch_selector_candidate_score(info, &candidate);
            if candidate_score > current_score {
                Some(candidate)
            } else {
                Some(current)
            }
        }
    }
}

fn switch_selector_candidate_score(info: &UseInfo, value: &SemanticValue) -> i32 {
    let mut score = semantic_value_preservation_score(value);
    match value {
        SemanticValue::Scalar(ScalarValue::Root(root)) => {
            if root.var.version == 0 {
                score -= 120;
            } else {
                score += 100;
            }
            let display = root.display_name();
            if let Some(alias) = info.var_aliases.get(&display) {
                if alias.eq_ignore_ascii_case("argc")
                    || alias.eq_ignore_ascii_case("argv")
                    || alias.eq_ignore_ascii_case("envp")
                    || alias.starts_with("arg")
                {
                    score -= 80;
                } else {
                    score += 80;
                }
            }
        }
        SemanticValue::Scalar(ScalarValue::Expr(expr)) => {
            score += call_arg_expr_preservation_score(expr, 0);
        }
        SemanticValue::Address(_) | SemanticValue::Load { .. } => {
            score -= 40;
        }
        SemanticValue::Unknown => score = -1,
    }
    score
}

#[cfg(test)]
pub(crate) fn collect_local_struct_field_access_profiles(
    info: &UseInfo,
    func: &SSAFunction,
    env: &PassEnv<'_>,
    arg_slot_map: &HashMap<String, usize>,
) -> Vec<LocalStructFieldAccessProfile> {
    let mut out = Vec::new();

    for block in func.blocks() {
        for op in &block.ops {
            match op {
                SSAOp::Load {
                    dst,
                    space: SpaceId::Ram,
                    addr,
                } => {
                    if let Some(profile) = struct_field_access_profile_for_addr(
                        info,
                        addr,
                        dst.size,
                        false,
                        env,
                        arg_slot_map,
                    ) {
                        out.push(profile);
                    }
                }
                SSAOp::Store {
                    space: SpaceId::Ram,
                    addr,
                    val,
                } => {
                    if let Some(profile) = struct_field_access_profile_for_addr(
                        info,
                        addr,
                        val.size,
                        true,
                        env,
                        arg_slot_map,
                    ) {
                        out.push(profile);
                    }
                }
                _ => {}
            }
        }
    }

    out.sort_by(|a, b| {
        a.arg_index
            .cmp(&b.arg_index)
            .then_with(|| a.field_offset.cmp(&b.field_offset))
            .then_with(|| a.access_size.cmp(&b.access_size))
            .then_with(|| a.is_write.cmp(&b.is_write))
    });
    out.dedup();
    out
}

#[cfg(test)]
fn struct_field_access_profile_for_addr(
    info: &UseInfo,
    addr: &SSAVar,
    access_size: u32,
    is_write: bool,
    env: &PassEnv<'_>,
    arg_slot_map: &HashMap<String, usize>,
) -> Option<LocalStructFieldAccessProfile> {
    let shape = semantic_addr_for_var(info, addr, env)?;
    if shape.offset_bytes < 0 {
        return None;
    }
    if shape.offset_bytes == 0 && shape.index.is_some() {
        return None;
    }

    let BaseRef::Value(base_ref) = &shape.base else {
        return None;
    };
    let arg_index = arg_slot_for_value_ref(info, base_ref, env, arg_slot_map, 0)?;

    Some(LocalStructFieldAccessProfile {
        arg_index,
        field_offset: shape.offset_bytes as u64,
        access_size,
        is_write,
    })
}

#[cfg(test)]
fn arg_slot_for_value_ref(
    info: &UseInfo,
    value_ref: &ValueRef,
    env: &PassEnv<'_>,
    arg_slot_map: &HashMap<String, usize>,
    depth: u32,
) -> Option<usize> {
    if depth > 8 {
        return None;
    }

    let key = value_ref.var.name.to_ascii_lowercase();
    if value_ref.var.version == 0
        && let Some(slot) = arg_slot_map.get(&key).copied()
    {
        return Some(slot);
    }

    let display = value_ref.var.display_name();
    if let Some(value) = info.semantic_values.get(&display) {
        match value {
            SemanticValue::Scalar(ScalarValue::Root(root)) => {
                if root.var != value_ref.var {
                    return arg_slot_for_value_ref(info, root, env, arg_slot_map, depth + 1);
                }
            }
            SemanticValue::Address(NormalizedAddr {
                base: BaseRef::Value(root),
                ..
            }) => {
                if root.var != value_ref.var {
                    return arg_slot_for_value_ref(info, root, env, arg_slot_map, depth + 1);
                }
            }
            SemanticValue::Load {
                space: SpaceId::Ram,
                addr:
                    NormalizedAddr {
                        base: BaseRef::Value(root),
                        ..
                    },
                ..
            } => {
                if root.var != value_ref.var {
                    return arg_slot_for_value_ref(info, root, env, arg_slot_map, depth + 1);
                }
            }
            _ => {}
        }
    }

    if let Some(prov) = info.forwarded_values.get(&display)
        && let Some(source_var) = &prov.source_var
        && *source_var != value_ref.var
    {
        return arg_slot_for_value_ref(
            info,
            &ValueRef::from(source_var),
            env,
            arg_slot_map,
            depth + 1,
        );
    }

    if let Some(alias) = env.param_register_aliases.get(&key)
        && let Some(slot) = alias
            .strip_prefix("arg")
            .and_then(|suffix| suffix.parse::<usize>().ok())
            .and_then(|idx| idx.checked_sub(1))
    {
        return Some(slot);
    }

    None
}

fn seed_entry_param_aliases(scratch: &mut UseScratch, blocks: &[SSABlock], env: &PassEnv<'_>) {
    for block in blocks {
        block.for_each_source(|src| {
            let var = src.var;
            if var.version != 0 {
                return;
            }
            if let Some(alias) = env
                .param_register_aliases
                .get(&var.name.to_ascii_lowercase())
            {
                scratch
                    .info
                    .var_aliases
                    .entry(var.display_name())
                    .or_insert_with(|| alias.clone());
            }
        });
        block.for_each_def(|def| {
            let var = def.var;
            if var.version != 0 {
                return;
            }
            if let Some(alias) = env
                .param_register_aliases
                .get(&var.name.to_ascii_lowercase())
            {
                scratch
                    .info
                    .var_aliases
                    .entry(var.display_name())
                    .or_insert_with(|| alias.clone());
            }
        });
    }
}

fn count_uses_and_conditions(scratch: &mut UseScratch, block: &SSABlock) {
    for phi in &block.phis {
        for (_, src) in &phi.sources {
            scratch.info.note_use_for_var(src);
        }
    }

    for op in &block.ops {
        for src in op.sources() {
            scratch.info.note_use_for_var(src);
        }

        if let SSAOp::CBranch { cond, .. } = op {
            scratch.info.note_condition_var(cond);
        }
    }
}

fn pin_loop_carried_phi_values(scratch: &mut UseScratch, blocks: &[SSABlock]) {
    if blocks.is_empty() {
        return;
    }

    let block_set: HashSet<u64> = blocks.iter().map(|block| block.addr).collect();
    let mut successors = BTreeMap::new();
    for (idx, block) in blocks.iter().enumerate() {
        let mut succs = infer_successors(block, idx, blocks, &block_set);
        succs.sort_unstable();
        succs.dedup();
        successors.insert(block.addr, succs);
    }
    let components = strongly_connected_components(&successors);

    for block in blocks {
        let Some(block_component) = components.get(&block.addr).copied() else {
            continue;
        };
        for phi in &block.phis {
            let is_loop_carried = phi.sources.iter().any(|(pred, _)| {
                components.get(pred).copied() == Some(block_component)
                    && successors
                        .get(pred)
                        .is_some_and(|succs| succs.contains(&block.addr))
            });
            if !is_loop_carried {
                continue;
            }

            pin_phi_materialized_var(&mut scratch.info, &phi.dst);
            for (_, src) in &phi.sources {
                pin_phi_materialized_var(&mut scratch.info, src);
            }
        }
    }
}

fn pin_phi_materialized_var(info: &mut UseInfo, var: &SSAVar) {
    if var.is_const() || var.is_temp() || utils::is_cpu_flag(&var.name.to_ascii_lowercase()) {
        return;
    }
    let display = var.display_name();
    info.pinned.insert(display.clone());
    info.pinned.insert(display.to_ascii_lowercase());
}

fn pin_aliases_for_pinned_values(info: &mut UseInfo) {
    let mut aliases = Vec::new();
    for pinned in &info.pinned {
        if let Some(alias) = info.var_aliases.get(pinned)
            && !alias.trim().is_empty()
        {
            aliases.push(alias.clone());
        }
    }
    for alias in aliases {
        info.pinned.insert(alias);
    }
}

fn strongly_connected_components(successors: &BTreeMap<u64, Vec<u64>>) -> HashMap<u64, usize> {
    let mut visited = HashSet::new();
    let mut order = Vec::with_capacity(successors.len());
    for start in successors.keys().copied() {
        if visited.contains(&start) {
            continue;
        }
        let mut stack = vec![(start, false)];
        while let Some((node, exiting)) = stack.pop() {
            if exiting {
                order.push(node);
                continue;
            }
            if !visited.insert(node) {
                continue;
            }
            stack.push((node, true));
            if let Some(succs) = successors.get(&node) {
                for succ in succs.iter().rev().copied() {
                    if successors.contains_key(&succ) && !visited.contains(&succ) {
                        stack.push((succ, false));
                    }
                }
            }
        }
    }

    let mut reverse: BTreeMap<u64, Vec<u64>> = successors
        .keys()
        .copied()
        .map(|addr| (addr, Vec::new()))
        .collect();
    for (src, succs) in successors {
        for succ in succs {
            if reverse.contains_key(succ) {
                reverse.entry(*succ).or_default().push(*src);
            }
        }
    }
    for preds in reverse.values_mut() {
        preds.sort_unstable();
        preds.dedup();
    }

    let mut components = HashMap::new();
    let mut next_component = 0usize;
    while let Some(start) = order.pop() {
        if components.contains_key(&start) {
            continue;
        }
        let mut stack = vec![start];
        while let Some(node) = stack.pop() {
            if components.insert(node, next_component).is_some() {
                continue;
            }
            if let Some(preds) = reverse.get(&node) {
                for pred in preds.iter().rev().copied() {
                    if !components.contains_key(&pred) {
                        stack.push(pred);
                    }
                }
            }
        }
        next_component += 1;
    }

    components
}

fn collect_definitions(
    scratch: &mut UseScratch,
    block: &SSABlock,
    env: &PassEnv<'_>,
    definition_overrides: &HashMap<String, CExpr>,
) {
    let mut block_stack_values: HashMap<i64, SSAVar> = HashMap::new();
    let mut block_stack_semantic_values: HashMap<i64, SemanticValue> = HashMap::new();
    let mut preserved_positive_stack_values: HashMap<i64, SSAVar> = HashMap::new();
    let mut preserved_positive_stack_semantic_values: HashMap<i64, SemanticValue> = HashMap::new();

    for phi in &block.phis {
        let dst_key = phi.dst.display_name();
        scratch.info.phi_sources.insert(
            dst_key.clone(),
            phi.sources.iter().map(|(_, src)| src.clone()).collect(),
        );
        collect_semantic_values(
            scratch,
            &SSAOp::Phi {
                dst: phi.dst.clone(),
                sources: phi.sources.iter().map(|(_, src)| src.clone()).collect(),
            },
            env,
        );
    }

    for op in &block.ops {
        if let SSAOp::Copy { dst, src } = op {
            scratch
                .info
                .copy_sources
                .insert(dst.display_name(), src.display_name());
        }

        if let SSAOp::Store {
            space: SpaceId::Ram,
            addr,
            val,
        } = op
        {
            let offset = stack_slot_offset_for_addr(&scratch.info, addr, env);
            if let Some(offset) = offset {
                preserved_positive_stack_values.remove(&offset);
                preserved_positive_stack_semantic_values.remove(&offset);
                let addr_key = format!("stack:{}", offset);
                scratch
                    .info
                    .memory_stores
                    .insert(addr_key, val.display_name());
                scratch
                    .info
                    .insert_stack_slot_for_var(addr, StackSlotProvenance::new(offset));
                block_stack_values.insert(offset, val.clone());
                if let Some(value) = semantic_stack_store_value(&scratch.info, val, env) {
                    block_stack_semantic_values.insert(offset, value);
                } else {
                    block_stack_semantic_values.remove(&offset);
                }
            } else {
                block_stack_values.clear();
                preserved_positive_stack_values.clear();
                block_stack_semantic_values.clear();
                preserved_positive_stack_semantic_values.clear();
            }
        }

        if let SSAOp::Load {
            dst,
            space: SpaceId::Ram,
            addr,
        } = op
            && let Some(offset) = stack_slot_offset_for_addr(&scratch.info, addr, env)
        {
            let addr_shape = semantic_addr_for_var(&scratch.info, addr, env);
            let forwarded_semantic =
                block_stack_semantic_values
                    .get(&offset)
                    .cloned()
                    .or_else(|| {
                        preserved_positive_stack_semantic_values
                            .get(&offset)
                            .cloned()
                    });
            let should_tag_loaded_value_as_stack_slot = should_tag_loaded_value_as_stack_slot(
                &scratch.info,
                &addr_shape,
                forwarded_semantic.as_ref(),
                addr,
                dst,
                env,
            );
            scratch
                .info
                .insert_stack_slot_for_var(addr, StackSlotProvenance::new(offset));
            if should_tag_loaded_value_as_stack_slot {
                scratch
                    .info
                    .insert_stack_slot_for_var(dst, StackSlotProvenance::new(offset));
            }

            if should_tag_loaded_value_as_stack_slot {
                if let Some(stored_val) = block_stack_values
                    .get(&offset)
                    .cloned()
                    .or_else(|| preserved_positive_stack_values.get(&offset).cloned())
                {
                    scratch
                        .info
                        .copy_sources
                        .insert(dst.display_name(), stored_val.display_name());
                    scratch.info.insert_forwarded_value_for_var(
                        dst,
                        ValueProvenance {
                            source: stored_val.display_name(),
                            source_value_id: scratch.info.value_id_for_var(&stored_val),
                            source_var: Some(stored_val),
                            stack_slot: Some(offset),
                        },
                    );
                }
                if let Some(value) = forwarded_semantic {
                    insert_semantic_value(&mut scratch.info, dst.display_name(), value);
                }
            }
        }

        if let SSAOp::PtrAdd {
            dst,
            base,
            index,
            element_size,
        } = op
        {
            scratch.info.insert_ptr_arith_for_var(
                dst,
                PtrArith {
                    base: base.clone(),
                    index: index.clone(),
                    element_size: *element_size,
                    is_sub: false,
                },
            );
        }

        if let SSAOp::PtrSub {
            dst,
            base,
            index,
            element_size,
        } = op
        {
            scratch.info.insert_ptr_arith_for_var(
                dst,
                PtrArith {
                    base: base.clone(),
                    index: index.clone(),
                    element_size: *element_size,
                    is_sub: true,
                },
            );
        }

        match op {
            SSAOp::IntAdd { dst, a, b } => {
                if let Some(offset) = utils::parse_const_offset(a) {
                    scratch
                        .info
                        .ptr_members
                        .insert(dst.display_name(), (b.clone(), offset));
                } else if let Some(offset) = utils::parse_const_offset(b) {
                    scratch
                        .info
                        .ptr_members
                        .insert(dst.display_name(), (a.clone(), offset));
                }
            }
            SSAOp::IntSub { dst, a, b } => {
                if let Some(offset) = utils::parse_const_offset(b) {
                    scratch
                        .info
                        .ptr_members
                        .insert(dst.display_name(), (a.clone(), -offset));
                }
            }
            _ => {}
        }

        if let Some(dst) = op.dst() {
            let key = dst.display_name();
            if let Some(expr) = definition_overrides.get(&key).cloned() {
                scratch.info.insert_definition_for_var(dst, expr);
            } else {
                let expr = {
                    let lower = LowerCtx {
                        use_info: None,
                        definitions: &scratch.info.definitions,
                        semantic_values: &scratch.info.semantic_values,
                        use_counts: &scratch.info.use_counts,
                        condition_vars: &scratch.info.condition_vars,
                        pinned: &scratch.info.pinned,
                        var_aliases: &scratch.info.var_aliases,
                        param_register_aliases: env.param_register_aliases,
                        type_hints: &scratch.info.type_hints,
                        ptr_arith: &scratch.info.ptr_arith,
                        stack_slots: &scratch.info.stack_slots,
                        forwarded_values: &scratch.info.forwarded_values,
                        type_oracle: env.type_oracle,
                    };
                    if let Some(prov) = scratch.info.forwarded_values.get(&key) {
                        lower.expr_for_ssa_name(&prov.source)
                    } else {
                        lower.op_to_expr(op)
                    }
                };
                scratch.info.insert_definition_for_var(dst, expr);
            }
        }

        collect_semantic_values(scratch, op, env);
        if let Some(dst) = op.dst() {
            scratch.producers.insert(dst.display_name(), op.clone());
        }

        if invalidates_block_stack_values(op, &scratch.info.definitions, env) {
            if is_call_like_stack_boundary_op(op) {
                preserved_positive_stack_values = block_stack_values
                    .iter()
                    .filter(|(offset, _)| **offset >= 0)
                    .map(|(offset, value)| (*offset, value.clone()))
                    .collect();
            } else {
                preserved_positive_stack_values.clear();
            }
            block_stack_values.clear();
        }
        if invalidates_semantic_stack_values(op) {
            if is_call_like_stack_boundary_op(op) {
                preserved_positive_stack_semantic_values = block_stack_semantic_values
                    .iter()
                    .filter(|(offset, _)| **offset >= 0)
                    .map(|(offset, value)| (*offset, value.clone()))
                    .collect();
            } else {
                preserved_positive_stack_semantic_values.clear();
            }
            block_stack_semantic_values.clear();
        }
    }
}

fn rebuild_definitions(
    scratch: &mut UseScratch,
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    definition_overrides: &HashMap<String, CExpr>,
) {
    let mut rebuilt = HashMap::new();

    for block in blocks {
        for op in &block.ops {
            let Some(dst) = op.dst() else {
                continue;
            };
            let key = dst.display_name();
            let expr = if let Some(expr) = definition_overrides.get(&key).cloned() {
                expr
            } else {
                let lower = LowerCtx {
                    use_info: None,
                    definitions: &rebuilt,
                    semantic_values: &scratch.info.semantic_values,
                    use_counts: &scratch.info.use_counts,
                    condition_vars: &scratch.info.condition_vars,
                    pinned: &scratch.info.pinned,
                    var_aliases: &scratch.info.var_aliases,
                    param_register_aliases: env.param_register_aliases,
                    type_hints: &scratch.info.type_hints,
                    ptr_arith: &scratch.info.ptr_arith,
                    stack_slots: &scratch.info.stack_slots,
                    forwarded_values: &scratch.info.forwarded_values,
                    type_oracle: env.type_oracle,
                };
                if let Some(prov) = scratch.info.forwarded_values.get(&key) {
                    lower.expr_for_ssa_name(&prov.source)
                } else {
                    lower.op_to_expr(op)
                }
            };
            rebuilt.insert(key, expr);
        }
    }

    scratch.info.definitions = rebuilt;
}

fn semantic_stack_store_value(
    info: &UseInfo,
    var: &SSAVar,
    env: &PassEnv<'_>,
) -> Option<SemanticValue> {
    if !semantic_var_is_pointer_like(info, var, env)
        && let Some(value) = scalar_semantic_source_value_for_var(info, var)
    {
        return Some(value);
    }
    if let Some(addr) = semantic_addr_for_var(info, var, env)
        && semantic_addr_has_meaningful_base(&addr)
    {
        return Some(SemanticValue::Address(addr));
    }
    if semantic_var_is_pointer_like(info, var, env) {
        let addr = normalized_addr_from_base_var(var);
        if semantic_addr_has_meaningful_base(&addr) {
            return Some(SemanticValue::Address(addr));
        }
    }
    semantic_source_value_for_var(info, var)
}

fn should_tag_loaded_value_as_stack_slot(
    info: &UseInfo,
    addr_shape: &Option<NormalizedAddr>,
    forwarded_semantic: Option<&SemanticValue>,
    addr: &SSAVar,
    _dst: &SSAVar,
    env: &PassEnv<'_>,
) -> bool {
    if let Some(shape) = addr_shape
        && frame_object_field_key(info, shape, env, 0).is_some()
    {
        return false;
    }

    let addr_name = addr.display_name();
    let addr_copy_root = resolve_copy_root_name(info, &addr_name);
    if stack_reloaded_value_slot_for_name(info, &addr_name).is_some()
        || (addr_copy_root != addr_name
            && stack_reloaded_value_slot_for_name(info, &addr_copy_root).is_some())
    {
        return false;
    }

    !matches!(
        forwarded_semantic,
        Some(SemanticValue::Address(_)) | Some(SemanticValue::Load { .. })
    )
}

fn merged_slot_store_value_for_pred(
    info: &UseInfo,
    block: &SSABlock,
    slot_offset: i64,
    env: &PassEnv<'_>,
    prepared: Option<&SsaArtifact>,
) -> Option<SemanticValue> {
    for (idx, op) in block.ops.iter().enumerate().rev() {
        if let SSAOp::Store {
            space: SpaceId::Ram,
            addr,
            val,
        } = op
            && prepared
                .and_then(|prepared| prepared_stack_offset_for_var(prepared, addr))
                .or_else(|| {
                    utils::extract_stack_offset_from_var(
                        addr,
                        &info.definitions,
                        env.fp_name,
                        env.sp_name,
                    )
                })
                == Some(slot_offset)
        {
            let base = semantic_stack_store_value(info, val, env);
            let family = (slot_offset >= 0)
                .then(|| {
                    same_register_family_semantic_value_before(info, &block.ops, idx, val, env)
                })
                .flatten();
            return match (base, family) {
                (Some(base), Some(family))
                    if should_prefer_same_family_store_value(&base, &family) =>
                {
                    Some(family)
                }
                (Some(base), _) => Some(base),
                (None, other) => other,
            };
        }
    }
    None
}

fn same_register_family_semantic_value_before(
    info: &UseInfo,
    ops: &[SSAOp],
    store_idx: usize,
    var: &SSAVar,
    env: &PassEnv<'_>,
) -> Option<SemanticValue> {
    let family = register_family_name_for_var(info, var)?;
    let mut best = None;

    for op in ops[..store_idx].iter().rev() {
        let Some(dst) = op.dst() else {
            continue;
        };
        let Some(dst_family) = register_family_name_for_var(info, dst) else {
            continue;
        };
        if dst_family != family {
            continue;
        }
        let Some(candidate) = semantic_stack_store_value(info, dst, env) else {
            continue;
        };
        best = match best {
            Some(current) if should_replace_same_family_candidate(&current, &candidate) => {
                Some(candidate)
            }
            Some(current) => Some(current),
            None => Some(candidate),
        };
        if matches!(best, Some(SemanticValue::Scalar(ScalarValue::Expr(_)))) {
            break;
        }
    }

    best
}

fn register_family_name_for_var(info: &UseInfo, var: &SSAVar) -> Option<String> {
    register_family_name(&var.name).or_else(|| {
        let root = resolve_copy_root_name(info, &var.display_name());
        (root != var.display_name())
            .then_some(root)
            .and_then(|root| register_family_name(&root))
    })
}

fn preserve_temp_copy_root_identity(
    dst: &SSAVar,
    src: &SSAVar,
    value: SemanticValue,
) -> SemanticValue {
    match value {
        SemanticValue::Scalar(ScalarValue::Root(root))
            if root.var == *src
                && utils::is_temporary_name(&dst.name)
                && src.version == 0
                && register_family_name(&src.name).is_some() =>
        {
            SemanticValue::Scalar(ScalarValue::Root(ValueRef::from(dst)))
        }
        other => other,
    }
}

fn collect_semantic_values(scratch: &mut UseScratch, op: &SSAOp, env: &PassEnv<'_>) {
    let mut cache = SemanticTypeHintCache::default();
    collect_semantic_values_with_cache(scratch, op, env, &mut cache);
}

fn collect_semantic_values_with_cache(
    scratch: &mut UseScratch,
    op: &SSAOp,
    env: &PassEnv<'_>,
    cache: &mut SemanticTypeHintCache,
) {
    match op {
        SSAOp::Copy { dst, src } => {
            let src_is_pointer_like =
                semantic_var_is_pointer_like_cached(&scratch.info, src, env, cache);
            if !src_is_pointer_like
                && let Some(value) = scalar_semantic_source_value_for_var(&scratch.info, src)
            {
                insert_semantic_value(
                    &mut scratch.info,
                    dst.display_name(),
                    preserve_temp_copy_root_identity(dst, src, value),
                );
                return;
            }
            if src_is_pointer_like
                && let Some(addr) = semantic_addr_for_var(&scratch.info, src, env)
                && is_authoritative_addr(&addr)
            {
                insert_semantic_value(
                    &mut scratch.info,
                    dst.display_name(),
                    SemanticValue::Address(addr),
                );
                return;
            }
            if let Some(value) = semantic_source_value_for_var(&scratch.info, src) {
                insert_semantic_value(
                    &mut scratch.info,
                    dst.display_name(),
                    preserve_temp_copy_root_identity(dst, src, value),
                );
            }
        }
        SSAOp::IntZExt { dst, src }
        | SSAOp::IntSExt { dst, src }
        | SSAOp::Trunc { dst, src }
        | SSAOp::Cast { dst, src }
        | SSAOp::Subpiece { dst, src, .. } => {
            let src_is_pointer_like =
                semantic_var_is_pointer_like_cached(&scratch.info, src, env, cache);
            if !src_is_pointer_like
                && let Some(value) = scalar_semantic_source_value_for_var(&scratch.info, src)
            {
                insert_semantic_value(&mut scratch.info, dst.display_name(), value);
                return;
            }
            if src_is_pointer_like
                && let Some(addr) = semantic_addr_for_var(&scratch.info, src, env)
                && is_authoritative_addr(&addr)
            {
                insert_semantic_value(
                    &mut scratch.info,
                    dst.display_name(),
                    SemanticValue::Address(addr),
                );
                return;
            }
            if let Some(value) = semantic_source_value_for_var(&scratch.info, src) {
                insert_semantic_value(&mut scratch.info, dst.display_name(), value);
            }
        }
        SSAOp::Phi { dst, sources } => {
            let mut selected: Option<SemanticValue> = None;
            for src in sources {
                let Some(value) = semantic_source_value_for_var(&scratch.info, src) else {
                    selected = None;
                    break;
                };
                selected = match selected {
                    None => Some(value),
                    Some(prev) if prev == value => Some(prev),
                    Some(_) => None,
                };
                if selected.is_none() {
                    break;
                }
            }
            if let Some(value) = selected {
                insert_semantic_value(&mut scratch.info, dst.display_name(), value);
            }
        }
        SSAOp::PtrAdd {
            dst,
            base,
            index,
            element_size,
        } => {
            let mut addr = semantic_addr_for_var(&scratch.info, base, env)
                .unwrap_or_else(|| normalized_addr_from_base_var(base));
            if addr.index.is_none()
                || addr
                    .index
                    .as_ref()
                    .is_some_and(|existing| existing == &ValueRef::from(index))
            {
                addr.index = Some(ValueRef::from(index));
                addr.scale_bytes = i64::from(*element_size);
            }
            insert_semantic_value(
                &mut scratch.info,
                dst.display_name(),
                SemanticValue::Address(addr),
            );
        }
        SSAOp::PtrSub {
            dst,
            base,
            index,
            element_size,
        } => {
            let mut addr = semantic_addr_for_var(&scratch.info, base, env)
                .unwrap_or_else(|| normalized_addr_from_base_var(base));
            if addr.index.is_none()
                || addr
                    .index
                    .as_ref()
                    .is_some_and(|existing| existing == &ValueRef::from(index))
            {
                addr.index = Some(ValueRef::from(index));
                addr.scale_bytes = -i64::from(*element_size);
            }
            insert_semantic_value(
                &mut scratch.info,
                dst.display_name(),
                SemanticValue::Address(addr),
            );
        }
        SSAOp::Load { dst, space, addr } => {
            let should_preserve_rooted_indirect_load_shape = |value: &SemanticValue| {
                matches!(
                    value,
                    SemanticValue::Scalar(ScalarValue::Root(root)) if root.var.size > dst.size
                )
            };
            if *space == SpaceId::Ram
                && let Some(shape) = semantic_addr_for_var(&scratch.info, addr, env)
                && let Some(key) = frame_object_field_key(&scratch.info, &shape, env, 0)
                && let Some(value) = scratch.info.frame_object_field_roots.get(&key).cloned()
            {
                replace_semantic_value(&mut scratch.info, dst.display_name(), value);
                insert_semantic_value(
                    &mut scratch.info,
                    addr.display_name(),
                    SemanticValue::Address(shape),
                );
                return;
            }
            if *space == SpaceId::Ram
                && let Some(offset) = scratch
                    .info
                    .stack_slots
                    .get(&addr.display_name())
                    .map(|slot| slot.offset)
                    .or_else(|| {
                        scratch
                            .info
                            .stack_slots
                            .get(&dst.display_name())
                            .map(|slot| slot.offset)
                    })
                && let Some(value) = scratch.info.stable_stack_values.get(&offset).cloned()
                && !should_preserve_rooted_indirect_load_shape(&value)
            {
                replace_semantic_value(&mut scratch.info, dst.display_name(), value);
                return;
            }
            if *space == SpaceId::Ram
                && let Some(shape) = semantic_addr_for_var(&scratch.info, addr, env)
                && let Some(offset) = normalized_stack_slot_offset(&shape)
                && let Some(value) = scratch.info.stable_stack_values.get(&offset).cloned()
                && !should_preserve_rooted_indirect_load_shape(&value)
            {
                replace_semantic_value(&mut scratch.info, dst.display_name(), value);
                insert_semantic_value(
                    &mut scratch.info,
                    addr.display_name(),
                    SemanticValue::Address(shape),
                );
                return;
            }
            if let Some(shape) = semantic_addr_for_var(&scratch.info, addr, env)
                && let Some(key) = normalized_memory_key(&scratch.info, *space, &shape, env)
                && let Some(value) = scratch
                    .info
                    .stable_memory_values
                    .get(&stable_memory_map_key(&key))
                    .cloned()
            {
                if should_preserve_rooted_structured_load_identity_for_stable_memory(
                    &scratch.info,
                    &shape,
                    env,
                    &value,
                ) {
                    insert_semantic_value(
                        &mut scratch.info,
                        dst.display_name(),
                        SemanticValue::Load {
                            space: *space,
                            addr: shape.clone(),
                            size: dst.size,
                        },
                    );
                } else {
                    replace_semantic_value(&mut scratch.info, dst.display_name(), value);
                }
                insert_semantic_value(
                    &mut scratch.info,
                    addr.display_name(),
                    SemanticValue::Address(shape),
                );
                return;
            }
            if let Some(prov) = scratch.info.forwarded_values.get(&dst.display_name())
                && let Some(value) = semantic_source_value_from_provenance(&scratch.info, prov, env)
            {
                insert_semantic_value(&mut scratch.info, dst.display_name(), value);
                return;
            }
            if let Some(shape) = semantic_addr_for_var(&scratch.info, addr, env) {
                let addr_key = addr.display_name();
                insert_semantic_value(
                    &mut scratch.info,
                    addr_key,
                    SemanticValue::Address(shape.clone()),
                );
                insert_semantic_value(
                    &mut scratch.info,
                    dst.display_name(),
                    SemanticValue::Load {
                        space: *space,
                        addr: shape,
                        size: dst.size,
                    },
                );
            }
        }
        SSAOp::IntAdd { dst, a, b } => {
            if let Some(addr) =
                semantic_addr_from_add_sub(&scratch.info, &scratch.producers, a, b, false, env)
            {
                insert_semantic_value(
                    &mut scratch.info,
                    dst.display_name(),
                    SemanticValue::Address(addr),
                );
            } else if let Some(addr) = semantic_addr_for_var(&scratch.info, dst, env)
                && is_authoritative_addr(&addr)
            {
                insert_semantic_value(
                    &mut scratch.info,
                    dst.display_name(),
                    SemanticValue::Address(addr),
                );
            }
        }
        SSAOp::IntSub { dst, a, b } => {
            if let Some(addr) =
                semantic_addr_from_add_sub(&scratch.info, &scratch.producers, a, b, true, env)
            {
                insert_semantic_value(
                    &mut scratch.info,
                    dst.display_name(),
                    SemanticValue::Address(addr),
                );
            } else if let Some(addr) = semantic_addr_for_var(&scratch.info, dst, env)
                && is_authoritative_addr(&addr)
            {
                insert_semantic_value(
                    &mut scratch.info,
                    dst.display_name(),
                    SemanticValue::Address(addr),
                );
            }
        }
        SSAOp::Store { addr, .. } => {
            if let Some(shape) = semantic_addr_for_var(&scratch.info, addr, env) {
                insert_semantic_value(
                    &mut scratch.info,
                    addr.display_name(),
                    SemanticValue::Address(shape),
                );
            }
        }
        _ => {}
    }
}

fn semantic_addr_from_add_sub(
    info: &UseInfo,
    producers: &HashMap<String, SSAOp>,
    a: &SSAVar,
    b: &SSAVar,
    is_sub: bool,
    env: &PassEnv<'_>,
) -> Option<NormalizedAddr> {
    if let Some(offset) = stack_slot_offset_from_add_sub(a, b, is_sub, env) {
        return Some(NormalizedAddr {
            base: BaseRef::StackSlot(offset),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        });
    }

    if let Some(offset) = utils::parse_const_offset(b)
        && let Some(base) = semantic_addr_for_var(info, a, env)
    {
        return add_addr_offset(base, if is_sub { -offset } else { offset });
    }
    if !is_sub
        && let Some(offset) = utils::parse_const_offset(a)
        && let Some(base) = semantic_addr_for_var(info, b, env)
    {
        return add_addr_offset(base, offset);
    }

    if let Some((index, scale)) = recover_scaled_index_from_var(info, producers, b, env, 0) {
        let signed_scale = if is_sub { scale.checked_neg()? } else { scale };
        let base = indexed_addr_base_for_var(info, a, env)?;
        return compose_indexed_addr(base, index, signed_scale);
    }

    if !is_sub
        && let Some((index, scale)) = recover_scaled_index_from_var(info, producers, a, env, 0)
    {
        let base = indexed_addr_base_for_var(info, b, env)?;
        return compose_indexed_addr(base, index, scale);
    }

    None
}

fn stack_slot_offset_for_addr(info: &UseInfo, addr: &SSAVar, env: &PassEnv<'_>) -> Option<i64> {
    if let Some(shape) = semantic_addr_for_var(info, addr, env) {
        if let Some(offset) = normalized_stack_slot_offset(&shape) {
            return Some(offset);
        }
        if semantic_addr_has_meaningful_base(&shape) {
            return None;
        }
    }

    let key = addr.display_name();
    let copy_root = resolve_copy_root_name(info, &key);
    if typed_pointer_stack_slot_for_name(info, &key, env).is_some()
        || (copy_root != key && typed_pointer_stack_slot_for_name(info, &copy_root, env).is_some())
        || stack_reloaded_value_slot_for_name(info, &key).is_some()
        || (copy_root != key && stack_reloaded_value_slot_for_name(info, &copy_root).is_some())
    {
        return None;
    }

    utils::extract_stack_offset_from_var(addr, &info.definitions, env.fp_name, env.sp_name)
}

fn stack_slot_offset_from_add_sub(
    a: &SSAVar,
    b: &SSAVar,
    is_sub: bool,
    env: &PassEnv<'_>,
) -> Option<i64> {
    let a_name = a.name.to_ascii_lowercase();
    let b_name = b.name.to_ascii_lowercase();
    if (a_name == env.fp_name || a_name == env.sp_name)
        && let Some(offset) = utils::parse_const_offset(b)
    {
        return Some(if is_sub { -offset } else { offset });
    }
    if !is_sub
        && (b_name == env.fp_name || b_name == env.sp_name)
        && let Some(offset) = utils::parse_const_offset(a)
    {
        return Some(offset);
    }
    None
}

fn recover_scaled_index_from_var(
    info: &UseInfo,
    producers: &HashMap<String, SSAOp>,
    var: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<(SSAVar, i64)> {
    if depth > 8
        || var.is_const()
        || semantic_var_is_pointer_like(info, var, env)
        || semantic_var_resolves_to_ptr_sized_entry_arg_root(info, var, env, depth)
    {
        return None;
    }

    let key = var.display_name();
    let op = producers.get(&key);
    match op {
        Some(SSAOp::Copy { src, .. })
        | Some(SSAOp::IntZExt { src, .. })
        | Some(SSAOp::IntSExt { src, .. })
        | Some(SSAOp::Trunc { src, .. })
        | Some(SSAOp::Cast { src, .. })
        | Some(SSAOp::Subpiece { src, .. }) => {
            recover_scaled_index_from_var(info, producers, src, env, depth + 1)
        }
        Some(SSAOp::IntMult { a, b, .. }) => {
            if let Some(scale) = recover_const_offset_from_var(info, producers, a, depth + 1) {
                let (inner, inner_scale) =
                    recover_scaled_index_from_var(info, producers, b, env, depth + 1)?;
                return inner_scale.checked_mul(scale).map(|s| (inner, s));
            }
            if let Some(scale) = recover_const_offset_from_var(info, producers, b, depth + 1) {
                let (inner, inner_scale) =
                    recover_scaled_index_from_var(info, producers, a, env, depth + 1)?;
                return inner_scale.checked_mul(scale).map(|s| (inner, s));
            }
            None
        }
        Some(SSAOp::IntLeft { a, b, .. }) => {
            let shift = recover_const_offset_from_var(info, producers, b, depth + 1)?;
            if !(0..=62).contains(&shift) {
                return None;
            }
            let scale = 1_i64.checked_shl(shift as u32)?;
            let (inner, inner_scale) =
                recover_scaled_index_from_var(info, producers, a, env, depth + 1)?;
            inner_scale.checked_mul(scale).map(|s| (inner, s))
        }
        Some(SSAOp::IntAdd { a, b, .. }) => {
            let (left, left_scale) =
                recover_scaled_index_from_var(info, producers, a, env, depth + 1)?;
            let (right, right_scale) =
                recover_scaled_index_from_var(info, producers, b, env, depth + 1)?;
            (left == right).then_some(()).and_then(|_| {
                left_scale
                    .checked_add(right_scale)
                    .map(|scale| (left, scale))
            })
        }
        Some(SSAOp::IntSub { a, b, .. }) => {
            if semantic_var_resolves_to_zero(info, producers, a, depth + 1) {
                let (inner, inner_scale) =
                    recover_scaled_index_from_var(info, producers, b, env, depth + 1)?;
                return inner_scale.checked_neg().map(|scale| (inner, scale));
            }
            if semantic_var_resolves_to_zero(info, producers, b, depth + 1) {
                return recover_scaled_index_from_var(info, producers, a, env, depth + 1);
            }
            let (left, left_scale) =
                recover_scaled_index_from_var(info, producers, a, env, depth + 1)?;
            let (right, right_scale) =
                recover_scaled_index_from_var(info, producers, b, env, depth + 1)?;
            (left == right).then_some(()).and_then(|_| {
                left_scale
                    .checked_sub(right_scale)
                    .map(|scale| (left, scale))
            })
        }
        Some(SSAOp::IntNegate { src, .. }) => {
            recover_scaled_index_from_var(info, producers, src, env, depth + 1)
                .and_then(|(inner, scale)| scale.checked_neg().map(|neg| (inner, neg)))
        }
        _ => Some((var.clone(), 1)),
    }
}

fn recover_const_offset_from_var(
    info: &UseInfo,
    producers: &HashMap<String, SSAOp>,
    var: &SSAVar,
    depth: u32,
) -> Option<i64> {
    if depth > 8 {
        return None;
    }

    if let Some(offset) = utils::parse_const_offset(var) {
        return Some(offset);
    }

    let key = var.display_name();
    match producers.get(&key) {
        Some(SSAOp::Copy { src, .. })
        | Some(SSAOp::IntZExt { src, .. })
        | Some(SSAOp::IntSExt { src, .. })
        | Some(SSAOp::Trunc { src, .. })
        | Some(SSAOp::Cast { src, .. })
        | Some(SSAOp::Subpiece { src, .. }) => {
            recover_const_offset_from_var(info, producers, src, depth + 1)
        }
        Some(SSAOp::IntAnd { a, b, .. }) => {
            let left = recover_const_offset_from_var(info, producers, a, depth + 1)?;
            let right = recover_const_offset_from_var(info, producers, b, depth + 1)?;
            Some(left & right)
        }
        Some(SSAOp::IntOr { a, b, .. }) => {
            let left = recover_const_offset_from_var(info, producers, a, depth + 1)?;
            let right = recover_const_offset_from_var(info, producers, b, depth + 1)?;
            Some(left | right)
        }
        Some(SSAOp::IntXor { a, b, .. }) => {
            let left = recover_const_offset_from_var(info, producers, a, depth + 1)?;
            let right = recover_const_offset_from_var(info, producers, b, depth + 1)?;
            Some(left ^ right)
        }
        _ => match semantic_source_value_for_var(info, var) {
            Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(value)))) => Some(value),
            Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::UIntLit(value)))) => {
                i64::try_from(value).ok()
            }
            _ => None,
        },
    }
}

fn var_is_ptr_sized_entry_arg_root(var: &SSAVar, env: &PassEnv<'_>) -> bool {
    let ptr_bytes = env.ptr_size.div_ceil(8).max(1);
    var.version == 0
        && var.size == ptr_bytes
        && env
            .arg_regs
            .iter()
            .any(|reg_name| reg_name.eq_ignore_ascii_case(&var.name))
}

fn entry_arg_root_type_hint_allows_pointer_base(
    info: &UseInfo,
    var: &SSAVar,
    env: &PassEnv<'_>,
) -> bool {
    let mut saw_type_hint = false;
    for name in semantic_type_hint_names(info, var, env) {
        let hint = info
            .type_hints
            .get(&name)
            .or_else(|| info.type_hints.get(&name.to_ascii_lowercase()))
            .or_else(|| env.type_hints.get(&name))
            .or_else(|| env.type_hints.get(&name.to_ascii_lowercase()));
        let Some(hint) = hint else {
            continue;
        };
        saw_type_hint = true;
        if matches!(
            hint,
            crate::ast::CType::Pointer(_)
                | crate::ast::CType::Struct(_)
                | crate::ast::CType::Array(_, _)
        ) {
            return true;
        }
    }

    !saw_type_hint
}

fn resolve_ptr_sized_entry_arg_root_var(
    info: &UseInfo,
    var: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<SSAVar> {
    if depth > 8 {
        return None;
    }

    if var_is_ptr_sized_entry_arg_root(var, env)
        && entry_arg_root_type_hint_allows_pointer_base(info, var, env)
    {
        return Some(var.clone());
    }

    let key = var.display_name();
    if let Some(SemanticValue::Scalar(ScalarValue::Root(root))) = info.semantic_values.get(&key)
        && root.var != *var
        && let Some(entry_root) =
            resolve_ptr_sized_entry_arg_root_var(info, &root.var, env, depth + 1)
    {
        return Some(entry_root);
    }

    if let Some(prov) = info.forwarded_values.get(&key)
        && let Some(source_var) = &prov.source_var
        && source_var != var
        && let Some(entry_root) =
            resolve_ptr_sized_entry_arg_root_var(info, source_var, env, depth + 1)
    {
        return Some(entry_root);
    }

    let copy_root = resolve_copy_root_name(info, &key);
    if copy_root != key
        && let Some(root_var) = ssa_var_from_display_name(&copy_root, var.size)
        && root_var != *var
    {
        return resolve_ptr_sized_entry_arg_root_var(info, &root_var, env, depth + 1);
    }

    None
}

fn semantic_var_resolves_to_ptr_sized_entry_arg_root(
    info: &UseInfo,
    var: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> bool {
    resolve_ptr_sized_entry_arg_root_var(info, var, env, depth).is_some()
}

fn semantic_var_resolves_to_zero(
    info: &UseInfo,
    producers: &HashMap<String, SSAOp>,
    var: &SSAVar,
    depth: u32,
) -> bool {
    if depth > 8 {
        return false;
    }

    if utils::parse_const_value(&var.name) == Some(0) {
        return true;
    }

    match semantic_source_value_for_var(info, var) {
        Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(0) | CExpr::UIntLit(0)))) => {
            return true;
        }
        Some(SemanticValue::Scalar(ScalarValue::Root(root))) if root.var != *var => {
            return semantic_var_resolves_to_zero(info, producers, &root.var, depth + 1);
        }
        _ => {}
    }

    let key = var.display_name();
    match producers.get(&key) {
        Some(SSAOp::Copy { src, .. })
        | Some(SSAOp::IntZExt { src, .. })
        | Some(SSAOp::IntSExt { src, .. })
        | Some(SSAOp::Trunc { src, .. })
        | Some(SSAOp::Cast { src, .. })
        | Some(SSAOp::Subpiece { src, .. }) => {
            semantic_var_resolves_to_zero(info, producers, src, depth + 1)
        }
        Some(SSAOp::IntXor { a, b, .. }) if a == b => true,
        _ => false,
    }
}

fn semantic_var_is_pointer_like(info: &UseInfo, var: &SSAVar, env: &PassEnv<'_>) -> bool {
    let key = var.display_name();
    let lower_name = var.name.to_ascii_lowercase();
    if lower_name == env.fp_name || lower_name == env.sp_name {
        return true;
    }
    if info
        .stack_slots
        .get(&key)
        .is_some_and(|slot| slot.value_kind == StackSlotValueKind::AddressLike)
    {
        return true;
    }
    if let Some(value) = info.semantic_values.get(&key) {
        match value {
            SemanticValue::Address(_) => return true,
            SemanticValue::Scalar(ScalarValue::Root(root)) if root.var != *var => {
                return semantic_var_is_pointer_like(info, &root.var, env);
            }
            _ => {}
        }
    }
    if let Some(prov) = info.forwarded_values.get(&key)
        && let Some(source_var) = &prov.source_var
        && source_var != var
        && semantic_var_is_pointer_like(info, source_var, env)
    {
        return true;
    }
    if info.ptr_arith.contains_key(&key) || info.ptr_members.contains_key(&key) {
        return true;
    }
    let copy_root = resolve_copy_root_name(info, &key);
    if copy_root != key
        && let Some(root_var) = ssa_var_from_display_name(&copy_root, var.size)
        && root_var != *var
        && semantic_var_is_pointer_like(info, &root_var, env)
    {
        return true;
    }
    if let Some(oracle) = env.type_oracle {
        let ty = oracle.type_of(var);
        if oracle.is_pointer(ty) || oracle.is_array(ty) {
            return true;
        }
    }
    semantic_type_hint_names(info, var, env)
        .into_iter()
        .find_map(|name| lookup_type_hint(info, env, &name))
        .map(|ty| {
            matches!(
                ty,
                CType::Pointer(_) | CType::Struct(_) | CType::Array(_, _)
            )
        })
        .unwrap_or(false)
}

fn semantic_var_is_pointer_like_cached(
    info: &UseInfo,
    var: &SSAVar,
    env: &PassEnv<'_>,
    cache: &mut SemanticTypeHintCache,
) -> bool {
    let key = var.display_name();
    let lower_name = var.name.to_ascii_lowercase();
    if lower_name == env.fp_name || lower_name == env.sp_name {
        return true;
    }
    if info
        .stack_slots
        .get(&key)
        .is_some_and(|slot| slot.value_kind == StackSlotValueKind::AddressLike)
    {
        return true;
    }
    if let Some(value) = info.semantic_values.get(&key) {
        match value {
            SemanticValue::Address(_) => return true,
            SemanticValue::Scalar(ScalarValue::Root(root)) if root.var != *var => {
                return semantic_var_is_pointer_like_cached(info, &root.var, env, cache);
            }
            _ => {}
        }
    }
    if let Some(prov) = info.forwarded_values.get(&key)
        && let Some(source_var) = &prov.source_var
        && source_var != var
        && semantic_var_is_pointer_like_cached(info, source_var, env, cache)
    {
        return true;
    }
    if info.ptr_arith.contains_key(&key) || info.ptr_members.contains_key(&key) {
        return true;
    }
    let copy_root = resolve_copy_root_name(info, &key);
    if copy_root != key
        && let Some(root_var) = ssa_var_from_display_name(&copy_root, var.size)
        && root_var != *var
        && semantic_var_is_pointer_like_cached(info, &root_var, env, cache)
    {
        return true;
    }
    if let Some(oracle) = env.type_oracle {
        let ty = oracle.type_of(var);
        if oracle.is_pointer(ty) || oracle.is_array(ty) {
            return true;
        }
    }
    semantic_type_hint_names_cached(info, var, env, cache)
        .into_iter()
        .find_map(|name| lookup_type_hint(info, env, &name))
        .map(|ty| {
            matches!(
                ty,
                CType::Pointer(_) | CType::Struct(_) | CType::Array(_, _)
            )
        })
        .unwrap_or(false)
}

fn stack_slot_offset_has_pointer_type_hint(info: &UseInfo, offset: i64, env: &PassEnv<'_>) -> bool {
    info.stack_slots.iter().any(|(name, slot)| {
        slot.offset == offset
            && lookup_type_hint(info, env, name).is_some_and(|ty| {
                matches!(
                    ty,
                    CType::Pointer(_) | CType::Struct(_) | CType::Array(_, _)
                )
            })
    })
}

fn typed_pointer_stack_slot_for_name(info: &UseInfo, name: &str, env: &PassEnv<'_>) -> Option<i64> {
    info.forwarded_values
        .get(name)
        .and_then(|prov| prov.stack_slot)
        .or_else(|| info.stack_slots.get(name).map(|slot| slot.offset))
        .filter(|offset| stack_slot_offset_has_pointer_type_hint(info, *offset, env))
}

fn stack_reloaded_value_slot_for_name(info: &UseInfo, name: &str) -> Option<i64> {
    info.forwarded_values
        .get(name)
        .and_then(|prov| prov.stack_slot)
}

fn semantic_type_hint_names(info: &UseInfo, var: &SSAVar, env: &PassEnv<'_>) -> Vec<String> {
    let mut names = Vec::new();
    let push_stack_slot_names = |names: &mut Vec<String>, offset: i64| {
        for (slot_name, slot) in &info.stack_slots {
            if slot.offset == offset {
                push_unique_casefold(names, slot_name.clone());
                push_unique_casefold(names, slot_name.to_ascii_lowercase());
            }
        }
    };

    let key = var.display_name();
    push_unique_casefold(&mut names, key.clone());
    push_unique_casefold(&mut names, key.to_ascii_lowercase());

    if let Some(offset) = info
        .forwarded_values
        .get(&key)
        .and_then(|prov| prov.stack_slot)
        .or_else(|| info.stack_slots.get(&key).map(|slot| slot.offset))
    {
        push_stack_slot_names(&mut names, offset);
    }

    if let Some(alias) = info.var_aliases.get(&key) {
        push_unique_casefold(&mut names, alias.clone());
        push_unique_casefold(&mut names, alias.to_ascii_lowercase());
    }

    if let Some(alias) = env
        .param_register_aliases
        .get(&var.name.to_ascii_lowercase())
    {
        push_unique_casefold(&mut names, alias.clone());
        push_unique_casefold(&mut names, alias.to_ascii_lowercase());
    }

    let root = resolve_copy_root_name(info, &key);
    if root != key {
        push_unique_casefold(&mut names, root.clone());
        push_unique_casefold(&mut names, root.to_ascii_lowercase());
        if let Some(offset) = info
            .forwarded_values
            .get(&root)
            .and_then(|prov| prov.stack_slot)
            .or_else(|| info.stack_slots.get(&root).map(|slot| slot.offset))
        {
            push_stack_slot_names(&mut names, offset);
        }
        if let Some(alias) = info.var_aliases.get(&root) {
            push_unique_casefold(&mut names, alias.clone());
            push_unique_casefold(&mut names, alias.to_ascii_lowercase());
        }
    }

    names
}

fn semantic_type_hint_names_cached(
    info: &UseInfo,
    var: &SSAVar,
    env: &PassEnv<'_>,
    cache: &mut SemanticTypeHintCache,
) -> Vec<String> {
    let ensure_stack_slot_names = |cache: &mut SemanticTypeHintCache, offset: i64| {
        cache
            .stack_slot_names_by_offset
            .entry(offset)
            .or_insert_with(|| {
                let mut slot_names = Vec::new();
                for (slot_name, slot) in &info.stack_slots {
                    if slot.offset == offset {
                        push_unique_casefold(&mut slot_names, slot_name.clone());
                        push_unique_casefold(&mut slot_names, slot_name.to_ascii_lowercase());
                    }
                }
                slot_names
            });
    };

    let key = var.display_name();
    if let Some(names) = cache.names_by_var.get(&key) {
        return names.clone();
    }

    let mut names = Vec::new();
    push_unique_casefold(&mut names, key.clone());
    push_unique_casefold(&mut names, key.to_ascii_lowercase());

    if let Some(offset) = info
        .forwarded_values
        .get(&key)
        .and_then(|prov| prov.stack_slot)
        .or_else(|| info.stack_slots.get(&key).map(|slot| slot.offset))
    {
        ensure_stack_slot_names(cache, offset);
        let Some(slot_names) = cache.stack_slot_names_by_offset.get(&offset) else {
            unreachable!("stack slot names cache should contain requested offset");
        };
        for slot_name in slot_names {
            push_unique_casefold(&mut names, slot_name.clone());
        }
    }

    if let Some(alias) = info.var_aliases.get(&key) {
        push_unique_casefold(&mut names, alias.clone());
        push_unique_casefold(&mut names, alias.to_ascii_lowercase());
    }

    if let Some(alias) = env
        .param_register_aliases
        .get(&var.name.to_ascii_lowercase())
    {
        push_unique_casefold(&mut names, alias.clone());
        push_unique_casefold(&mut names, alias.to_ascii_lowercase());
    }

    let root = resolve_copy_root_name(info, &key);
    if root != key {
        push_unique_casefold(&mut names, root.clone());
        push_unique_casefold(&mut names, root.to_ascii_lowercase());
        if let Some(offset) = info
            .forwarded_values
            .get(&root)
            .and_then(|prov| prov.stack_slot)
            .or_else(|| info.stack_slots.get(&root).map(|slot| slot.offset))
        {
            ensure_stack_slot_names(cache, offset);
            let Some(slot_names) = cache.stack_slot_names_by_offset.get(&offset) else {
                unreachable!("stack slot names cache should contain requested offset");
            };
            for slot_name in slot_names {
                push_unique_casefold(&mut names, slot_name.clone());
            }
        }
        if let Some(alias) = info.var_aliases.get(&root) {
            push_unique_casefold(&mut names, alias.clone());
            push_unique_casefold(&mut names, alias.to_ascii_lowercase());
        }
    }

    cache.names_by_var.insert(key, names.clone());
    names
}

fn normalized_addr_from_base_var(var: &SSAVar) -> NormalizedAddr {
    NormalizedAddr {
        base: BaseRef::Value(ValueRef::from(var)),
        index: None,
        scale_bytes: 0,
        offset_bytes: 0,
    }
}

fn indexed_addr_base_for_var(
    info: &UseInfo,
    var: &SSAVar,
    env: &PassEnv<'_>,
) -> Option<NormalizedAddr> {
    if let Some(addr) = semantic_addr_for_var(info, var, env)
        && !matches!(addr.base, BaseRef::Raw(_))
    {
        return Some(addr);
    }

    (semantic_var_is_pointer_like(info, var, env)
        || semantic_var_resolves_to_ptr_sized_entry_arg_root(info, var, env, 0))
    .then(|| normalized_addr_from_base_var(var))
}

fn semantic_addr_has_meaningful_base(addr: &NormalizedAddr) -> bool {
    match &addr.base {
        BaseRef::StackSlot(_) => true,
        BaseRef::Value(value_ref) => !value_ref.var.is_const(),
        BaseRef::Raw(_) => false,
    }
}

fn add_addr_offset(mut addr: NormalizedAddr, delta: i64) -> Option<NormalizedAddr> {
    addr.offset_bytes = addr.offset_bytes.checked_add(delta)?;
    Some(addr)
}

fn compose_indexed_addr(
    mut addr: NormalizedAddr,
    index: SSAVar,
    signed_scale: i64,
) -> Option<NormalizedAddr> {
    match &addr.index {
        None => {
            addr.index = Some(ValueRef::from(index));
            addr.scale_bytes = signed_scale;
            Some(addr)
        }
        Some(existing) if existing.var == index => {
            addr.scale_bytes = addr.scale_bytes.checked_add(signed_scale)?;
            Some(addr)
        }
        Some(_) => None,
    }
}

fn semantic_addr_for_var(
    info: &UseInfo,
    var: &SSAVar,
    env: &PassEnv<'_>,
) -> Option<NormalizedAddr> {
    semantic_addr_for_var_with_depth(info, var, env, 0)
}

fn semantic_addr_for_var_with_depth(
    info: &UseInfo,
    var: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<NormalizedAddr> {
    if depth > 8 {
        return None;
    }

    let key = var.display_name();
    let ptr_bytes = env.ptr_size.div_ceil(8).max(1);
    let lower_name = var.name.to_ascii_lowercase();
    if lower_name == env.sp_name || lower_name == env.fp_name {
        return Some(NormalizedAddr {
            base: BaseRef::StackSlot(0),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        });
    }
    if let Some(SemanticValue::Address(addr)) = info.semantic_values.get(&key) {
        return Some(addr.clone());
    }

    if let Some(SemanticValue::Scalar(ScalarValue::Root(root))) = info.semantic_values.get(&key)
        && (semantic_var_is_pointer_like(info, &root.var, env)
            || resolve_ptr_sized_entry_arg_root_var(info, &root.var, env, depth + 1).is_some())
    {
        let root_base = resolve_ptr_sized_entry_arg_root_var(info, &root.var, env, depth + 1)
            .unwrap_or_else(|| root.var.clone());
        return semantic_addr_for_var_with_depth(info, &root_base, env, depth + 1)
            .or_else(|| Some(normalized_addr_from_base_var(&root_base)));
    }
    if let Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var(alias)))) =
        info.semantic_values.get(&key)
        && var.size == ptr_bytes
        && let Some(slot) = alias
            .strip_prefix("arg")
            .and_then(|suffix| suffix.parse::<usize>().ok())
            .and_then(|idx| idx.checked_sub(1))
        && let Some(reg_name) = env.arg_regs.get(slot)
    {
        return Some(normalized_addr_from_base_var(&SSAVar::new(
            reg_name, 0, ptr_bytes,
        )));
    }

    if let Some(prov) = info.forwarded_values.get(&key)
        && let Some(source_var) = &prov.source_var
    {
        let entry_root = (prov.stack_slot.is_some() && var.size == ptr_bytes)
            .then(|| resolve_ptr_sized_entry_arg_root_var(info, source_var, env, depth + 1))
            .flatten();
        let base_var = entry_root.as_ref().unwrap_or(source_var);
        let is_ptr_sized_entry_arg_root = entry_root.is_some();
        if semantic_var_is_pointer_like(info, source_var, env) || is_ptr_sized_entry_arg_root {
            return semantic_addr_for_var_with_depth(info, base_var, env, depth + 1)
                .or_else(|| Some(normalized_addr_from_base_var(base_var)));
        }
    }

    let copy_root = resolve_copy_root_name(info, &key);
    if var.size == ptr_bytes
        && (typed_pointer_stack_slot_for_name(info, &key, env).is_some()
            || (copy_root != key
                && typed_pointer_stack_slot_for_name(info, &copy_root, env).is_some())
            || stack_reloaded_value_slot_for_name(info, &key).is_some()
            || (copy_root != key && stack_reloaded_value_slot_for_name(info, &copy_root).is_some()))
    {
        return Some(normalized_addr_from_base_var(var));
    }

    if copy_root != key
        && let Some(root_var) = ssa_var_from_display_name(&copy_root, var.size)
        && root_var != *var
        && let Some(addr) = semantic_addr_for_var_with_depth(info, &root_var, env, depth + 1)
    {
        return Some(addr);
    }

    if let Some(slot) = info.stack_slots.get(&key) {
        return Some(NormalizedAddr {
            base: BaseRef::StackSlot(slot.offset),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        });
    }

    if let Some(ptr) = info.ptr_arith.get(&key) {
        let base = semantic_addr_for_var_with_depth(info, &ptr.base, env, depth + 1)
            .unwrap_or_else(|| normalized_addr_from_base_var(&ptr.base));
        return compose_indexed_addr(
            base,
            ptr.index.clone(),
            if ptr.is_sub {
                -i64::from(ptr.element_size)
            } else {
                i64::from(ptr.element_size)
            },
        );
    }

    if let Some((base, offset)) = info.ptr_members.get(&key) {
        let base = semantic_addr_for_var_with_depth(info, base, env, depth + 1)
            .unwrap_or_else(|| normalized_addr_from_base_var(base));
        return add_addr_offset(base, *offset);
    }

    let has_non_address_semantic = matches!(
        info.semantic_values.get(&key),
        Some(SemanticValue::Scalar(_)) | Some(SemanticValue::Load { .. })
    );
    if !has_non_address_semantic
        && (copy_root != key || utils::is_temporary_name(&key))
        && let Some(offset) =
            utils::extract_stack_offset_from_var(var, &info.definitions, env.fp_name, env.sp_name)
    {
        return Some(NormalizedAddr {
            base: BaseRef::StackSlot(offset),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        });
    }

    if let Some(oracle) = env.type_oracle
        && oracle.field_name(oracle.type_of(var), 0).is_some()
    {
        return Some(NormalizedAddr {
            base: BaseRef::Value(ValueRef::from(var)),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        });
    }

    info.definitions
        .get(&key)
        .cloned()
        .map(|expr| NormalizedAddr {
            base: BaseRef::Raw(expr),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        })
}

fn semantic_value_rank(value: &SemanticValue) -> i32 {
    match value {
        SemanticValue::Unknown => 0,
        SemanticValue::Scalar(ScalarValue::Expr(_)) => 40,
        SemanticValue::Scalar(ScalarValue::Root(_)) => 45,
        SemanticValue::Address(addr) => 100 + normalized_addr_rank(addr),
        SemanticValue::Load { addr, .. } => 120 + normalized_addr_rank(addr),
    }
}

fn should_prefer_same_family_store_value(base: &SemanticValue, family: &SemanticValue) -> bool {
    match (base, family) {
        (
            SemanticValue::Scalar(ScalarValue::Root(_)),
            SemanticValue::Scalar(ScalarValue::Expr(
                CExpr::IntLit(_)
                | CExpr::UIntLit(_)
                | CExpr::FloatLit(_)
                | CExpr::CharLit(_)
                | CExpr::StringLit(_),
            )),
        ) => true,
        (SemanticValue::Scalar(ScalarValue::Root(_)), _) => {
            semantic_value_rank(family) > semantic_value_rank(base)
        }
        _ => false,
    }
}

fn should_replace_same_family_candidate(
    current: &SemanticValue,
    candidate: &SemanticValue,
) -> bool {
    if should_prefer_same_family_store_value(current, candidate) {
        return true;
    }

    matches!(current, SemanticValue::Unknown) && !matches!(candidate, SemanticValue::Unknown)
}

fn normalized_addr_rank(addr: &NormalizedAddr) -> i32 {
    let base_rank = match addr.base {
        BaseRef::Raw(_) => 5,
        BaseRef::StackSlot(_) => 10,
        BaseRef::Value(_) => 50,
    };
    let index_bonus = if addr.index.is_some() { 30 } else { 0 };
    let offset_bonus = if addr.offset_bytes != 0 { 20 } else { 0 };
    base_rank + index_bonus + offset_bonus
}

fn normalized_stack_slot_offset(addr: &NormalizedAddr) -> Option<i64> {
    match addr.base {
        BaseRef::StackSlot(base) if addr.index.is_none() => base.checked_add(addr.offset_bytes),
        _ => None,
    }
}

fn is_authoritative_addr(addr: &NormalizedAddr) -> bool {
    !matches!(addr.base, BaseRef::Raw(_))
}

fn should_preserve_rooted_structured_load_identity_for_stable_memory(
    info: &UseInfo,
    addr: &NormalizedAddr,
    env: &PassEnv<'_>,
    value: &SemanticValue,
) -> bool {
    if !matches!(value, SemanticValue::Scalar(_))
        || (addr.index.is_none() && addr.offset_bytes == 0)
    {
        return false;
    }

    let BaseRef::Value(base_ref) = &addr.base else {
        return false;
    };

    let lower = base_ref.var.name.to_ascii_lowercase();
    if lower == env.fp_name || lower == env.sp_name {
        return false;
    }

    env.param_register_aliases.contains_key(&lower)
        || semantic_type_hint_names(info, &base_ref.var, env)
            .iter()
            .any(|name| env.type_hints.contains_key(name))
}

fn insert_semantic_value(info: &mut UseInfo, key: String, candidate: SemanticValue) {
    match info.semantic_values.get(&key) {
        Some(current) if semantic_value_rank(current) > semantic_value_rank(&candidate) => {}
        _ => {
            if let Some(value_id) = info.value_id_for_name(&key) {
                let replace_by_value = match info.semantic_values_by_value.get(&value_id) {
                    Some(current) => {
                        semantic_value_rank(current) <= semantic_value_rank(&candidate)
                    }
                    None => true,
                };
                if replace_by_value {
                    info.semantic_values_by_value
                        .insert(value_id, candidate.clone());
                }
            }
            info.insert_semantic_value_for_name(&key, candidate);
        }
    }
}

fn replace_semantic_value(info: &mut UseInfo, key: String, candidate: SemanticValue) {
    info.insert_semantic_value_for_name(&key, candidate);
}

fn resolve_stable_stack_load_semantic_value(
    info: &UseInfo,
    value: &SemanticValue,
    depth: u32,
) -> Option<SemanticValue> {
    if depth > 8 {
        return None;
    }

    match value {
        SemanticValue::Load {
            space: SpaceId::Ram,
            addr,
            ..
        } => {
            let stable_scalar = normalized_stack_slot_offset(addr)
                .filter(|offset| *offset < 0)
                .and_then(|offset| info.stable_stack_values.get(&offset))
                .filter(|stable| matches!(stable, SemanticValue::Scalar(_)));
            stable_scalar
                .and_then(|stable| {
                    resolve_stable_stack_load_semantic_value(info, stable, depth + 1)
                })
                .or_else(|| Some(value.clone()))
        }
        SemanticValue::Scalar(ScalarValue::Root(root)) => {
            match info
                .semantic_values
                .get(&root.display_name())
                .and_then(|inner| resolve_stable_stack_load_semantic_value(info, inner, depth + 1))
            {
                Some(inner @ SemanticValue::Scalar(_)) => Some(inner),
                Some(SemanticValue::Address(_))
                | Some(SemanticValue::Load { .. })
                | Some(SemanticValue::Unknown)
                | None => Some(value.clone()),
            }
        }
        _ => Some(value.clone()),
    }
}

fn semantic_source_value_for_var(info: &UseInfo, var: &SSAVar) -> Option<SemanticValue> {
    if let Some(value) = info
        .semantic_values
        .get(&var.display_name())
        .and_then(|value| resolve_stable_stack_load_semantic_value(info, value, 0))
    {
        return Some(value);
    }
    if var.is_const() {
        let value = utils::parse_const_value(&var.name)?;
        let expr = if value > 0x7fff_ffff {
            CExpr::UIntLit(value)
        } else {
            CExpr::IntLit(value as i64)
        };
        return Some(SemanticValue::Scalar(ScalarValue::Expr(expr)));
    }
    let root = resolve_copy_root_name(info, &var.display_name());
    if root != var.display_name()
        && let Some(value) = semantic_or_scalar_source_value(info, &root)
    {
        return Some(value);
    }
    let lower = var.name.to_ascii_lowercase();
    if lower == "stack"
        || lower == "saved_fp"
        || lower.starts_with("stack_")
        || is_raw_temporary_or_memory_like_name(&var.name)
    {
        return None;
    }
    Some(SemanticValue::Scalar(ScalarValue::Root(ValueRef::from(
        var,
    ))))
}

fn scalar_semantic_source_value_for_var(info: &UseInfo, var: &SSAVar) -> Option<SemanticValue> {
    semantic_source_value_for_var(info, var)
        .filter(|value| matches!(value, SemanticValue::Scalar(_)))
}

fn ssa_var_from_display_name(display_name: &str, default_size: u32) -> Option<SSAVar> {
    let (base, version) = ssa_key_parts(display_name)?;
    Some(SSAVar::new(base, version, default_size))
}

fn semantic_source_value_from_provenance(
    info: &UseInfo,
    provenance: &ValueProvenance,
    env: &PassEnv<'_>,
) -> Option<SemanticValue> {
    if let Some(source_var) = &provenance.source_var {
        if !semantic_var_is_pointer_like(info, source_var, env)
            && let Some(value) = scalar_semantic_source_value_for_var(info, source_var)
        {
            return Some(value);
        }
        if semantic_var_is_pointer_like(info, source_var, env) {
            return Some(SemanticValue::Address(
                semantic_addr_for_var(info, source_var, env)
                    .unwrap_or_else(|| normalized_addr_from_base_var(source_var)),
            ));
        }
        if let Some(value) = semantic_source_value_for_var(info, source_var) {
            return Some(value);
        }
    }
    semantic_or_scalar_source_value(info, &provenance.source)
}

fn semantic_or_scalar_source_value(info: &UseInfo, source_name: &str) -> Option<SemanticValue> {
    if let Some(value) = info
        .semantic_values
        .get(source_name)
        .and_then(|value| resolve_stable_stack_load_semantic_value(info, value, 0))
    {
        return Some(value);
    }

    let root = resolve_copy_root_name(info, source_name);
    if let Some(value) = info
        .semantic_values
        .get(&root)
        .and_then(|value| resolve_stable_stack_load_semantic_value(info, value, 0))
    {
        return Some(value);
    }

    if let Some(value) = utils::parse_const_value(&root) {
        let expr = if value > 0x7fff_ffff {
            CExpr::UIntLit(value)
        } else {
            CExpr::IntLit(value as i64)
        };
        return Some(SemanticValue::Scalar(ScalarValue::Expr(expr)));
    }

    let rendered = utils::format_traced_name(&root, &info.var_aliases);
    let lower = rendered.to_ascii_lowercase();
    if is_raw_temporary_or_memory_like_name(&root)
        || lower == "stack"
        || lower == "saved_fp"
        || lower.starts_with("stack_")
    {
        return None;
    }

    Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var(
        rendered,
    ))))
}

fn resolve_copy_root_name(info: &UseInfo, name: &str) -> String {
    let mut current = name.to_string();
    let mut seen = HashSet::new();
    while seen.insert(current.clone()) {
        let Some(next) = info.copy_sources.get(&current).cloned() else {
            break;
        };
        current = next;
    }
    current
}

fn invalidates_block_stack_values(
    op: &SSAOp,
    definitions: &HashMap<String, CExpr>,
    env: &PassEnv<'_>,
) -> bool {
    match op {
        SSAOp::Store {
            space: SpaceId::Ram,
            addr,
            ..
        } => utils::extract_stack_offset_from_var(addr, definitions, env.fp_name, env.sp_name)
            .is_none(),
        SSAOp::Call { .. } | SSAOp::CallInd { .. } | SSAOp::CallOther { .. } => true,
        SSAOp::StoreConditional {
            space: SpaceId::Ram,
            ..
        }
        | SSAOp::AtomicCAS {
            space: SpaceId::Ram,
            ..
        }
        | SSAOp::StoreGuarded {
            space: SpaceId::Ram,
            ..
        } => true,
        _ => false,
    }
}

fn is_call_like_stack_boundary_op(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Call { .. }
            | SSAOp::CallInd { .. }
            | SSAOp::CallOther { .. }
            | SSAOp::StoreConditional {
                space: SpaceId::Ram,
                ..
            }
            | SSAOp::AtomicCAS {
                space: SpaceId::Ram,
                ..
            }
            | SSAOp::StoreGuarded {
                space: SpaceId::Ram,
                ..
            }
    )
}

fn invalidates_semantic_stack_values(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Call { .. }
            | SSAOp::CallInd { .. }
            | SSAOp::CallOther { .. }
            | SSAOp::StoreConditional {
                space: SpaceId::Ram,
                ..
            }
            | SSAOp::AtomicCAS {
                space: SpaceId::Ram,
                ..
            }
            | SSAOp::StoreGuarded {
                space: SpaceId::Ram,
                ..
            }
    )
}

fn build_formatted_defs(scratch: &mut UseScratch, env: &PassEnv<'_>) {
    scratch.info.formatted_defs.clear();
    let mut defs: Vec<_> = scratch
        .info
        .definitions
        .iter()
        .map(|(ssa_key, expr)| (ssa_key.clone(), expr.clone()))
        .collect();
    defs.sort_by(|a, b| a.0.cmp(&b.0));

    let mut selected: HashMap<String, (String, CExpr)> = HashMap::new();
    for (ssa_key, expr) in defs {
        let formatted = utils::format_traced_name(&ssa_key, &scratch.info.var_aliases);
        match selected.get_mut(&formatted) {
            Some((winner_key, winner_expr))
                if is_preferred_formatted_def_candidate(
                    &ssa_key,
                    &expr,
                    winner_key.as_str(),
                    winner_expr,
                    env,
                ) =>
            {
                *winner_key = ssa_key;
                *winner_expr = expr;
            }
            None => {
                selected.insert(formatted, (ssa_key, expr));
            }
            Some(_) => {}
        }
    }

    let mut formatted_keys: Vec<_> = selected.into_iter().collect();
    formatted_keys.sort_by(|a, b| a.0.cmp(&b.0));
    for (formatted, (_, expr)) in formatted_keys {
        scratch.info.formatted_defs.insert(formatted, expr);
    }
}

fn is_preferred_formatted_def_candidate(
    candidate: &str,
    candidate_expr: &CExpr,
    incumbent: &str,
    incumbent_expr: &CExpr,
    env: &PassEnv<'_>,
) -> bool {
    let candidate_quality = formatted_def_expr_quality(candidate_expr, env);
    let incumbent_quality = formatted_def_expr_quality(incumbent_expr, env);
    if candidate_quality != incumbent_quality {
        return candidate_quality > incumbent_quality;
    }
    is_preferred_formatted_def(candidate, incumbent)
}

fn is_preferred_formatted_def(candidate: &str, incumbent: &str) -> bool {
    let candidate_version = ssa_key_parts(candidate)
        .map(|(_, version)| version)
        .unwrap_or(0);
    let incumbent_version = ssa_key_parts(incumbent)
        .map(|(_, version)| version)
        .unwrap_or(0);
    candidate_version > incumbent_version
        || (candidate_version == incumbent_version && candidate < incumbent)
}

fn formatted_def_expr_quality(expr: &CExpr, env: &PassEnv<'_>) -> (i32, i32, i32, i32, i32, i32) {
    let mut quality = (0, 0, 0, 0, 0, 0);
    accumulate_formatted_def_expr_quality(expr, env, &mut quality);
    quality
}

fn accumulate_formatted_def_expr_quality(
    expr: &CExpr,
    env: &PassEnv<'_>,
    quality: &mut (i32, i32, i32, i32, i32, i32),
) {
    match expr {
        CExpr::Var(name) => {
            if is_generic_stack_alias_name(name) {
                quality.3 -= 8;
            } else if is_low_signal_name(name) {
                quality.5 -= 4;
            } else if is_register_candidate_base(name, env) {
                quality.4 -= 6;
            } else {
                quality.1 += 3;
            }
        }
        CExpr::Subscript { base, index } => {
            quality.0 += 6;
            quality.2 += 2;
            accumulate_formatted_def_expr_quality(base, env, quality);
            accumulate_formatted_def_expr_quality(index, env, quality);
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            quality.0 += 7;
            quality.2 += 2;
            accumulate_formatted_def_expr_quality(base, env, quality);
        }
        CExpr::Deref(inner) | CExpr::AddrOf(inner) => {
            quality.2 += 1;
            accumulate_formatted_def_expr_quality(inner, env, quality);
        }
        CExpr::Cast { expr: inner, .. }
        | CExpr::Paren(inner)
        | CExpr::Unary { operand: inner, .. }
        | CExpr::Sizeof(inner) => accumulate_formatted_def_expr_quality(inner, env, quality),
        CExpr::Binary { op, left, right } => {
            if matches!(op, crate::ast::BinaryOp::Add | crate::ast::BinaryOp::Sub)
                && (literal_zero(left) || literal_zero(right))
            {
                quality.5 -= 10;
            }
            accumulate_formatted_def_expr_quality(left, env, quality);
            accumulate_formatted_def_expr_quality(right, env, quality);
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            accumulate_formatted_def_expr_quality(cond, env, quality);
            accumulate_formatted_def_expr_quality(then_expr, env, quality);
            accumulate_formatted_def_expr_quality(else_expr, env, quality);
        }
        CExpr::Call { func, args } => {
            accumulate_formatted_def_expr_quality(func, env, quality);
            for arg in args {
                accumulate_formatted_def_expr_quality(arg, env, quality);
            }
        }
        CExpr::Comma(exprs) => {
            for inner in exprs {
                accumulate_formatted_def_expr_quality(inner, env, quality);
            }
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_) => {}
    }
}

fn literal_zero(expr: &CExpr) -> bool {
    matches!(expr, CExpr::IntLit(0) | CExpr::UIntLit(0))
}

fn is_generic_stack_alias_name(name: &str) -> bool {
    name == "stack"
        || name.starts_with("local_")
        || name.starts_with("stack_")
        || name == "saved_fp"
}

fn is_raw_ssa_storage_or_register_name(name: &str) -> bool {
    matches!(
        utils::ssa_name_kind(name),
        SSAVarNameKind::RegisterAlias
            | SSAVarNameKind::Temporary
            | SSAVarNameKind::Constant
            | SSAVarNameKind::Memory
            | SSAVarNameKind::AddressSpace
    )
}

fn is_raw_temporary_or_memory_like_name(name: &str) -> bool {
    matches!(
        utils::ssa_name_kind(name),
        SSAVarNameKind::Temporary | SSAVarNameKind::Memory | SSAVarNameKind::AddressSpace
    )
}

fn is_symbol_or_object_name(name: &str) -> bool {
    matches!(
        SSAVarNameKind::classify(name),
        SSAVarNameKind::Symbol | SSAVarNameKind::Object
    )
}

fn is_low_signal_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    is_raw_ssa_storage_or_register_name(name)
        || lower.starts_with('t')
            && lower
                .trim_start_matches('t')
                .chars()
                .all(|ch| ch.is_ascii_digit())
}

fn ssa_key_parts(name: &str) -> Option<(&str, u32)> {
    let (base, version) = name.rsplit_once('_')?;
    let parsed = version.parse::<u32>().ok()?;
    Some((base, parsed))
}

fn is_semantic_binding_base(base: &str) -> bool {
    let lower = base.to_ascii_lowercase();
    lower.starts_with("local_")
        || lower.starts_with("arg")
        || lower.starts_with("field_")
        || lower.starts_with("var_")
        || lower.starts_with("sub_")
        || lower.starts_with("str.")
        || lower.starts_with("0x")
        || lower.contains('.')
        || is_raw_ssa_storage_or_register_name(base)
}

fn is_decimal_suffix(name: &str, prefix: &str) -> bool {
    let Some(rest) = name.strip_prefix(prefix) else {
        return false;
    };
    !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
}

fn is_x86_register_base(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    if matches!(
        lower.as_str(),
        "rax"
            | "rbx"
            | "rcx"
            | "rdx"
            | "rsi"
            | "rdi"
            | "rbp"
            | "rsp"
            | "rip"
            | "eax"
            | "ebx"
            | "ecx"
            | "edx"
            | "esi"
            | "edi"
            | "ebp"
            | "esp"
            | "eip"
            | "ax"
            | "bx"
            | "cx"
            | "dx"
            | "si"
            | "di"
            | "bp"
            | "sp"
            | "ip"
            | "al"
            | "bl"
            | "cl"
            | "dl"
            | "ah"
            | "bh"
            | "ch"
            | "dh"
            | "cs"
            | "ds"
            | "es"
            | "fs"
            | "gs"
            | "ss"
            | "cf"
            | "pf"
            | "af"
            | "zf"
            | "sf"
            | "of"
            | "df"
            | "tf"
    ) {
        return true;
    }
    is_decimal_suffix(&lower, "xmm")
        || is_decimal_suffix(&lower, "ymm")
        || is_decimal_suffix(&lower, "zmm")
        || is_decimal_suffix(&lower, "mm")
        || is_decimal_suffix(&lower, "k")
        || is_decimal_suffix(&lower, "r")
        || (lower.starts_with('r')
            && lower.len() > 2
            && lower[..lower.len() - 1]
                .strip_prefix('r')
                .map(|rest| !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit()))
                .unwrap_or(false)
            && matches!(lower.chars().last(), Some('b' | 'w' | 'd')))
}

fn is_arm_like_register_base(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    matches!(lower.as_str(), "sp" | "fp" | "lr" | "pc" | "cpsr" | "nzcv")
        || is_decimal_suffix(&lower, "r")
        || is_decimal_suffix(&lower, "x")
        || is_decimal_suffix(&lower, "w")
}

fn is_mips_like_register_base(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    if matches!(
        lower.as_str(),
        "zero"
            | "at"
            | "gp"
            | "sp"
            | "fp"
            | "ra"
            | "hi"
            | "lo"
            | "pc"
            | "status"
            | "cause"
            | "badvaddr"
    ) {
        return true;
    }
    is_decimal_suffix(&lower, "v")
        || is_decimal_suffix(&lower, "a")
        || is_decimal_suffix(&lower, "t")
        || is_decimal_suffix(&lower, "s")
        || is_decimal_suffix(&lower, "k")
}

fn is_riscv_like_register_base(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    if matches!(
        lower.as_str(),
        "zero" | "ra" | "sp" | "gp" | "tp" | "fp" | "pc"
    ) {
        return true;
    }
    is_decimal_suffix(&lower, "x")
        || is_decimal_suffix(&lower, "t")
        || is_decimal_suffix(&lower, "s")
        || is_decimal_suffix(&lower, "a")
        || is_decimal_suffix(&lower, "ft")
        || is_decimal_suffix(&lower, "fs")
        || is_decimal_suffix(&lower, "fa")
        || is_decimal_suffix(&lower, "v")
}

fn is_register_candidate_base(base: &str, env: &PassEnv<'_>) -> bool {
    if is_semantic_binding_base(base) {
        return false;
    }

    let lower = base.to_ascii_lowercase();
    if lower == env.sp_name || lower == env.fp_name {
        return false;
    }
    if !lower.chars().all(|c| c.is_ascii_alphanumeric()) {
        return false;
    }

    if is_x86_register_base(base)
        || is_arm_like_register_base(base)
        || is_mips_like_register_base(base)
        || is_riscv_like_register_base(base)
    {
        return true;
    }

    env.arg_regs
        .iter()
        .any(|arg| arg.eq_ignore_ascii_case(base))
}

fn is_register_candidate_key(key: &str, env: &PassEnv<'_>) -> bool {
    let Some((base, _)) = ssa_key_parts(key) else {
        return false;
    };
    is_register_candidate_base(base, env)
}

fn is_register_candidate_var(var: &r2ssa::SSAVar, env: &PassEnv<'_>) -> bool {
    is_register_candidate_base(&var.name, env)
}

fn parse_target_addr(target: &r2ssa::SSAVar) -> Option<u64> {
    crate::address::parse_address_from_var_name(&target.name)
}

fn infer_successors(
    block: &SSABlock,
    idx: usize,
    blocks: &[SSABlock],
    block_set: &HashSet<u64>,
) -> Vec<u64> {
    let fallthrough = blocks.get(idx + 1).map(|b| b.addr);

    let mut term = None;
    for op in block.ops.iter().rev() {
        if matches!(
            op,
            SSAOp::Return { .. }
                | SSAOp::Branch { .. }
                | SSAOp::CBranch { .. }
                | SSAOp::BranchInd { .. }
        ) {
            term = Some(op);
            break;
        }
    }

    match term {
        Some(SSAOp::Return { .. }) => Vec::new(),
        Some(SSAOp::Branch { target }) => parse_target_addr(target)
            .filter(|addr| block_set.contains(addr))
            .into_iter()
            .collect(),
        Some(SSAOp::CBranch { target, .. }) => {
            let mut out = Vec::new();
            if let Some(addr) = parse_target_addr(target)
                && block_set.contains(&addr)
            {
                out.push(addr);
            }
            if let Some(next) = fallthrough
                && !out.contains(&next)
            {
                out.push(next);
            }
            out
        }
        Some(SSAOp::BranchInd { .. }) => fallthrough.into_iter().collect(),
        _ => fallthrough.into_iter().collect(),
    }
}

fn pair_key(a: &str, b: &str) -> (String, String) {
    if a <= b {
        (a.to_string(), b.to_string())
    } else {
        (b.to_string(), a.to_string())
    }
}

fn sort_members_by_version(members: &mut [String], version_by_name: &HashMap<String, u32>) {
    members.sort_by(|a, b| {
        version_by_name
            .get(a)
            .copied()
            .unwrap_or(u32::MAX)
            .cmp(&version_by_name.get(b).copied().unwrap_or(u32::MAX))
            .then_with(|| a.cmp(b))
    });
}

fn alias_class_sort_key(
    class: &[String],
    version_by_name: &HashMap<String, u32>,
) -> (bool, u32, String) {
    let has_zero = class
        .iter()
        .any(|name| version_by_name.get(name) == Some(&0));
    let min_version = class
        .iter()
        .filter_map(|name| version_by_name.get(name))
        .copied()
        .min()
        .unwrap_or(u32::MAX);
    let smallest_member = class.iter().min().cloned().unwrap_or_default();
    (!has_zero, min_version, smallest_member)
}

#[allow(clippy::too_many_arguments)]
fn pair_interferes(
    a: &str,
    b: &str,
    blocks: &[SSABlock],
    live_in: &HashMap<u64, HashSet<String>>,
    live_out: &HashMap<u64, HashSet<String>>,
    phi_defs: &HashMap<u64, HashSet<String>>,
    candidate_keys: &HashSet<String>,
) -> bool {
    for block in blocks {
        if let Some(set) = live_in.get(&block.addr)
            && set.contains(a)
            && set.contains(b)
        {
            return true;
        }

        let mut live = live_out.get(&block.addr).cloned().unwrap_or_default();
        if live.contains(a) && live.contains(b) {
            return true;
        }

        for op in block.ops.iter().rev() {
            if let Some(dst) = op.dst() {
                let dst_key = dst.display_name();
                if candidate_keys.contains(&dst_key) {
                    if dst_key == a && live.contains(b) {
                        return true;
                    }
                    if dst_key == b && live.contains(a) {
                        return true;
                    }
                    live.remove(&dst_key);
                }
            }

            for src in op.sources() {
                let src_key = src.display_name();
                if candidate_keys.contains(&src_key) {
                    live.insert(src_key);
                }
            }

            if live.contains(a) && live.contains(b) {
                return true;
            }
        }

        if let Some(defs) = phi_defs.get(&block.addr) {
            if defs.contains(a) && live.contains(b) {
                return true;
            }
            if defs.contains(b) && live.contains(a) {
                return true;
            }
        }
    }

    false
}

fn coalesce_variables(
    scratch: &mut UseScratch,
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
    control: DecompileWorkControl<'_>,
) -> Result<(), DecompileExecutionStop> {
    control.poll()?;
    const MAX_INTERFERENCE_PAIRS: usize = 16_384;
    const MAX_INTERFERENCE_WORK: usize = 512_000;

    let mut reg_versions: HashMap<String, Vec<(String, u32)>> = HashMap::new();

    for block in blocks {
        control.poll()?;
        block.for_each_def(|def| {
            if !is_register_candidate_var(def.var, env) {
                return;
            }
            let base = def.var.name.to_ascii_lowercase();
            reg_versions
                .entry(base)
                .or_default()
                .push((def.var.display_name(), def.var.version));
        });

        block.for_each_source(|src| {
            if !is_register_candidate_var(src.var, env) {
                return;
            }
            let base = src.var.name.to_ascii_lowercase();
            reg_versions
                .entry(base)
                .or_default()
                .push((src.var.display_name(), src.var.version));
        });
    }

    let mut bases: Vec<_> = reg_versions.keys().cloned().collect();
    bases.sort();

    let mut uf_parent: HashMap<String, String> = HashMap::new();
    for base in &bases {
        control.poll()?;
        let Some(versions) = reg_versions.get(base) else {
            continue;
        };
        for (name, _) in versions {
            uf_parent
                .entry(name.clone())
                .or_insert_with(|| name.clone());
        }
    }

    // Keep interference-aware coalescing responsive on very large functions.
    // If the estimated pair/block work is too large, skip this optional pass
    // and leave original SSA naming intact.
    let mut estimated_pairs = 0usize;
    for base in &bases {
        control.poll()?;
        let Some(versions) = reg_versions.get(base) else {
            continue;
        };
        let mut seen = HashSet::new();
        for (name, _) in versions {
            seen.insert(name);
        }
        let n = seen.len();
        if n > 1 {
            estimated_pairs = estimated_pairs.saturating_add(n.saturating_mul(n - 1) / 2);
        }
    }
    let estimated_work = estimated_pairs.saturating_mul(blocks.len());
    if estimated_pairs > MAX_INTERFERENCE_PAIRS || estimated_work > MAX_INTERFERENCE_WORK {
        return Ok(());
    }

    let mut key_to_base: HashMap<String, String> = HashMap::new();
    for base in &bases {
        control.poll()?;
        let Some(versions) = reg_versions.get(base) else {
            continue;
        };
        for (name, _) in versions {
            key_to_base.insert(name.clone(), base.clone());
        }
    }

    for block in blocks {
        control.poll()?;
        for phi in &block.phis {
            if !is_register_candidate_var(&phi.dst, env) {
                continue;
            }
            let dst_key = phi.dst.display_name();
            let Some(dst_base) = key_to_base.get(&dst_key).cloned() else {
                continue;
            };
            for (_, src) in &phi.sources {
                if !is_register_candidate_var(src, env) {
                    continue;
                }
                let src_key = src.display_name();
                if key_to_base.get(&src_key) != Some(&dst_base) {
                    continue;
                }
                let root_a = utils::uf_find(&mut uf_parent, &dst_key);
                let root_b = utils::uf_find(&mut uf_parent, &src_key);
                if root_a != root_b {
                    uf_parent.insert(root_a, root_b);
                }
            }
        }
    }

    let block_set: HashSet<u64> = blocks.iter().map(|b| b.addr).collect();
    let mut successors: HashMap<u64, Vec<u64>> = HashMap::new();
    for (idx, block) in blocks.iter().enumerate() {
        successors.insert(block.addr, infer_successors(block, idx, blocks, &block_set));
    }

    let mut phi_defs: HashMap<u64, HashSet<String>> = HashMap::new();
    let mut edge_phi_uses: HashMap<(u64, u64), HashSet<String>> = HashMap::new();
    let mut def_sets: HashMap<u64, HashSet<String>> = HashMap::new();
    let mut use_sets: HashMap<u64, HashSet<String>> = HashMap::new();
    let candidate_keys: HashSet<String> = key_to_base.keys().cloned().collect();

    for block in blocks {
        let mut defs = HashSet::new();
        let mut uses = HashSet::new();
        let mut defined_so_far = HashSet::new();

        for phi in &block.phis {
            let dst_key = phi.dst.display_name();
            if candidate_keys.contains(&dst_key) {
                defs.insert(dst_key.clone());
                defined_so_far.insert(dst_key.clone());
                phi_defs.entry(block.addr).or_default().insert(dst_key);
            }
            for (pred, src) in &phi.sources {
                let src_key = src.display_name();
                if candidate_keys.contains(&src_key) {
                    edge_phi_uses
                        .entry((*pred, block.addr))
                        .or_default()
                        .insert(src_key);
                }
            }
        }

        for op in &block.ops {
            for src in op.sources() {
                let src_key = src.display_name();
                if !candidate_keys.contains(&src_key) {
                    continue;
                }
                if !defined_so_far.contains(&src_key) {
                    uses.insert(src_key.clone());
                }
            }
            if let Some(dst) = op.dst() {
                let dst_key = dst.display_name();
                if candidate_keys.contains(&dst_key) {
                    defs.insert(dst_key.clone());
                    defined_so_far.insert(dst_key);
                }
            }
        }

        def_sets.insert(block.addr, defs);
        use_sets.insert(block.addr, uses);
    }

    let mut live_in: HashMap<u64, HashSet<String>> = HashMap::new();
    let mut live_out: HashMap<u64, HashSet<String>> = HashMap::new();

    let mut changed = true;
    while changed {
        control.poll()?;
        changed = false;
        for block in blocks.iter().rev() {
            control.poll()?;
            let mut new_live_out = HashSet::new();
            for succ in successors.get(&block.addr).into_iter().flatten() {
                let mut succ_live_in = live_in.get(succ).cloned().unwrap_or_default();
                if let Some(succ_phi_defs) = phi_defs.get(succ) {
                    succ_live_in.retain(|name| !succ_phi_defs.contains(name));
                }
                new_live_out.extend(succ_live_in);
                if let Some(phi_uses) = edge_phi_uses.get(&(block.addr, *succ)) {
                    new_live_out.extend(phi_uses.iter().cloned());
                }
            }

            let defs = def_sets.get(&block.addr).cloned().unwrap_or_default();
            let mut new_live_in = use_sets.get(&block.addr).cloned().unwrap_or_default();
            for name in &new_live_out {
                if !defs.contains(name) {
                    new_live_in.insert(name.clone());
                }
            }

            let out_entry = live_out.entry(block.addr).or_default();
            if *out_entry != new_live_out {
                *out_entry = new_live_out;
                changed = true;
            }

            let in_entry = live_in.entry(block.addr).or_default();
            if *in_entry != new_live_in {
                *in_entry = new_live_in;
                changed = true;
            }
        }
    }

    let mut interference_cache: HashMap<(String, String), bool> = HashMap::new();

    for base in &bases {
        control.poll()?;
        let Some(versions) = reg_versions.get(base) else {
            continue;
        };
        if *base == env.sp_name || *base == env.fp_name {
            continue;
        }
        let mut unique: Vec<(String, u32)> = versions.clone();
        unique.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(&b.0)));
        unique.dedup_by(|a, b| a.0 == b.0);
        if unique.len() <= 1 {
            continue;
        }

        let mut groups: HashMap<String, Vec<String>> = HashMap::new();
        for (ssa_name, _) in &unique {
            let root = utils::uf_find(&mut uf_parent, ssa_name);
            groups.entry(root).or_default().push(ssa_name.clone());
        }

        let version_by_name: HashMap<String, u32> = unique
            .iter()
            .map(|(name, ver)| (name.clone(), *ver))
            .collect();
        let mut alias_classes: Vec<Vec<String>> = Vec::new();

        let mut roots: Vec<_> = groups.keys().cloned().collect();
        roots.sort();
        for root in roots {
            control.poll()?;
            let Some(members) = groups.get(&root) else {
                continue;
            };
            let mut sorted_members = members.clone();
            sort_members_by_version(&mut sorted_members, &version_by_name);

            let mut classes: Vec<Vec<String>> = Vec::new();
            for member in sorted_members {
                control.poll()?;
                let mut placed = false;
                for class in &mut classes {
                    let mut interferes = false;
                    for other in class.iter() {
                        let key = pair_key(&member, other);
                        let entry = interference_cache.entry(key.clone()).or_insert_with(|| {
                            pair_interferes(
                                &key.0,
                                &key.1,
                                blocks,
                                &live_in,
                                &live_out,
                                &phi_defs,
                                &candidate_keys,
                            )
                        });
                        if *entry {
                            interferes = true;
                            break;
                        }
                    }
                    if !interferes {
                        class.push(member.clone());
                        placed = true;
                        break;
                    }
                }

                if !placed {
                    classes.push(vec![member]);
                }
            }
            for class in &mut classes {
                sort_members_by_version(class, &version_by_name);
            }
            classes.sort_by(|a, b| {
                alias_class_sort_key(a, &version_by_name)
                    .cmp(&alias_class_sort_key(b, &version_by_name))
            });
            alias_classes.extend(classes);
        }

        let mut merged = true;
        while merged {
            control.poll()?;
            merged = false;
            'outer: for i in 0..alias_classes.len() {
                for j in (i + 1)..alias_classes.len() {
                    let mut has_interference = false;
                    for a in &alias_classes[i] {
                        for b in &alias_classes[j] {
                            let key = pair_key(a, b);
                            let entry =
                                interference_cache.entry(key.clone()).or_insert_with(|| {
                                    pair_interferes(
                                        &key.0,
                                        &key.1,
                                        blocks,
                                        &live_in,
                                        &live_out,
                                        &phi_defs,
                                        &candidate_keys,
                                    )
                                });
                            if *entry {
                                has_interference = true;
                                break;
                            }
                        }
                        if has_interference {
                            break;
                        }
                    }

                    if !has_interference {
                        let rhs = alias_classes.remove(j);
                        alias_classes[i].extend(rhs);
                        sort_members_by_version(&mut alias_classes[i], &version_by_name);
                        merged = true;
                        break 'outer;
                    }
                }
            }
        }

        for class in &mut alias_classes {
            sort_members_by_version(class, &version_by_name);
        }
        alias_classes.sort_by(|a, b| {
            alias_class_sort_key(a, &version_by_name)
                .cmp(&alias_class_sort_key(b, &version_by_name))
        });

        for (idx, class) in alias_classes.iter().enumerate() {
            let alias = if idx == 0 {
                base.clone()
            } else {
                format!("{}_{}", base, idx + 1)
            };
            for member in class {
                if is_register_candidate_key(member, env) {
                    scratch
                        .info
                        .var_aliases
                        .insert(member.clone(), alias.clone());
                }
            }
        }
    }
    control.poll()?;
    Ok(())
}

fn analyze_call_args(scratch: &mut UseScratch, blocks: &[SSABlock], env: &PassEnv<'_>) {
    if env.arg_regs.is_empty() {
        return;
    }

    let ret_family = register_family_name(env.ret_reg_name);
    for block in blocks {
        let ops = &block.ops;
        let block_producer_map = ops
            .iter()
            .enumerate()
            .filter_map(|(idx, op)| op.dst().map(|dst| (dst.display_name(), idx)))
            .collect::<HashMap<_, _>>();
        for (call_idx, op) in ops.iter().enumerate() {
            let is_call = matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. });
            if !is_call {
                continue;
            }

            let producer_map = ops[..call_idx]
                .iter()
                .enumerate()
                .filter_map(|(idx, op)| op.dst().map(|dst| (dst.display_name(), idx)))
                .collect::<HashMap<_, _>>();
            let lower = LowerCtx {
                use_info: None,
                definitions: &scratch.info.definitions,
                semantic_values: &scratch.info.semantic_values,
                use_counts: &scratch.info.use_counts,
                condition_vars: &scratch.info.condition_vars,
                pinned: &scratch.info.pinned,
                var_aliases: &scratch.info.var_aliases,
                param_register_aliases: env.param_register_aliases,
                type_hints: &scratch.info.type_hints,
                ptr_arith: &scratch.info.ptr_arith,
                stack_slots: &scratch.info.stack_slots,
                forwarded_values: &scratch.info.forwarded_values,
                type_oracle: env.type_oracle,
            };
            let post_call_query = PostCallResultQuery {
                info: &scratch.info,
                lower: &lower,
                block_addr: block.addr,
                ops,
                producers: &producer_map,
                env,
            };
            let mut found_regs: BTreeMap<String, CallArgCandidate> = BTreeMap::new();
            let mut direct_inlined_call_results = HashSet::new();
            let mut i = call_idx;
            while i > 0 {
                i -= 1;
                let prev_op = &ops[i];

                if matches!(prev_op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
                    break;
                }

                let candidate = if let Some(dst) = prev_op.dst() {
                    let dst_base = dst.name.to_lowercase();
                    if !env.arg_regs.contains(&dst_base) || !is_call_arg_producer(prev_op) {
                        None
                    } else {
                        let dst_key = dst.display_name();
                        let expr = lower.expr_for_ssa_name(&dst_key);
                        let (input_var, input_expr) = match prev_op {
                            SSAOp::Copy { src, .. }
                            | SSAOp::IntZExt { src, .. }
                            | SSAOp::IntSExt { src, .. }
                            | SSAOp::Trunc { src, .. }
                            | SSAOp::Cast { src, .. }
                            | SSAOp::Subpiece { src, .. } => {
                                let source_expr = lower.expr_for_ssa_name(&src.display_name());
                                (src, source_expr)
                            }
                            _ => (dst, expr.clone()),
                        };
                        let result_candidate =
                            call_result_expr_for_post_call_source(&post_call_query, i, dst)
                                .or_else(|| {
                                    lowered_var_alias_from_expr(&expr, dst.size)
                                        .filter(|alias| alias.display_name() != dst_key)
                                        .and_then(|alias| {
                                            call_result_expr_for_post_call_source(
                                                &post_call_query,
                                                i,
                                                &alias,
                                            )
                                        })
                                });
                        let mut binding = result_candidate
                            .map(|(result_call_idx, expr)| {
                                direct_inlined_call_results.insert((block.addr, result_call_idx));
                                CallArgBinding::result(SemanticCallArg::FallbackExpr(expr))
                                    .with_source_call(block.addr, result_call_idx)
                            })
                            .unwrap_or_else(|| {
                                let binding = CallArgBinding::input(semantic_call_arg_for_var(
                                    &scratch.info,
                                    input_var,
                                    input_expr.clone(),
                                    env,
                                ));
                                bind_call_arg_source_var(&scratch.info, binding, input_var)
                            });
                        let binding_has_stable_negative_source =
                            canonicalize_call_arg_binding_to_negative_stack_load(
                                &scratch.info,
                                &mut binding,
                                Some(input_var),
                                input_var.size,
                            )
                            .is_some();
                        if !binding.is_result()
                            && !binding_has_stable_negative_source
                            && same_register_family_call_arg_source(input_var, dst)
                            && let Some(family_value) = same_register_family_semantic_value_before(
                                &scratch.info,
                                ops,
                                i,
                                dst,
                                env,
                            )
                        {
                            let family_arg = SemanticCallArg::semantic(family_value);
                            let should_replace =
                                (semantic_call_arg_is_generic_entry_root(&binding.arg, env)
                                    && same_family_call_arg_is_more_specific(
                                        &binding.arg,
                                        &family_arg,
                                    ))
                                    || semantic_call_arg_score(
                                        &scratch.info,
                                        input_var,
                                        &family_arg,
                                        &input_expr,
                                        env,
                                    ) > semantic_call_arg_score(
                                        &scratch.info,
                                        input_var,
                                        &binding.arg,
                                        &input_expr,
                                        env,
                                    );
                            if should_replace {
                                binding.arg = family_arg;
                            }
                        }
                        if !binding.is_result() && !binding_has_stable_negative_source {
                            improve_call_arg_binding_from_copy_root(
                                &scratch.info,
                                &mut binding,
                                input_var,
                                &input_expr,
                                &lower,
                                env,
                            );
                        }
                        let score = semantic_call_arg_score(
                            &scratch.info,
                            input_var,
                            &binding.arg,
                            &input_expr,
                            env,
                        );
                        Some((dst_base, binding, score, i, dst_key))
                    }
                } else {
                    None
                };

                let Some((dst_base, binding, score, idx, dst_key)) = candidate else {
                    continue;
                };

                let replace = match found_regs.get(&dst_base) {
                    None => true,
                    Some(current) => {
                        if idx < current.producer_idx
                            && should_keep_later_call_arg_candidate(
                                &current.binding.arg,
                                &binding.arg,
                            )
                        {
                            false
                        } else {
                            score > current.score
                                || (score == current.score && idx > current.producer_idx)
                        }
                    }
                };
                if replace {
                    found_regs.insert(
                        dst_base,
                        CallArgCandidate {
                            binding,
                            score,
                            producer_idx: idx,
                            dst_key,
                        },
                    );
                }
            }

            let mut args = Vec::new();
            let mut consumed_keys = Vec::new();
            let imported_like_call_target =
                call_target_uses_imported_like_args(block.addr, call_idx, op, env);
            scratch
                .info
                .inlined_call_results
                .extend(direct_inlined_call_results);
            for reg in env.arg_regs {
                if let Some(candidate) = found_regs.remove(reg) {
                    args.push(candidate.binding);
                    consumed_keys.push(candidate.dst_key);
                    continue;
                }

                if let Some(phi) = block.phis.iter().find(|phi| {
                    phi.dst.name.eq_ignore_ascii_case(reg)
                        && !phi.dst.name.eq_ignore_ascii_case(env.sp_name)
                        && !phi.dst.name.eq_ignore_ascii_case(env.fp_name)
                }) {
                    let dst_key = phi.dst.display_name();
                    args.push(bind_call_arg_source_var(
                        &scratch.info,
                        CallArgBinding::input(SemanticCallArg::value_root(phi.dst.clone())),
                        &phi.dst,
                    ));
                    consumed_keys.push(dst_key);
                } else {
                    break;
                }
            }
            let (stack_args, inlined_call_results) = collect_immediate_stack_call_args(
                block.addr,
                ops,
                call_idx,
                &producer_map,
                &lower,
                &scratch.info,
                env,
            );
            scratch
                .info
                .inlined_call_results
                .extend(inlined_call_results);
            if imported_like_call_target
                || should_append_unknown_stack_args(&scratch.info, &args, &stack_args, env)
            {
                for (_, arg, value_key, addr_key) in &stack_args {
                    args.push(arg.clone());
                    consumed_keys.push(value_key.clone());
                    consumed_keys.push(addr_key.clone());
                }
            } else if !stack_args.is_empty() {
                merge_arm64_stack_home_call_args(&mut args, &stack_args, env);
                for (_, _, value_key, addr_key) in &stack_args {
                    consumed_keys.push(value_key.clone());
                    consumed_keys.push(addr_key.clone());
                }
            }

            if !args.is_empty() {
                scratch.info.call_args.insert((block.addr, call_idx), args);
                for key in consumed_keys {
                    scratch.info.consumed_by_call.insert(key);
                }
            }

            if let Some(ret_family) = ret_family.as_deref() {
                let lower = LowerCtx {
                    use_info: None,
                    definitions: &scratch.info.definitions,
                    semantic_values: &scratch.info.semantic_values,
                    use_counts: &scratch.info.use_counts,
                    condition_vars: &scratch.info.condition_vars,
                    pinned: &scratch.info.pinned,
                    var_aliases: &scratch.info.var_aliases,
                    param_register_aliases: env.param_register_aliases,
                    type_hints: &scratch.info.type_hints,
                    ptr_arith: &scratch.info.ptr_arith,
                    stack_slots: &scratch.info.stack_slots,
                    forwarded_values: &scratch.info.forwarded_values,
                    type_oracle: env.type_oracle,
                };
                let call_expr = call_result_expr_for_call_at(
                    &scratch.info,
                    &lower,
                    block.addr,
                    call_idx,
                    op,
                    env,
                );
                if let Some(call_expr) = call_expr {
                    record_call_result_expr(&mut scratch.info, (block.addr, call_idx), &call_expr);
                    bind_call_result_alias_definitions(
                        &mut scratch.info,
                        block,
                        call_idx,
                        &block_producer_map,
                        &call_expr,
                        ret_family,
                        env,
                        None,
                    );
                }
            }

            let mut j = call_idx;
            while j > 0 {
                j -= 1;
                let prev = &ops[j];
                if matches!(prev, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
                    break;
                }
                if let SSAOp::Store {
                    space: SpaceId::Ram,
                    addr,
                    val,
                } = prev
                {
                    let addr_lower = addr.name.to_lowercase();
                    if addr_lower.contains(env.sp_name) && val.is_const() {
                        scratch.info.consumed_by_call.insert(val.display_name());
                        scratch.info.consumed_by_call.insert(addr.display_name());
                        if j > 0 {
                            let prev2 = &ops[j - 1];
                            if let SSAOp::IntSub { dst, b, .. } = prev2 {
                                let dst_lower = dst.name.to_lowercase();
                                if dst_lower.contains(env.sp_name) && b.is_const() {
                                    scratch.info.consumed_by_call.insert(dst.display_name());
                                }
                            }
                        }
                        break;
                    }
                }
            }
        }
    }
}

fn bind_single_use_call_result_definitions(
    scratch: &mut UseScratch,
    blocks: &[SSABlock],
    env: &PassEnv<'_>,
) {
    let Some(ret_family) = register_family_name(env.ret_reg_name) else {
        return;
    };
    let mut call_result_defs = HashMap::new();

    for block in blocks {
        let producer_map = block
            .ops
            .iter()
            .enumerate()
            .filter_map(|(idx, op)| op.dst().map(|dst| (dst.display_name(), idx)))
            .collect::<HashMap<_, _>>();
        for (op_idx, op) in block.ops.iter().enumerate() {
            let lower = LowerCtx {
                use_info: None,
                definitions: &scratch.info.definitions,
                semantic_values: &scratch.info.semantic_values,
                use_counts: &scratch.info.use_counts,
                condition_vars: &scratch.info.condition_vars,
                pinned: &scratch.info.pinned,
                var_aliases: &scratch.info.var_aliases,
                param_register_aliases: env.param_register_aliases,
                type_hints: &scratch.info.type_hints,
                ptr_arith: &scratch.info.ptr_arith,
                stack_slots: &scratch.info.stack_slots,
                forwarded_values: &scratch.info.forwarded_values,
                type_oracle: env.type_oracle,
            };
            let call_expr =
                call_result_expr_for_call_at(&scratch.info, &lower, block.addr, op_idx, op, env);
            let Some(call_expr) = call_expr else {
                continue;
            };

            record_call_result_expr(&mut scratch.info, (block.addr, op_idx), &call_expr);
            bind_call_result_alias_definitions(
                &mut scratch.info,
                block,
                op_idx,
                &producer_map,
                &call_expr,
                &ret_family,
                env,
                Some(&mut call_result_defs),
            );
        }
    }

    if call_result_defs.is_empty() {
        return;
    }

    for args in scratch.info.call_args.values_mut() {
        for binding in args {
            if let Some(rewritten) = rewrite_call_result_binding(binding, &call_result_defs) {
                *binding = rewritten;
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn bind_call_result_alias_definitions(
    info: &mut UseInfo,
    block: &SSABlock,
    call_idx: usize,
    producer_map: &HashMap<String, usize>,
    call_expr: &CExpr,
    ret_family: &str,
    env: &PassEnv<'_>,
    mut call_result_defs: Option<&mut HashMap<String, CExpr>>,
) {
    let mut next_idx = call_idx + 1;
    while let Some(next_op) = block.ops.get(next_idx) {
        if matches!(next_op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
            break;
        }

        if let Some(dst) = next_op.dst() {
            let is_direct_ret = matches!(next_op, SSAOp::CallDefine { .. })
                && register_family_name(&dst.name).as_deref() == Some(ret_family);
            let is_post_call_alias = if matches!(next_op, SSAOp::CallDefine { .. }) {
                false
            } else {
                let alias_query = PostCallAliasQuery {
                    info,
                    block,
                    producers: producer_map,
                    env,
                };
                is_post_call_result_alias_for_call(
                    &alias_query,
                    call_idx,
                    next_idx,
                    dst,
                    ret_family,
                )
            };
            if (is_direct_ret || is_post_call_alias)
                && info
                    .use_counts
                    .get(&dst.display_name())
                    .copied()
                    .unwrap_or(0)
                    > 0
            {
                record_call_result_alias(info, (block.addr, call_idx), &dst.display_name());
                record_direct_call_result_alias(info, &dst.display_name());
                info.insert_definition_for_var(dst, call_expr.clone());
                if let Some(call_result_defs) = call_result_defs.as_deref_mut() {
                    call_result_defs.insert(dst.display_name(), call_expr.clone());
                    call_result_defs
                        .insert(dst.display_name().to_ascii_lowercase(), call_expr.clone());
                }
            }
        }

        for src in next_op.sources() {
            let src_key = src.display_name();
            let uses_current_call_result = {
                let lower = LowerCtx {
                    use_info: None,
                    definitions: &info.definitions,
                    semantic_values: &info.semantic_values,
                    use_counts: &info.use_counts,
                    condition_vars: &info.condition_vars,
                    pinned: &info.pinned,
                    var_aliases: &info.var_aliases,
                    param_register_aliases: env.param_register_aliases,
                    type_hints: &info.type_hints,
                    ptr_arith: &info.ptr_arith,
                    stack_slots: &info.stack_slots,
                    forwarded_values: &info.forwarded_values,
                    type_oracle: env.type_oracle,
                };
                let query = PostCallResultQuery {
                    info,
                    lower: &lower,
                    block_addr: block.addr,
                    ops: &block.ops,
                    producers: producer_map,
                    env,
                };
                call_result_expr_for_post_call_source(&query, next_idx, src)
                    .is_some_and(|(result_call_idx, _)| result_call_idx == call_idx)
            };
            if !uses_current_call_result || info.use_counts.get(&src_key).copied().unwrap_or(0) == 0
            {
                continue;
            }

            record_call_result_alias(info, (block.addr, call_idx), &src_key);
            record_direct_call_result_alias(info, &src_key);
            info.insert_definition_for_var(src, call_expr.clone());
            info.inlined_call_results.insert((block.addr, call_idx));
            if let Some(call_result_defs) = call_result_defs.as_deref_mut() {
                call_result_defs.insert(src_key.clone(), call_expr.clone());
                call_result_defs.insert(src_key.to_ascii_lowercase(), call_expr.clone());
            }
        }
        next_idx += 1;
    }
}

fn call_result_source_for_alias(info: &UseInfo, alias: &str) -> Option<(u64, usize)> {
    info.call_result_source_for_name(alias).or_else(|| {
        let lowered = alias.to_ascii_lowercase();
        (lowered != alias)
            .then(|| info.call_result_source_for_name(&lowered))
            .flatten()
    })
}

fn propagate_call_result_aliases(
    info: &mut UseInfo,
    control: DecompileWorkControl<'_>,
) -> Result<(), DecompileExecutionStop> {
    let mut changed = true;
    while changed {
        control.poll()?;
        changed = false;

        for (dst, src) in info.copy_sources.clone() {
            control.poll()?;
            let Some(source_call) = call_result_source_for_alias(info, &src) else {
                continue;
            };
            if call_result_source_for_alias(info, &dst).is_none() {
                record_call_result_alias(info, source_call, &dst);
                changed = true;
            }
        }

        for (dst, prov) in info.forwarded_values.clone() {
            control.poll()?;
            let source_call = call_result_source_for_alias(info, &prov.source).or_else(|| {
                prov.source_var.as_ref().and_then(|source_var| {
                    call_result_source_for_alias(info, &source_var.display_name())
                })
            });
            let Some(source_call) = source_call else {
                continue;
            };
            if call_result_source_for_alias(info, &dst).is_none() {
                record_call_result_alias(info, source_call, &dst);
                changed = true;
            }
        }

        for (name, value) in info.semantic_values.clone() {
            control.poll()?;
            let source_alias = match value {
                SemanticValue::Scalar(ScalarValue::Root(root)) => Some(root.display_name()),
                SemanticValue::Scalar(ScalarValue::Expr(expr)) => {
                    lowered_var_alias_from_expr(&expr, 0).map(|alias| alias.display_name())
                }
                SemanticValue::Address(NormalizedAddr {
                    base: BaseRef::Value(root),
                    index: None,
                    scale_bytes: 0,
                    offset_bytes: 0,
                }) => Some(root.display_name()),
                _ => None,
            };
            let Some(source_alias) = source_alias else {
                continue;
            };
            let Some(source_call) = call_result_source_for_alias(info, &source_alias) else {
                continue;
            };
            if call_result_source_for_alias(info, &name).is_none() {
                record_call_result_alias(info, source_call, &name);
                changed = true;
            }
        }
    }
    Ok(())
}

fn call_result_expr_for_call_at(
    info: &UseInfo,
    lower: &LowerCtx<'_>,
    block_addr: u64,
    op_idx: usize,
    op: &SSAOp,
    env: &PassEnv<'_>,
) -> Option<CExpr> {
    let bindings = info
        .call_args
        .get(&(block_addr, op_idx))
        .cloned()
        .unwrap_or_default();
    let mut args = Vec::with_capacity(bindings.len());
    for binding in bindings {
        let rendered = call_arg_expr_for_definition(info, lower, binding.clone());
        let rendered = rendered?;
        args.push(rendered);
    }

    let func = if let Some(identity) = resolved_callee_expr_for_site(block_addr, op_idx, env) {
        identity
    } else {
        match op {
            SSAOp::Call { target } => lower.get_expr(target),
            SSAOp::CallInd { target } => {
                let resolved = lower.get_expr(target);
                match resolved {
                    CExpr::Var(_) => resolved,
                    other => CExpr::Deref(Box::new(other)),
                }
            }
            _ => return None,
        }
    };

    Some(CExpr::call(func, args))
}

fn resolved_callee_expr_for_site(
    block_addr: u64,
    op_idx: usize,
    env: &PassEnv<'_>,
) -> Option<CExpr> {
    let resolved = CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
        identity: CalleeTargetIdentityRequest {
            resolution: env.callee_resolution,
            callsite: Some(CallsiteKey {
                block_addr,
                op_index: op_idx,
            }),
            prepared_identity: None,
            prepared_direct_target: None,
            direct_target_context: None,
        },
        callee_facts: env.callee_facts,
    })?;
    Some(CExpr::Var(
        resolved
            .identity
            .display_name
            .clone()
            .unwrap_or_else(|| resolved.identity.primary_key()),
    ))
}

fn call_arg_expr_for_definition(
    info: &UseInfo,
    lower: &LowerCtx<'_>,
    binding: CallArgBinding,
) -> Option<CExpr> {
    let expr = match binding.arg {
        SemanticCallArg::Semantic(value) => render_call_arg_semantic_value_for_definition(
            info,
            lower,
            &value,
            0,
            &mut HashSet::new(),
        ),
        SemanticCallArg::StringAddr(_) => None,
        SemanticCallArg::FallbackExpr(expr) => Some(expr),
    }?;

    let normalized =
        normalize_call_arg_expr_for_definition(info, lower, expr, 0, &mut HashSet::new())?;
    expr_is_valid_for_synthesized_call_arg(&normalized).then_some(normalized)
}

fn render_call_arg_semantic_value_for_definition(
    info: &UseInfo,
    lower: &LowerCtx<'_>,
    value: &SemanticValue,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<CExpr> {
    if depth > 8 {
        return None;
    }

    if let Some(rendered) = lower.expr_for_semantic_value(value) {
        return Some(rendered);
    }

    match value {
        SemanticValue::Scalar(ScalarValue::Expr(expr)) => Some(expr.clone()),
        SemanticValue::Scalar(ScalarValue::Root(root)) => {
            let key = root.display_name();
            let visit_key = format!("call-def-root:{key}");
            if !visited.insert(visit_key.clone()) {
                return None;
            }
            let rendered = lower.expr_for_ssa_name(&key);
            visited.remove(&visit_key);
            Some(rendered)
        }
        SemanticValue::Address(addr) => {
            render_call_arg_addr_for_definition(info, lower, addr, depth + 1, visited)
        }
        SemanticValue::Load { space, addr, size } => render_call_arg_load_for_definition(
            info,
            lower,
            *space,
            addr,
            *size,
            depth + 1,
            visited,
        ),
        SemanticValue::Unknown => None,
    }
}

fn render_call_arg_addr_for_definition(
    info: &UseInfo,
    lower: &LowerCtx<'_>,
    addr: &NormalizedAddr,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<CExpr> {
    match &addr.base {
        BaseRef::StackSlot(offset) => {
            if *offset >= 0 {
                return None;
            }
            render_visible_stack_slot_expr_for_definition(info, lower, *offset, depth + 1, visited)
                .and_then(take_address_of_definition_expr)
        }
        _ => {
            let rendered = lower.expr_for_semantic_value(&SemanticValue::Address(addr.clone()))?;
            Some(rendered)
        }
    }
}

fn render_call_arg_load_for_definition(
    info: &UseInfo,
    lower: &LowerCtx<'_>,
    space: SpaceId,
    addr: &NormalizedAddr,
    size: u32,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<CExpr> {
    if space != SpaceId::Ram {
        return lower.expr_for_semantic_value(&SemanticValue::Load {
            space,
            addr: addr.clone(),
            size,
        });
    }
    match &addr.base {
        BaseRef::StackSlot(offset) => {
            render_visible_stack_slot_expr_for_definition(info, lower, *offset, depth + 1, visited)
        }
        _ => {
            let rendered = lower.expr_for_semantic_value(&SemanticValue::Load {
                space: SpaceId::Ram,
                addr: addr.clone(),
                size,
            })?;
            Some(rendered)
        }
    }
}

fn render_visible_stack_slot_expr_for_definition(
    info: &UseInfo,
    lower: &LowerCtx<'_>,
    offset: i64,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<CExpr> {
    let visit_key = format!("call-def-stack-slot:{offset}");
    if !visited.insert(visit_key.clone()) {
        return None;
    }

    let visible_local = {
        let mut stack_slot_names = lower
            .stack_slots
            .iter()
            .filter_map(|(name, slot)| (slot.offset == offset).then_some(name.clone()))
            .collect::<BTreeSet<_>>();
        stack_slot_names
            .pop_first()
            .map(|name| lower.expr_for_ssa_name(&name))
            .filter(expr_is_valid_for_synthesized_call_arg)
            .or_else(|| (offset < 0).then(|| CExpr::Var(format!("local_{:x}", (-offset) as u64))))
    };

    let stable_value = info.stable_stack_values.get(&offset).and_then(|value| {
        render_call_arg_semantic_value_for_definition(info, lower, value, depth + 1, visited)
    });

    let rendered = if offset < 0 {
        visible_local.or(stable_value)
    } else {
        stable_value.or(visible_local)
    };

    visited.remove(&visit_key);
    rendered
}

fn normalize_call_arg_expr_for_definition(
    info: &UseInfo,
    lower: &LowerCtx<'_>,
    expr: CExpr,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<CExpr> {
    if depth > 12 {
        return None;
    }

    match expr {
        CExpr::Var(name) => {
            normalize_call_arg_var_for_definition(info, lower, name, depth, visited)
        }
        CExpr::Paren(inner) => {
            normalize_call_arg_expr_for_definition(info, lower, *inner, depth + 1, visited)
                .map(|expr| CExpr::Paren(Box::new(expr)))
        }
        CExpr::Cast { ty, expr: inner } => {
            normalize_call_arg_expr_for_definition(info, lower, *inner, depth + 1, visited)
                .map(|expr| CExpr::cast(ty, expr))
        }
        CExpr::AddrOf(inner) => {
            normalize_call_arg_expr_for_definition(info, lower, *inner, depth + 1, visited)
                .and_then(take_address_of_definition_expr)
        }
        CExpr::Deref(inner) => {
            normalize_call_arg_expr_for_definition(info, lower, *inner, depth + 1, visited)
                .map(|expr| CExpr::Deref(Box::new(expr)))
        }
        CExpr::Unary { op, operand } => {
            normalize_call_arg_expr_for_definition(info, lower, *operand, depth + 1, visited)
                .map(|operand| CExpr::unary(op, operand))
        }
        CExpr::Binary { op, left, right } => {
            let left =
                normalize_call_arg_expr_for_definition(info, lower, *left, depth + 1, visited)?;
            let right =
                normalize_call_arg_expr_for_definition(info, lower, *right, depth + 1, visited)?;
            Some(CExpr::binary(op, left, right))
        }
        CExpr::Subscript { base, index } => {
            let base =
                normalize_call_arg_expr_for_definition(info, lower, *base, depth + 1, visited)?;
            let index =
                normalize_call_arg_expr_for_definition(info, lower, *index, depth + 1, visited)?;
            Some(CExpr::Subscript {
                base: Box::new(base),
                index: Box::new(index),
            })
        }
        CExpr::Member { base, member } => {
            normalize_call_arg_expr_for_definition(info, lower, *base, depth + 1, visited).map(
                |base| CExpr::Member {
                    base: Box::new(base),
                    member,
                },
            )
        }
        CExpr::PtrMember { base, member } => {
            normalize_call_arg_expr_for_definition(info, lower, *base, depth + 1, visited).map(
                |base| CExpr::PtrMember {
                    base: Box::new(base),
                    member,
                },
            )
        }
        CExpr::Call { func, args } => {
            let func =
                normalize_call_arg_expr_for_definition(info, lower, *func, depth + 1, visited)?;
            let args = args
                .into_iter()
                .map(|arg| {
                    normalize_call_arg_expr_for_definition(info, lower, arg, depth + 1, visited)
                })
                .collect::<Option<Vec<_>>>()?;
            Some(CExpr::call(func, args))
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            let cond =
                normalize_call_arg_expr_for_definition(info, lower, *cond, depth + 1, visited)?;
            let then_expr = normalize_call_arg_expr_for_definition(
                info,
                lower,
                *then_expr,
                depth + 1,
                visited,
            )?;
            let else_expr = normalize_call_arg_expr_for_definition(
                info,
                lower,
                *else_expr,
                depth + 1,
                visited,
            )?;
            Some(CExpr::Ternary {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
            })
        }
        CExpr::Comma(items) => items
            .into_iter()
            .map(|item| {
                normalize_call_arg_expr_for_definition(info, lower, item, depth + 1, visited)
            })
            .collect::<Option<Vec<_>>>()
            .map(CExpr::Comma),
        CExpr::Sizeof(inner) => {
            normalize_call_arg_expr_for_definition(info, lower, *inner, depth + 1, visited)
                .map(|expr| CExpr::Sizeof(Box::new(expr)))
        }
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_) => Some(expr),
    }
}

fn normalize_call_arg_var_for_definition(
    info: &UseInfo,
    lower: &LowerCtx<'_>,
    name: String,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<CExpr> {
    let visit_key = format!("call-def-var:{name}");
    if !visited.insert(visit_key.clone()) {
        return Some(CExpr::Var(name));
    }

    let rendered = if utils::parse_const_value(&name).is_some()
        || crate::address::parse_address_from_var_name(&name).is_some()
    {
        Some(lower.expr_for_ssa_name(&name))
    } else if let Some(prov) = lower.forwarded_values.get(&name) {
        normalize_call_arg_var_for_definition(info, lower, prov.source.clone(), depth + 1, visited)
    } else if let Some(value) = info.semantic_values.get(&name) {
        render_call_arg_semantic_value_for_definition(info, lower, value, depth + 1, visited)
            .and_then(|expr| {
                normalize_call_arg_expr_for_definition(info, lower, expr, depth + 1, visited)
            })
    } else if let Some(def) = lower.definitions.get(&name) {
        normalize_call_arg_expr_for_definition(info, lower, def.clone(), depth + 1, visited)
    } else if let Some(alias) = lower.var_aliases.get(&name) {
        Some(CExpr::Var(alias.clone()))
    } else {
        let lowered = lower.expr_for_ssa_name(&name);
        match lowered {
            CExpr::Var(ref lowered_name) if lowered_name == &name => Some(CExpr::Var(name.clone())),
            other => normalize_call_arg_expr_for_definition(info, lower, other, depth + 1, visited),
        }
    };

    visited.remove(&visit_key);
    rendered.or(Some(CExpr::Var(name)))
}

fn take_address_of_definition_expr(expr: CExpr) -> Option<CExpr> {
    match expr {
        CExpr::Var(_)
        | CExpr::Subscript { .. }
        | CExpr::Member { .. }
        | CExpr::PtrMember { .. }
        | CExpr::Deref(_) => Some(CExpr::AddrOf(Box::new(expr))),
        CExpr::Paren(inner) => {
            take_address_of_definition_expr(*inner).map(|expr| CExpr::Paren(Box::new(expr)))
        }
        CExpr::Cast { ty, expr: inner } => {
            take_address_of_definition_expr(*inner).map(|expr| CExpr::cast(ty, expr))
        }
        _ => None,
    }
}

fn expr_is_valid_for_synthesized_call_arg(expr: &CExpr) -> bool {
    !call_arg_expr_contains_stack_placeholder(expr, 0)
        && !call_arg_expr_contains_transient_name(expr, 0)
}

fn rewrite_call_result_binding(
    binding: &CallArgBinding,
    call_result_defs: &HashMap<String, CExpr>,
) -> Option<CallArgBinding> {
    let arg = match &binding.arg {
        SemanticCallArg::FallbackExpr(CExpr::Var(name)) => call_result_defs
            .get(name)
            .cloned()
            .map(SemanticCallArg::FallbackExpr),
        SemanticCallArg::FallbackExpr(CExpr::Paren(inner))
        | SemanticCallArg::FallbackExpr(CExpr::Cast { expr: inner, .. }) => {
            let inner_arg = SemanticCallArg::FallbackExpr((**inner).clone());
            rewrite_call_result_binding(&CallArgBinding::from(inner_arg), call_result_defs)
                .map(|binding| binding.arg)
        }
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Root(root))) => {
            call_result_defs
                .get(&root.display_name())
                .cloned()
                .map(SemanticCallArg::FallbackExpr)
        }
        _ => None,
    }?;

    Some(CallArgBinding {
        arg,
        role: CallArgRole::Result,
        stack_offset: binding.stack_offset,
        source_call: binding.source_call,
        source_value_id: binding.source_value_id,
        source_var_name: binding.source_var_name.clone(),
    })
}

#[cfg(test)]
fn call_target_is_imported(
    block_addr: u64,
    op_index: usize,
    op: &SSAOp,
    env: &PassEnv<'_>,
) -> bool {
    call_target_policy_decision(block_addr, op_index, op, env).is_some_and(|policy| policy.imported)
}

fn call_target_uses_imported_like_args(
    block_addr: u64,
    op_index: usize,
    op: &SSAOp,
    env: &PassEnv<'_>,
) -> bool {
    call_target_policy_decision(block_addr, op_index, op, env)
        .is_some_and(|policy| policy.arg_policy() == CalleeCallArgPolicy::ImportedLike)
}

fn call_target_policy_decision(
    block_addr: u64,
    op_index: usize,
    op: &SSAOp,
    env: &PassEnv<'_>,
) -> Option<CalleeTargetPolicyDecision> {
    if !matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
        return None;
    }
    CalleeResolutionFacts::resolve_target_policy(CalleeTargetResolutionRequest {
        identity: CalleeTargetIdentityRequest {
            resolution: env.callee_resolution,
            callsite: Some(CallsiteKey {
                block_addr,
                op_index,
            }),
            prepared_identity: None,
            prepared_direct_target: None,
            direct_target_context: None,
        },
        callee_facts: env.callee_facts,
    })
    .map(|resolved| resolved.policy)
}

fn should_append_unknown_stack_args(
    info: &UseInfo,
    args: &[CallArgBinding],
    stack_args: &[(i64, CallArgBinding, String, String)],
    env: &PassEnv<'_>,
) -> bool {
    let Some((_, first_stack, _, _)) = stack_args.first() else {
        return false;
    };
    let Some(first_current) = args.first() else {
        return true;
    };
    !(first_current.arg == first_stack.arg
        || call_args_share_semantic_source(info, &first_current.arg, &first_stack.arg)
        || semantic_call_arg_is_generic_entry_root(&first_current.arg, env)
        || semantic_call_arg_is_generic_register_root(&first_current.arg, env)
        || should_prefer_stack_home_call_arg(first_current, first_stack, env))
}

fn collect_immediate_stack_call_args(
    block_addr: u64,
    ops: &[SSAOp],
    call_idx: usize,
    producers: &HashMap<String, usize>,
    lower: &LowerCtx<'_>,
    info: &UseInfo,
    env: &PassEnv<'_>,
) -> StackCallArgCollection {
    let uses_arm64_arg_regs = env
        .arg_regs
        .first()
        .is_some_and(|reg| reg.starts_with('x') || reg.starts_with('w'));
    if !uses_arm64_arg_regs {
        return (Vec::new(), HashSet::new());
    }

    let mut args = Vec::new();
    let mut inlined_call_results = HashSet::new();
    let mut owned_result_source_calls = HashSet::new();
    let mut seen_offsets = HashSet::new();
    let mut collecting = false;
    let mut synthetic_call_home_base: Option<String> = None;
    let post_call_query = PostCallResultQuery {
        info,
        lower,
        block_addr,
        ops,
        producers,
        env,
    };

    let mut i = call_idx;
    while i > 0 {
        i -= 1;
        let prev = &ops[i];
        if matches!(prev, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
            break;
        }

        match prev {
            SSAOp::Store {
                space: SpaceId::Ram,
                addr,
                val,
            } => {
                let Some(offset) = call_stack_arg_offset(ops, producers, info, addr, env, 0)
                    .or_else(|| {
                        synthetic_call_home_offset(
                            ops,
                            producers,
                            addr,
                            &mut synthetic_call_home_base,
                            env,
                            0,
                        )
                    })
                    .filter(|off| *off >= 0)
                else {
                    if collecting {
                        break;
                    }
                    continue;
                };
                if seen_offsets.insert(offset) {
                    let key = val.display_name();
                    let expr = visible_call_arg_seed_expr(lower, val);
                    let raw_result_candidate =
                        call_result_expr_for_post_call_source(&post_call_query, i, val)
                            .or_else(|| {
                                lowered_var_alias_from_expr(&expr, val.size)
                                    .filter(|alias| alias.display_name() != key)
                                    .and_then(|alias| {
                                        call_result_expr_for_post_call_source(
                                            &post_call_query,
                                            i,
                                            &alias,
                                        )
                                    })
                            })
                            .or_else(|| {
                                let ret_family =
                                    register_family_name(post_call_query.env.ret_reg_name)?;
                                lowered_var_alias_from_expr(&expr, val.size)
                                    .filter(|alias| {
                                        register_family_name(&alias.name).as_deref()
                                            == Some(ret_family.as_str())
                                    })
                                    .and_then(|_| latest_preceding_call_expr(&post_call_query, i))
                            });
                    let (call_result_candidate, duplicate_result_binding) =
                        if let Some((result_call_idx, expr)) = raw_result_candidate {
                            let stack_home_query = StackHomeQuery {
                                ops,
                                producers,
                                info,
                                lower,
                                env,
                            };
                            if owned_result_source_calls.insert((block_addr, result_call_idx)) {
                                (Some((result_call_idx, expr)), None)
                            } else {
                                (
                                    None,
                                    duplicate_result_input_binding_from_preserved_stack_home(
                                        &stack_home_query,
                                        val,
                                        result_call_idx,
                                        offset,
                                    ),
                                )
                            }
                        } else {
                            (None, None)
                        };
                    let mut binding = duplicate_result_binding
                        .unwrap_or_else(|| {
                            call_result_candidate
                                .clone()
                                .map(|(call_idx, expr)| {
                                    inlined_call_results.insert((block_addr, call_idx));
                                    CallArgBinding::result(SemanticCallArg::FallbackExpr(expr))
                                        .with_source_call(block_addr, call_idx)
                                })
                                .unwrap_or_else(|| {
                                    let binding = CallArgBinding::input(
                                        preferred_stack_input_call_arg(info, val, &expr, env),
                                    );
                                    bind_call_arg_source_var(info, binding, val)
                                })
                        })
                        .with_stack_offset(offset);
                    let binding_has_stable_negative_source =
                        canonicalize_call_arg_binding_to_negative_stack_load(
                            info,
                            &mut binding,
                            Some(val),
                            val.size,
                        )
                        .is_some();
                    if !binding.is_result()
                        && !binding_has_stable_negative_source
                        && let Some(family_value) =
                            same_register_family_semantic_value_before(info, ops, i, val, env)
                    {
                        let family_arg = SemanticCallArg::semantic(family_value);
                        let should_replace =
                            (semantic_call_arg_is_generic_entry_root(&binding.arg, env)
                                && same_family_call_arg_is_more_specific(
                                    &binding.arg,
                                    &family_arg,
                                ))
                                || semantic_call_arg_score(info, val, &family_arg, &expr, env)
                                    > semantic_call_arg_score(info, val, &binding.arg, &expr, env);
                        if should_replace {
                            binding.arg = family_arg;
                        }
                    }
                    if !binding.is_result() && !binding_has_stable_negative_source {
                        improve_call_arg_binding_from_copy_root(
                            info,
                            &mut binding,
                            val,
                            &expr,
                            lower,
                            env,
                        );
                    }
                    args.push((offset, binding, key, addr.display_name()));
                }
                collecting = true;
            }
            SSAOp::IntAdd { .. }
            | SSAOp::IntSub { .. }
            | SSAOp::Copy { .. }
            | SSAOp::Load { .. }
            | SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. }
            | SSAOp::Trunc { .. }
            | SSAOp::Cast { .. }
            | SSAOp::Subpiece { .. } => {
                if !collecting {
                    continue;
                }
            }
            _ => {
                if collecting {
                    break;
                }
            }
        }
    }

    args.sort_by_key(|(offset, _, _, _)| *offset);
    (args, inlined_call_results)
}

fn preserved_input_binding_from_stack_home(
    query: &StackHomeQuery<'_, '_>,
    val: &SSAVar,
    search_limit_idx: usize,
    printf_stack_offset: i64,
) -> Option<CallArgBinding> {
    let (_, load_idx) = producer_entry_for_var(query.producers, val)?;
    let SSAOp::Load {
        space: SpaceId::Ram,
        addr,
        ..
    } = query.ops.get(load_idx)?
    else {
        return None;
    };
    let home_offset =
        call_stack_arg_offset(query.ops, query.producers, query.info, addr, query.env, 0)
            .filter(|offset| *offset >= 0)?;
    let preserved_input = query
        .ops
        .iter()
        .enumerate()
        .take(search_limit_idx)
        .rev()
        .find_map(|(_, op)| match op {
            SSAOp::Store {
                space: SpaceId::Ram,
                addr,
                val,
            } if call_stack_arg_offset(
                query.ops,
                query.producers,
                query.info,
                addr,
                query.env,
                0,
            ) == Some(home_offset) =>
            {
                Some(val.clone())
            }
            _ => None,
        })?;
    let preserved_input_value = exact_call_arg_source_value_id(query.info, &preserved_input)?;
    let expr = visible_call_arg_seed_expr(query.lower, &preserved_input);
    let mut binding = CallArgBinding::input(preferred_stack_input_call_arg(
        query.info,
        &preserved_input,
        &expr,
        query.env,
    ))
    .with_source_var(&preserved_input)
    .with_source_value_id(preserved_input_value)
    .with_stack_offset(printf_stack_offset);
    canonicalize_call_arg_binding_to_negative_stack_load(
        query.info,
        &mut binding,
        Some(&preserved_input),
        preserved_input.size,
    );
    Some(binding)
}

fn duplicate_result_input_binding_from_preserved_stack_home(
    query: &StackHomeQuery<'_, '_>,
    val: &SSAVar,
    result_call_idx: usize,
    printf_stack_offset: i64,
) -> Option<CallArgBinding> {
    preserved_input_binding_from_stack_home(query, val, result_call_idx, printf_stack_offset)
}

fn preferred_stack_input_call_arg(
    info: &UseInfo,
    var: &SSAVar,
    expr: &CExpr,
    env: &PassEnv<'_>,
) -> SemanticCallArg {
    let arg = info
        .semantic_values
        .get(&var.display_name())
        .filter(|value| match value {
            SemanticValue::Load {
                space: SpaceId::Ram,
                addr,
                ..
            }
            | SemanticValue::Address(addr) => {
                normalized_stack_slot_offset(addr).is_some_and(|offset| offset < 0)
            }
            _ => false,
        })
        .cloned()
        .map(SemanticCallArg::semantic)
        .unwrap_or_else(|| semantic_call_arg_for_var(info, var, expr.clone(), env));
    let mut binding = CallArgBinding::input(arg).with_source_var(var);
    canonicalize_call_arg_binding_to_negative_stack_load(info, &mut binding, Some(var), var.size);
    binding.arg
}

fn semantic_call_arg_is_transient_register_fallback(
    arg: &SemanticCallArg,
    env: &PassEnv<'_>,
) -> bool {
    match arg {
        SemanticCallArg::FallbackExpr(CExpr::Var(name)) => {
            let lower = name.to_ascii_lowercase();
            is_call_arg_placeholder_name(&lower)
                || is_call_arg_transient_name(&lower)
                || env.param_register_aliases.contains_key(&lower)
        }
        SemanticCallArg::FallbackExpr(CExpr::Paren(inner))
        | SemanticCallArg::FallbackExpr(CExpr::Cast { expr: inner, .. }) => {
            semantic_call_arg_is_transient_register_fallback(
                &SemanticCallArg::FallbackExpr((**inner).clone()),
                env,
            )
        }
        _ => false,
    }
}

fn improve_call_arg_binding_from_copy_root(
    info: &UseInfo,
    binding: &mut CallArgBinding,
    var: &SSAVar,
    expr: &CExpr,
    lower: &LowerCtx<'_>,
    env: &PassEnv<'_>,
) {
    if binding.is_result() {
        return;
    }

    let key = var.display_name();
    let copy_root = resolve_copy_root_name(info, &key);
    if copy_root == key {
        return;
    }

    let Some(root_var) = ssa_var_from_display_name(&copy_root, var.size) else {
        return;
    };
    if root_var == *var {
        return;
    }

    let root_expr = visible_call_arg_seed_expr(lower, &root_var);
    let root_binding = CallArgBinding::input(semantic_call_arg_for_var(
        info,
        &root_var,
        root_expr.clone(),
        env,
    ));
    let mut root_binding = bind_call_arg_source_var(info, root_binding, &root_var);
    let root_has_stable_negative_source = canonicalize_call_arg_binding_to_negative_stack_load(
        info,
        &mut root_binding,
        Some(&root_var),
        root_var.size,
    )
    .is_some();
    let current_score = semantic_call_arg_score(info, var, &binding.arg, expr, env);
    let root_score = semantic_call_arg_score(info, &root_var, &root_binding.arg, &root_expr, env);
    let current_is_transient = semantic_call_arg_is_transient_register_fallback(&binding.arg, env)
        || semantic_call_arg_is_generic_entry_root(&binding.arg, env);

    if root_has_stable_negative_source
        || (current_is_transient && root_score >= current_score)
        || root_score > current_score
    {
        binding.arg = root_binding.arg;
    }
}

fn visible_call_arg_seed_expr(lower: &LowerCtx<'_>, var: &SSAVar) -> CExpr {
    if var.is_const() {
        return lower.get_expr(var);
    }

    CExpr::Var(lower.var_name(var))
}

fn call_result_expr_for_post_call_source(
    query: &PostCallResultQuery<'_, '_>,
    use_idx: usize,
    var: &SSAVar,
) -> Option<(usize, CExpr)> {
    let ret_family = register_family_name(query.env.ret_reg_name)?;
    let source_var = resolve_post_call_result_source_var_with_facts(
        query.info,
        query.ops,
        query.producers,
        var,
        query.env,
        0,
    )
    .or_else(|| {
        lowered_post_call_result_source_var(
            query.info,
            query.lower,
            query.ops,
            query.producers,
            var,
            query.env,
        )
    })
    .unwrap_or_else(|| var.clone());
    if register_family_name(&source_var.name).as_deref() != Some(ret_family.as_str()) {
        return None;
    }

    let producer_idx = producer_entry_for_var(query.producers, &source_var).map(|(_, idx)| idx);
    if producer_idx.is_some_and(|idx| idx >= use_idx) {
        return None;
    }

    let call_idx = query
        .ops
        .iter()
        .enumerate()
        .take(use_idx)
        .rev()
        .find_map(|(idx, op)| {
            matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }).then_some(idx)
        })?;
    let producer_is_call_define = producer_idx.is_some_and(|idx| {
        matches!(
            query.ops.get(idx),
            Some(SSAOp::CallDefine { dst })
                if register_family_name(&dst.name).as_deref() == Some(ret_family.as_str())
        )
    });
    if producer_is_call_define && !producer_idx.is_some_and(|idx| call_idx < idx && idx < use_idx) {
        return None;
    }
    if producer_idx.is_some_and(|idx| call_idx <= idx) && !producer_is_call_define {
        return None;
    }
    if !producer_is_call_define {
        let allowed_keys = post_call_result_alias_chain_keys_with_facts(
            query.info,
            query.ops,
            query.producers,
            var,
            query.env,
            0,
        );
        if has_intervening_return_family_write(
            query.ops,
            call_idx + 1,
            use_idx,
            ret_family.as_str(),
            &allowed_keys,
        ) {
            return None;
        }
    }

    let call_op = query.ops.get(call_idx)?;
    call_result_expr_for_call_at(
        query.info,
        query.lower,
        query.block_addr,
        call_idx,
        call_op,
        query.env,
    )
    .map(|expr| (call_idx, expr))
}

fn is_post_call_result_alias_for_call(
    query: &PostCallAliasQuery<'_, '_>,
    call_idx: usize,
    use_idx: usize,
    var: &SSAVar,
    ret_family: &str,
) -> bool {
    let Some(source_var) = resolve_post_call_result_source_var_with_facts(
        query.info,
        &query.block.ops,
        query.producers,
        var,
        query.env,
        0,
    ) else {
        return false;
    };
    if register_family_name(&source_var.name).as_deref() != Some(ret_family) {
        return false;
    }
    let source_entry = producer_entry_for_var(query.producers, &source_var);
    let source_is_call_define = matches!(
        source_entry
            .as_ref()
            .and_then(|(_, idx)| query.block.ops.get(*idx)),
        Some(SSAOp::CallDefine { dst })
            if register_family_name(&dst.name).as_deref() == Some(ret_family)
    );
    if source_is_call_define
        && !source_entry
            .as_ref()
            .is_some_and(|(_, source_idx)| call_idx < *source_idx && *source_idx < use_idx)
    {
        return false;
    }
    if source_entry
        .as_ref()
        .is_some_and(|(_, source_idx)| *source_idx >= call_idx)
        && !source_is_call_define
    {
        return false;
    }
    if source_is_call_define {
        true
    } else {
        let allowed_keys = post_call_result_alias_chain_keys_with_facts(
            query.info,
            &query.block.ops,
            query.producers,
            var,
            query.env,
            0,
        );
        !has_intervening_return_family_write(
            &query.block.ops,
            call_idx + 1,
            use_idx,
            ret_family,
            &allowed_keys,
        )
    }
}

fn resolve_post_call_result_source_var(
    ops: &[SSAOp],
    producers: &HashMap<String, usize>,
    var: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<SSAVar> {
    if depth > 8 {
        return None;
    }

    let ret_family = register_family_name(env.ret_reg_name)?;
    if let Some((_, producer_idx)) = producer_entry_for_var(producers, var)
        && let Some(
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::Subpiece { src, .. },
        ) = ops.get(producer_idx)
        && let Some(resolved) =
            resolve_post_call_result_source_var(ops, producers, src, env, depth + 1)
    {
        return Some(resolved);
    }

    (register_family_name(&var.name).as_deref() == Some(ret_family.as_str())).then_some(var.clone())
}

fn semantic_post_call_result_alias_var(info: &UseInfo, var: &SSAVar, depth: u32) -> Option<SSAVar> {
    if depth > 8 {
        return None;
    }

    let key = var.display_name();
    if let Some(source_var) = info
        .forwarded_values
        .get(&key)
        .and_then(|prov| prov.source_var.clone())
        .filter(|source_var| source_var != var)
    {
        return semantic_post_call_result_alias_var(info, &source_var, depth + 1)
            .or(Some(source_var));
    }

    match info.semantic_values.get(&key) {
        Some(SemanticValue::Scalar(ScalarValue::Root(root))) if root.var != *var => {
            semantic_post_call_result_alias_var(info, &root.var, depth + 1)
                .or(Some(root.var.clone()))
        }
        Some(SemanticValue::Scalar(ScalarValue::Expr(expr))) => {
            lowered_var_alias_from_expr(expr, var.size)
                .filter(|alias| alias != var)
                .and_then(|alias| {
                    semantic_post_call_result_alias_var(info, &alias, depth + 1).or(Some(alias))
                })
        }
        _ => None,
    }
}

fn resolve_post_call_result_source_var_with_facts(
    info: &UseInfo,
    ops: &[SSAOp],
    producers: &HashMap<String, usize>,
    var: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<SSAVar> {
    if depth > 8 {
        return None;
    }

    resolve_post_call_result_source_var(ops, producers, var, env, 0).or_else(|| {
        let has_stable_negative_source =
            semantic_value_source_offset_by_name(info, &var.display_name(), 0, &mut HashSet::new())
                .is_some_and(|offset| offset < 0);
        (!has_stable_negative_source)
            .then(|| semantic_post_call_result_alias_var(info, var, depth + 1))
            .flatten()
            .and_then(|alias| {
                resolve_post_call_result_source_var_with_facts(
                    info,
                    ops,
                    producers,
                    &alias,
                    env,
                    depth + 1,
                )
                .or(Some(alias))
            })
    })
}

fn post_call_result_alias_chain_keys(
    ops: &[SSAOp],
    producers: &HashMap<String, usize>,
    var: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> HashSet<String> {
    if depth > 8 {
        return HashSet::from([var.display_name()]);
    }

    let mut keys = HashSet::from([var.display_name()]);
    let Some((_, producer_idx)) = producer_entry_for_var(producers, var) else {
        return keys;
    };

    match ops.get(producer_idx) {
        Some(
            SSAOp::Copy { src, .. }
            | SSAOp::IntZExt { src, .. }
            | SSAOp::IntSExt { src, .. }
            | SSAOp::Trunc { src, .. }
            | SSAOp::Cast { src, .. }
            | SSAOp::Subpiece { src, .. },
        ) => {
            if let Some(ret_family) = register_family_name(env.ret_reg_name)
                && register_family_name(&src.name).as_deref() == Some(ret_family.as_str())
            {
                keys.extend(post_call_result_alias_chain_keys(
                    ops,
                    producers,
                    src,
                    env,
                    depth + 1,
                ));
            }
            keys
        }
        _ => keys,
    }
}

fn post_call_result_alias_chain_keys_with_facts(
    info: &UseInfo,
    ops: &[SSAOp],
    producers: &HashMap<String, usize>,
    var: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> HashSet<String> {
    let mut keys = post_call_result_alias_chain_keys(ops, producers, var, env, 0);
    if depth > 8 {
        return keys;
    }

    if let Some(alias) = semantic_post_call_result_alias_var(info, var, depth + 1)
        && alias.display_name() != var.display_name()
    {
        keys.insert(alias.display_name());
        keys.extend(post_call_result_alias_chain_keys_with_facts(
            info,
            ops,
            producers,
            &alias,
            env,
            depth + 1,
        ));
    }

    keys
}

fn has_intervening_return_family_write(
    ops: &[SSAOp],
    start_idx: usize,
    end_idx: usize,
    ret_family: &str,
    allowed_keys: &HashSet<String>,
) -> bool {
    ops.iter()
        .enumerate()
        .skip(start_idx)
        .take(end_idx.saturating_sub(start_idx))
        .any(|(_, op)| {
            let Some(dst) = op.dst() else {
                return false;
            };
            register_family_name(&dst.name).as_deref() == Some(ret_family)
                && !allowed_keys.contains(&dst.display_name())
        })
}

fn producer_entry_for_var(
    producers: &HashMap<String, usize>,
    var: &SSAVar,
) -> Option<(SSAVar, usize)> {
    let key = var.display_name();
    if let Some(idx) = producers.get(&key).copied() {
        return Some((var.clone(), idx));
    }

    producers.iter().find_map(|(candidate, idx)| {
        candidate.eq_ignore_ascii_case(&key).then(|| {
            (
                ssa_var_from_display_name(candidate, var.size).unwrap_or_else(|| var.clone()),
                *idx,
            )
        })
    })
}

fn lowered_post_call_result_source_var(
    info: &UseInfo,
    lower: &LowerCtx<'_>,
    ops: &[SSAOp],
    producers: &HashMap<String, usize>,
    var: &SSAVar,
    env: &PassEnv<'_>,
) -> Option<SSAVar> {
    lowered_var_alias_from_expr(&lower.expr_for_ssa_name(&var.display_name()), var.size).and_then(
        |alias| {
            resolve_post_call_result_source_var_with_facts(info, ops, producers, &alias, env, 0)
                .or(Some(alias))
        },
    )
}

fn lowered_var_alias_from_expr(expr: &CExpr, default_size: u32) -> Option<SSAVar> {
    match expr {
        CExpr::Var(name) => ssa_var_from_display_name(name, default_size),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            lowered_var_alias_from_expr(inner, default_size)
        }
        _ => None,
    }
}

fn latest_preceding_call_expr(
    query: &PostCallResultQuery<'_, '_>,
    use_idx: usize,
) -> Option<(usize, CExpr)> {
    let (call_idx, call_op) = query
        .ops
        .iter()
        .enumerate()
        .take(use_idx)
        .rev()
        .find(|(_, op)| matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }))?;
    call_result_expr_for_call_at(
        query.info,
        query.lower,
        query.block_addr,
        call_idx,
        call_op,
        query.env,
    )
    .map(|expr| (call_idx, expr))
}

fn merge_arm64_stack_home_call_args(
    args: &mut Vec<CallArgBinding>,
    stack_args: &[(i64, CallArgBinding, String, String)],
    env: &PassEnv<'_>,
) {
    for (idx, (_, stack_arg, _, _)) in stack_args.iter().enumerate() {
        match args.get(idx).cloned() {
            Some(_) if stack_arg.is_result() => {
                args[idx] = stack_arg.clone();
            }
            Some(current)
                if semantic_call_arg_is_generic_entry_root(&current.arg, env)
                    || semantic_call_arg_is_generic_register_root(&current.arg, env)
                    || should_prefer_stack_home_call_arg(&current, stack_arg, env) =>
            {
                args[idx] = stack_arg.clone();
            }
            Some(_) => {}
            None => args.push(stack_arg.clone()),
        }
    }

    while args.len() > stack_args.len() {
        let Some(last) = args.last() else {
            break;
        };
        let is_duplicate_stack_home = stack_args
            .iter()
            .any(|(_, stack_arg, _, _)| stack_arg == last);
        if is_duplicate_stack_home
            || semantic_call_arg_is_generic_entry_root(&last.arg, env)
            || semantic_call_arg_is_generic_register_root(&last.arg, env)
            || semantic_call_arg_is_transient_fallback(&last.arg)
        {
            args.pop();
            continue;
        }
        break;
    }
}

fn call_args_share_semantic_source(
    info: &UseInfo,
    a: &SemanticCallArg,
    b: &SemanticCallArg,
) -> bool {
    let Some(a_offset) = call_arg_semantic_source_offset(info, a, 0, &mut HashSet::new()) else {
        return false;
    };
    let Some(b_offset) = call_arg_semantic_source_offset(info, b, 0, &mut HashSet::new()) else {
        return false;
    };
    a_offset == b_offset
}

fn call_arg_semantic_source_offset(
    info: &UseInfo,
    arg: &SemanticCallArg,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<i64> {
    if depth > 8 {
        return None;
    }

    match arg {
        SemanticCallArg::Semantic(value) => {
            semantic_value_source_offset(info, value, depth + 1, visited)
        }
        SemanticCallArg::FallbackExpr(CExpr::Var(name)) => {
            semantic_value_source_offset_by_name(info, name, depth + 1, visited)
        }
        SemanticCallArg::FallbackExpr(CExpr::Paren(inner))
        | SemanticCallArg::FallbackExpr(CExpr::Cast { expr: inner, .. }) => {
            call_arg_semantic_source_offset(
                info,
                &SemanticCallArg::FallbackExpr((**inner).clone()),
                depth + 1,
                visited,
            )
        }
        _ => None,
    }
}

fn semantic_value_source_offset(
    info: &UseInfo,
    value: &SemanticValue,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<i64> {
    if depth > 8 {
        return None;
    }

    match value {
        SemanticValue::Load {
            space: SpaceId::Ram,
            addr,
            ..
        }
        | SemanticValue::Address(addr) => {
            semantic_addr_source_offset(info, addr, depth + 1, visited)
        }
        SemanticValue::Scalar(ScalarValue::Root(root)) => {
            semantic_value_source_offset_by_name(info, &root.display_name(), depth + 1, visited)
        }
        _ => None,
    }
}

fn semantic_addr_source_offset(
    info: &UseInfo,
    addr: &NormalizedAddr,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<i64> {
    if let Some(offset) = normalized_stack_slot_offset(addr) {
        return Some(offset);
    }

    if addr.index.is_some() {
        return None;
    }

    let BaseRef::Value(root) = &addr.base else {
        return None;
    };

    semantic_value_source_offset_by_name(info, &root.display_name(), depth + 1, visited)
        .and_then(|base| base.checked_add(addr.offset_bytes))
}

fn semantic_value_source_offset_by_name(
    info: &UseInfo,
    name: &str,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<i64> {
    if depth > 8 || !visited.insert(name.to_string()) {
        return None;
    }

    let offset = info
        .semantic_values
        .get(name)
        .and_then(|value| semantic_value_source_offset(info, value, depth + 1, visited))
        .or_else(|| {
            info.forwarded_values
                .get(name)
                .and_then(|prov| prov.stack_slot)
                .filter(|offset| *offset < 0)
        })
        .or_else(|| {
            info.stack_slots
                .get(name)
                .map(|slot| slot.offset)
                .filter(|offset| *offset < 0)
        })
        .or_else(|| {
            info.copy_sources
                .get(name)
                .and_then(|src| semantic_value_source_offset_by_name(info, src, depth + 1, visited))
        })
        .or_else(|| unique_negative_stack_slot_for_stored_value(info, name));
    visited.remove(name);
    offset
}

fn unique_negative_stack_slot_for_stored_value(info: &UseInfo, name: &str) -> Option<i64> {
    let mut matches = info
        .memory_stores
        .iter()
        .filter_map(|(addr_key, stored)| stored.eq_ignore_ascii_case(name).then_some(addr_key))
        .filter_map(|addr_key| addr_key.strip_prefix("stack:"))
        .filter_map(|offset| offset.parse::<i64>().ok())
        .filter(|offset| *offset < 0)
        .collect::<BTreeSet<_>>();

    (matches.len() == 1).then(|| matches.pop_first()).flatten()
}

fn should_prefer_stack_home_call_arg(
    current: &CallArgBinding,
    stack_arg: &CallArgBinding,
    env: &PassEnv<'_>,
) -> bool {
    stack_arg.is_result()
        || (is_plain_scalar_call_arg_candidate(&current.arg)
            && is_structured_call_arg_candidate(&stack_arg.arg))
        || (semantic_call_arg_is_generic_register_root(&current.arg, env)
            && !semantic_call_arg_is_generic_register_root(&stack_arg.arg, env))
        || (semantic_call_arg_is_transient_fallback(&current.arg)
            && !semantic_call_arg_is_transient_fallback(&stack_arg.arg))
}

fn semantic_call_arg_is_transient_fallback(arg: &SemanticCallArg) -> bool {
    match arg {
        SemanticCallArg::FallbackExpr(CExpr::Var(name)) => {
            is_call_arg_transient_name(name) || is_call_arg_placeholder_name(name)
        }
        SemanticCallArg::FallbackExpr(CExpr::Paren(inner))
        | SemanticCallArg::FallbackExpr(CExpr::Cast { expr: inner, .. }) => {
            semantic_call_arg_is_transient_fallback(&SemanticCallArg::FallbackExpr(
                (**inner).clone(),
            ))
        }
        _ => false,
    }
}

fn semantic_call_arg_is_generic_register_root(arg: &SemanticCallArg, env: &PassEnv<'_>) -> bool {
    match arg {
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Root(root))) => env
            .arg_regs
            .iter()
            .any(|reg| root.var.name.eq_ignore_ascii_case(reg)),
        SemanticCallArg::FallbackExpr(CExpr::Var(name)) => ssa_key_parts(name)
            .map(|(base, _)| {
                env.arg_regs
                    .iter()
                    .any(|reg| base.eq_ignore_ascii_case(reg.as_str()))
            })
            .unwrap_or(false),
        SemanticCallArg::FallbackExpr(CExpr::Paren(inner))
        | SemanticCallArg::FallbackExpr(CExpr::Cast { expr: inner, .. }) => {
            semantic_call_arg_is_generic_register_root(
                &SemanticCallArg::FallbackExpr((**inner).clone()),
                env,
            )
        }
        _ => false,
    }
}

fn synthetic_call_home_offset(
    ops: &[SSAOp],
    producers: &HashMap<String, usize>,
    addr: &SSAVar,
    expected_base: &mut Option<String>,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<i64> {
    let (base, offset) = synthetic_call_home_base_and_offset(ops, producers, addr, env, depth)?;
    if let Some(current) = expected_base.as_ref() {
        if current != &base {
            return None;
        }
    } else {
        *expected_base = Some(base);
    }
    Some(offset)
}

fn synthetic_call_home_base_and_offset(
    ops: &[SSAOp],
    producers: &HashMap<String, usize>,
    addr: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<(String, i64)> {
    if depth > 8 || addr.is_const() {
        return None;
    }

    let key = addr.display_name();
    let lower = addr.name.to_ascii_lowercase();
    if lower == env.sp_name || lower == env.fp_name {
        return None;
    }

    let Some(producer_idx) = producers.get(&key) else {
        return is_plausible_call_home_base(&lower, env).then_some((key, 0));
    };

    match &ops[*producer_idx] {
        SSAOp::IntAdd { a, b, .. } => {
            if let Some(offset) = utils::parse_const_offset(b) {
                let (base, base_offset) =
                    synthetic_call_home_base_and_offset(ops, producers, a, env, depth + 1)?;
                return Some((base, base_offset.saturating_add(offset)));
            }
            if let Some(offset) = utils::parse_const_offset(a) {
                let (base, base_offset) =
                    synthetic_call_home_base_and_offset(ops, producers, b, env, depth + 1)?;
                return Some((base, base_offset.saturating_add(offset)));
            }
            None
        }
        SSAOp::IntSub { a, b, .. } => {
            let offset = utils::parse_const_offset(b)?;
            let (base, base_offset) =
                synthetic_call_home_base_and_offset(ops, producers, a, env, depth + 1)?;
            Some((base, base_offset.saturating_sub(offset)))
        }
        SSAOp::Copy { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::Subpiece { src, .. } => {
            synthetic_call_home_base_and_offset(ops, producers, src, env, depth + 1)
        }
        _ => None,
    }
}

fn is_plausible_call_home_base(name: &str, env: &PassEnv<'_>) -> bool {
    if name == env.sp_name || name == env.fp_name {
        return false;
    }

    if env
        .arg_regs
        .iter()
        .any(|reg| name == reg || name == reg.as_str())
    {
        return false;
    }

    utils::is_temporary_name(name)
        || name.starts_with('x')
        || name.starts_with('w')
        || name.starts_with('r')
}

fn semantic_call_arg_for_var(
    info: &UseInfo,
    var: &SSAVar,
    expr: CExpr,
    env: &PassEnv<'_>,
) -> SemanticCallArg {
    let string_addr = semantic_call_arg_string_addr(info, var, &expr, env, 0);
    let preserve_visible_expr_for_string_addr =
        string_addr.is_some() && expr_preserves_pointer_identity_for_call_arg(&expr, env);
    if let Some(value) = preferred_semantic_call_arg_value(info, var, &expr, env) {
        if let Some(addr) = string_addr
            && semantic_call_arg_prefers_string_addr(&value)
            && !preserve_visible_expr_for_string_addr
        {
            return SemanticCallArg::StringAddr(addr);
        }
        if semantic_call_arg_prefers_expr_over_stack_reload(&value, &expr, env) {
            return SemanticCallArg::FallbackExpr(expr);
        }
        return SemanticCallArg::semantic(value);
    }
    if let Some(addr) = string_addr
        && !preserve_visible_expr_for_string_addr
    {
        return SemanticCallArg::StringAddr(addr);
    }
    if var.is_const() {
        return SemanticCallArg::FallbackExpr(expr);
    }
    SemanticCallArg::FallbackExpr(expr)
}

fn expr_preserves_pointer_identity_for_call_arg(expr: &CExpr, env: &PassEnv<'_>) -> bool {
    match expr {
        CExpr::Var(name) => {
            !is_call_arg_placeholder_name(name)
                && !is_call_arg_transient_name(name)
                && !is_call_arg_low_quality_name(name)
                && !is_generic_entry_arg_name(name)
                && !env
                    .param_register_aliases
                    .contains_key(&name.to_ascii_lowercase())
        }
        CExpr::Subscript { .. }
        | CExpr::Member { .. }
        | CExpr::PtrMember { .. }
        | CExpr::Deref(_)
        | CExpr::AddrOf(_) => true,
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            expr_preserves_pointer_identity_for_call_arg(inner, env)
        }
        _ => false,
    }
}

fn semantic_call_arg_prefers_string_addr(value: &SemanticValue) -> bool {
    matches!(value, SemanticValue::Unknown | SemanticValue::Scalar(_))
}

fn preferred_semantic_call_arg_value(
    info: &UseInfo,
    var: &SSAVar,
    expr: &CExpr,
    env: &PassEnv<'_>,
) -> Option<SemanticValue> {
    let mut best = canonical_frame_object_call_arg_value(info, var, expr, env);
    if let Some(value) = info.semantic_values.get(&var.display_name()).cloned() {
        best = preferred_semantic_call_arg_value_candidate(info, var, expr, env, best, value);
    }
    if let Some(value) = info
        .forwarded_values
        .get(&var.display_name())
        .and_then(|prov| semantic_source_value_from_provenance(info, prov, env))
    {
        best = preferred_semantic_call_arg_value_candidate(info, var, expr, env, best, value);
    }
    best
}

fn preferred_semantic_call_arg_value_candidate(
    info: &UseInfo,
    var: &SSAVar,
    expr: &CExpr,
    env: &PassEnv<'_>,
    current: Option<SemanticValue>,
    candidate: SemanticValue,
) -> Option<SemanticValue> {
    if !should_use_semantic_call_arg_value(info, var, &candidate, expr, env) {
        return current;
    }

    match current {
        None => Some(candidate),
        Some(existing) => {
            let current_score = semantic_call_arg_score(
                info,
                var,
                &SemanticCallArg::semantic(existing.clone()),
                expr,
                env,
            );
            let candidate_score = semantic_call_arg_score(
                info,
                var,
                &SemanticCallArg::semantic(candidate.clone()),
                expr,
                env,
            );
            if candidate_score > current_score {
                Some(candidate)
            } else {
                Some(existing)
            }
        }
    }
}

fn semantic_call_arg_prefers_expr_over_stack_reload(
    value: &SemanticValue,
    expr: &CExpr,
    env: &PassEnv<'_>,
) -> bool {
    let Some(addr) = (match value {
        SemanticValue::Address(addr)
        | SemanticValue::Load {
            space: SpaceId::Ram,
            addr,
            ..
        } => Some(addr),
        _ => None,
    }) else {
        return false;
    };

    normalized_stack_slot_offset(addr).is_some()
        && !call_arg_expr_contains_stack_placeholder(expr, 0)
        && !call_arg_expr_contains_transient_name(expr, 0)
        && expr_is_meaningful_stack_reload_fallback(expr, env)
        && call_arg_expr_score(expr, env) > 0
}

fn expr_is_meaningful_stack_reload_fallback(expr: &CExpr, env: &PassEnv<'_>) -> bool {
    match expr {
        CExpr::Var(name) => {
            let lower = name.to_ascii_lowercase();
            !name.eq_ignore_ascii_case("argc")
                && !name.eq_ignore_ascii_case("argv")
                && !name.eq_ignore_ascii_case("envp")
                && !is_call_arg_placeholder_name(&lower)
                && !is_call_arg_transient_name(&lower)
                && !is_call_arg_low_quality_name(&lower)
                && !is_generic_entry_arg_name(&lower)
                && !env.param_register_aliases.contains_key(&lower)
        }
        CExpr::Subscript { .. }
        | CExpr::Member { .. }
        | CExpr::PtrMember { .. }
        | CExpr::StringLit(_)
        | CExpr::Call { .. } => true,
        CExpr::Unary { operand, .. } => expr_is_meaningful_stack_reload_fallback(operand, env),
        CExpr::Binary { left, right, .. } => {
            let left_meaningful = expr_is_meaningful_stack_reload_fallback(left, env);
            let right_meaningful = expr_is_meaningful_stack_reload_fallback(right, env);
            let left_constish = matches!(
                left.as_ref(),
                CExpr::IntLit(_)
                    | CExpr::UIntLit(_)
                    | CExpr::FloatLit(_)
                    | CExpr::CharLit(_)
                    | CExpr::SizeofType(_)
            );
            let right_constish = matches!(
                right.as_ref(),
                CExpr::IntLit(_)
                    | CExpr::UIntLit(_)
                    | CExpr::FloatLit(_)
                    | CExpr::CharLit(_)
                    | CExpr::SizeofType(_)
            );
            (left_meaningful && (right_meaningful || right_constish))
                || (right_meaningful && left_constish)
        }
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            expr_is_meaningful_stack_reload_fallback(inner, env)
        }
        _ => false,
    }
}

fn canonical_frame_object_call_arg_value(
    info: &UseInfo,
    var: &SSAVar,
    expr: &CExpr,
    env: &PassEnv<'_>,
) -> Option<SemanticValue> {
    let direct = semantic_addr_for_var(info, var, env)
        .and_then(|addr| frame_object_field_key(info, &addr, env, 0))
        .and_then(|key| info.frame_object_field_roots.get(&key).cloned());
    let semantic = info
        .semantic_values
        .get(&var.display_name())
        .and_then(|value| match value {
            SemanticValue::Address(addr)
            | SemanticValue::Load {
                space: SpaceId::Ram,
                addr,
                ..
            } => frame_object_field_key(info, addr, env, 0)
                .and_then(|key| info.frame_object_field_roots.get(&key).cloned()),
            SemanticValue::Scalar(ScalarValue::Root(root))
                if root.var != *var
                    && should_use_semantic_call_arg_value(
                        info,
                        var,
                        &SemanticValue::Scalar(ScalarValue::Root(root.clone())),
                        expr,
                        env,
                    ) =>
            {
                Some(SemanticValue::Scalar(ScalarValue::Root(root.clone())))
            }
            _ => None,
        });

    direct
        .into_iter()
        .chain(semantic)
        .find(|value| should_use_semantic_call_arg_value(info, var, value, expr, env))
}

fn should_use_semantic_call_arg_value(
    info: &UseInfo,
    var: &SSAVar,
    value: &SemanticValue,
    expr: &CExpr,
    env: &PassEnv<'_>,
) -> bool {
    match value {
        SemanticValue::Address(_) | SemanticValue::Load { .. } => true,
        SemanticValue::Scalar(ScalarValue::Expr(semantic_expr)) => {
            call_arg_expr_score(semantic_expr, env) >= call_arg_expr_score(expr, env)
        }
        SemanticValue::Scalar(ScalarValue::Root(root)) => {
            let has_stable_negative_stack_source = semantic_value_source_offset_by_name(
                info,
                &root.display_name(),
                0,
                &mut HashSet::new(),
            )
            .is_some_and(|offset| offset < 0);
            root.var != *var
                && (root.var.version == 0
                    || env
                        .param_register_aliases
                        .contains_key(&root.var.name.to_ascii_lowercase())
                    || semantic_var_is_pointer_like(info, &root.var, env)
                    || has_stable_negative_stack_source)
                && !is_call_arg_placeholder_name(&root.var.display_name())
                && (!is_call_arg_transient_name(&root.var.display_name())
                    || has_stable_negative_stack_source)
        }
        SemanticValue::Unknown => false,
    }
}

fn stable_negative_stack_load_size(arg: &SemanticCallArg, default_size: u32) -> u32 {
    match arg {
        SemanticCallArg::Semantic(SemanticValue::Load { size, .. }) if *size > 0 => *size,
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Root(root))) => {
            root.var.size.max(1)
        }
        SemanticCallArg::FallbackExpr(CExpr::Paren(inner))
        | SemanticCallArg::FallbackExpr(CExpr::Cast { expr: inner, .. }) => {
            stable_negative_stack_load_size(
                &SemanticCallArg::FallbackExpr((**inner).clone()),
                default_size,
            )
        }
        SemanticCallArg::FallbackExpr(CExpr::Var(name)) => {
            ssa_var_from_display_name(name, default_size)
                .map(|var| var.size.max(1))
                .unwrap_or(default_size.max(1))
        }
        _ => default_size.max(1),
    }
}

fn exact_negative_stack_offset_for_addr(addr: &NormalizedAddr) -> Option<i64> {
    match addr.base {
        BaseRef::StackSlot(base) if addr.index.is_none() && addr.offset_bytes == 0 && base < 0 => {
            Some(base)
        }
        _ => None,
    }
}

fn exact_negative_stack_offset_for_value(
    info: &UseInfo,
    value: &SemanticValue,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<i64> {
    if depth > 8 {
        return None;
    }

    match value {
        SemanticValue::Load {
            space: SpaceId::Ram,
            addr,
            ..
        }
        | SemanticValue::Address(addr) => exact_negative_stack_offset_for_addr(addr),
        SemanticValue::Scalar(ScalarValue::Root(root)) => {
            exact_negative_stack_offset_by_name(info, &root.display_name(), depth + 1, visited)
        }
        _ => None,
    }
}

fn exact_negative_stack_offset_by_name(
    info: &UseInfo,
    name: &str,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<i64> {
    if depth > 8 || !visited.insert(name.to_string()) {
        return None;
    }

    let offset = info
        .semantic_values
        .get(name)
        .and_then(|value| exact_negative_stack_offset_for_value(info, value, depth + 1, visited))
        .or_else(|| {
            info.forwarded_values
                .get(name)
                .and_then(|prov| prov.stack_slot)
                .filter(|offset| *offset < 0)
        })
        .or_else(|| {
            info.stack_slots
                .get(name)
                .map(|slot| slot.offset)
                .filter(|offset| *offset < 0)
        })
        .or_else(|| {
            info.copy_sources
                .get(name)
                .and_then(|src| exact_negative_stack_offset_by_name(info, src, depth + 1, visited))
        });
    visited.remove(name);
    offset
}

fn exact_negative_stack_offset_for_call_arg(
    info: &UseInfo,
    arg: &SemanticCallArg,
    depth: u32,
    visited: &mut HashSet<String>,
) -> Option<i64> {
    if depth > 8 {
        return None;
    }

    match arg {
        SemanticCallArg::Semantic(value) => {
            exact_negative_stack_offset_for_value(info, value, depth + 1, visited)
        }
        SemanticCallArg::FallbackExpr(CExpr::Var(name)) => {
            exact_negative_stack_offset_by_name(info, name, depth + 1, visited)
        }
        SemanticCallArg::FallbackExpr(CExpr::Paren(inner))
        | SemanticCallArg::FallbackExpr(CExpr::Cast { expr: inner, .. }) => {
            exact_negative_stack_offset_for_call_arg(
                info,
                &SemanticCallArg::FallbackExpr((**inner).clone()),
                depth + 1,
                visited,
            )
        }
        _ => None,
    }
}

fn canonicalize_call_arg_binding_to_negative_stack_load(
    info: &UseInfo,
    binding: &mut CallArgBinding,
    source_var: Option<&SSAVar>,
    default_size: u32,
) -> Option<i64> {
    if binding.is_result() {
        return None;
    }

    let offset =
        exact_negative_stack_offset_for_call_arg(info, &binding.arg, 0, &mut HashSet::new())
            .filter(|offset| *offset < 0)
            .or_else(|| {
                source_var.and_then(|var| {
                    exact_negative_stack_offset_by_name(
                        info,
                        &var.display_name(),
                        0,
                        &mut HashSet::new(),
                    )
                    .filter(|offset| *offset < 0)
                })
            })?;
    let size = source_var
        .map(|var| var.size.max(1))
        .unwrap_or_else(|| stable_negative_stack_load_size(&binding.arg, default_size));
    binding.arg = SemanticCallArg::semantic(SemanticValue::Load {
        space: SpaceId::Ram,
        addr: NormalizedAddr {
            base: BaseRef::StackSlot(offset),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        },
        size,
    });
    Some(offset)
}

fn semantic_call_arg_string_addr(
    info: &UseInfo,
    var: &SSAVar,
    expr: &CExpr,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<u64> {
    let mut visited = BTreeSet::new();
    semantic_call_arg_string_addr_inner(info, var, expr, env, depth, &mut visited)
}

fn semantic_call_arg_string_addr_inner(
    info: &UseInfo,
    var: &SSAVar,
    expr: &CExpr,
    env: &PassEnv<'_>,
    depth: u32,
    visited: &mut BTreeSet<String>,
) -> Option<u64> {
    if depth > 8 {
        return None;
    }

    if let Some(addr) = constish_call_arg_address(expr, env) {
        return Some(addr);
    }

    if let Some(addr) = hex_digit_offset_call_arg_address(expr, env, 0) {
        return Some(addr);
    }

    let key = var.display_name();
    if !visited.insert(key.clone()) {
        return None;
    }

    let resolved = match info.semantic_values.get(&key) {
        Some(SemanticValue::Scalar(ScalarValue::Expr(inner))) => {
            semantic_call_arg_addr_from_expr(info, inner, env, depth + 1, visited)
        }
        Some(SemanticValue::Scalar(ScalarValue::Root(root))) if root.var != *var => {
            let root_key = root.var.display_name();
            let root_expr =
                lookup_call_arg_definition_expr(info, &root_key).unwrap_or_else(|| expr.clone());
            semantic_call_arg_string_addr_inner(
                info,
                &root.var,
                &root_expr,
                env,
                depth + 1,
                visited,
            )
        }
        Some(SemanticValue::Address(NormalizedAddr {
            base: BaseRef::Raw(inner),
            index: None,
            scale_bytes: 0,
            offset_bytes: 0,
        })) => semantic_call_arg_addr_from_expr(info, inner, env, depth + 1, visited),
        _ => None,
    }
    .or_else(|| {
        info.forwarded_values.get(&key).and_then(|prov| {
            prov.source_var.as_ref().and_then(|source_var| {
                let source_expr = lookup_call_arg_definition_expr(info, &source_var.display_name())
                    .unwrap_or_else(|| expr.clone());
                semantic_call_arg_string_addr_inner(
                    info,
                    source_var,
                    &source_expr,
                    env,
                    depth + 1,
                    visited,
                )
            })
        })
    })
    .or_else(|| {
        lookup_call_arg_definition_expr(info, &key).and_then(|inner| {
            semantic_call_arg_addr_from_expr(info, &inner, env, depth + 1, visited)
        })
    });

    visited.remove(&key);
    resolved
}

fn semantic_call_arg_addr_from_expr(
    info: &UseInfo,
    expr: &CExpr,
    env: &PassEnv<'_>,
    depth: u32,
    visited: &mut BTreeSet<String>,
) -> Option<u64> {
    if depth > 8 {
        return None;
    }

    if let Some(addr) = constish_call_arg_address(expr, env) {
        return Some(addr);
    }

    if let Some(addr) = hex_digit_offset_call_arg_address(expr, env, depth) {
        return Some(addr);
    }

    match expr {
        CExpr::Var(name) => {
            if !visited.insert(name.clone()) {
                return None;
            }

            let resolved = lookup_call_arg_definition_expr(info, name)
                .and_then(|inner| {
                    semantic_call_arg_addr_from_expr(info, &inner, env, depth + 1, visited)
                })
                .or_else(|| {
                    lookup_call_arg_semantic_value(info, name).and_then(|value| match value {
                        SemanticValue::Scalar(ScalarValue::Expr(inner)) => {
                            semantic_call_arg_addr_from_expr(info, inner, env, depth + 1, visited)
                        }
                        SemanticValue::Scalar(ScalarValue::Root(root)) => {
                            let root_expr =
                                lookup_call_arg_definition_expr(info, &root.display_name())
                                    .unwrap_or_else(|| CExpr::Var(root.display_name()));
                            semantic_call_arg_string_addr_inner(
                                info,
                                &root.var,
                                &root_expr,
                                env,
                                depth + 1,
                                visited,
                            )
                        }
                        SemanticValue::Address(NormalizedAddr {
                            base: BaseRef::Raw(inner),
                            index: None,
                            scale_bytes: 0,
                            offset_bytes: 0,
                        }) => {
                            semantic_call_arg_addr_from_expr(info, inner, env, depth + 1, visited)
                        }
                        _ => None,
                    })
                })
                .or_else(|| {
                    info.forwarded_values.get(name).and_then(|prov| {
                        prov.source_var.as_ref().and_then(|source_var| {
                            let source_expr =
                                lookup_call_arg_definition_expr(info, &source_var.display_name())
                                    .unwrap_or_else(|| CExpr::Var(source_var.display_name()));
                            semantic_call_arg_string_addr_inner(
                                info,
                                source_var,
                                &source_expr,
                                env,
                                depth + 1,
                                visited,
                            )
                        })
                    })
                });

            visited.remove(name);
            resolved
        }
        CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
            semantic_call_arg_addr_from_expr(info, inner, env, depth + 1, visited)
        }
        CExpr::Cast { expr: inner, .. } => {
            semantic_call_arg_addr_from_expr(info, inner, env, depth + 1, visited)
        }
        CExpr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub,
            ..
        } => constish_call_arg_address(expr, env),
        _ => None,
    }
}

fn lookup_call_arg_semantic_value<'a>(info: &'a UseInfo, name: &str) -> Option<&'a SemanticValue> {
    info.semantic_values
        .get(name)
        .or_else(|| info.semantic_values.get(&name.to_ascii_lowercase()))
        .or_else(|| {
            name.rsplit_once('_').and_then(|(base, version)| {
                info.semantic_values
                    .get(&format!("{}_{}", base.to_ascii_lowercase(), version))
                    .or_else(|| {
                        info.semantic_values.get(&format!(
                            "{}_{}",
                            base.to_ascii_uppercase(),
                            version
                        ))
                    })
            })
        })
}

fn lookup_call_arg_definition_expr(info: &UseInfo, name: &str) -> Option<CExpr> {
    info.definitions
        .get(name)
        .cloned()
        .or_else(|| info.definitions.get(&name.to_ascii_lowercase()).cloned())
        .or_else(|| {
            name.rsplit_once('_').and_then(|(base, version)| {
                info.definitions
                    .get(&format!("{}_{}", base.to_ascii_lowercase(), version))
                    .cloned()
                    .or_else(|| {
                        info.definitions
                            .get(&format!("{}_{}", base.to_ascii_uppercase(), version))
                            .cloned()
                    })
            })
        })
}

fn constish_call_arg_address(_expr: &CExpr, _env: &PassEnv<'_>) -> Option<u64> {
    None
}

fn hex_digit_offset_call_arg_address(expr: &CExpr, env: &PassEnv<'_>, depth: u32) -> Option<u64> {
    if depth > 8 {
        return None;
    }

    let addr = match expr {
        CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
            return hex_digit_offset_call_arg_address(inner, env, depth + 1);
        }
        CExpr::Cast { expr: inner, .. } => {
            return hex_digit_offset_call_arg_address(inner, env, depth + 1);
        }
        CExpr::Binary {
            op: BinaryOp::Add,
            left,
            right,
        } => {
            let base = call_arg_expr_literal_value(left, depth + 1)?;
            let delta = reinterpret_decimal_digits_as_hex_call_arg(right, depth + 1)?;
            base.checked_add(delta)?
        }
        CExpr::Binary {
            op: BinaryOp::Sub,
            left,
            right,
        } => {
            let base = call_arg_expr_literal_value(left, depth + 1)?;
            let delta = reinterpret_decimal_digits_as_hex_call_arg(right, depth + 1)?;
            base.checked_sub(delta)?
        }
        _ => return None,
    };

    let _ = (addr, env);
    None
}

fn reinterpret_decimal_digits_as_hex_call_arg(expr: &CExpr, depth: u32) -> Option<u64> {
    if depth > 8 {
        return None;
    }

    match expr {
        CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
            reinterpret_decimal_digits_as_hex_call_arg(inner, depth + 1)
        }
        CExpr::Cast { expr: inner, .. } => {
            reinterpret_decimal_digits_as_hex_call_arg(inner, depth + 1)
        }
        CExpr::IntLit(value) if *value >= 0 => reinterpret_decimal_digits_as_hex(*value as u64),
        CExpr::UIntLit(value) => reinterpret_decimal_digits_as_hex(*value),
        _ => None,
    }
}

fn reinterpret_decimal_digits_as_hex(value: u64) -> Option<u64> {
    let digits = value.to_string();
    if digits.is_empty() || digits.len() > 4 || !digits.chars().all(|ch| ch.is_ascii_digit()) {
        return None;
    }
    u64::from_str_radix(&digits, 16).ok()
}

fn call_arg_candidate_score(info: &UseInfo, var: &SSAVar, expr: &CExpr, env: &PassEnv<'_>) -> i32 {
    let mut score = call_arg_expr_score(expr, env);
    if semantic_call_arg_string_addr(info, var, expr, env, 0).is_some() {
        score += 200;
    }
    match info.semantic_values.get(&var.display_name()) {
        Some(SemanticValue::Load { .. }) | Some(SemanticValue::Address(_)) => score += 80,
        Some(SemanticValue::Scalar(_)) => score += 40,
        Some(SemanticValue::Unknown) | None => {}
    }
    score
}

fn semantic_call_arg_score(
    info: &UseInfo,
    var: &SSAVar,
    arg: &SemanticCallArg,
    expr: &CExpr,
    env: &PassEnv<'_>,
) -> i32 {
    match arg {
        SemanticCallArg::StringAddr(_) => 300 + call_arg_expr_score(expr, env),
        SemanticCallArg::Semantic(SemanticValue::Load { addr, .. })
        | SemanticCallArg::Semantic(SemanticValue::Address(addr)) => {
            let mut score = 220 + call_arg_expr_score(expr, env);
            if let Some(offset) = normalized_stack_slot_offset(addr) {
                if offset >= 0 {
                    score -= 80;
                } else {
                    score += 20;
                }
            }
            score
        }
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Root(root))) => {
            let mut score = 180 + call_arg_expr_score(expr, env);
            if canonical_frame_object_call_arg_value(info, var, expr, env).is_some() {
                score += 80;
            }
            if root.var.version == 0
                && env
                    .param_register_aliases
                    .contains_key(&root.var.name.to_ascii_lowercase())
            {
                score += 40;
            } else if root.var.version != 0 {
                score += 60;
            }
            score
        }
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Expr(_))) => {
            140 + call_arg_expr_score(expr, env)
        }
        SemanticCallArg::Semantic(SemanticValue::Unknown) => {
            call_arg_candidate_score(info, var, expr, env)
        }
        SemanticCallArg::FallbackExpr(actual_expr) => {
            let mut score = call_arg_candidate_score(info, var, actual_expr, env);
            if matches!(actual_expr, CExpr::Call { .. }) {
                score += 220;
            }
            score
        }
    }
}

fn semantic_call_arg_is_generic_entry_root(arg: &SemanticCallArg, env: &PassEnv<'_>) -> bool {
    match arg {
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Root(root))) => {
            root.var.version == 0
                && env
                    .param_register_aliases
                    .contains_key(&root.var.name.to_ascii_lowercase())
        }
        SemanticCallArg::FallbackExpr(CExpr::Var(name)) => {
            name.eq_ignore_ascii_case("argc")
                || name.eq_ignore_ascii_case("argv")
                || name.eq_ignore_ascii_case("envp")
                || name.strip_prefix("arg").is_some_and(|suffix| {
                    !suffix.is_empty() && suffix.chars().all(|ch| ch.is_ascii_digit())
                })
        }
        SemanticCallArg::FallbackExpr(CExpr::Paren(inner))
        | SemanticCallArg::FallbackExpr(CExpr::Cast { expr: inner, .. }) => {
            semantic_call_arg_is_generic_entry_root(
                &SemanticCallArg::FallbackExpr((**inner).clone()),
                env,
            )
        }
        _ => false,
    }
}

fn same_family_call_arg_is_more_specific(
    current: &SemanticCallArg,
    family: &SemanticCallArg,
) -> bool {
    let family_is_specific = matches!(
        family,
        SemanticCallArg::StringAddr(_)
            | SemanticCallArg::Semantic(SemanticValue::Address(_))
            | SemanticCallArg::Semantic(SemanticValue::Load { .. })
            | SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Expr(_)))
    ) || matches!(
        family,
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Root(root)))
            if root.var.version != 0
    );

    family_is_specific
        && !matches!(
            current,
            SemanticCallArg::StringAddr(_)
                | SemanticCallArg::Semantic(SemanticValue::Address(_))
                | SemanticCallArg::Semantic(SemanticValue::Load { .. })
                | SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Expr(_)))
        )
}

fn should_keep_later_call_arg_candidate(
    current: &SemanticCallArg,
    earlier_candidate: &SemanticCallArg,
) -> bool {
    is_structured_call_arg_candidate(current)
        && is_plain_scalar_call_arg_candidate(earlier_candidate)
}

fn is_plain_scalar_call_arg_candidate(arg: &SemanticCallArg) -> bool {
    matches!(
        arg,
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Expr(
            CExpr::IntLit(_) | CExpr::UIntLit(_) | CExpr::FloatLit(_) | CExpr::CharLit(_)
        ))) | SemanticCallArg::FallbackExpr(
            CExpr::IntLit(_) | CExpr::UIntLit(_) | CExpr::FloatLit(_) | CExpr::CharLit(_)
        )
    )
}

fn is_structured_call_arg_candidate(arg: &SemanticCallArg) -> bool {
    match arg {
        SemanticCallArg::StringAddr(_) => true,
        SemanticCallArg::Semantic(SemanticValue::Address(_))
        | SemanticCallArg::Semantic(SemanticValue::Load { .. }) => true,
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Expr(expr)))
        | SemanticCallArg::FallbackExpr(expr) => !matches!(
            expr,
            CExpr::IntLit(_) | CExpr::UIntLit(_) | CExpr::FloatLit(_) | CExpr::CharLit(_)
        ),
        SemanticCallArg::Semantic(SemanticValue::Scalar(ScalarValue::Root(_)))
        | SemanticCallArg::Semantic(SemanticValue::Unknown) => false,
    }
}

fn call_stack_arg_offset(
    ops: &[SSAOp],
    producers: &HashMap<String, usize>,
    info: &UseInfo,
    addr: &SSAVar,
    env: &PassEnv<'_>,
    depth: u32,
) -> Option<i64> {
    if depth > 8 {
        return None;
    }

    let addr_name = addr.name.to_ascii_lowercase();
    if addr_name == env.sp_name {
        return Some(0);
    }

    if let Some(offset) = stack_slot_offset_for_addr(info, addr, env) {
        return Some(offset);
    }

    if let Some(offset) =
        utils::extract_stack_offset_from_var(addr, &info.definitions, env.fp_name, env.sp_name)
    {
        return Some(offset);
    }

    let producer_idx = producers.get(&addr.display_name())?;
    match &ops[*producer_idx] {
        SSAOp::IntAdd { a, b, .. } => stack_slot_offset_from_add_sub(a, b, false, env),
        SSAOp::IntSub { a, b, .. } => stack_slot_offset_from_add_sub(a, b, true, env),
        SSAOp::Copy { src, .. }
        | SSAOp::IntZExt { src, .. }
        | SSAOp::IntSExt { src, .. }
        | SSAOp::Trunc { src, .. }
        | SSAOp::Cast { src, .. }
        | SSAOp::Subpiece { src, .. } => {
            call_stack_arg_offset(ops, producers, info, src, env, depth + 1)
        }
        _ => None,
    }
}

fn call_arg_expr_score(expr: &CExpr, env: &PassEnv<'_>) -> i32 {
    let mut score = 0;
    if call_arg_expr_resolves_to_literal(expr, env, 0) {
        score += 100;
    }
    score += call_arg_expr_semantic_weight(expr, 0);
    if call_arg_expr_contains_stack_placeholder(expr, 0) {
        score -= 80;
    }
    if call_arg_expr_contains_transient_name(expr, 0) {
        score -= 20;
    }
    if call_arg_expr_contains_low_quality_name(expr, 0) {
        score -= 30;
    }
    score
}

fn call_arg_expr_semantic_weight(expr: &CExpr, depth: u32) -> i32 {
    if depth > 8 {
        return 0;
    }
    match expr {
        CExpr::StringLit(_) => 80,
        CExpr::Subscript { base, index } => {
            40 + call_arg_expr_semantic_weight(base, depth + 1)
                + call_arg_expr_semantic_weight(index, depth + 1)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            45 + call_arg_expr_semantic_weight(base, depth + 1)
        }
        CExpr::Deref(inner) | CExpr::AddrOf(inner) => {
            20 + call_arg_expr_semantic_weight(inner, depth + 1)
        }
        CExpr::Cast { expr: inner, .. } | CExpr::Paren(inner) => {
            call_arg_expr_semantic_weight(inner, depth + 1)
        }
        CExpr::Unary { operand, .. } => call_arg_expr_semantic_weight(operand, depth + 1),
        CExpr::Binary { left, right, .. } => {
            10 + call_arg_expr_semantic_weight(left, depth + 1)
                + call_arg_expr_semantic_weight(right, depth + 1)
        }
        CExpr::Var(name) => {
            if is_call_arg_placeholder_name(name) {
                -20
            } else if is_call_arg_low_quality_name(name) {
                -15
            } else if is_call_arg_transient_name(name) {
                -10
            } else {
                25
            }
        }
        CExpr::Call { func, args } => {
            call_arg_expr_semantic_weight(func, depth + 1)
                + args
                    .iter()
                    .map(|arg| call_arg_expr_semantic_weight(arg, depth + 1))
                    .sum::<i32>()
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            call_arg_expr_semantic_weight(cond, depth + 1)
                + call_arg_expr_semantic_weight(then_expr, depth + 1)
                + call_arg_expr_semantic_weight(else_expr, depth + 1)
        }
        CExpr::Comma(items) => items
            .iter()
            .map(|item| call_arg_expr_semantic_weight(item, depth + 1))
            .sum(),
        CExpr::IntLit(_) | CExpr::UIntLit(_) | CExpr::FloatLit(_) | CExpr::CharLit(_) => 5,
        CExpr::Sizeof(_) | CExpr::SizeofType(_) => 0,
    }
}

fn call_arg_expr_contains_stack_placeholder(expr: &CExpr, depth: u32) -> bool {
    if depth > 8 {
        return false;
    }
    match expr {
        CExpr::Var(name) => is_call_arg_placeholder_name(name),
        CExpr::Deref(inner)
        | CExpr::AddrOf(inner)
        | CExpr::Paren(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::Unary { operand: inner, .. }
        | CExpr::Sizeof(inner) => call_arg_expr_contains_stack_placeholder(inner, depth + 1),
        CExpr::Binary { left, right, .. } => {
            call_arg_expr_contains_stack_placeholder(left, depth + 1)
                || call_arg_expr_contains_stack_placeholder(right, depth + 1)
        }
        CExpr::Subscript { base, index } => {
            call_arg_expr_contains_stack_placeholder(base, depth + 1)
                || call_arg_expr_contains_stack_placeholder(index, depth + 1)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            call_arg_expr_contains_stack_placeholder(base, depth + 1)
        }
        CExpr::Call { func, args } => {
            call_arg_expr_contains_stack_placeholder(func, depth + 1)
                || args
                    .iter()
                    .any(|arg| call_arg_expr_contains_stack_placeholder(arg, depth + 1))
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            call_arg_expr_contains_stack_placeholder(cond, depth + 1)
                || call_arg_expr_contains_stack_placeholder(then_expr, depth + 1)
                || call_arg_expr_contains_stack_placeholder(else_expr, depth + 1)
        }
        CExpr::Comma(items) => items
            .iter()
            .any(|item| call_arg_expr_contains_stack_placeholder(item, depth + 1)),
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_) => false,
    }
}

fn call_arg_expr_contains_transient_name(expr: &CExpr, depth: u32) -> bool {
    if depth > 8 {
        return false;
    }
    match expr {
        CExpr::Var(name) => is_call_arg_transient_name(name),
        CExpr::Deref(inner)
        | CExpr::AddrOf(inner)
        | CExpr::Paren(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::Unary { operand: inner, .. }
        | CExpr::Sizeof(inner) => call_arg_expr_contains_transient_name(inner, depth + 1),
        CExpr::Binary { left, right, .. } => {
            call_arg_expr_contains_transient_name(left, depth + 1)
                || call_arg_expr_contains_transient_name(right, depth + 1)
        }
        CExpr::Subscript { base, index } => {
            call_arg_expr_contains_transient_name(base, depth + 1)
                || call_arg_expr_contains_transient_name(index, depth + 1)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            call_arg_expr_contains_transient_name(base, depth + 1)
        }
        CExpr::Call { func, args } => {
            call_arg_expr_contains_transient_name(func, depth + 1)
                || args
                    .iter()
                    .any(|arg| call_arg_expr_contains_transient_name(arg, depth + 1))
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            call_arg_expr_contains_transient_name(cond, depth + 1)
                || call_arg_expr_contains_transient_name(then_expr, depth + 1)
                || call_arg_expr_contains_transient_name(else_expr, depth + 1)
        }
        CExpr::Comma(items) => items
            .iter()
            .any(|item| call_arg_expr_contains_transient_name(item, depth + 1)),
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_) => false,
    }
}

fn call_arg_expr_contains_low_quality_name(expr: &CExpr, depth: u32) -> bool {
    if depth > 8 {
        return false;
    }
    match expr {
        CExpr::Var(name) => is_call_arg_low_quality_name(name),
        CExpr::Deref(inner)
        | CExpr::AddrOf(inner)
        | CExpr::Paren(inner)
        | CExpr::Cast { expr: inner, .. }
        | CExpr::Unary { operand: inner, .. }
        | CExpr::Sizeof(inner) => call_arg_expr_contains_low_quality_name(inner, depth + 1),
        CExpr::Binary { left, right, .. } => {
            call_arg_expr_contains_low_quality_name(left, depth + 1)
                || call_arg_expr_contains_low_quality_name(right, depth + 1)
        }
        CExpr::Subscript { base, index } => {
            call_arg_expr_contains_low_quality_name(base, depth + 1)
                || call_arg_expr_contains_low_quality_name(index, depth + 1)
        }
        CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
            call_arg_expr_contains_low_quality_name(base, depth + 1)
        }
        CExpr::Call { func, args } => {
            call_arg_expr_contains_low_quality_name(func, depth + 1)
                || args
                    .iter()
                    .any(|arg| call_arg_expr_contains_low_quality_name(arg, depth + 1))
        }
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            call_arg_expr_contains_low_quality_name(cond, depth + 1)
                || call_arg_expr_contains_low_quality_name(then_expr, depth + 1)
                || call_arg_expr_contains_low_quality_name(else_expr, depth + 1)
        }
        CExpr::Comma(items) => items
            .iter()
            .any(|item| call_arg_expr_contains_low_quality_name(item, depth + 1)),
        CExpr::IntLit(_)
        | CExpr::UIntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_) => false,
    }
}

fn call_arg_expr_resolves_to_literal(expr: &CExpr, env: &PassEnv<'_>, depth: u32) -> bool {
    if depth > 8 {
        return false;
    }

    let addr = match expr {
        CExpr::IntLit(value) => (*value >= 0).then_some(*value as u64),
        CExpr::UIntLit(value) => Some(*value),
        CExpr::Paren(inner) | CExpr::AddrOf(inner) => {
            return call_arg_expr_resolves_to_literal(inner, env, depth + 1);
        }
        CExpr::Cast { expr: inner, .. } => {
            return call_arg_expr_resolves_to_literal(inner, env, depth + 1);
        }
        CExpr::Binary {
            op: BinaryOp::Add,
            left,
            right,
        } => match (
            call_arg_expr_literal_value(left, depth + 1),
            call_arg_expr_literal_value(right, depth + 1),
        ) {
            (Some(a), Some(b)) => a.checked_add(b),
            _ => None,
        },
        CExpr::Binary {
            op: BinaryOp::Sub,
            left,
            right,
        } => match (
            call_arg_expr_literal_value(left, depth + 1),
            call_arg_expr_literal_value(right, depth + 1),
        ) {
            (Some(a), Some(b)) => a.checked_sub(b),
            _ => None,
        },
        _ => None,
    };

    let _ = (addr, env);
    false
}

fn call_arg_expr_literal_value(expr: &CExpr, depth: u32) -> Option<u64> {
    if depth > 8 {
        return None;
    }
    match expr {
        CExpr::IntLit(value) => (*value >= 0).then_some(*value as u64),
        CExpr::UIntLit(value) => Some(*value),
        CExpr::Paren(inner) | CExpr::AddrOf(inner) => call_arg_expr_literal_value(inner, depth + 1),
        CExpr::Cast { expr: inner, .. } => call_arg_expr_literal_value(inner, depth + 1),
        CExpr::Binary {
            op: BinaryOp::Add,
            left,
            right,
        } => call_arg_expr_literal_value(left, depth + 1)?
            .checked_add(call_arg_expr_literal_value(right, depth + 1)?),
        CExpr::Binary {
            op: BinaryOp::Sub,
            left,
            right,
        } => call_arg_expr_literal_value(left, depth + 1)?
            .checked_sub(call_arg_expr_literal_value(right, depth + 1)?),
        _ => None,
    }
}

fn is_call_arg_placeholder_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower == "stack" || lower == "saved_fp" || lower.starts_with("stack_")
}

fn is_call_arg_low_quality_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.starts_with("var_")
        || lower == "saved_fp"
        || lower.starts_with("stack_")
        || is_generic_entry_arg_name(&lower)
}

fn is_call_arg_transient_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    utils::is_temporary_constant_or_memory_name(name)
        || utils::is_cpu_flag(&lower)
        || lower.starts_with("eax")
        || lower.starts_with("rax")
        || lower.starts_with("ecx")
        || lower.starts_with("rcx")
        || lower.starts_with("edx")
        || lower.starts_with("rdx")
        || lower.starts_with("esi")
        || lower.starts_with("rsi")
        || lower.starts_with("edi")
        || lower.starts_with("rdi")
        || lower.starts_with('x')
        || lower.starts_with('w')
}

fn is_call_arg_producer(op: &SSAOp) -> bool {
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
            | SSAOp::IntNegate { .. }
            | SSAOp::IntNot { .. }
            | SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. }
            | SSAOp::Trunc { .. }
            | SSAOp::Cast { .. }
            | SSAOp::Piece { .. }
            | SSAOp::Subpiece { .. }
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::CType;
    use r2ssa::{PhiNode, SSAVar};

    fn mk(name: &str, version: u32, size: u32) -> SSAVar {
        SSAVar::new(name, version, size)
    }

    #[derive(Debug)]
    struct TestEnvFixture {
        function_names: HashMap<u64, String>,
        strings: HashMap<u64, String>,
        symbols: HashMap<u64, String>,
        callee_facts: BTreeMap<u64, r2types::CalleeFact>,
        summary_view: Option<r2types::InterprocSummaryView>,
        arg_regs: Vec<String>,
        caller_saved_regs: HashSet<String>,
        type_hints: HashMap<String, CType>,
        param_register_aliases: HashMap<String, String>,
        sp_name: String,
        fp_name: String,
    }

    impl Default for TestEnvFixture {
        fn default() -> Self {
            Self {
                function_names: HashMap::new(),
                strings: HashMap::new(),
                symbols: HashMap::new(),
                callee_facts: BTreeMap::new(),
                summary_view: None,
                arg_regs: Vec::new(),
                caller_saved_regs: HashSet::new(),
                type_hints: HashMap::new(),
                param_register_aliases: HashMap::new(),
                sp_name: "rsp".to_string(),
                fp_name: "rbp".to_string(),
            }
        }
    }

    impl TestEnvFixture {
        fn new() -> Self {
            Self {
                arg_regs: vec![
                    "rdi".to_string(),
                    "rsi".to_string(),
                    "rdx".to_string(),
                    "rcx".to_string(),
                    "r8".to_string(),
                    "r9".to_string(),
                ],
                ..Self::default()
            }
        }

        fn env(&self) -> PassEnv<'_> {
            PassEnv {
                ptr_size: 64,
                sp_name: &self.sp_name,
                fp_name: &self.fp_name,
                ret_reg_name: "rax",
                function_names: &self.function_names,
                strings: &self.strings,
                symbols: &self.symbols,
                callee_facts: &self.callee_facts,
                callee_resolution: None,
                summary_view: self.summary_view.as_ref(),
                arg_regs: &self.arg_regs,
                param_register_aliases: &self.param_register_aliases,
                caller_saved_regs: &self.caller_saved_regs,
                type_hints: &self.type_hints,
                type_oracle: None,
            }
        }
    }

    fn aliases_for(blocks: Vec<SSABlock>) -> HashMap<String, String> {
        let fixture = TestEnvFixture::new();
        analyze(&blocks, &fixture.env()).var_aliases
    }

    fn analyze_info(blocks: Vec<SSABlock>) -> UseInfo {
        let fixture = TestEnvFixture::new();
        analyze(&blocks, &fixture.env())
    }

    #[test]
    fn low_quality_stack_spill_names_do_not_preserve_call_arg_pointer_identity() {
        let fixture = TestEnvFixture::new();
        let env = fixture.env();

        assert!(!expr_preserves_pointer_identity_for_call_arg(
            &CExpr::Var("var_20h".to_string()),
            &env
        ));
        assert!(expr_preserves_pointer_identity_for_call_arg(
            &CExpr::Var("buf".to_string()),
            &env
        ));
    }

    #[test]
    fn call_arg_expr_score_penalizes_low_quality_stack_spills() {
        let fixture = TestEnvFixture::new();
        let env = fixture.env();

        assert!(
            call_arg_expr_score(&CExpr::Var("len".to_string()), &env)
                > call_arg_expr_score(&CExpr::Var("var_20h".to_string()), &env)
        );
    }

    #[test]
    fn value_id_for_var_does_not_use_ambiguous_base_register_versions() {
        let x8_0 = mk("X8", 0, 8);
        let x8_1 = mk("X8", 1, 8);
        let x8_2 = mk("X8", 2, 8);
        let info = analyze_info(vec![single_block(vec![
            SSAOp::Copy {
                dst: x8_1.clone(),
                src: x8_0.clone(),
            },
            SSAOp::Copy {
                dst: x8_2.clone(),
                src: x8_1.clone(),
            },
        ])]);

        let entry_id = info
            .value_id_for_var(&x8_0)
            .expect("entry register value id");
        assert_eq!(info.value_id_for_name("X8"), Some(entry_id));
        assert_eq!(
            info.exact_value_id_for_var(&x8_1),
            info.value_id_for_var(&x8_1)
        );
        assert_eq!(
            info.exact_value_id_for_var(&x8_2),
            info.value_id_for_var(&x8_2)
        );
        assert_ne!(info.value_id_for_var(&x8_1), Some(entry_id));
        assert_ne!(info.value_id_for_var(&x8_2), Some(entry_id));
    }

    #[test]
    fn exact_value_id_binding_does_not_use_colliding_display_names() {
        let mut first = SSAVar::constant(1, 8);
        let mut second = SSAVar::constant(2, 8);
        first.name = "spoofed".to_string();
        second.name = "spoofed".to_string();
        assert_eq!(first.display_name(), second.display_name());
        assert_ne!(
            first, second,
            "semantic constant bits distinguish the values"
        );
        let spoofed_display = first.display_name();

        let mut info = UseInfo::default();
        info.definitions
            .insert(spoofed_display.clone(), CExpr::IntLit(99));
        assert_eq!(info.bind_value_id(&first, ValueId(1)), Some(ValueId(1)));

        assert_eq!(info.value_id_for_var(&second), None);
        info.insert_definition_for_var(&second, CExpr::IntLit(88));
        assert_eq!(info.definition_for_value(ValueId(1)), None);

        let _ = info.bind_value_id(&second, ValueId(2));

        assert_eq!(info.exact_value_id_for_var(&first), Some(ValueId(1)));
        assert_eq!(info.exact_value_id_for_var(&second), Some(ValueId(2)));
        assert_eq!(info.value_id_for_name(&spoofed_display), None);
        assert_eq!(info.definition_for_name(&spoofed_display), None);
        assert_eq!(
            info.render_definition_for_name(&spoofed_display),
            Some(&CExpr::IntLit(88))
        );
        assert_eq!(info.definitions_by_value.get(&ValueId(1)), None);
        assert_eq!(info.definitions_by_value.get(&ValueId(2)), None);
        assert_eq!(info.var_for_value_id(ValueId(1)), Some(&first));
        assert_eq!(info.var_for_value_id(ValueId(2)), Some(&second));

        info.semantic_values
            .insert(spoofed_display, SemanticValue::Unknown);
        rebuild_id_mirrors_from_name_maps(&mut info);
        assert_eq!(info.semantic_values_by_value.get(&ValueId(1)), None);
        assert_eq!(info.semantic_values_by_value.get(&ValueId(2)), None);

        info.insert_definition_for_var(&first, CExpr::IntLit(1));
        info.insert_definition_for_var(&second, CExpr::IntLit(2));
        assert_eq!(
            info.definition_for_value(ValueId(1)),
            Some(&CExpr::IntLit(1))
        );
        assert_eq!(
            info.definition_for_value(ValueId(2)),
            Some(&CExpr::IntLit(2))
        );

        let duplicate = mk("RAX", 0, 8);
        let mut duplicate_info = UseInfo::default();
        assert_eq!(
            duplicate_info.bind_value_id(&duplicate, ValueId(3)),
            Some(ValueId(3))
        );
        duplicate_info.insert_definition_for_var(&duplicate, CExpr::IntLit(3));
        duplicate_info.insert_semantic_value_for_name(
            &duplicate.display_name(),
            SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(3))),
        );
        assert_eq!(duplicate_info.bind_value_id(&duplicate, ValueId(4)), None);
        assert_eq!(duplicate_info.exact_value_id_for_var(&duplicate), None);
        assert_eq!(duplicate_info.value_id_for_var(&duplicate), None);
        assert_eq!(duplicate_info.value_id_for_name("RAX"), None);
        assert_eq!(duplicate_info.value_id_for_name("RAX_0"), None);
        assert_eq!(duplicate_info.var_for_value_id(ValueId(3)), None);
        assert_eq!(duplicate_info.var_for_value_id(ValueId(4)), None);
        assert_eq!(duplicate_info.definition_for_value(ValueId(3)), None);
        assert_eq!(duplicate_info.semantic_value_for_value(ValueId(3)), None);
        assert_eq!(duplicate_info.definition_for_var(&duplicate), None);
        assert_eq!(duplicate_info.semantic_value_for_var(&duplicate), None);

        let shared_left = mk("LEFT", 0, 8);
        let shared_right = mk("RIGHT", 0, 8);
        let mut shared_info = UseInfo::default();
        let _ = shared_info.bind_value_id(&shared_left, ValueId(5));
        let _ = shared_info.bind_value_id(&shared_right, ValueId(5));
        assert_eq!(shared_info.value_id_for_var(&shared_left), None);
        assert_eq!(shared_info.value_id_for_var(&shared_right), None);
        assert_eq!(shared_info.var_for_value_id(ValueId(5)), None);
        shared_info.insert_definition_for_var(&shared_left, CExpr::IntLit(5));
        assert_eq!(shared_info.definitions_by_value.get(&ValueId(5)), None);

        let source = mk("SRC", 1, 8);
        let destination = mk("DST", 1, 8);
        let conflicting_source = mk("OTHER", 1, 8);
        let mut dependency_info = UseInfo::default();
        assert_eq!(
            dependency_info.bind_value_id(&source, ValueId(6)),
            Some(ValueId(6))
        );
        assert_eq!(
            dependency_info.bind_value_id(&destination, ValueId(7)),
            Some(ValueId(7))
        );
        dependency_info
            .copy_sources_by_value
            .insert(ValueId(7), ValueId(6));
        dependency_info.forwarded_values_by_value.insert(
            ValueId(7),
            ValueProvenance {
                source: source.display_name(),
                source_value_id: Some(ValueId(6)),
                source_var: Some(source.clone()),
                stack_slot: None,
            },
        );
        dependency_info.semantic_values_by_value.insert(
            ValueId(7),
            SemanticValue::Scalar(ScalarValue::Root(ValueRef::with_value_id(
                ValueId(6),
                source,
            ))),
        );
        assert_eq!(
            dependency_info.bind_value_id(&conflicting_source, ValueId(6)),
            None
        );
        assert!(dependency_info.copy_sources_by_value.is_empty());
        assert!(dependency_info.forwarded_values_by_value.is_empty());
        assert!(dependency_info.semantic_values_by_value.is_empty());
    }

    fn single_block(ops: Vec<SSAOp>) -> SSABlock {
        SSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops,
        }
    }

    fn minimal_callee_fact(addr: u64, name: &str) -> r2types::CalleeFact {
        minimal_callee_fact_with_linkage(addr, name, r2types::CalleeLinkage::Unknown)
    }

    fn minimal_callee_fact_with_linkage(
        addr: u64,
        name: &str,
        linkage: r2types::CalleeLinkage,
    ) -> r2types::CalleeFact {
        r2types::CalleeFact {
            function_id: addr,
            name: Some(name.to_string()),
            linkage,
            signature: None,
            signature_callconv: None,
            signature_noreturn: false,
            model_policy_evidence: BTreeSet::new(),
            direct_callees: Vec::new(),
            callsite_count: 0,
            has_unknown_calls: false,
            arg_effects: BTreeMap::new(),
            memory_effects: Vec::new(),
            transfer_effects: Vec::new(),
            allocation_effects: Vec::new(),
            lifetime_effects: Vec::new(),
            sync_effects: Vec::new(),
            atomic_effects: Vec::new(),
            param_type_hints: BTreeMap::new(),
            return_type_hint: None,
            return_relation: r2types::CalleeReturnRelation::Unknown,
            reads_global_memory: false,
            writes_global_memory: false,
            touches_unknown_memory: false,
        }
    }

    fn imported_callee_fact(addr: u64, name: &str) -> r2types::CalleeFact {
        minimal_callee_fact_with_linkage(addr, name, r2types::CalleeLinkage::Imported)
    }

    #[test]
    fn call_target_import_policy_uses_typed_callee_identity() {
        let op = SSAOp::Call {
            target: mk("ram:401000", 0, 8),
        };

        for name in ["sym.imp.printf", "imp.printf"] {
            let mut fixture = TestEnvFixture::default();
            fixture.function_names.insert(0x401000, name.to_string());
            let env = fixture.env();
            assert!(
                !call_target_is_imported(0x1000, 0, &op, &env),
                "raw function-name fallback must not own import policy: {name}"
            );
        }
        let mut fixture = TestEnvFixture::default();
        fixture
            .symbols
            .insert(0x401000, "sym.imp.printf".to_string());
        let env = fixture.env();
        assert!(
            !call_target_is_imported(0x1000, 0, &op, &env),
            "raw symbol fallback must not own import policy"
        );

        for name in ["sym.helper", "fcn.401000", "plain_helper"] {
            let mut fixture = TestEnvFixture::default();
            fixture.function_names.insert(0x401000, name.to_string());
            let env = fixture.env();
            assert!(!call_target_is_imported(0x1000, 0, &op, &env), "{name}");
        }

        let mut fixture = TestEnvFixture::default();
        fixture
            .function_names
            .insert(0x401000, "sym.imp.printf".to_string());
        let base_env = fixture.env();
        let empty_resolution = r2types::CalleeResolutionFacts::default();
        let env = PassEnv {
            callee_resolution: Some(&empty_resolution),
            ..base_env
        };
        assert!(
            !call_target_is_imported(0x1000, 0, &op, &env),
            "typed resolution miss must not inherit raw function-name import policy"
        );

        let mut fixture = TestEnvFixture::default();
        fixture
            .symbols
            .insert(0x401000, "sym.imp.printf".to_string());
        let base_env = fixture.env();
        let env = PassEnv {
            callee_resolution: Some(&empty_resolution),
            ..base_env
        };
        assert!(
            !call_target_is_imported(0x1000, 0, &op, &env),
            "typed resolution miss must not inherit raw symbol import policy"
        );

        let fallback_function_names = HashMap::from([(0x401000, "sym.helper".to_string())]);
        let typed_function_names = HashMap::from([(0x401000, "sym.imp.printf".to_string())]);
        let symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_function_signatures = HashMap::new();
        let resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(
                CallsiteKey {
                    block_addr: 0x1000,
                    op_index: 0,
                },
                0x401000,
            )],
            &r2types::CalleeIdentityContext {
                function_names: &typed_function_names,
                symbols: &symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_function_signatures,
            },
        );
        let fixture = TestEnvFixture {
            function_names: fallback_function_names,
            ..TestEnvFixture::default()
        };
        let base_env = fixture.env();
        let env = PassEnv {
            callee_facts: &callee_facts,
            callee_resolution: Some(&resolution),
            ..base_env
        };
        assert!(
            !call_target_is_imported(0x1000, 0, &op, &env),
            "typed function names remain import hints until callee facts certify import linkage"
        );

        let fallback_function_names = HashMap::from([(0x401000, "sym.helper".to_string())]);
        let typed_function_names = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_function_signatures = HashMap::new();
        let resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(
                CallsiteKey {
                    block_addr: 0x1000,
                    op_index: 0,
                },
                0x401000,
            )],
            &r2types::CalleeIdentityContext {
                function_names: &typed_function_names,
                symbols: &symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_function_signatures,
            },
        );
        let fixture = TestEnvFixture {
            function_names: fallback_function_names,
            ..TestEnvFixture::default()
        };
        let base_env = fixture.env();
        let env = PassEnv {
            callee_facts: &callee_facts,
            callee_resolution: Some(&resolution),
            ..base_env
        };
        assert!(
            call_target_is_imported(0x1000, 0, &op, &env),
            "callee facts can certify import policy only through typed resolution"
        );

        let fallback_function_names = HashMap::from([(0x401000, "sym.helper".to_string())]);
        let typed_function_names = HashMap::new();
        let mut modeled_fact = minimal_callee_fact(0x401000, "sym.imp.printf");
        modeled_fact
            .model_policy_evidence
            .insert(r2types::CalleeModelPolicyEvidence::InterprocSummary);
        let callee_facts = BTreeMap::from([(0x401000, modeled_fact)]);
        let known_function_signatures = HashMap::new();
        let resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(
                CallsiteKey {
                    block_addr: 0x1000,
                    op_index: 0,
                },
                0x401000,
            )],
            &r2types::CalleeIdentityContext {
                function_names: &typed_function_names,
                symbols: &symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_function_signatures,
            },
        );
        let fixture = TestEnvFixture {
            function_names: fallback_function_names,
            ..TestEnvFixture::default()
        };
        let base_env = fixture.env();
        let env = PassEnv {
            callee_facts: &callee_facts,
            callee_resolution: Some(&resolution),
            ..base_env
        };
        assert!(
            !call_target_is_imported(0x1000, 0, &op, &env),
            "import-looking callee fact names need explicit import linkage evidence"
        );
        assert!(
            call_target_uses_imported_like_args(0x1000, 0, &op, &env),
            "modeled callee facts use imported-like argument collection without import linkage"
        );

        let fallback_function_names = HashMap::from([(0x401000, "sym.imp.printf".to_string())]);
        let typed_function_names = HashMap::from([(0x401000, "sym.helper".to_string())]);
        let callee_facts = BTreeMap::new();
        let known_function_signatures = HashMap::new();
        let resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(
                CallsiteKey {
                    block_addr: 0x1000,
                    op_index: 0,
                },
                0x401000,
            )],
            &r2types::CalleeIdentityContext {
                function_names: &typed_function_names,
                symbols: &symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_function_signatures,
            },
        );
        let fixture = TestEnvFixture {
            function_names: fallback_function_names,
            ..TestEnvFixture::default()
        };
        let base_env = fixture.env();
        let env = PassEnv {
            callee_facts: &callee_facts,
            callee_resolution: Some(&resolution),
            ..base_env
        };
        assert!(!call_target_is_imported(0x1000, 0, &op, &env));
    }

    #[test]
    fn call_target_import_policy_requires_callsite_resolution_not_raw_direct_address() {
        let op = SSAOp::Call {
            target: mk("ram:402000", 0, 8),
        };
        let function_names = HashMap::new();
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x402000, imported_callee_fact(0x402000, "sym.imp.printf"))]);
        let known_function_signatures = HashMap::new();
        let resolution =
            r2types::CalleeResolutionFacts::from_context(&r2types::CalleeIdentityContext {
                function_names: &function_names,
                symbols: &symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_function_signatures,
            });
        let fixture = TestEnvFixture::default();
        let base_env = fixture.env();
        let env = PassEnv {
            callee_facts: &callee_facts,
            callee_resolution: Some(&resolution),
            ..base_env
        };

        assert!(
            !call_target_is_imported(0x1000, 0, &op, &env),
            "stale direct-address identity must not authorize import policy without a callsite binding"
        );
        assert!(
            !call_target_uses_imported_like_args(0x1000, 0, &op, &env),
            "stale direct-address identity must not authorize imported-like argument collection"
        );
    }

    #[test]
    fn call_target_import_policy_uses_callsite_resolution_over_raw_import_address() {
        let op = SSAOp::Call {
            target: mk("ram:402000", 0, 8),
        };
        let callsite = CallsiteKey {
            block_addr: 0x1000,
            op_index: 0,
        };
        let function_names = HashMap::from([(0x401000, "sym.local_helper".to_string())]);
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x402000, imported_callee_fact(0x402000, "sym.imp.printf"))]);
        let known_function_signatures = HashMap::new();
        let resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(callsite, 0x401000)],
            &r2types::CalleeIdentityContext {
                function_names: &function_names,
                symbols: &symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_function_signatures,
            },
        );
        let fixture = TestEnvFixture::default();
        let base_env = fixture.env();
        let env = PassEnv {
            callee_facts: &callee_facts,
            callee_resolution: Some(&resolution),
            ..base_env
        };

        assert!(
            !call_target_is_imported(0x1000, 0, &op, &env),
            "engine callsite identity should reject import policy when the rendered target names a different imported address"
        );
        assert!(
            !call_target_uses_imported_like_args(0x1000, 0, &op, &env),
            "engine callsite identity should reject imported-like argument collection for a conflicting raw import address"
        );
    }

    #[test]
    fn call_target_import_policy_uses_callsite_resolution_over_raw_local_address() {
        let op = SSAOp::Call {
            target: mk("ram:402000", 0, 8),
        };
        let callsite = CallsiteKey {
            block_addr: 0x1000,
            op_index: 0,
        };
        let function_names = HashMap::from([(0x402000, "sym.local_raw_target".to_string())]);
        let symbols = HashMap::new();
        let callee_facts =
            BTreeMap::from([(0x401000, imported_callee_fact(0x401000, "sym.imp.printf"))]);
        let known_function_signatures = HashMap::new();
        let resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(callsite, 0x401000)],
            &r2types::CalleeIdentityContext {
                function_names: &function_names,
                symbols: &symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_function_signatures,
            },
        );
        let fixture = TestEnvFixture::default();
        let base_env = fixture.env();
        let env = PassEnv {
            callee_facts: &callee_facts,
            callee_resolution: Some(&resolution),
            ..base_env
        };

        assert!(
            call_target_is_imported(0x1000, 0, &op, &env),
            "engine callsite identity should authorize import policy even when the rendered target names a different local address"
        );
        assert!(
            call_target_uses_imported_like_args(0x1000, 0, &op, &env),
            "engine callsite identity should drive imported-like argument collection"
        );
    }

    #[test]
    fn call_target_import_policy_uses_typed_indirect_callsite_identity() {
        let op = SSAOp::CallInd {
            target: mk("X16", 0, 8),
        };
        let callsite = CallsiteKey {
            block_addr: 0x1000,
            op_index: 0,
        };
        let key = r2types::CalleeIdentityKey::IndirectSite(callsite);
        let mut resolution = r2types::CalleeResolutionFacts::default();
        resolution.by_key.insert(
            key.clone(),
            r2types::CalleeIdentity::from_name("sym.imp.printf").with_import_linkage_evidence(),
        );
        resolution.by_callsite.insert(callsite, key);

        let fixture = TestEnvFixture::default();
        let base_env = fixture.env();
        let env = PassEnv {
            callee_resolution: Some(&resolution),
            ..base_env
        };

        assert!(
            call_target_is_imported(0x1000, 0, &op, &env),
            "indirect calls must use typed callsite identity when no address can be parsed"
        );
    }

    #[test]
    fn call_arg_ranking_prefers_literalish_expression_over_stack_placeholder() {
        let mut fixture = TestEnvFixture::default();
        fixture
            .strings
            .insert(0x1000_229e, "Unknown test: %d\\n".to_string());
        let env = fixture.env();
        let literalish = CExpr::binary(
            BinaryOp::Add,
            CExpr::UIntLit(0x1000_2000),
            CExpr::IntLit(0x29e),
        );
        let stacky = CExpr::Deref(Box::new(CExpr::binary(
            BinaryOp::Add,
            CExpr::Var("stack_178".to_string()),
            CExpr::IntLit(160),
        )));

        assert!(
            call_arg_expr_score(&literalish, &env) > call_arg_expr_score(&stacky, &env),
            "literal-capable const-add should outrank stack placeholder chain"
        );
    }

    #[test]
    fn call_arg_collection_includes_immediate_stack_call_args() {
        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string()],
            ..Default::default()
        };

        let sp = mk("SP", 0, 8);
        let x0 = mk("X0", 1, 8);
        let x8 = mk("X8", 1, 8);
        let x9 = mk("X9", 1, 8);
        let arg8 = mk("tmp:arg8", 1, 8);
        let block = single_block(vec![
            SSAOp::Copy {
                dst: x0.clone(),
                src: mk("const:100002000", 0, 8),
            },
            SSAOp::Copy {
                dst: x8.clone(),
                src: mk("W2", 0, 4),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: sp.clone(),
                val: x8.clone(),
            },
            SSAOp::IntAdd {
                dst: arg8.clone(),
                a: sp.clone(),
                b: mk("const:8", 0, 8),
            },
            SSAOp::Copy {
                dst: x9.clone(),
                src: mk("W3", 0, 4),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: arg8.clone(),
                val: x9.clone(),
            },
            SSAOp::Call {
                target: mk("ram:10000259c", 0, 8),
            },
        ]);

        let info = analyze(&[block], &fixture.env());
        let args = info.call_args.get(&(0x1000, 6)).expect("call args");
        assert_eq!(
            args.len(),
            3,
            "x0 plus two stack-spilled call args should be collected"
        );
        assert!(
            args[1] != args[2],
            "stack arg ordering should preserve distinct offsets, got {args:?}"
        );
    }

    #[test]
    fn custom_space_stack_stores_are_not_call_arguments() {
        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string()],
            ..Default::default()
        };

        let sp = mk("SP", 0, 8);
        let x0 = mk("X0", 1, 8);
        let x8 = mk("X8", 1, 8);
        let block = single_block(vec![
            SSAOp::Copy {
                dst: x0,
                src: mk("const:100002000", 0, 8),
            },
            SSAOp::Copy {
                dst: x8.clone(),
                src: mk("W2", 0, 4),
            },
            SSAOp::Store {
                space: SpaceId::Custom(7),
                addr: sp,
                val: x8,
            },
            SSAOp::Call {
                target: mk("ram:10000259c", 0, 8),
            },
        ]);

        let info = analyze(&[block], &fixture.env());
        assert_eq!(
            info.call_args.get(&(0x1000, 3)).map(Vec::len),
            Some(1),
            "only the register argument may remain; Custom-space stack-shaped stores are not ABI stack arguments"
        );
    }

    #[test]
    fn call_arg_collection_tracks_immediate_stack_args_through_copied_stack_base() {
        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string()],
            ..Default::default()
        };

        let sp = mk("SP", 0, 8);
        let x0 = mk("X0", 1, 8);
        let x8 = mk("X8", 1, 8);
        let x9 = mk("X9", 1, 8);
        let sp_alias = mk("tmp:spbase", 1, 8);
        let arg8 = mk("tmp:arg8", 1, 8);
        let block = single_block(vec![
            SSAOp::Copy {
                dst: x0.clone(),
                src: mk("const:100002000", 0, 8),
            },
            SSAOp::Copy {
                dst: sp_alias.clone(),
                src: sp.clone(),
            },
            SSAOp::Copy {
                dst: x8.clone(),
                src: mk("W2", 0, 4),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: sp_alias.clone(),
                val: x8.clone(),
            },
            SSAOp::IntAdd {
                dst: arg8.clone(),
                a: sp_alias,
                b: mk("const:8", 0, 8),
            },
            SSAOp::Copy {
                dst: x9.clone(),
                src: mk("W3", 0, 4),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: arg8,
                val: x9.clone(),
            },
            SSAOp::Call {
                target: mk("ram:10000259c", 0, 8),
            },
        ]);

        let info = analyze(&[block], &fixture.env());
        let args = info.call_args.get(&(0x1000, 7)).expect("call args");
        assert_eq!(
            args.len(),
            3,
            "copied stack-base aliases should still preserve stack-spilled call args"
        );
    }

    #[test]
    fn call_arg_collection_tracks_immediate_stack_args_through_synthetic_call_home_base() {
        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string()],
            ..Default::default()
        };

        let x0 = mk("X0", 1, 8);
        let x8 = mk("X8", 1, 8);
        let x9 = mk("X9", 0, 8);
        let home0 = mk("tmp:home", 1, 8);
        let home8 = mk("tmp:home", 2, 8);
        let block = single_block(vec![
            SSAOp::Copy {
                dst: x8.clone(),
                src: mk("W2", 0, 4),
            },
            SSAOp::Copy {
                dst: home0.clone(),
                src: x9.clone(),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: home0,
                val: x8.clone(),
            },
            SSAOp::IntAdd {
                dst: home8.clone(),
                a: x9,
                b: mk("const:8", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: home8,
                val: x0.clone(),
            },
            SSAOp::Copy {
                dst: x0,
                src: mk("const:100002000", 0, 8),
            },
            SSAOp::Call {
                target: mk("ram:10000259c", 0, 8),
            },
        ]);

        let info = analyze(&[block], &fixture.env());
        let args = info.call_args.get(&(0x1000, 6)).expect("call args");
        assert_eq!(
            args.len(),
            3,
            "synthetic arm64 call-home stores should still materialize variadic call args"
        );
    }

    #[test]
    fn non_imported_arm64_helper_call_prefers_stack_home_args_over_missing_registers() {
        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec![
                "x0".to_string(),
                "x1".to_string(),
                "x2".to_string(),
                "x3".to_string(),
            ],
            ..Default::default()
        };

        let sp = mk("SP", 2, 8);
        let fp = mk("tmp:fpbase", 1, 8);
        let slot_a = mk("tmp:slota", 1, 8);
        let slot_b = mk("tmp:slotb", 1, 8);
        let slot_c = mk("tmp:slotc", 1, 8);
        let val_a = mk("tmp:vala", 1, 4);
        let val_b = mk("tmp:valb", 1, 4);
        let val_c = mk("tmp:valc", 1, 4);
        let arg_a = mk("X8", 30, 8);
        let arg_b = mk("X8", 31, 8);
        let arg_c = mk("X8", 32, 8);
        let home_a = mk("tmp:home", 1, 8);
        let home_b = mk("tmp:home", 2, 8);
        let home_c = mk("tmp:home", 3, 8);
        let x0 = mk("X0", 12, 8);

        let block = single_block(vec![
            SSAOp::IntAdd {
                dst: slot_a.clone(),
                a: fp.clone(),
                b: mk("const:ffffffffffffffd4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_a.clone(),
                val: mk("W0", 15, 4),
            },
            SSAOp::IntAdd {
                dst: slot_b.clone(),
                a: fp.clone(),
                b: mk("const:ffffffffffffffd0", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_b.clone(),
                val: mk("W0", 17, 4),
            },
            SSAOp::IntAdd {
                dst: slot_c.clone(),
                a: fp.clone(),
                b: mk("const:ffffffffffffffcc", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_c.clone(),
                val: mk("W0", 19, 4),
            },
            SSAOp::Load {
                dst: val_a.clone(),
                space: r2il::SpaceId::Ram,
                addr: slot_a,
            },
            SSAOp::IntZExt {
                dst: arg_a.clone(),
                src: val_a,
            },
            SSAOp::IntAdd {
                dst: home_a.clone(),
                a: sp.clone(),
                b: mk("const:150", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: home_a,
                val: arg_a.clone(),
            },
            SSAOp::Load {
                dst: val_b.clone(),
                space: r2il::SpaceId::Ram,
                addr: slot_b,
            },
            SSAOp::IntZExt {
                dst: arg_b.clone(),
                src: val_b,
            },
            SSAOp::IntAdd {
                dst: home_b.clone(),
                a: sp.clone(),
                b: mk("const:158", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: home_b,
                val: arg_b.clone(),
            },
            SSAOp::Load {
                dst: val_c.clone(),
                space: r2il::SpaceId::Ram,
                addr: slot_c,
            },
            SSAOp::IntZExt {
                dst: arg_c.clone(),
                src: val_c,
            },
            SSAOp::IntAdd {
                dst: home_c.clone(),
                a: sp.clone(),
                b: mk("const:160", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: home_c,
                val: arg_c.clone(),
            },
            SSAOp::Copy {
                dst: x0.clone(),
                src: arg_a,
            },
            SSAOp::Call {
                target: mk("ram:1000005d4", 0, 8),
            },
        ]);

        let info = analyze(&[block], &fixture.env());
        let args = info.call_args.get(&(0x1000, 19)).expect("call args");
        assert_eq!(
            args.len(),
            3,
            "non-imported arm64 helper call should use the three stack-home semantic args, got {args:?}"
        );
        assert!(
            !args.iter().any(|binding| {
                semantic_call_arg_is_generic_register_root(&binding.arg, &fixture.env())
            }),
            "helper call args should not fall back to generic register roots, got {args:?}"
        );
    }

    #[test]
    fn imported_call_arg_prefers_forwarded_local_source_over_positive_stack_home_reload() {
        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
            ..Default::default()
        };
        let env = fixture.env();

        let sp = mk("SP", 2, 8);
        let fp = mk("tmp:fpbase", 1, 8);
        let local_slot = mk("tmp:localslot", 1, 8);
        let local_load = mk("tmp:localload", 1, 4);
        let local_arg = mk("X8", 86, 8);
        let home_slot = mk("tmp:home", 1, 8);
        let reloaded_home = mk("X8", 87, 8);

        let info = analyze(
            &[single_block(vec![
                SSAOp::IntAdd {
                    dst: local_slot.clone(),
                    a: fp,
                    b: mk("const:ffffffffffffffa4", 0, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: local_slot.clone(),
                    val: mk("W0", 70, 4),
                },
                SSAOp::Load {
                    dst: local_load.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: local_slot,
                },
                SSAOp::IntZExt {
                    dst: local_arg.clone(),
                    src: local_load,
                },
                SSAOp::IntAdd {
                    dst: home_slot.clone(),
                    a: sp,
                    b: mk("const:148", 0, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: home_slot.clone(),
                    val: local_arg,
                },
                SSAOp::Load {
                    dst: reloaded_home.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: home_slot,
                },
            ])],
            &env,
        );

        let arg = semantic_call_arg_for_var(
            &info,
            &reloaded_home,
            CExpr::Var(reloaded_home.display_name()),
            &env,
        );
        assert!(
            !matches!(
                arg,
                SemanticCallArg::Semantic(SemanticValue::Load { ref addr, .. })
                    | SemanticCallArg::Semantic(SemanticValue::Address(ref addr))
                    if normalized_stack_slot_offset(addr).is_some_and(|offset| offset >= 0)
            ),
            "imported-call arg should not stay pinned to a positive stack-home reload, got {arg:?}"
        );
    }

    #[test]
    fn imported_printf_after_helper_call_keeps_forwarded_local_arg_out_of_positive_stack_home() {
        fn fallback_contains_stack_placeholder(expr: &CExpr) -> bool {
            match expr {
                CExpr::Var(name) => {
                    let lower = name.to_ascii_lowercase();
                    lower == "stack" || lower == "saved_fp" || lower.starts_with("stack_")
                }
                CExpr::Paren(inner)
                | CExpr::AddrOf(inner)
                | CExpr::Deref(inner)
                | CExpr::Sizeof(inner) => fallback_contains_stack_placeholder(inner),
                CExpr::Cast { expr: inner, .. } | CExpr::Unary { operand: inner, .. } => {
                    fallback_contains_stack_placeholder(inner)
                }
                CExpr::Binary { left, right, .. } => {
                    fallback_contains_stack_placeholder(left)
                        || fallback_contains_stack_placeholder(right)
                }
                CExpr::Subscript { base, index } => {
                    fallback_contains_stack_placeholder(base)
                        || fallback_contains_stack_placeholder(index)
                }
                CExpr::Member { base, .. } | CExpr::PtrMember { base, .. } => {
                    fallback_contains_stack_placeholder(base)
                }
                CExpr::Call { func, args } => {
                    fallback_contains_stack_placeholder(func)
                        || args.iter().any(fallback_contains_stack_placeholder)
                }
                CExpr::Ternary {
                    cond,
                    then_expr,
                    else_expr,
                } => {
                    fallback_contains_stack_placeholder(cond)
                        || fallback_contains_stack_placeholder(then_expr)
                        || fallback_contains_stack_placeholder(else_expr)
                }
                CExpr::Comma(items) => items.iter().any(fallback_contains_stack_placeholder),
                CExpr::IntLit(_)
                | CExpr::UIntLit(_)
                | CExpr::FloatLit(_)
                | CExpr::StringLit(_)
                | CExpr::CharLit(_)
                | CExpr::SizeofType(_) => false,
            }
        }

        let mut fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
            ..Default::default()
        };
        fixture
            .function_names
            .insert(0x1000_0259c, "sym.imp.printf".to_string());
        let env = fixture.env();

        let sp = mk("SP", 2, 8);
        let fp = mk("tmp:fpbase", 1, 8);
        let local_slot = mk("tmp:localslot", 1, 8);
        let local_load = mk("tmp:localload", 1, 4);
        let local_arg = mk("X8", 86, 8);
        let preserved_home = mk("tmp:home", 1, 8);
        let reloaded_home = mk("X8", 87, 8);
        let call_home0 = mk("tmp:callhome", 1, 8);
        let call_home1 = mk("tmp:callhome", 2, 8);

        let block = single_block(vec![
            SSAOp::IntAdd {
                dst: local_slot.clone(),
                a: fp,
                b: mk("const:ffffffffffffffa4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: local_slot.clone(),
                val: mk("W0", 70, 4),
            },
            SSAOp::Load {
                dst: local_load.clone(),
                space: r2il::SpaceId::Ram,
                addr: local_slot,
            },
            SSAOp::IntZExt {
                dst: local_arg.clone(),
                src: local_load,
            },
            SSAOp::IntAdd {
                dst: preserved_home.clone(),
                a: sp.clone(),
                b: mk("const:148", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: preserved_home.clone(),
                val: local_arg.clone(),
            },
            SSAOp::Call {
                target: mk("ram:10000081c", 0, 8),
            },
            SSAOp::Load {
                dst: reloaded_home.clone(),
                space: r2il::SpaceId::Ram,
                addr: preserved_home,
            },
            SSAOp::Copy {
                dst: mk("X0", 45, 8),
                src: mk("const:100002292", 0, 8),
            },
            SSAOp::Copy {
                dst: call_home0.clone(),
                src: sp.clone(),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: call_home0,
                val: reloaded_home.clone(),
            },
            SSAOp::IntAdd {
                dst: call_home1.clone(),
                a: sp,
                b: mk("const:8", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: call_home1,
                val: mk("X0", 45, 8),
            },
            SSAOp::Call {
                target: mk("ram:10000259c", 0, 8),
            },
        ]);

        let info = analyze(std::slice::from_ref(&block), &env);
        let lower = LowerCtx {
            use_info: Some(&info),
            definitions: &info.definitions,
            semantic_values: &info.semantic_values,
            use_counts: &info.use_counts,
            condition_vars: &info.condition_vars,
            pinned: &info.pinned,
            var_aliases: &info.var_aliases,
            param_register_aliases: env.param_register_aliases,
            type_hints: &info.type_hints,
            ptr_arith: &info.ptr_arith,
            stack_slots: &info.stack_slots,
            forwarded_values: &info.forwarded_values,
            type_oracle: env.type_oracle,
        };
        let producers = block
            .ops
            .iter()
            .enumerate()
            .filter_map(|(idx, op)| op.dst().map(|dst| (dst.display_name(), idx)))
            .collect::<HashMap<_, _>>();
        let (_, reloaded_home_idx) =
            producer_entry_for_var(&producers, &reloaded_home).expect("reloaded home producer");
        let stack_home_query = StackHomeQuery {
            ops: &block.ops,
            producers: &producers,
            info: &info,
            lower: &lower,
            env: &env,
        };
        let preserved = preserved_input_binding_from_stack_home(
            &stack_home_query,
            &reloaded_home,
            reloaded_home_idx,
            0,
        )
        .expect("preserved stack-home binding");
        let local_arg_name = local_arg.display_name();
        assert_eq!(
            preserved.source_var_name.as_deref(),
            Some(local_arg_name.as_str())
        );
        assert_eq!(
            preserved.source_value_id,
            info.value_id_for_var(&local_arg),
            "stack-home repair candidates must be backed by canonical ValueId provenance"
        );

        let args = info.call_args.get(&(0x1000, 13)).expect("printf args");
        assert!(
            !matches!(
                args.get(1),
                Some(CallArgBinding {
                    arg:
                        SemanticCallArg::Semantic(SemanticValue::Load { addr, .. })
                        | SemanticCallArg::Semantic(SemanticValue::Address(addr)),
                    ..
                }) if normalized_stack_slot_offset(addr).is_some_and(|offset| offset >= 0)
            ),
            "first post-helper printf arg should not regress to a positive stack-home reload, got {args:?}"
        );
        assert!(
            !matches!(
                args.get(1),
                Some(CallArgBinding {
                    arg: SemanticCallArg::FallbackExpr(expr),
                    ..
                })
                    if fallback_contains_stack_placeholder(expr)
            ),
            "first post-helper printf arg should not regress to a stack placeholder fallback, got {args:?}"
        );
        let repaired = args
            .get(1)
            .expect("first post-helper printf arg should stay bound");
        if let Some(source_value_id) = repaired.source_value_id {
            let resolved_name = info
                .display_name_for_value_id(source_value_id)
                .expect("post-helper printf arg ValueId should resolve");
            assert_eq!(
                repaired.source_var_name.as_deref(),
                Some(resolved_name.as_str()),
                "post-helper printf arg source variable and ValueId must agree, binding={repaired:?}"
            );
        }
    }

    #[test]
    fn no_calldefine_arm64_copy_from_w0_binds_to_prior_imported_call_expr() {
        let mut fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
            ..Default::default()
        };
        fixture
            .function_names
            .insert(0x1000025d8, "sym.imp.atoi".to_string());
        fixture
            .param_register_aliases
            .insert("x1".to_string(), "argv".to_string());
        fixture
            .type_hints
            .insert("argv".to_string(), CType::ptr(CType::ptr(CType::Int(8))));
        let callsite = CallsiteKey {
            block_addr: 0x1000,
            op_index: 2,
        };
        let callee_facts = BTreeMap::from([(
            0x1000025d8,
            imported_callee_fact(0x1000025d8, "sym.imp.atoi"),
        )]);
        let symbols = HashMap::new();
        let known_function_signatures = HashMap::new();
        let resolution = r2types::CalleeResolutionFacts::from_direct_call_targets(
            [(callsite, 0x1000025d8)],
            &r2types::CalleeIdentityContext {
                function_names: &fixture.function_names,
                symbols: &symbols,
                callee_facts: &callee_facts,
                known_function_signatures: &known_function_signatures,
            },
        );
        let base_env = fixture.env();
        let env = PassEnv {
            ret_reg_name: "x0",
            callee_facts: &callee_facts,
            callee_resolution: Some(&resolution),
            ..base_env
        };

        let block = single_block(vec![
            SSAOp::IntAdd {
                dst: mk("tmp:argv4", 1, 8),
                a: mk("X1", 0, 8),
                b: mk("const:20", 0, 8),
            },
            SSAOp::Load {
                dst: mk("X0", 10, 8),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:argv4", 1, 8),
            },
            SSAOp::Call {
                target: mk("ram:1000025d8", 0, 8),
            },
            SSAOp::Copy {
                dst: mk("tmp:3a680", 7, 4),
                src: mk("W0", 0, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:6980", 14, 8),
                a: mk("X29", 1, 8),
                b: mk("const:ffffffffffffffcc", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6980", 14, 8),
                val: mk("tmp:3a680", 7, 4),
            },
        ]);

        let info = analyze(&[block], &env);
        assert!(
            matches!(
                info.definitions.get("tmp:3a680_7"),
                Some(CExpr::Call { func, .. }) if **func == CExpr::Var("sym.imp.atoi".to_string())
            ),
            "expected copied W0 temp to bind to the imported call expression, got {:?}",
            info.definitions.get("tmp:3a680_7")
        );
    }

    #[test]
    fn direct_x0_reuse_shape_can_synthesize_helper_call_result_expr() {
        let mut fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec![
                "x0".to_string(),
                "x1".to_string(),
                "x2".to_string(),
                "x3".to_string(),
            ],
            ..Default::default()
        };
        fixture
            .function_names
            .insert(0x1000025d8, "sym.imp.atoi".to_string());
        fixture
            .function_names
            .insert(0x1000005d4, "sym._unlock".to_string());
        fixture
            .param_register_aliases
            .insert("x1".to_string(), "argv".to_string());
        fixture
            .type_hints
            .insert("argv".to_string(), CType::ptr(CType::ptr(CType::Int(8))));
        let base_env = fixture.env();
        let env = PassEnv {
            ret_reg_name: "x0",
            ..base_env
        };

        let block = single_block(vec![
            SSAOp::IntAdd {
                dst: mk("tmp:argv2", 1, 8),
                a: mk("X1", 0, 8),
                b: mk("const:10", 0, 8),
            },
            SSAOp::Load {
                dst: mk("X0", 8, 8),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:argv2", 1, 8),
            },
            SSAOp::Call {
                target: mk("ram:1000025d8", 0, 8),
            },
            SSAOp::Copy {
                dst: mk("tmp:3a680", 5, 4),
                src: mk("W0", 0, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:6980", 12, 8),
                a: mk("X29", 1, 8),
                b: mk("const:ffffffffffffffd4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6980", 12, 8),
                val: mk("tmp:3a680", 5, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:argv3", 1, 8),
                a: mk("X1", 0, 8),
                b: mk("const:18", 0, 8),
            },
            SSAOp::Load {
                dst: mk("X0", 9, 8),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:argv3", 1, 8),
            },
            SSAOp::Call {
                target: mk("ram:1000025d8", 0, 8),
            },
            SSAOp::Copy {
                dst: mk("tmp:3a680", 6, 4),
                src: mk("W0", 0, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:6980", 13, 8),
                a: mk("X29", 1, 8),
                b: mk("const:ffffffffffffffd0", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6980", 13, 8),
                val: mk("tmp:3a680", 6, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:argv4", 1, 8),
                a: mk("X1", 0, 8),
                b: mk("const:20", 0, 8),
            },
            SSAOp::Load {
                dst: mk("X0", 10, 8),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:argv4", 1, 8),
            },
            SSAOp::Call {
                target: mk("ram:1000025d8", 0, 8),
            },
            SSAOp::Copy {
                dst: mk("tmp:3a680", 7, 4),
                src: mk("W0", 0, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:6980", 14, 8),
                a: mk("X29", 1, 8),
                b: mk("const:ffffffffffffffcc", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6980", 14, 8),
                val: mk("tmp:3a680", 7, 4),
            },
            SSAOp::Load {
                dst: mk("tmp:24d00", 8, 4),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6980", 12, 8),
            },
            SSAOp::IntZExt {
                dst: mk("X8", 30, 8),
                src: mk("tmp:24d00", 8, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:6500", 26, 8),
                a: mk("SP", 2, 8),
                b: mk("const:150", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6500", 26, 8),
                val: mk("X8", 30, 8),
            },
            SSAOp::Load {
                dst: mk("tmp:24d00", 9, 4),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6980", 13, 8),
            },
            SSAOp::IntZExt {
                dst: mk("X8", 31, 8),
                src: mk("tmp:24d00", 9, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:6500", 27, 8),
                a: mk("SP", 2, 8),
                b: mk("const:158", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6500", 27, 8),
                val: mk("X8", 31, 8),
            },
            SSAOp::Load {
                dst: mk("tmp:24d00", 10, 4),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6980", 14, 8),
            },
            SSAOp::IntZExt {
                dst: mk("X8", 32, 8),
                src: mk("tmp:24d00", 10, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:6500", 28, 8),
                a: mk("SP", 2, 8),
                b: mk("const:160", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6500", 28, 8),
                val: mk("X8", 32, 8),
            },
            SSAOp::Load {
                dst: mk("tmp:24d00", 11, 4),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6980", 12, 8),
            },
            SSAOp::IntZExt {
                dst: mk("X0", 12, 8),
                src: mk("tmp:24d00", 11, 4),
            },
            SSAOp::Call {
                target: mk("ram:1000005d4", 0, 8),
            },
        ]);

        let info = analyze(std::slice::from_ref(&block), &env);
        let lower = LowerCtx {
            use_info: None,
            definitions: &info.definitions,
            semantic_values: &info.semantic_values,
            use_counts: &info.use_counts,
            condition_vars: &info.condition_vars,
            pinned: &info.pinned,
            var_aliases: &info.var_aliases,
            param_register_aliases: env.param_register_aliases,
            type_hints: &info.type_hints,
            ptr_arith: &info.ptr_arith,
            stack_slots: &info.stack_slots,
            forwarded_values: &info.forwarded_values,
            type_oracle: env.type_oracle,
        };
        let helper_idx = block
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Call { target } if target.display_name() == "ram:1000005d4_0"))
            .expect("helper call idx");
        let expr = call_result_expr_for_call_at(
            &info,
            &lower,
            block.addr,
            helper_idx,
            &block.ops[helper_idx],
            &env,
        );
        assert!(
            expr.is_none(),
            "direct-X0 reuse shape must not synthesize helper call-result expressions without canonical call-result ownership proof, helper args={:?}, x8_32={:?}, load_10={:?}",
            info.call_args.get(&(block.addr, helper_idx)),
            info.semantic_values.get("X8_32"),
            info.semantic_values.get("tmp:24d00_10")
        );
    }

    #[test]
    fn forwards_positive_stack_home_across_a_single_call_boundary() {
        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
            ..Default::default()
        };

        let sp = mk("SP", 2, 8);
        let home = mk("tmp:home", 1, 8);
        let stored = mk("X8", 30, 8);
        let loaded = mk("X11", 2, 8);

        let info = analyze(
            &[single_block(vec![
                SSAOp::IntAdd {
                    dst: home.clone(),
                    a: sp.clone(),
                    b: mk("const:150", 0, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: home.clone(),
                    val: stored.clone(),
                },
                SSAOp::Call {
                    target: mk("ram:1000005d4", 0, 8),
                },
                SSAOp::Load {
                    dst: loaded.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: home,
                },
            ])],
            &fixture.env(),
        );

        assert_eq!(
            info.forwarded_values.get(&loaded.display_name()),
            Some(&ValueProvenance {
                source: stored.display_name(),
                source_value_id: info.value_id_for_var(&stored),
                source_var: Some(stored),
                stack_slot: Some(0x150),
            })
        );
    }

    #[test]
    fn does_not_forward_positive_stack_home_across_multiple_call_boundaries() {
        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "x29".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
            ..Default::default()
        };

        let sp = mk("SP", 2, 8);
        let home = mk("tmp:home", 1, 8);
        let loaded = mk("X11", 2, 8);

        let info = analyze(
            &[single_block(vec![
                SSAOp::IntAdd {
                    dst: home.clone(),
                    a: sp.clone(),
                    b: mk("const:150", 0, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: home.clone(),
                    val: mk("X8", 30, 8),
                },
                SSAOp::Call {
                    target: mk("ram:1000005d4", 0, 8),
                },
                SSAOp::Call {
                    target: mk("ram:10000081c", 0, 8),
                },
                SSAOp::Load {
                    dst: loaded.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: home,
                },
            ])],
            &fixture.env(),
        );

        assert!(
            !info.forwarded_values.contains_key(&loaded.display_name()),
            "positive call-home forwarding should not survive an unrelated second call"
        );
    }

    #[test]
    fn coalesces_non_interfering_register_versions_in_same_block() {
        let edi_0 = mk("EDI", 0, 4);
        let eax_1 = mk("EAX", 1, 4);
        let eax_2 = mk("EAX", 2, 4);
        let ecx_1 = mk("ECX", 1, 4);
        let one = SSAVar::constant(1, 4);

        let block = SSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Copy {
                    dst: eax_1.clone(),
                    src: edi_0,
                },
                SSAOp::Copy {
                    dst: eax_2.clone(),
                    src: eax_1,
                },
                SSAOp::IntAdd {
                    dst: ecx_1.clone(),
                    a: eax_2,
                    b: one,
                },
                SSAOp::Return { target: ecx_1 },
            ],
        };

        let aliases = aliases_for(vec![block]);
        assert_eq!(aliases.get("EAX_1"), Some(&"eax".to_string()));
        assert_eq!(aliases.get("EAX_2"), Some(&"eax".to_string()));
    }

    #[test]
    fn does_not_coalesce_interfering_register_versions() {
        let edi_0 = mk("EDI", 0, 4);
        let eax_1 = mk("EAX", 1, 4);
        let eax_2 = mk("EAX", 2, 4);
        let ecx_1 = mk("ECX", 1, 4);

        let block = SSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Copy {
                    dst: eax_1.clone(),
                    src: edi_0,
                },
                SSAOp::Copy {
                    dst: eax_2.clone(),
                    src: eax_1.clone(),
                },
                SSAOp::IntAdd {
                    dst: ecx_1.clone(),
                    a: eax_1,
                    b: eax_2,
                },
                SSAOp::Return { target: ecx_1 },
            ],
        };

        let aliases = aliases_for(vec![block]);
        assert_ne!(aliases.get("EAX_1"), aliases.get("EAX_2"));
    }

    #[test]
    fn coalesces_phi_connected_non_interfering_register_versions() {
        let eax_1 = mk("EAX", 1, 4);
        let eax_2 = mk("EAX", 2, 4);
        let eax_3 = mk("EAX", 3, 4);
        let edx_1 = mk("EDX", 1, 4);
        let c1 = SSAVar::constant(1, 4);
        let c2 = SSAVar::constant(2, 4);
        let br_target = mk("ram:2000", 0, 8);

        let b1 = SSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Copy {
                    dst: eax_1.clone(),
                    src: c1,
                },
                SSAOp::Branch {
                    target: br_target.clone(),
                },
            ],
        };
        let b2 = SSABlock {
            addr: 0x1100,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Copy {
                    dst: eax_2.clone(),
                    src: c2,
                },
                SSAOp::Branch { target: br_target },
            ],
        };
        let b3 = SSABlock {
            addr: 0x2000,
            size: 4,
            phis: vec![PhiNode {
                dst: eax_3.clone(),
                sources: vec![(0x1000, eax_1), (0x1100, eax_2)],
                canonical_storage: None,
            }],
            ops: vec![
                SSAOp::Copy {
                    dst: edx_1.clone(),
                    src: eax_3,
                },
                SSAOp::Return { target: edx_1 },
            ],
        };

        let aliases = aliases_for(vec![b1, b2, b3]);
        assert_eq!(aliases.get("EAX_1"), Some(&"eax".to_string()));
        assert_eq!(aliases.get("EAX_2"), Some(&"eax".to_string()));
        assert_eq!(aliases.get("EAX_3"), Some(&"eax".to_string()));
    }

    #[test]
    fn semantic_name_filters_use_typed_ssa_storage_and_register_kinds() {
        for name in [
            "tmp:1",
            "TMP:1",
            "const:1",
            "ram:401000",
            "reg:10",
            "space1:20",
        ] {
            assert!(
                is_low_signal_name(name),
                "{name} should be low-signal raw SSA storage/register"
            );
            assert!(
                is_semantic_binding_base(name),
                "{name} should be a semantic binding base"
            );
        }

        assert!(is_low_signal_name("t42"));
        assert!(!is_semantic_binding_base("t42"));
        assert!(is_semantic_binding_base("local_4"));
        assert!(is_semantic_binding_base("arg1"));
        assert!(is_semantic_binding_base("sym.helper"));
        assert!(!is_low_signal_name("value"));
        assert!(!is_semantic_binding_base("value"));
    }

    #[test]
    fn call_arg_name_filters_use_typed_ssa_storage_kinds() {
        let fixture = TestEnvFixture::new();
        let env = fixture.env();

        assert!(is_plausible_call_home_base("tmp:home", &env));
        assert!(is_plausible_call_home_base("TMP:home", &env));
        assert!(is_plausible_call_home_base("x8", &env));
        assert!(is_plausible_call_home_base("r10", &env));
        assert!(!is_plausible_call_home_base("rsp", &env));
        assert!(!is_plausible_call_home_base("rbp", &env));
        assert!(!is_plausible_call_home_base("rdi", &env));

        for name in [
            "tmp:1",
            "TMP:1",
            "const:1",
            "CONST:1",
            "ram:401000",
            "RAM:401000",
        ] {
            assert!(
                is_call_arg_transient_name(name),
                "{name} should be a transient call-argument carrier"
            );
        }

        assert!(is_call_arg_transient_name("rax_1"));
        assert!(is_call_arg_transient_name("x8_0"));
        assert!(!is_call_arg_transient_name("space1:20"));
        assert!(!is_call_arg_transient_name("value"));
    }

    #[test]
    fn call_arg_preservation_score_uses_typed_symbol_and_object_names() {
        assert_eq!(
            call_arg_expr_preservation_score(&CExpr::Var("tmp:1".to_string()), 0),
            -60
        );
        assert_eq!(
            call_arg_expr_preservation_score(&CExpr::Var("sym.helper".to_string()), 0),
            180
        );
        assert_eq!(
            call_arg_expr_preservation_score(&CExpr::Var("obj.global".to_string()), 0),
            180
        );
        assert_eq!(
            call_arg_expr_preservation_score(&CExpr::Var("data.global".to_string()), 0),
            70
        );
        assert_eq!(
            call_arg_expr_preservation_score(&CExpr::Var("got.slot".to_string()), 0),
            70
        );
    }

    #[test]
    fn semantic_source_values_reject_raw_temporary_and_memory_storage_names() {
        let info = UseInfo::default();

        for var in [
            mk("tmp:1", 0, 8),
            mk("ram:401000", 0, 8),
            mk("space1:20", 0, 8),
            mk("stack", 0, 8),
            mk("saved_fp", 0, 8),
            mk("stack_10", 0, 8),
        ] {
            assert_eq!(
                semantic_source_value_for_var(&info, &var),
                None,
                "{} should not become a semantic root",
                var.display_name()
            );
            assert_eq!(
                semantic_or_scalar_source_value(&info, &var.display_name()),
                None,
                "{} should not become a fallback scalar expression",
                var.display_name()
            );
        }

        let ordinary = mk("value", 0, 8);
        assert!(matches!(
            semantic_source_value_for_var(&info, &ordinary),
            Some(SemanticValue::Scalar(ScalarValue::Root(root))) if root.var == ordinary
        ));
        assert!(matches!(
            semantic_or_scalar_source_value(&info, "value_0"),
            Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var(name)))) if name == "value"
        ));
        assert!(matches!(
            semantic_or_scalar_source_value(&info, "const:1_0"),
            Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(1))))
        ));
    }

    #[test]
    fn semantic_source_addresses_recover_stack_slots_without_overriding_scalar_semantics() {
        let fixture = TestEnvFixture::new();
        let env = fixture.env();
        let temp_slot = mk("tmp:slot", 1, 8);
        let alias_slot = mk("alias", 1, 8);
        let mut info = UseInfo::default();
        info.definitions.insert(
            temp_slot.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("rsp_0".to_string()),
                CExpr::IntLit(0x20),
            ),
        );
        info.definitions.insert(
            alias_slot.display_name(),
            CExpr::binary(
                BinaryOp::Add,
                CExpr::Var("rsp_0".to_string()),
                CExpr::IntLit(0x28),
            ),
        );
        info.copy_sources
            .insert(alias_slot.display_name(), "source_1".to_string());

        assert_eq!(
            semantic_addr_for_var_with_depth(&info, &temp_slot, &env, 0),
            Some(NormalizedAddr {
                base: BaseRef::StackSlot(0x20),
                index: None,
                scale_bytes: 0,
                offset_bytes: 0,
            })
        );
        assert_eq!(
            semantic_addr_for_var_with_depth(&info, &alias_slot, &env, 0),
            Some(NormalizedAddr {
                base: BaseRef::StackSlot(0x28),
                index: None,
                scale_bytes: 0,
                offset_bytes: 0,
            })
        );

        info.semantic_values.insert(
            temp_slot.display_name(),
            SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var("semantic".to_string()))),
        );
        assert!(matches!(
            semantic_addr_for_var_with_depth(&info, &temp_slot, &env, 0),
            Some(NormalizedAddr {
                base: BaseRef::Raw(_),
                index: None,
                scale_bytes: 0,
                offset_bytes: 0,
            })
        ));
    }

    #[test]
    fn excludes_sp_fp_and_semantic_names_from_coalescing() {
        let rsp_0 = mk("RSP", 0, 8);
        let rsp_1 = mk("RSP", 1, 8);
        let local_4_0 = mk("local_4", 0, 8);
        let local_4_1 = mk("local_4", 1, 8);
        let rax_1 = mk("RAX", 1, 8);
        let rax_2 = mk("RAX", 2, 8);
        let one = SSAVar::constant(1, 8);

        let block = SSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Copy {
                    dst: rsp_1.clone(),
                    src: rsp_0,
                },
                SSAOp::Copy {
                    dst: local_4_1.clone(),
                    src: local_4_0,
                },
                SSAOp::Copy {
                    dst: rax_1.clone(),
                    src: one.clone(),
                },
                SSAOp::Copy {
                    dst: rax_2.clone(),
                    src: rax_1,
                },
                SSAOp::Return { target: rax_2 },
            ],
        };

        let aliases = aliases_for(vec![block]);
        assert!(!aliases.contains_key(&rsp_1.display_name()));
        assert!(!aliases.contains_key(&local_4_1.display_name()));
        assert_eq!(aliases.get("RAX_1"), Some(&"rax".to_string()));
    }

    #[test]
    fn formatted_defs_keep_latest_ssa_version_for_colliding_visible_name() {
        let eax_1 = mk("EAX", 1, 4);
        let eax_2 = mk("EAX", 2, 4);
        let block = SSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::Copy {
                    dst: eax_1.clone(),
                    src: SSAVar::constant(1, 4),
                },
                SSAOp::Copy {
                    dst: eax_2.clone(),
                    src: SSAVar::constant(2, 4),
                },
                SSAOp::Return { target: eax_2 },
            ],
        };

        let info = analyze_info(vec![block]);
        assert_eq!(info.var_aliases.get("EAX_1"), Some(&"eax".to_string()));
        assert_eq!(info.var_aliases.get("EAX_2"), Some(&"eax".to_string()));
        assert_eq!(info.formatted_defs.get("eax"), Some(&CExpr::IntLit(2)));
    }

    #[test]
    fn alias_class_sort_key_uses_lex_smallest_member_as_final_tiebreaker() {
        let versions = HashMap::from([
            ("eax_beta_7".to_string(), 7),
            ("eax_gamma_7".to_string(), 7),
            ("eax_alpha_7".to_string(), 7),
            ("eax_delta_7".to_string(), 7),
        ]);
        let left = vec!["eax_beta_7".to_string(), "eax_gamma_7".to_string()];
        let right = vec!["eax_alpha_7".to_string(), "eax_delta_7".to_string()];

        assert!(alias_class_sort_key(&right, &versions) < alias_class_sort_key(&left, &versions));
    }

    #[test]
    fn forwards_same_slot_stack_store_and_load_within_block() {
        let rbp_1 = mk("RBP", 1, 8);
        let addr = mk("tmp:stackaddr", 1, 8);
        let stored = mk("ESI", 0, 4);
        let loaded = mk("tmp:load", 1, 4);

        let info = analyze_info(vec![single_block(vec![
            SSAOp::IntAdd {
                dst: addr.clone(),
                a: rbp_1,
                b: SSAVar::constant(0xffff_ffff_ffff_fff4, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: addr.clone(),
                val: stored.clone(),
            },
            SSAOp::Load {
                dst: loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr,
            },
        ])]);

        assert_eq!(
            info.forwarded_values.get(&loaded.display_name()),
            Some(&ValueProvenance {
                source: stored.display_name(),
                source_value_id: info.value_id_for_var(&stored),
                source_var: Some(stored.clone()),
                stack_slot: Some(-12),
            })
        );
    }

    #[test]
    fn stack_store_load_forwarding_is_ram_only() {
        let rbp = mk("RBP", 1, 8);
        let addr = mk("tmp:stackaddr", 1, 8);
        let stored = mk("ESI", 0, 4);
        let custom_loaded = mk("tmp:custom_load", 1, 4);
        let ram_loaded = mk("tmp:ram_load", 1, 4);

        let info = analyze_info(vec![single_block(vec![
            SSAOp::IntAdd {
                dst: addr.clone(),
                a: rbp,
                b: SSAVar::constant(0xffff_ffff_ffff_fff4, 8),
            },
            SSAOp::Store {
                space: SpaceId::Ram,
                addr: addr.clone(),
                val: stored.clone(),
            },
            SSAOp::Load {
                dst: custom_loaded.clone(),
                space: SpaceId::Custom(7),
                addr: addr.clone(),
            },
            SSAOp::Load {
                dst: ram_loaded.clone(),
                space: SpaceId::Ram,
                addr,
            },
        ])]);

        assert!(
            !info
                .forwarded_values
                .contains_key(&custom_loaded.display_name()),
            "Custom-space loads must not reuse Ram stack state"
        );
        assert_eq!(
            info.forwarded_values
                .get(&ram_loaded.display_name())
                .and_then(|provenance| provenance.source_var.as_ref()),
            Some(&stored),
            "the exact Ram store/load pair should still forward"
        );
    }

    #[test]
    fn generic_memory_forwarding_is_keyed_by_exact_space() {
        let mut fixture = TestEnvFixture::new();
        fixture
            .param_register_aliases
            .insert("rdi".to_string(), "arg1".to_string());
        fixture
            .type_hints
            .insert("arg1".to_string(), CType::ptr(CType::u8()));
        let base = mk("RDI", 0, 8);
        let addr = mk("tmp:addr", 1, 8);
        let ram_loaded = mk("tmp:ram_load", 1, 4);
        let custom_loaded = mk("tmp:custom_load", 1, 4);

        let ram_only = analyze(
            &[single_block(vec![
                SSAOp::IntAdd {
                    dst: addr.clone(),
                    a: base.clone(),
                    b: SSAVar::constant(0, 8),
                },
                SSAOp::Store {
                    space: SpaceId::Ram,
                    addr: addr.clone(),
                    val: SSAVar::constant(0x11, 4),
                },
                SSAOp::Load {
                    dst: custom_loaded.clone(),
                    space: SpaceId::Custom(7),
                    addr: addr.clone(),
                },
                SSAOp::Load {
                    dst: ram_loaded.clone(),
                    space: SpaceId::Ram,
                    addr: addr.clone(),
                },
            ])],
            &fixture.env(),
        );
        assert!(
            matches!(
                ram_only.semantic_values.get(&ram_loaded.display_name()),
                Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(
                    0x11
                ))))
            ),
            "Ram semantic={:?}, stable={:?}",
            ram_only.semantic_values.get(&ram_loaded.display_name()),
            ram_only.stable_memory_values
        );
        assert!(!matches!(
            ram_only.semantic_values.get(&custom_loaded.display_name()),
            Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(
                0x11
            ))))
        ));

        let custom_only = analyze(
            &[single_block(vec![
                SSAOp::IntAdd {
                    dst: addr.clone(),
                    a: base,
                    b: SSAVar::constant(0, 8),
                },
                SSAOp::Store {
                    space: SpaceId::Custom(7),
                    addr: addr.clone(),
                    val: SSAVar::constant(0x22, 4),
                },
                SSAOp::Load {
                    dst: custom_loaded.clone(),
                    space: SpaceId::Custom(7),
                    addr,
                },
            ])],
            &fixture.env(),
        );
        assert!(matches!(
            custom_only
                .semantic_values
                .get(&custom_loaded.display_name()),
            Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(
                0x22
            ))))
        ));
    }

    #[test]
    fn formatted_defs_prefer_semantic_expr_over_register_artifact() {
        let fixture = TestEnvFixture::new();
        let mut scratch = UseScratch::default();
        scratch
            .info
            .var_aliases
            .insert("tmp:pick_1".to_string(), "picked".to_string());
        scratch
            .info
            .var_aliases
            .insert("tmp:pick_2".to_string(), "picked".to_string());
        scratch
            .info
            .definitions
            .insert("tmp:pick_1".to_string(), CExpr::Var("rdx_2".to_string()));
        scratch.info.definitions.insert(
            "tmp:pick_2".to_string(),
            CExpr::Subscript {
                base: Box::new(CExpr::cast(
                    CType::ptr(CType::u32()),
                    CExpr::Var("arr".to_string()),
                )),
                index: Box::new(CExpr::Var("idx".to_string())),
            },
        );

        build_formatted_defs(&mut scratch, &fixture.env());

        assert!(
            matches!(
                scratch.info.formatted_defs.get("picked"),
                Some(CExpr::Subscript { .. })
            ),
            "formatted defs should keep the stronger semantic expression when aliases collide"
        );
    }

    #[test]
    fn unknown_store_blocks_stack_forwarding() {
        let rbp_1 = mk("RBP", 1, 8);
        let slot_addr = mk("tmp:slotaddr", 1, 8);
        let unknown_addr = mk("RAX", 1, 8);
        let stored = mk("ESI", 0, 4);
        let loaded = mk("tmp:load", 1, 4);

        let info = analyze_info(vec![single_block(vec![
            SSAOp::IntAdd {
                dst: slot_addr.clone(),
                a: rbp_1,
                b: SSAVar::constant(0xffff_ffff_ffff_fff4, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_addr.clone(),
                val: stored,
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: unknown_addr,
                val: SSAVar::constant(0x41, 1),
            },
            SSAOp::Load {
                dst: loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr: slot_addr,
            },
        ])]);

        assert!(
            !info.forwarded_values.contains_key(&loaded.display_name()),
            "unknown memory stores must invalidate same-slot forwarding"
        );
    }

    #[test]
    fn does_not_forward_stack_values_across_block_boundaries() {
        let rbp_1 = mk("RBP", 1, 8);
        let slot_addr_1 = mk("tmp:slotaddr", 1, 8);
        let slot_addr_2 = mk("tmp:slotaddr", 2, 8);
        let stored = mk("ESI", 0, 4);
        let loaded = mk("tmp:load", 1, 4);

        let info = analyze_info(vec![
            single_block(vec![
                SSAOp::IntAdd {
                    dst: slot_addr_1.clone(),
                    a: rbp_1.clone(),
                    b: SSAVar::constant(0xffff_ffff_ffff_fff4, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: slot_addr_1,
                    val: stored,
                },
            ]),
            SSABlock {
                addr: 0x1100,
                size: 4,
                phis: Vec::new(),
                ops: vec![
                    SSAOp::IntAdd {
                        dst: slot_addr_2.clone(),
                        a: rbp_1,
                        b: SSAVar::constant(0xffff_ffff_ffff_fff4, 8),
                    },
                    SSAOp::Load {
                        dst: loaded.clone(),
                        space: r2il::SpaceId::Ram,
                        addr: slot_addr_2,
                    },
                ],
            },
        ]);

        assert!(
            !info.forwarded_values.contains_key(&loaded.display_name()),
            "forwarding should stay block-local unless dominance is proven explicitly"
        );
    }

    #[test]
    fn semantic_values_capture_ptr_add_load_shape() {
        let arr = mk("RDI", 0, 8);
        let idx = mk("ESI", 0, 4);
        let addr = mk("tmp:ptr", 1, 8);
        let loaded = mk("tmp:load", 1, 4);

        let info = analyze_info(vec![single_block(vec![
            SSAOp::PtrAdd {
                dst: addr.clone(),
                base: arr.clone(),
                index: idx.clone(),
                element_size: 4,
            },
            SSAOp::Load {
                dst: loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr: addr.clone(),
            },
        ])]);

        assert!(matches!(
            info.semantic_values.get(&addr.display_name()),
            Some(SemanticValue::Address(NormalizedAddr {
                index: Some(index),
                scale_bytes: 4,
                offset_bytes: 0,
                ..
            })) if index.var == idx
        ));
        assert!(matches!(
            info.semantic_values.get(&loaded.display_name()),
            Some(SemanticValue::Load {
                space: SpaceId::Ram,
                addr: NormalizedAddr {
                    index: Some(index),
                    scale_bytes: 4,
                    offset_bytes: 0,
                    ..
                },
                size: 4,
            }) if index.var == idx
        ));
    }

    #[test]
    fn semantic_load_shape_preserves_exact_memory_space() {
        let semantic_space = |space| {
            let addr = mk("tmp:ptr", 1, 8);
            let loaded = mk("tmp:load", 1, 4);
            let info = analyze_info(vec![single_block(vec![
                SSAOp::PtrAdd {
                    dst: addr.clone(),
                    base: mk("RDI", 0, 8),
                    index: mk("ESI", 0, 4),
                    element_size: 4,
                },
                SSAOp::Load {
                    dst: loaded.clone(),
                    space,
                    addr,
                },
            ])]);
            match info.semantic_values.get(&loaded.display_name()) {
                Some(SemanticValue::Load { space, .. }) => *space,
                other => panic!("expected semantic load, got {other:?}"),
            }
        };

        assert_eq!(semantic_space(SpaceId::Ram), SpaceId::Ram);
        assert_eq!(semantic_space(SpaceId::Custom(7)), SpaceId::Custom(7));
    }

    #[test]
    fn semantic_values_propagate_copies_of_memory_values() {
        let arr = mk("RDI", 0, 8);
        let idx = mk("ESI", 0, 4);
        let addr = mk("tmp:ptr", 1, 8);
        let loaded = mk("tmp:load", 1, 4);
        let copied = mk("tmp:copy", 1, 4);

        let info = analyze_info(vec![single_block(vec![
            SSAOp::PtrAdd {
                dst: addr.clone(),
                base: arr,
                index: idx,
                element_size: 4,
            },
            SSAOp::Load {
                dst: loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr,
            },
            SSAOp::Copy {
                dst: copied.clone(),
                src: loaded.clone(),
            },
        ])]);

        assert_eq!(
            info.semantic_values.get(&copied.display_name()),
            info.semantic_values.get(&loaded.display_name())
        );
    }

    #[test]
    fn semantic_values_keep_indexed_load_shape_through_stack_reload_and_return_copy_chain() {
        let rbp = mk("RBP", 1, 8);
        let arr = mk("RDI", 0, 8);
        let idx = mk("ESI", 0, 4);
        let arr_slot = mk("tmp:arrslot", 1, 8);
        let idx_slot = mk("tmp:idxslot", 1, 8);
        let idx_slot_reload = mk("tmp:idxslot", 2, 8);
        let arr_slot_reload = mk("tmp:arrslot", 2, 8);
        let idx_loaded = mk("tmp:idxload", 1, 4);
        let idx_ext = mk("RAX", 1, 8);
        let scaled = mk("tmp:scaled", 1, 8);
        let arr_loaded = mk("tmp:arrload", 1, 8);
        let arr_copy = mk("RDX", 1, 8);
        let addr = mk("tmp:addr", 1, 8);
        let loaded = mk("tmp:load", 1, 4);
        let ret = mk("EAX", 1, 4);

        let info = analyze_info(vec![single_block(vec![
            SSAOp::IntAdd {
                dst: arr_slot.clone(),
                a: rbp.clone(),
                b: SSAVar::constant(0xffff_ffff_ffff_fff8, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: arr_slot,
                val: arr.clone(),
            },
            SSAOp::IntAdd {
                dst: idx_slot.clone(),
                a: rbp.clone(),
                b: SSAVar::constant(0xffff_ffff_ffff_fff4, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: idx_slot,
                val: idx.clone(),
            },
            SSAOp::IntAdd {
                dst: idx_slot_reload.clone(),
                a: rbp.clone(),
                b: SSAVar::constant(0xffff_ffff_ffff_fff4, 8),
            },
            SSAOp::Load {
                dst: idx_loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr: idx_slot_reload,
            },
            SSAOp::IntSExt {
                dst: idx_ext.clone(),
                src: idx_loaded.clone(),
            },
            SSAOp::IntMult {
                dst: scaled.clone(),
                a: idx_ext,
                b: SSAVar::constant(4, 8),
            },
            SSAOp::IntAdd {
                dst: arr_slot_reload.clone(),
                a: rbp,
                b: SSAVar::constant(0xffff_ffff_ffff_fff8, 8),
            },
            SSAOp::Load {
                dst: arr_loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr: arr_slot_reload,
            },
            SSAOp::Copy {
                dst: arr_copy.clone(),
                src: arr_loaded,
            },
            SSAOp::IntAdd {
                dst: addr.clone(),
                a: arr_copy,
                b: scaled,
            },
            SSAOp::Load {
                dst: loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr,
            },
            SSAOp::Copy {
                dst: ret.clone(),
                src: loaded.clone(),
            },
        ])]);

        let idx_semantic = info.semantic_values.get(&idx_loaded.display_name());
        assert!(
            match idx_semantic {
                Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::Var(name)))) => {
                    name != "stack" && name != "saved_fp" && !name.starts_with("local_")
                }
                Some(SemanticValue::Scalar(ScalarValue::Root(value_ref))) => {
                    !value_ref.var.name_kind().is_temporary()
                        && !value_ref.var.name.eq_ignore_ascii_case("stack")
                        && !value_ref.var.name.eq_ignore_ascii_case("saved_fp")
                }
                _ => false,
            },
            "stack-reloaded scalar index should stay a semantic scalar, got {idx_semantic:?}"
        );
        assert!(
            matches!(
                info.semantic_values.get(&loaded.display_name()),
                Some(SemanticValue::Load {
                    space: SpaceId::Ram,
                    addr: NormalizedAddr {
                        index: Some(index),
                        scale_bytes: 4,
                        offset_bytes: 0,
                        ..
                    },
                    size: 4,
                }) if index.var == idx_loaded
            ),
            "final loaded value should keep indexed-load semantics through stack reloads"
        );
        assert_eq!(
            info.semantic_values.get(&ret.display_name()),
            info.semantic_values.get(&loaded.display_name()),
            "return-register copy should preserve the indexed-load semantic value"
        );
    }

    #[test]
    fn semantic_pointer_likeness_uses_param_alias_type_hints() {
        let mut fixture = TestEnvFixture::new();
        fixture
            .param_register_aliases
            .insert("x0".to_string(), "arg1".to_string());
        fixture
            .type_hints
            .insert("arg1".to_string(), CType::ptr(CType::u32()));
        let env = fixture.env();
        let x0 = mk("X0", 0, 8);

        assert!(
            semantic_var_is_pointer_like(&UseInfo::default(), &x0, &env),
            "entry-register aliases should participate in pointer-like detection"
        );
    }

    #[test]
    fn semantic_addr_prefers_forwarded_pointer_source_over_stack_slot_identity() {
        let mut fixture = TestEnvFixture::new();
        fixture
            .param_register_aliases
            .insert("x0".to_string(), "arg1".to_string());
        fixture
            .type_hints
            .insert("arg1".to_string(), CType::ptr(CType::u32()));
        let env = fixture.env();
        let mut info = UseInfo::default();
        let loaded = mk("X9", 1, 8);
        let src = mk("X0", 0, 8);

        info.stack_slots
            .insert(loaded.display_name(), StackSlotProvenance::new(8));
        info.forwarded_values.insert(
            loaded.display_name(),
            ValueProvenance {
                source: src.display_name(),
                source_value_id: None,
                source_var: Some(src.clone()),
                stack_slot: Some(8),
            },
        );

        assert!(matches!(
            semantic_addr_for_var(&info, &loaded, &env),
            Some(NormalizedAddr {
                base: BaseRef::Value(value_ref),
                index: None,
                scale_bytes: 0,
                offset_bytes: 0,
            }) if value_ref.var == src
        ));
    }

    #[test]
    fn semantic_values_keep_live_arm64_struct_array_base_root_through_stack_reload() {
        let mut fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "fp".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
            ..Default::default()
        };
        fixture
            .param_register_aliases
            .insert("x0".to_string(), "arg1".to_string());
        fixture
            .param_register_aliases
            .insert("x1".to_string(), "arg2".to_string());
        fixture
            .type_hints
            .insert("arg1".to_string(), CType::ptr(CType::u32()));
        fixture
            .type_hints
            .insert("arg2".to_string(), CType::Int(32));
        let env = fixture.env();

        let sp0 = mk("SP", 0, 8);
        let sp1 = mk("SP", 1, 8);
        let x0 = mk("X0", 0, 8);
        let w1 = mk("W1", 0, 4);
        let w2 = mk("W2", 0, 4);
        let stack_ptr = mk("tmp:6500", 1, 8);
        let idx_ptr = mk("tmp:6400", 1, 8);
        let reloaded_base_addr = mk("tmp:6500", 2, 8);
        let reloaded_idx_addr = mk("tmp:6400", 2, 8);
        let reloaded_base = mk("X9", 1, 8);
        let reloaded_idx = mk("tmp:26b00", 1, 4);
        let sext_idx = mk("X10", 1, 8);
        let scaled_idx = mk("X10", 2, 8);
        let addr_sum = mk("tmp:12480", 1, 8);
        let copied_addr = mk("X9", 2, 8);
        let field_addr = mk("tmp:6400", 3, 8);

        let block = single_block(vec![
            SSAOp::IntSub {
                dst: sp1.clone(),
                a: sp0,
                b: SSAVar::constant(0x10, 8),
            },
            SSAOp::IntAdd {
                dst: stack_ptr.clone(),
                a: sp1.clone(),
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: stack_ptr,
                val: x0.clone(),
            },
            SSAOp::IntAdd {
                dst: idx_ptr.clone(),
                a: sp1.clone(),
                b: SSAVar::constant(4, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: idx_ptr,
                val: w1.clone(),
            },
            SSAOp::IntAdd {
                dst: reloaded_base_addr.clone(),
                a: sp1.clone(),
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Load {
                dst: reloaded_base.clone(),
                space: r2il::SpaceId::Ram,
                addr: reloaded_base_addr,
            },
            SSAOp::IntAdd {
                dst: reloaded_idx_addr.clone(),
                a: sp1,
                b: SSAVar::constant(4, 8),
            },
            SSAOp::Load {
                dst: reloaded_idx.clone(),
                space: r2il::SpaceId::Ram,
                addr: reloaded_idx_addr,
            },
            SSAOp::IntSExt {
                dst: sext_idx.clone(),
                src: reloaded_idx,
            },
            SSAOp::IntMult {
                dst: scaled_idx.clone(),
                a: sext_idx,
                b: SSAVar::constant(0x38, 8),
            },
            SSAOp::IntAdd {
                dst: addr_sum.clone(),
                a: reloaded_base.clone(),
                b: scaled_idx,
            },
            SSAOp::Copy {
                dst: copied_addr.clone(),
                src: addr_sum.clone(),
            },
            SSAOp::IntAdd {
                dst: field_addr.clone(),
                a: copied_addr,
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: field_addr.clone(),
                val: w2,
            },
        ]);

        let info = analyze(&[block], &env);

        assert!(
            matches!(
                info.semantic_values.get(&reloaded_base.display_name()),
                Some(SemanticValue::Address(NormalizedAddr {
                    base: BaseRef::Value(value_ref),
                    index: None,
                    scale_bytes: 0,
                    offset_bytes: 0,
                })) if value_ref.var == x0
            ),
            "reloaded base semantic value = {:?}, forwarded = {:?}",
            info.semantic_values.get(&reloaded_base.display_name()),
            info.forwarded_values.get(&reloaded_base.display_name())
        );

        assert!(
            matches!(
                info.semantic_values.get(&field_addr.display_name()),
                Some(SemanticValue::Address(NormalizedAddr {
                    base: BaseRef::Value(value_ref),
                    index: Some(_),
                    scale_bytes: 0x38,
                    offset_bytes: 8,
                })) if value_ref.var == x0
            ),
            "field addr semantic value = {:?}",
            info.semantic_values.get(&field_addr.display_name())
        );
    }

    #[test]
    fn stable_entry_stack_values_preserve_masked_x86_struct_array_index_root() {
        let mut fixture = TestEnvFixture::new();
        fixture
            .param_register_aliases
            .insert("rdi".to_string(), "arr".to_string());
        fixture.type_hints.insert(
            "arr".to_string(),
            CType::ptr(CType::Struct("DemoStruct".to_string())),
        );
        let env = fixture.env();

        let rsp0 = mk("RSP", 0, 8);
        let rsp1 = mk("RSP", 1, 8);
        let rbp0 = mk("RBP", 0, 8);
        let rbp1 = mk("RBP", 1, 8);
        let rdi0 = mk("RDI", 0, 8);
        let esi0 = mk("ESI", 0, 4);
        let edx0 = mk("EDX", 0, 4);
        let slot_arr = mk("tmp:4700", 1, 8);
        let slot_idx = mk("tmp:4700", 2, 8);
        let slot_val = mk("tmp:4700", 3, 8);
        let reloaded_idx = mk("tmp:11f00", 1, 4);
        let sext_idx = mk("RDX", 1, 8);
        let shift_1 = mk("tmp:6a800", 1, 8);
        let scaled_1 = mk("RAX", 3, 8);
        let scaled_2 = mk("RAX", 4, 8);
        let shift_2 = mk("tmp:6a800", 2, 8);
        let scaled_3 = mk("RAX", 5, 8);
        let reloaded_arr = mk("tmp:11f80", 1, 8);
        let indexed_base = mk("RDX", 3, 8);
        let field_addr = mk("tmp:4700", 7, 8);

        let block = single_block(vec![
            SSAOp::IntSub {
                dst: rsp1.clone(),
                a: rsp0,
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: rsp1.clone(),
                val: rbp0,
            },
            SSAOp::Copy {
                dst: rbp1.clone(),
                src: rsp1.clone(),
            },
            SSAOp::IntAdd {
                dst: slot_arr.clone(),
                a: rbp1.clone(),
                b: mk("const:fffffffffffffff8", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_arr.clone(),
                val: rdi0.clone(),
            },
            SSAOp::IntAdd {
                dst: slot_idx.clone(),
                a: rbp1.clone(),
                b: mk("const:fffffffffffffff4", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_idx.clone(),
                val: esi0,
            },
            SSAOp::IntAdd {
                dst: slot_val.clone(),
                a: rbp1,
                b: mk("const:fffffffffffffff0", 0, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_val,
                val: edx0,
            },
            SSAOp::Load {
                dst: reloaded_idx.clone(),
                space: r2il::SpaceId::Ram,
                addr: slot_idx,
            },
            SSAOp::IntSExt {
                dst: sext_idx.clone(),
                src: reloaded_idx,
            },
            SSAOp::IntAnd {
                dst: shift_1.clone(),
                a: mk("const:3", 0, 8),
                b: mk("const:63", 0, 8),
            },
            SSAOp::IntLeft {
                dst: scaled_1.clone(),
                a: sext_idx.clone(),
                b: shift_1,
            },
            SSAOp::IntSub {
                dst: scaled_2.clone(),
                a: scaled_1,
                b: sext_idx,
            },
            SSAOp::IntAnd {
                dst: shift_2.clone(),
                a: mk("const:3", 0, 8),
                b: mk("const:63", 0, 8),
            },
            SSAOp::IntLeft {
                dst: scaled_3.clone(),
                a: scaled_2,
                b: shift_2,
            },
            SSAOp::Load {
                dst: reloaded_arr.clone(),
                space: r2il::SpaceId::Ram,
                addr: slot_arr,
            },
            SSAOp::IntAdd {
                dst: indexed_base.clone(),
                a: scaled_3,
                b: reloaded_arr,
            },
            SSAOp::IntAdd {
                dst: field_addr.clone(),
                a: indexed_base,
                b: SSAVar::constant(8, 8),
            },
        ]);

        let info = analyze(&[block], &env);

        assert!(
            matches!(
                info.semantic_values.get(&field_addr.display_name()),
                Some(SemanticValue::Address(NormalizedAddr {
                    base: BaseRef::Value(value_ref),
                    index: Some(_),
                    scale_bytes: 0x38,
                    offset_bytes: 8,
                })) if value_ref.var == rdi0
            ),
            "masked x86 struct-array field addr semantic value = {:?}",
            info.semantic_values.get(&field_addr.display_name())
        );
    }

    #[test]
    fn stable_entry_stack_values_preserve_live_arm64_main_atoi_root_across_blocks() {
        let mut fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "fp".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
            ..Default::default()
        };
        fixture
            .param_register_aliases
            .insert("x1".to_string(), "arg2".to_string());
        fixture
            .type_hints
            .insert("arg2".to_string(), CType::ptr(CType::ptr(CType::Int(8))));
        let env = fixture.env();

        let sp0 = mk("SP", 0, 8);
        let sp1 = mk("SP", 1, 8);
        let frame_base = mk("X8", 1, 8);
        let slot_178 = mk("tmp:slot", 1, 8);
        let slot_argv = mk("tmp:slot", 2, 8);
        let entry = SSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntSub {
                    dst: sp1.clone(),
                    a: sp0,
                    b: SSAVar::constant(0x10, 8),
                },
                SSAOp::IntAdd {
                    dst: frame_base.clone(),
                    a: sp1.clone(),
                    b: SSAVar::constant(0x3e0, 8),
                },
                SSAOp::IntAdd {
                    dst: slot_178.clone(),
                    a: sp1.clone(),
                    b: SSAVar::constant(0x178, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: slot_178,
                    val: frame_base.clone(),
                },
                SSAOp::IntAdd {
                    dst: slot_argv.clone(),
                    a: frame_base,
                    b: SSAVar::constant(160, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: slot_argv,
                    val: mk("X1", 0, 8),
                },
            ],
        };

        let reload_slot = mk("tmp:slot", 3, 8);
        let reloaded_frame = mk("X8", 9, 8);
        let argv_addr = mk("tmp:slot", 4, 8);
        let argv_root = mk("X8", 10, 8);
        let arg_addr = mk("tmp:slot", 5, 8);
        let arg_value = mk("X0", 5, 8);
        let reload = SSABlock {
            addr: 0x1010,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: reload_slot.clone(),
                    a: sp1.clone(),
                    b: SSAVar::constant(0x178, 8),
                },
                SSAOp::Load {
                    dst: reloaded_frame.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: reload_slot,
                },
                SSAOp::IntAdd {
                    dst: argv_addr.clone(),
                    a: reloaded_frame,
                    b: SSAVar::constant(160, 8),
                },
                SSAOp::Load {
                    dst: argv_root.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: argv_addr,
                },
                SSAOp::IntAdd {
                    dst: arg_addr.clone(),
                    a: argv_root.clone(),
                    b: SSAVar::constant(8, 8),
                },
                SSAOp::Load {
                    dst: arg_value.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: arg_addr,
                },
            ],
        };

        let info = analyze(&[entry, reload], &env);

        let argv_semantic = info.semantic_values.get(&argv_root.display_name());
        assert!(
            matches!(
                argv_semantic,
                Some(SemanticValue::Address(NormalizedAddr {
                    base: BaseRef::Value(value_ref),
                    index: None,
                    scale_bytes: 0,
                    offset_bytes: 0,
                })) if value_ref.var == mk("X1", 0, 8)
            ),
            "expected argv root to stay semantic across blocks, got {argv_semantic:?}"
        );
        let loaded = info.semantic_values.get(&arg_value.display_name());
        assert!(
            matches!(
                loaded,
                Some(SemanticValue::Load {
                    space: SpaceId::Ram,
                    addr: NormalizedAddr {
                        base: BaseRef::Value(value_ref),
                        ..
                    },
                    ..
                }) if value_ref.var == mk("X1", 0, 8) || value_ref.var == argv_root
            ),
            "expected final imported-call arg load to keep the semantic argv root, got {loaded:?}"
        );
    }

    #[test]
    fn frame_object_field_roots_survive_flat_stack_slot_conflicts() {
        let mut fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "fp".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
            ..Default::default()
        };
        fixture
            .param_register_aliases
            .insert("x1".to_string(), "arg2".to_string());
        fixture
            .type_hints
            .insert("arg2".to_string(), CType::ptr(CType::ptr(CType::Int(8))));
        let env = fixture.env();

        let sp0 = mk("SP", 0, 8);
        let sp1 = mk("SP", 1, 8);
        let frame_base = mk("X8", 1, 8);
        let slot_frame = mk("tmp:slot", 1, 8);
        let slot_argv = mk("tmp:slot", 2, 8);
        let entry = SSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntSub {
                    dst: sp1.clone(),
                    a: sp0,
                    b: SSAVar::constant(0x10, 8),
                },
                SSAOp::IntAdd {
                    dst: frame_base.clone(),
                    a: sp1.clone(),
                    b: SSAVar::constant(0x3e0, 8),
                },
                SSAOp::IntAdd {
                    dst: slot_frame.clone(),
                    a: sp1.clone(),
                    b: SSAVar::constant(0x178, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: slot_frame,
                    val: frame_base.clone(),
                },
                SSAOp::IntAdd {
                    dst: slot_argv.clone(),
                    a: frame_base,
                    b: SSAVar::constant(160, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: slot_argv,
                    val: mk("X1", 0, 8),
                },
            ],
        };

        let conflict_slot = mk("tmp:slot", 3, 8);
        let conflict = SSABlock {
            addr: 0x1008,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: conflict_slot.clone(),
                    a: sp1.clone(),
                    b: SSAVar::constant(0x480, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: conflict_slot,
                    val: mk("X2", 0, 8),
                },
            ],
        };

        let reload_slot = mk("tmp:slot", 4, 8);
        let reloaded_frame = mk("X8", 9, 8);
        let argv_addr = mk("tmp:slot", 5, 8);
        let argv_root = mk("X8", 10, 8);
        let arg_addr = mk("tmp:slot", 6, 8);
        let arg_value = mk("X0", 5, 8);
        let reload = SSABlock {
            addr: 0x1010,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: reload_slot.clone(),
                    a: sp1.clone(),
                    b: SSAVar::constant(0x178, 8),
                },
                SSAOp::Load {
                    dst: reloaded_frame.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: reload_slot,
                },
                SSAOp::IntAdd {
                    dst: argv_addr.clone(),
                    a: reloaded_frame,
                    b: SSAVar::constant(160, 8),
                },
                SSAOp::Load {
                    dst: argv_root.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: argv_addr,
                },
                SSAOp::IntAdd {
                    dst: arg_addr.clone(),
                    a: argv_root.clone(),
                    b: SSAVar::constant(8, 8),
                },
                SSAOp::Load {
                    dst: arg_value.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: arg_addr,
                },
            ],
        };

        let info = analyze(&[entry, conflict, reload], &env);

        assert!(
            !info.stable_stack_values.contains_key(&0x480),
            "flat stack-slot conflict should invalidate the generic stable slot, got {:?}",
            info.stable_stack_values.get(&0x480)
        );

        let root_key = FrameObjectFieldKey {
            base_slot_offset: 0x3e0,
            field_offset: 160,
        };
        assert!(
            matches!(
                info.frame_object_field_roots.get(&root_key),
                Some(SemanticValue::Address(NormalizedAddr {
                    base: BaseRef::Value(value_ref),
                    index: None,
                    scale_bytes: 0,
                    offset_bytes: 0,
                })) if value_ref.var == mk("X1", 0, 8)
            ),
            "expected semantic argv root to survive as a frame-object field fact, got {:?}",
            info.frame_object_field_roots.get(&root_key)
        );

        assert!(
            matches!(
                info.semantic_values.get(&argv_root.display_name()),
                Some(SemanticValue::Address(NormalizedAddr {
                    base: BaseRef::Value(value_ref),
                    index: None,
                    scale_bytes: 0,
                    offset_bytes: 0,
                })) if value_ref.var == mk("X1", 0, 8)
            ),
            "reloaded frame field should still resolve to argv root, got {:?}",
            info.semantic_values.get(&argv_root.display_name())
        );

        assert!(
            matches!(
                info.semantic_values.get(&arg_value.display_name()),
                Some(SemanticValue::Load {
                    space: SpaceId::Ram,
                    addr: NormalizedAddr {
                        base: BaseRef::Value(value_ref),
                        ..
                    },
                    ..
                }) if value_ref.var == mk("X1", 0, 8)
            ),
            "final imported-call arg load should still use argv root, got {:?}",
            info.semantic_values.get(&arg_value.display_name())
        );
    }

    #[test]
    fn frame_object_field_roots_survive_semantically_equivalent_restores() {
        let mut fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "fp".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
            ..Default::default()
        };
        fixture
            .param_register_aliases
            .insert("x1".to_string(), "arg2".to_string());
        fixture
            .type_hints
            .insert("arg2".to_string(), CType::ptr(CType::ptr(CType::Int(8))));
        let env = fixture.env();

        let sp0 = mk("SP", 0, 8);
        let sp1 = mk("SP", 1, 8);
        let frame_base = mk("X8", 1, 8);
        let slot_frame = mk("tmp:slot", 1, 8);
        let slot_argv = mk("tmp:slot", 2, 8);
        let entry = SSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntSub {
                    dst: sp1.clone(),
                    a: sp0,
                    b: SSAVar::constant(0x10, 8),
                },
                SSAOp::IntAdd {
                    dst: frame_base.clone(),
                    a: sp1.clone(),
                    b: SSAVar::constant(0x3e0, 8),
                },
                SSAOp::IntAdd {
                    dst: slot_frame.clone(),
                    a: sp1.clone(),
                    b: SSAVar::constant(0x178, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: slot_frame,
                    val: frame_base.clone(),
                },
                SSAOp::IntAdd {
                    dst: slot_argv.clone(),
                    a: frame_base,
                    b: SSAVar::constant(160, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: slot_argv,
                    val: mk("X1", 0, 8),
                },
            ],
        };

        let reload_slot = mk("tmp:slot", 3, 8);
        let reloaded_frame = mk("X8", 9, 8);
        let argv_addr = mk("tmp:slot", 4, 8);
        let argv_root = mk("X8", 10, 8);
        let argv_addr_reloaded = mk("tmp:slot", 5, 8);
        let restorer = SSABlock {
            addr: 0x1010,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntAdd {
                    dst: reload_slot.clone(),
                    a: sp1.clone(),
                    b: SSAVar::constant(0x178, 8),
                },
                SSAOp::Load {
                    dst: reloaded_frame.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: reload_slot,
                },
                SSAOp::IntAdd {
                    dst: argv_addr.clone(),
                    a: reloaded_frame.clone(),
                    b: SSAVar::constant(160, 8),
                },
                SSAOp::Load {
                    dst: argv_root.clone(),
                    space: r2il::SpaceId::Ram,
                    addr: argv_addr,
                },
                SSAOp::IntAdd {
                    dst: argv_addr_reloaded.clone(),
                    a: reloaded_frame,
                    b: SSAVar::constant(160, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: argv_addr_reloaded,
                    val: argv_root.clone(),
                },
            ],
        };

        let info = analyze(&[entry, restorer], &env);

        let root_key = FrameObjectFieldKey {
            base_slot_offset: 0x3e0,
            field_offset: 160,
        };
        assert!(
            matches!(
                info.frame_object_field_roots.get(&root_key),
                Some(SemanticValue::Address(NormalizedAddr {
                    base: BaseRef::Value(value_ref),
                    index: None,
                    scale_bytes: 0,
                    offset_bytes: 0,
                })) if value_ref.var == mk("X1", 0, 8)
            ),
            "expected frame-object root to survive semantically equivalent restore, got {:?}",
            info.frame_object_field_roots.get(&root_key)
        );
        assert!(
            matches!(
                info.semantic_values.get(&argv_root.display_name()),
                Some(SemanticValue::Address(NormalizedAddr {
                    base: BaseRef::Value(value_ref),
                    index: None,
                    scale_bytes: 0,
                    offset_bytes: 0,
                })) if value_ref.var == mk("X1", 0, 8)
            ),
            "expected reloaded frame field to stay rooted at argv, got {:?}",
            info.semantic_values.get(&argv_root.display_name())
        );
    }

    #[test]
    fn semantic_values_capture_observed_live_arm64_struct_array_loads() {
        let mut fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "fp".to_string(),
            arg_regs: vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
            ..Default::default()
        };
        fixture
            .param_register_aliases
            .insert("x0".to_string(), "arg1".to_string());
        fixture
            .param_register_aliases
            .insert("x1".to_string(), "arg2".to_string());
        fixture.type_hints.insert(
            "arg1".to_string(),
            CType::ptr(CType::Struct("demo_layout".to_string())),
        );
        fixture
            .type_hints
            .insert("arg2".to_string(), CType::Int(32));
        let env = fixture.env();

        let sp0 = mk("SP", 0, 8);
        let sp1 = mk("SP", 1, 8);
        let x0 = mk("X0", 0, 8);
        let w1 = mk("W1", 0, 4);
        let w2 = mk("W2", 0, 4);
        let slot_base = mk("tmp:6500", 1, 8);
        let slot_idx = mk("tmp:6400", 1, 8);
        let slot_v = mk("tmp:6780", 1, 8);
        let reload_v = mk("tmp:6780", 2, 8);
        let loaded_v = mk("tmp:24c00", 1, 4);
        let zext_v = mk("X8", 1, 8);
        let reload_base_addr = mk("tmp:6500", 2, 8);
        let reload_base = mk("X9", 1, 8);
        let reload_idx_addr = mk("tmp:6400", 2, 8);
        let reload_idx = mk("tmp:26b00", 1, 4);
        let sext_idx = mk("X10", 1, 8);
        let scaled_idx = mk("X10", 2, 8);
        let copied_scale = mk("tmp:12380", 1, 8);
        let sum_addr = mk("tmp:12480", 1, 8);
        let copied_sum = mk("X9", 2, 8);
        let store_addr = mk("tmp:6400", 3, 8);
        let reload_base_addr_2 = mk("tmp:6500", 3, 8);
        let reload_base_2 = mk("X8", 2, 8);
        let reload_idx_addr_2 = mk("tmp:6400", 4, 8);
        let reload_idx_2 = mk("tmp:26b00", 2, 4);
        let sext_idx_2 = mk("X9", 3, 8);
        let scaled_idx_2 = mk("X9", 4, 8);
        let copied_scale_2 = mk("tmp:12380", 2, 8);
        let sum_addr_2 = mk("tmp:12480", 2, 8);
        let copied_sum_2 = mk("X8", 3, 8);
        let load_addr_8 = mk("tmp:6400", 5, 8);
        let load_8 = mk("tmp:24c00", 2, 4);
        let zext_8 = mk("X8", 4, 8);
        let reload_base_addr_3 = mk("tmp:6500", 4, 8);
        let reload_base_3 = mk("X9", 5, 8);
        let reload_idx_addr_3 = mk("tmp:6400", 6, 8);
        let reload_idx_3 = mk("tmp:26b00", 3, 4);
        let sext_idx_3 = mk("X10", 3, 8);
        let scaled_idx_3 = mk("X10", 4, 8);
        let copied_scale_3 = mk("tmp:12380", 3, 8);
        let sum_addr_3 = mk("tmp:12480", 3, 8);
        let copied_sum_3 = mk("X9", 6, 8);
        let load_addr_34 = mk("tmp:6400", 7, 8);
        let load_34 = mk("tmp:24c00", 3, 4);
        let zext_34 = mk("X9", 7, 8);

        let block = single_block(vec![
            SSAOp::IntSub {
                dst: sp1.clone(),
                a: sp0,
                b: SSAVar::constant(0x10, 8),
            },
            SSAOp::IntAdd {
                dst: slot_base.clone(),
                a: sp1.clone(),
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_base,
                val: x0.clone(),
            },
            SSAOp::IntAdd {
                dst: slot_idx.clone(),
                a: sp1.clone(),
                b: SSAVar::constant(4, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_idx,
                val: w1.clone(),
            },
            SSAOp::Copy {
                dst: slot_v.clone(),
                src: sp1.clone(),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: slot_v,
                val: w2,
            },
            SSAOp::Copy {
                dst: reload_v.clone(),
                src: sp1.clone(),
            },
            SSAOp::Load {
                dst: loaded_v.clone(),
                space: r2il::SpaceId::Ram,
                addr: reload_v,
            },
            SSAOp::IntZExt {
                dst: zext_v,
                src: loaded_v,
            },
            SSAOp::IntAdd {
                dst: reload_base_addr.clone(),
                a: sp1.clone(),
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Load {
                dst: reload_base.clone(),
                space: r2il::SpaceId::Ram,
                addr: reload_base_addr,
            },
            SSAOp::IntAdd {
                dst: reload_idx_addr.clone(),
                a: sp1.clone(),
                b: SSAVar::constant(4, 8),
            },
            SSAOp::Load {
                dst: reload_idx.clone(),
                space: r2il::SpaceId::Ram,
                addr: reload_idx_addr,
            },
            SSAOp::IntSExt {
                dst: sext_idx.clone(),
                src: reload_idx,
            },
            SSAOp::IntMult {
                dst: scaled_idx.clone(),
                a: sext_idx,
                b: SSAVar::constant(0x38, 8),
            },
            SSAOp::Copy {
                dst: copied_scale.clone(),
                src: scaled_idx,
            },
            SSAOp::IntAdd {
                dst: sum_addr.clone(),
                a: reload_base,
                b: copied_scale.clone(),
            },
            SSAOp::Copy {
                dst: copied_sum.clone(),
                src: sum_addr,
            },
            SSAOp::IntAdd {
                dst: store_addr.clone(),
                a: copied_sum,
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: store_addr,
                val: mk("W8", 0, 4),
            },
            SSAOp::IntAdd {
                dst: reload_base_addr_2.clone(),
                a: sp1.clone(),
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Load {
                dst: reload_base_2.clone(),
                space: r2il::SpaceId::Ram,
                addr: reload_base_addr_2,
            },
            SSAOp::IntAdd {
                dst: reload_idx_addr_2.clone(),
                a: sp1.clone(),
                b: SSAVar::constant(4, 8),
            },
            SSAOp::Load {
                dst: reload_idx_2.clone(),
                space: r2il::SpaceId::Ram,
                addr: reload_idx_addr_2,
            },
            SSAOp::IntSExt {
                dst: sext_idx_2.clone(),
                src: reload_idx_2,
            },
            SSAOp::IntMult {
                dst: scaled_idx_2.clone(),
                a: sext_idx_2,
                b: SSAVar::constant(0x38, 8),
            },
            SSAOp::Copy {
                dst: copied_scale_2.clone(),
                src: scaled_idx_2,
            },
            SSAOp::IntAdd {
                dst: sum_addr_2.clone(),
                a: reload_base_2,
                b: copied_scale_2.clone(),
            },
            SSAOp::Copy {
                dst: copied_sum_2.clone(),
                src: sum_addr_2,
            },
            SSAOp::IntAdd {
                dst: load_addr_8.clone(),
                a: copied_sum_2,
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Load {
                dst: load_8.clone(),
                space: r2il::SpaceId::Ram,
                addr: load_addr_8,
            },
            SSAOp::IntZExt {
                dst: zext_8,
                src: load_8.clone(),
            },
            SSAOp::IntAdd {
                dst: reload_base_addr_3.clone(),
                a: sp1.clone(),
                b: SSAVar::constant(8, 8),
            },
            SSAOp::Load {
                dst: reload_base_3.clone(),
                space: r2il::SpaceId::Ram,
                addr: reload_base_addr_3,
            },
            SSAOp::IntAdd {
                dst: reload_idx_addr_3.clone(),
                a: sp1,
                b: SSAVar::constant(4, 8),
            },
            SSAOp::Load {
                dst: reload_idx_3.clone(),
                space: r2il::SpaceId::Ram,
                addr: reload_idx_addr_3,
            },
            SSAOp::IntSExt {
                dst: sext_idx_3.clone(),
                src: reload_idx_3,
            },
            SSAOp::IntMult {
                dst: scaled_idx_3.clone(),
                a: sext_idx_3,
                b: SSAVar::constant(0x38, 8),
            },
            SSAOp::Copy {
                dst: copied_scale_3.clone(),
                src: scaled_idx_3,
            },
            SSAOp::IntAdd {
                dst: sum_addr_3.clone(),
                a: reload_base_3,
                b: copied_scale_3.clone(),
            },
            SSAOp::Copy {
                dst: copied_sum_3.clone(),
                src: sum_addr_3,
            },
            SSAOp::IntAdd {
                dst: load_addr_34.clone(),
                a: copied_sum_3,
                b: SSAVar::constant(0x34, 8),
            },
            SSAOp::Load {
                dst: load_34.clone(),
                space: r2il::SpaceId::Ram,
                addr: load_addr_34,
            },
            SSAOp::IntZExt {
                dst: zext_34,
                src: load_34.clone(),
            },
        ]);

        let info = analyze(&[block], &env);

        assert!(
            matches!(
                info.semantic_values.get(&load_8.display_name()),
                Some(SemanticValue::Scalar(ScalarValue::Root(root)))
                    if root.var == mk("W8", 0, 4)
            ) || matches!(
                info.semantic_values.get(&load_8.display_name()),
                Some(SemanticValue::Load {
                    space: SpaceId::Ram,
                    addr: NormalizedAddr {
                        base: BaseRef::Value(value_ref),
                        index: Some(_),
                        scale_bytes: 0x38,
                        offset_bytes: 8,
                    },
                    size: 4,
                }) if value_ref.var == x0
            ),
            "semantic load shape for {} = {:?}",
            load_8.display_name(),
            info.semantic_values.get(&load_8.display_name())
        );
        assert!(
            matches!(
                info.semantic_values.get(&load_34.display_name()),
                Some(SemanticValue::Load {
                    space: SpaceId::Ram,
                    addr: NormalizedAddr {
                        base: BaseRef::Value(value_ref),
                        index: Some(_),
                        scale_bytes: 0x38,
                        offset_bytes: 0x34,
                    },
                    size: 4,
                }) if value_ref.var == x0
            ),
            "semantic load shape for {} = {:?}",
            load_34.display_name(),
            info.semantic_values.get(&load_34.display_name())
        );
    }

    #[test]
    fn frame_slot_merges_capture_if_else_return_slot_values() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "fp".to_string(),
            ..Default::default()
        };
        let env = fixture.env();

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1020, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut fallthrough = R2ILBlock::new(0x1004, 4);
        fallthrough.push(R2ILOp::Branch {
            target: Varnode::constant(0x1008, 8),
        });
        let mut else_block = R2ILBlock::new(0x1008, 4);
        else_block.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut then_block = R2ILBlock::new(0x1020, 4);
        then_block.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut exit = R2ILBlock::new(0x1010, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[
            entry,
            fallthrough,
            else_block,
            then_block,
            exit,
        ])
        .expect("ssa function");
        func.get_block_mut(0x1000).expect("entry").ops = vec![SSAOp::CBranch {
            target: mk("ram:1020", 0, 8),
            cond: mk("tmp:a00", 1, 1),
        }];
        func.get_block_mut(0x1004).expect("fallthrough").ops = vec![SSAOp::Branch {
            target: mk("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("else").ops = vec![
            SSAOp::IntAdd {
                dst: mk("tmp:6400", 3, 8),
                a: mk("SP", 1, 8),
                b: SSAVar::constant(0xc, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6400", 3, 8),
                val: SSAVar::constant(1, 4),
            },
            SSAOp::Branch {
                target: mk("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x1020).expect("then").ops = vec![
            SSAOp::IntAdd {
                dst: mk("tmp:6400", 4, 8),
                a: mk("SP", 1, 8),
                b: SSAVar::constant(0xc, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6400", 4, 8),
                val: SSAVar::constant(0, 4),
            },
            SSAOp::Branch {
                target: mk("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x1010).expect("exit").ops = vec![
            SSAOp::IntAdd {
                dst: mk("tmp:6400", 6, 8),
                a: mk("SP", 1, 8),
                b: SSAVar::constant(0xc, 8),
            },
            SSAOp::Load {
                dst: mk("tmp:24c00", 2, 4),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6400", 6, 8),
            },
            SSAOp::IntZExt {
                dst: mk("X0", 1, 8),
                src: mk("tmp:24c00", 2, 4),
            },
            SSAOp::Return {
                target: mk("X30", 0, 8),
            },
        ];

        let blocks = func.blocks().cloned().collect::<Vec<_>>();
        let mut info = analyze(&blocks, &env);
        populate_frame_slot_merges(&mut info, &func, &env, None);

        let summary = info
            .frame_slot_merges
            .get("tmp:24c00_2")
            .expect("merged return-slot load summary");
        assert_eq!(summary.slot_offset, 12);
        assert!(matches!(
            summary.incoming.get(&0x1020),
            Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(0))))
        ));
        assert!(matches!(
            summary.incoming.get(&0x1008),
            Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(1))))
        ));
    }

    #[test]
    fn preserve_temp_copy_root_identity_requires_raw_temp_copy_from_entry_register() {
        let dst = mk("tmp:retcopy", 1, 4);
        let src = mk("W8", 0, 4);
        let root = SemanticValue::Scalar(ScalarValue::Root(ValueRef::from(src.clone())));

        assert_eq!(
            preserve_temp_copy_root_identity(&dst, &src, root.clone()),
            SemanticValue::Scalar(ScalarValue::Root(ValueRef::from(dst.clone())))
        );
        assert_eq!(
            preserve_temp_copy_root_identity(&mk("local_retcopy", 1, 4), &src, root.clone()),
            root
        );

        let other_src = mk("W9", 0, 4);
        let other_root = SemanticValue::Scalar(ScalarValue::Root(ValueRef::from(other_src)));
        assert_eq!(
            preserve_temp_copy_root_identity(&dst, &src, other_root.clone()),
            other_root
        );

        let versioned_src = mk("W8", 1, 4);
        let versioned_root =
            SemanticValue::Scalar(ScalarValue::Root(ValueRef::from(versioned_src.clone())));
        assert_eq!(
            preserve_temp_copy_root_identity(&dst, &versioned_src, versioned_root.clone()),
            versioned_root
        );
    }

    #[test]
    fn frame_slot_merges_prefer_same_family_register_value_through_temp_copy() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "fp".to_string(),
            ..Default::default()
        };
        let env = fixture.env();

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1020, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut fallthrough = R2ILBlock::new(0x1004, 4);
        fallthrough.push(R2ILOp::Branch {
            target: Varnode::constant(0x1008, 8),
        });
        let mut else_block = R2ILBlock::new(0x1008, 4);
        else_block.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut then_block = R2ILBlock::new(0x1020, 4);
        then_block.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut exit = R2ILBlock::new(0x1010, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[
            entry,
            fallthrough,
            else_block,
            then_block,
            exit,
        ])
        .expect("ssa function");
        func.get_block_mut(0x1000).expect("entry").ops = vec![SSAOp::CBranch {
            target: mk("ram:1020", 0, 8),
            cond: mk("tmp:a00", 1, 1),
        }];
        func.get_block_mut(0x1004).expect("fallthrough").ops = vec![SSAOp::Branch {
            target: mk("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("else").ops = vec![
            SSAOp::Copy {
                dst: mk("X8", 1, 8),
                src: SSAVar::constant(1, 8),
            },
            SSAOp::Copy {
                dst: mk("tmp:retcopy", 1, 4),
                src: mk("W8", 0, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:6400", 3, 8),
                a: mk("SP", 1, 8),
                b: SSAVar::constant(0xc, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6400", 3, 8),
                val: mk("tmp:retcopy", 1, 4),
            },
            SSAOp::Branch {
                target: mk("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x1020).expect("then").ops = vec![
            SSAOp::IntAdd {
                dst: mk("tmp:6400", 4, 8),
                a: mk("SP", 1, 8),
                b: SSAVar::constant(0xc, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6400", 4, 8),
                val: SSAVar::constant(0, 4),
            },
            SSAOp::Branch {
                target: mk("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x1010).expect("exit").ops = vec![
            SSAOp::IntAdd {
                dst: mk("tmp:6400", 6, 8),
                a: mk("SP", 1, 8),
                b: SSAVar::constant(0xc, 8),
            },
            SSAOp::Load {
                dst: mk("tmp:24c00", 2, 4),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6400", 6, 8),
            },
            SSAOp::IntZExt {
                dst: mk("X0", 1, 8),
                src: mk("tmp:24c00", 2, 4),
            },
            SSAOp::Return {
                target: mk("X30", 0, 8),
            },
        ];

        let blocks = func.blocks().cloned().collect::<Vec<_>>();
        let mut info = analyze(&blocks, &env);
        populate_frame_slot_merges(&mut info, &func, &env, None);

        let summary = info
            .frame_slot_merges
            .get("tmp:24c00_2")
            .expect("merged return-slot load summary");
        assert!(
            matches!(
                summary.incoming.get(&0x1008),
                Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(1))))
            ),
            "unexpected else incoming: {:?}",
            summary.incoming
        );
        assert!(
            matches!(
                summary.incoming.get(&0x1020),
                Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(0))))
            ),
            "unexpected then incoming: {:?}",
            summary.incoming
        );
    }

    #[test]
    fn frame_slot_merges_keep_most_recent_same_family_constant_over_older_root_history() {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        use r2ssa::SSAFunction;

        let fixture = TestEnvFixture {
            sp_name: "sp".to_string(),
            fp_name: "fp".to_string(),
            ..Default::default()
        };
        let env = fixture.env();

        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::constant(0x1020, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut usage = R2ILBlock::new(0x1004, 4);
        usage.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut body = R2ILBlock::new(0x1020, 4);
        body.push(R2ILOp::Branch {
            target: Varnode::constant(0x1010, 8),
        });
        let mut exit = R2ILBlock::new(0x1010, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        let mut func = SSAFunction::from_blocks_raw_no_arch(&[entry, usage, body, exit])
            .expect("ssa function");
        func.get_block_mut(0x1000).expect("entry").ops = vec![SSAOp::CBranch {
            target: mk("ram:1020", 0, 8),
            cond: mk("tmp:a00", 1, 1),
        }];
        func.get_block_mut(0x1004).expect("usage").ops = vec![
            SSAOp::Copy {
                dst: mk("X8", 4, 8),
                src: mk("argc", 0, 8),
            },
            SSAOp::Copy {
                dst: mk("X8", 7, 8),
                src: SSAVar::constant(1, 8),
            },
            SSAOp::Copy {
                dst: mk("tmp:retcopy", 1, 4),
                src: mk("W8", 0, 4),
            },
            SSAOp::IntAdd {
                dst: mk("tmp:6400", 1, 8),
                a: mk("SP", 1, 8),
                b: SSAVar::constant(0xc, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6400", 1, 8),
                val: mk("tmp:retcopy", 1, 4),
            },
            SSAOp::Branch {
                target: mk("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x1020).expect("body").ops = vec![
            SSAOp::IntAdd {
                dst: mk("tmp:6400", 2, 8),
                a: mk("SP", 1, 8),
                b: SSAVar::constant(0xc, 8),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6400", 2, 8),
                val: SSAVar::constant(0, 4),
            },
            SSAOp::Branch {
                target: mk("ram:1010", 0, 8),
            },
        ];
        func.get_block_mut(0x1010).expect("exit").ops = vec![
            SSAOp::IntAdd {
                dst: mk("tmp:6400", 3, 8),
                a: mk("SP", 1, 8),
                b: SSAVar::constant(0xc, 8),
            },
            SSAOp::Load {
                dst: mk("tmp:24c00", 1, 4),
                space: r2il::SpaceId::Ram,
                addr: mk("tmp:6400", 3, 8),
            },
            SSAOp::Return {
                target: mk("X30", 0, 8),
            },
        ];

        let blocks = func.blocks().cloned().collect::<Vec<_>>();
        let mut info = analyze(&blocks, &env);
        populate_frame_slot_merges(&mut info, &func, &env, None);

        let summary = info
            .frame_slot_merges
            .get("tmp:24c00_1")
            .expect("merged return-slot load summary");
        assert!(
            matches!(
                summary.incoming.get(&0x1004),
                Some(SemanticValue::Scalar(ScalarValue::Expr(CExpr::IntLit(1))))
            ),
            "most recent same-family constant should beat older root history: {:?}",
            summary.incoming
        );
    }
}
