use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use r2ssa::function::DefLocation;
use r2ssa::{
    CompareKind, MemoryLocation, ObjectKind, SSAOp, SSAVar, SsaArtifact, ValueId, ValueOwner,
};
use r2types::{
    CalleeIdentity, CalleeResolutionFacts, CalleeTargetIdentityRequest, CallsiteKey,
    FunctionCallResultFacts, FunctionCallsiteFacts, FunctionFacts,
};
#[cfg(test)]
use r2types::{
    ExternalStackBase, ExternalStackSlotRole, ExternalStackSlotSpec, StackSlotKey, VisibleBinding,
    VisibleBindingKind,
};

use super::{DecompilerFacts, SSABlock, StackInfo, UseInfo, ValueProvenance};
use crate::ast::{BinaryOp, CExpr, UnaryOp};
use crate::binding_plan::{
    PlannedParameterSymbol, PlannedStackSymbol, PlannedValueSymbol, RenderedIdentityRefusal,
};

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StackAliasView {
    pub(crate) visible_name: String,
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

#[derive(Debug, Clone, Default)]
pub(crate) struct PreparedSemanticView {
    /// The sole BindingId-to-SymbolId projection for this rendering. Keeping
    /// the resolver itself avoids a second ValueId/name table that could drift
    /// from the sealed binding plan.
    pub(crate) binding_names: Option<Rc<crate::binding_plan::BindingNameResolution>>,
    #[cfg(test)]
    pub(crate) stack_aliases_by_offset: BTreeMap<i64, StackAliasView>,
    pub(crate) value_id_by_var: HashMap<SSAVar, ValueId>,
    pub(crate) var_by_value_id: HashMap<ValueId, SSAVar>,
    pub(crate) owner_expr_by_value: HashMap<ValueId, CExpr>,
    pub(crate) stack_offset_by_value: HashMap<ValueId, i64>,
    pub(crate) predicate_expr_by_value: HashMap<ValueId, CExpr>,
    pub(crate) call_view_by_site: BTreeMap<(u64, usize), PreparedCallView>,
    pub(crate) call_result_facts_by_value: BTreeMap<ValueId, r2types::CallResultFact>,
    pub(crate) call_result_source_by_value: HashMap<ValueId, (u64, usize)>,
    /// Byte offset and width of every access the capture projects onto a struct
    /// member rather than an array element. An index must not be invented for
    /// these: the offset reaches a field, and its stride is not an element size.
    pub(crate) member_projected_accesses: HashSet<(u64, u32)>,
    #[cfg(test)]
    pub(crate) certified_rendering_required: bool,
    #[cfg(test)]
    pub(crate) authorized_stack_owner_names: BTreeMap<i64, BTreeSet<String>>,
    #[cfg(test)]
    pub(crate) authorized_stack_owner_names_by_object:
        BTreeMap<(r2ssa::ObjectId, i64), BTreeSet<String>>,
    pub(crate) certified_loop_carrier_values: BTreeSet<ValueId>,
}

pub(crate) struct PreparedSemanticViewInputs<'a> {
    pub(crate) prepared: &'a SsaArtifact,
    #[cfg(test)]
    pub(crate) stack_slots: &'a BTreeMap<StackSlotKey, ExternalStackSlotSpec>,
    #[cfg(test)]
    pub(crate) visible_bindings: &'a [VisibleBinding],
    pub(crate) function_facts: &'a FunctionFacts,
    #[cfg(test)]
    pub(crate) certified_rendering_required: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PreparedSemanticViewBuildError {
    SourceAuthorityMismatch,
    SymbolTableMismatch,
    RenderedIdentity(RenderedIdentityRefusal),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PreparedRuntimeFactsError {
    ExecutionStop(crate::DecompileExecutionStop),
    Lowering(crate::analysis::lower::OpLoweringRefusal),
}

impl From<crate::DecompileExecutionStop> for PreparedRuntimeFactsError {
    fn from(stop: crate::DecompileExecutionStop) -> Self {
        Self::ExecutionStop(stop)
    }
}

impl From<crate::analysis::lower::OpLoweringRefusal> for PreparedRuntimeFactsError {
    fn from(refusal: crate::analysis::lower::OpLoweringRefusal) -> Self {
        Self::Lowering(refusal)
    }
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
    #[cfg(test)]
    pub(crate) fn build(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        inputs: PreparedSemanticViewInputs<'_>,
    ) -> Self {
        Self::build_inner(symbols, inputs, None)
    }

    pub(crate) fn build_with_bindings(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        inputs: PreparedSemanticViewInputs<'_>,
        binding_names: Rc<crate::binding_plan::BindingNameResolution>,
    ) -> Result<Self, PreparedSemanticViewBuildError> {
        if !binding_names.validates_artifact(inputs.prepared) {
            return Err(PreparedSemanticViewBuildError::SourceAuthorityMismatch);
        }
        if !binding_names.owns_symbol_table(symbols) {
            return Err(PreparedSemanticViewBuildError::SymbolTableMismatch);
        }
        preflight_rendered_identities(&inputs, &binding_names)
            .map_err(PreparedSemanticViewBuildError::RenderedIdentity)?;
        Ok(Self::build_inner(symbols, inputs, Some(binding_names)))
    }

    fn build_inner(
        symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
        inputs: PreparedSemanticViewInputs<'_>,
        binding_names: Option<Rc<crate::binding_plan::BindingNameResolution>>,
    ) -> Self {
        #[cfg(test)]
        let certified_rendering_required = inputs.certified_rendering_required;
        let mut view = Self {
            binding_names,
            #[cfg(test)]
            certified_rendering_required,
            member_projected_accesses: inputs
                .prepared
                .machine_context()
                .function_interface()
                .and_then(|interface| {
                    inputs
                        .prepared
                        .aggregate_accesses()
                        .projections_for_revision(interface.revision_identity())
                })
                .map(|projections| {
                    projections
                        .values()
                        .filter(|projection| projection.element_index.is_none())
                        .map(|projection| (projection.byte_offset, projection.byte_width))
                        .collect()
                })
                .unwrap_or_default(),
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
        view.init_value_indexes(inputs.prepared);

        #[cfg(test)]
        populate_stack_aliases(&mut view, &inputs);
        populate_stack_offsets(&mut view, inputs.prepared);
        #[cfg(test)]
        populate_authorized_stack_owner_names(&mut view, &inputs);
        populate_owner_exprs(symbols, &mut view, &inputs);
        populate_call_result_sources(&mut view, inputs.call_result_facts());
        populate_calls(symbols, &mut view, &inputs);
        populate_predicates(symbols, &mut view, &inputs);
        view
    }

    #[cfg(test)]
    pub(crate) fn stack_alias_for_offset(&self, offset: i64) -> Option<&StackAliasView> {
        self.stack_aliases_by_offset.get(&offset)
    }

    pub(crate) fn value_id_for_var(&self, var: &SSAVar) -> Option<ValueId> {
        self.value_id_by_var.get(var).copied()
    }

    /// Project one exact value through the already-admitted binding plan.
    ///
    /// `build_with_bindings` validates every dense disposition first, so an
    /// error here would mean the sealed plan changed after admission. Inline
    /// and elided values intentionally return no program-variable symbol.
    fn admitted_value_symbol(&self, var: &SSAVar) -> Option<crate::symbol::SymbolId> {
        let resolver = self.binding_names.as_ref()?;
        let value = self.value_id_for_var(var)?;
        let disposition = match resolver.require_value(value) {
            Ok(disposition) => disposition,
            Err(_) => return None,
        };
        match disposition {
            PlannedValueSymbol::Bound(symbol) => Some(symbol),
            PlannedValueSymbol::Inline(_)
            | PlannedValueSymbol::Elided(_)
            | PlannedValueSymbol::Refused(_)
            | PlannedValueSymbol::Absent => None,
        }
    }

    /// Project one exact formal parameter without consulting its register or
    /// presentation spelling.
    fn admitted_parameter_symbol(
        &self,
        prepared: &SsaArtifact,
        var: &SSAVar,
    ) -> Option<crate::symbol::SymbolId> {
        let slot = prepared
            .function()
            .decompile_prep_facts()?
            .formal_parameter_of(var)?;
        let slot = u32::try_from(slot).ok()?;
        let disposition = match self.binding_names.as_ref()?.require_parameter_slot(slot) {
            Ok(disposition) => disposition,
            Err(_) => return None,
        };
        let PlannedParameterSymbol::Bound { symbol, .. } = disposition;
        Some(symbol)
    }

    /// Project one exact source-owned stack object. Offset and alias tables
    /// remain presentation evidence only and never authorize the identifier.
    fn admitted_stack_symbol(&self, object: r2ssa::ObjectId) -> Option<crate::symbol::SymbolId> {
        let resolver = self.binding_names.as_ref()?;
        let _ = resolver.plan().stack_object_disposition(object)?;
        let disposition = match resolver.require_stack(object) {
            Ok(disposition) => disposition,
            Err(_) => return None,
        };
        let PlannedStackSymbol::Bound(symbol) = disposition;
        Some(symbol)
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
    }

    pub(crate) fn predicate_expr_for_cond(&self, var: &SSAVar) -> Option<&CExpr> {
        self.value_id_for_var(var)
            .and_then(|value_id| self.predicate_expr_by_value.get(&value_id))
    }

    #[allow(dead_code)]
    pub(crate) fn predicate_expr_for_value_id(&self, value_id: ValueId) -> Option<&CExpr> {
        self.predicate_expr_by_value.get(&value_id)
    }

    pub(crate) fn call_view_for_site(&self, site: (u64, usize)) -> Option<&PreparedCallView> {
        self.call_view_by_site.get(&site)
    }

    pub(crate) fn call_result_source_for_var(&self, var: &SSAVar) -> Option<(u64, usize)> {
        self.value_id_for_var(var)
            .and_then(|value_id| self.call_result_source_by_value.get(&value_id).copied())
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

fn preflight_rendered_identities(
    inputs: &PreparedSemanticViewInputs<'_>,
    resolver: &crate::binding_plan::BindingNameResolution,
) -> Result<(), RenderedIdentityRefusal> {
    for value in &inputs.prepared.graph().values {
        let _ = resolver.require_value(value.id)?;
    }

    let mut parameter_slots = BTreeSet::new();
    if let Some(interface) = inputs.prepared.machine_context().function_interface() {
        parameter_slots.extend(
            interface
                .parameters()
                .iter()
                .map(|parameter| parameter.index()),
        );
    }
    if let Some(prep) = inputs.prepared.function().decompile_prep_facts() {
        parameter_slots.extend(
            prep.formal_parameters
                .values()
                .filter_map(|slot| u32::try_from(*slot).ok()),
        );
    }
    if let Some(render) = inputs.function_facts.render() {
        for entity in render.certified_entities.values() {
            match entity {
                r2types::CertifiedEntity::Parameter { slot, .. } => {
                    parameter_slots.insert(*slot);
                }
                r2types::CertifiedEntity::StackSlot { object, .. } => {
                    // A discovered stack address is not necessarily a C
                    // variable: saved frame pointers and return-stack
                    // machinery also occupy exact stack objects.  Preflight
                    // proves the sealed plan covers the complete object
                    // domain, while the surviving lowering site is what must
                    // require a Bound disposition.  This keeps an unused or
                    // structurally elided machine resource from becoming a
                    // fabricated program variable without letting a live use
                    // bypass its typed refusal.
                    if resolver.plan().stack_object_disposition(*object).is_none() {
                        return Err(RenderedIdentityRefusal::MissingStackDisposition {
                            object: *object,
                        });
                    }
                }
                r2types::CertifiedEntity::LoopCarrier { .. } => {}
            }
        }
    }
    for slot in parameter_slots {
        let _ = resolver.require_parameter_slot(slot)?;
    }
    Ok(())
}

/// Resolve a program-variable expression only after exact value identity has
/// reached the sealed binding plan. Test-only views built without a plan retain
/// their fixture spelling path; native views never enter it.
fn prepared_value_program_expr(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    var: &SSAVar,
) -> Option<CExpr> {
    // The binding plan answers, or nothing does. The alias ladder that used to
    // spell a name here under test consulted tables with no writers.
    let _ = symbols;
    view.admitted_value_symbol(var).map(CExpr::Var)
}

fn prepared_parameter_program_expr(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    prepared: &SsaArtifact,
    var: &SSAVar,
) -> Option<CExpr> {
    if view.binding_names.is_some() {
        return view
            .admitted_parameter_symbol(prepared, var)
            .map(CExpr::Var);
    }

    // The parameter's certified slot answers, or nothing does. A register
    // spelling looked up in an alias map is not an ABI slot, and the map had
    // no writer.
    let _ = symbols;
    None
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
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    blocks: &[SSABlock],
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) -> DecompilerFacts {
    let execution = r2ssa::SsaExecutionControl::default();
    let control =
        crate::DecompileWorkControl::new(&execution, crate::DecompileWorkPhase::Structuring);
    let origins =
        crate::normalize::NormalizationOrigins::for_unchanged(prepared.function(), prepared);
    build_prepared_runtime_facts_with_control(symbols, blocks, prepared, view, &origins, control)
        .expect("default decompiler work control cannot stop")
}

pub(crate) fn build_prepared_runtime_facts_with_control(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    blocks: &[SSABlock],
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    origins: &crate::normalize::NormalizationOrigins,
    control: crate::DecompileWorkControl<'_>,
) -> Result<DecompilerFacts, PreparedRuntimeFactsError> {
    control.poll()?;
    let mut use_info = UseInfo::default();
    let mut stack_info = StackInfo::default();

    seed_prepared_stack_facts(symbols, &mut use_info, &mut stack_info, prepared, view);
    collect_prepared_runtime_facts(&mut use_info, blocks, prepared, view);
    #[cfg(test)]
    pin_prepared_loop_carried_phi_values(&mut use_info, prepared, view);
    populate_prepared_call_runtime_facts(symbols, &mut use_info, blocks, prepared, view, origins);

    control.poll()?;
    Ok(DecompilerFacts {
        use_info,
        stack_info,
    })
}

#[cfg(test)]
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

#[cfg(test)]
fn pin_prepared_phi_materialized_var(use_info: &mut UseInfo, var: &SSAVar) {
    if var.is_const() || var.is_temp() {
        return;
    }
    let display = var.display_name();
    use_info.pinned.insert(display.clone());
    use_info.pinned.insert(display.to_ascii_lowercase());
}

#[cfg(test)]
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
        let offset = prepared_stack_slot_offset(slot);
        let entry = view
            .stack_aliases_by_offset
            .entry(offset)
            .or_insert_with(|| StackAliasView {
                visible_name: name.to_string(),
                binding_kind: Some(binding.kind),
            });
        if entry.visible_name.is_empty() {
            entry.visible_name = name.to_string();
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
                binding_kind: None,
            });
        if entry.visible_name.is_empty() {
            entry.visible_name = visible_name;
        }
    }
}

#[cfg(test)]
fn prepared_stack_slot_offset(slot: &StackSlotKey) -> i64 {
    match slot.base {
        ExternalStackBase::FramePointer => slot.offset.saturating_abs().saturating_neg(),
        _ => slot.offset,
    }
}

#[cfg(test)]
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

#[cfg(test)]
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

fn populate_owner_exprs(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &mut PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
) {
    let prepared = inputs.prepared;
    let mut producer_by_dst = HashMap::<SSAVar, &SSAOp>::new();
    for block in prepared.function().blocks() {
        for op in &block.ops {
            if let Some(dst) = op.dst() {
                producer_by_dst.insert(dst.clone(), op);
            }
        }
    }

    for (value, _offset) in view.stack_offset_entries() {
        if !is_prepared_stack_address_carrier(prepared, &value) {
            continue;
        }
        if prepared_stack_object_for_var(prepared, &value).is_none() {
            continue;
        }
        let Some(stack_expr) = prepared_stack_program_expr_for_var(symbols, view, prepared, &value)
        else {
            continue;
        };
        view.insert_owner_expr(&value, CExpr::AddrOf(Box::new(stack_expr)));
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
                        local_store_owner_expr_for_offset(
                            symbols, view, prepared, block, op_idx, offset,
                        )
                        .map(|expr| (expr, Some(offset)))
                        .or_else(|| {
                            prepared_stack_alias_expr_for_offset(symbols, view, offset)
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
                                stack_program_expr_for_memory_location(
                                    symbols,
                                    view,
                                    &fact.location,
                                )
                                .map(|expr| (expr, Some(offset)))
                            })
                    })
                    .or_else(|| {
                        prepared_load_access_expr_for_addr(
                            symbols, prepared, block, view, addr, dst.size,
                        )
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
                        if let Some(expr) = view.owner_expr_for_var(src).cloned().or_else(|| {
                            scalar_owner_expr_for_value(symbols, prepared, view, src, src.size)
                        }) && view.owner_expr_for_var(dst) != Some(&expr)
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
                        let derived = prepared_binary_owner_expr(
                            symbols,
                            prepared,
                            view,
                            BinaryOp::Sub,
                            a,
                            b,
                            compare_width,
                        )
                        .or_else(|| {
                            prepared_address_owner_expr_for_value(
                                symbols,
                                prepared,
                                view,
                                a,
                                compare_width,
                            )
                            .zip(prepared_address_owner_expr_for_value(
                                symbols,
                                prepared,
                                view,
                                b,
                                compare_width,
                            ))
                            .map(|(lhs, rhs)| {
                                prepared_simplify_binary_expr(
                                    symbols,
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
                        let derived = prepared_binary_owner_expr(
                            symbols,
                            prepared,
                            view,
                            BinaryOp::Shl,
                            a,
                            b,
                            compare_width,
                        )
                        .or_else(|| {
                            prepared_scaled_index_owner_expr(
                                symbols,
                                prepared,
                                view,
                                a,
                                compare_width,
                            )
                            .zip(scalar_owner_expr_for_value(
                                symbols,
                                prepared,
                                view,
                                b,
                                compare_width,
                            ))
                            .map(|(lhs, rhs)| {
                                prepared_simplify_binary_expr(
                                    symbols,
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
                        let derived = prepared_binary_owner_expr(
                            symbols,
                            prepared,
                            view,
                            BinaryOp::Mul,
                            a,
                            b,
                            compare_width,
                        )
                        .or_else(|| {
                            prepared_scaled_index_owner_expr(
                                symbols,
                                prepared,
                                view,
                                a,
                                compare_width,
                            )
                            .zip(prepared_scaled_index_owner_expr(
                                symbols,
                                prepared,
                                view,
                                b,
                                compare_width,
                            ))
                            .map(|(lhs, rhs)| {
                                prepared_simplify_binary_expr(
                                    symbols,
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
                        let derived = prepared_binary_owner_expr(
                            symbols,
                            prepared,
                            view,
                            BinaryOp::Add,
                            a,
                            b,
                            compare_width,
                        )
                        .or_else(|| {
                            prepared_address_owner_expr_for_value(
                                symbols,
                                prepared,
                                view,
                                a,
                                compare_width,
                            )
                            .zip(prepared_address_owner_expr_for_value(
                                symbols,
                                prepared,
                                view,
                                b,
                                compare_width,
                            ))
                            .map(|(lhs, rhs)| {
                                prepared_simplify_binary_expr(
                                    symbols,
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
                        if let Some(expr) = prepared_binary_owner_expr(
                            symbols,
                            prepared,
                            view,
                            op,
                            a,
                            b,
                            compare_width,
                        ) && view.owner_expr_for_var(dst) != Some(&expr)
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
                        let derived = prepared_signed_dividend_expr(
                            symbols,
                            prepared,
                            view,
                            &producer_by_dst,
                            a,
                        )
                        .zip(scalar_owner_expr_for_value(
                            symbols,
                            prepared,
                            view,
                            b,
                            compare_width,
                        ))
                        .map(|(lhs, rhs)| {
                            prepared_simplify_binary_expr(symbols, view, op, lhs, rhs)
                        })
                        .or_else(|| {
                            prepared_binary_owner_expr(
                                symbols,
                                prepared,
                                view,
                                op,
                                a,
                                b,
                                compare_width,
                            )
                        });
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
                        if let Some(expr) = prepared_binary_owner_expr(
                            symbols,
                            prepared,
                            view,
                            op,
                            a,
                            b,
                            compare_width,
                        ) && view.owner_expr_for_var(dst) != Some(&expr)
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

    refine_load_owner_exprs(symbols, view, inputs);
}

fn refine_load_owner_exprs(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
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
                    local_store_owner_expr_for_offset(
                        symbols, view, prepared, block, op_idx, offset,
                    )
                    .map(|expr| (expr, Some(offset)))
                    .or_else(|| {
                        prepared_stack_alias_expr_for_offset(symbols, view, offset)
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
                            stack_program_expr_for_memory_location(symbols, view, &fact.location)
                                .map(|expr| (expr, Some(offset)))
                        })
                })
                .or_else(|| {
                    prepared_load_access_expr_for_addr(
                        symbols, prepared, block, view, addr, dst.size,
                    )
                    .map(|expr| (expr, None))
                });
            let Some((candidate_expr, candidate_offset)) = candidate else {
                continue;
            };
            let should_replace = view.owner_expr_for_var(dst).is_none_or(|current| {
                prepared_load_owner_candidate_should_replace(symbols, current, &candidate_expr)
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

fn prepared_load_owner_candidate_should_replace(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    current: &CExpr,
    candidate: &CExpr,
) -> bool {
    current != candidate
        && ((prepared_expr_is_generic_scalar_alias(symbols, current)
            && !prepared_expr_is_generic_scalar_alias(symbols, candidate))
            || (prepared_expr_is_plain_visible_alias(current)
                && prepared_expr_is_structured_load_access(candidate)))
}

fn prepared_expr_is_generic_scalar_alias(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    expr: &CExpr,
) -> bool {
    #[cfg(not(test))]
    {
        let _ = (symbols, expr);
        false
    }
    #[cfg(test)]
    {
        match expr {
            CExpr::Var(name) => {
                is_generic_prepared_stack_alias(&crate::symbol::spelling(symbols, *name))
                    || crate::symbol::spelling(symbols, *name).ends_with("_home")
            }
            CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
                prepared_expr_is_generic_scalar_alias(symbols, inner)
            }
            CExpr::Binary { left, right, .. } => {
                prepared_expr_is_generic_scalar_alias(symbols, left)
                    && prepared_expr_is_generic_scalar_alias(symbols, right)
            }
            _ => false,
        }
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
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    prepared: &SsaArtifact,
    block: &r2ssa::FunctionSSABlock,
    view: &PreparedSemanticView,
    addr: &SSAVar,
    elem_size: u32,
) -> Option<CExpr> {
    let addr_expr = authoritative_scalar_expr_for_value(symbols, prepared, block, view, addr, 0)
        .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, addr, addr.size))
        .or_else(|| view.owner_expr_for_var(addr).cloned())?;
    prepared_load_access_expr_from_visible_addr(
        addr_expr,
        elem_size,
        &view.member_projected_accesses,
    )
}

fn prepared_load_access_expr_from_visible_addr(
    expr: CExpr,
    elem_size: u32,
    member_projected: &HashSet<(u64, u32)>,
) -> Option<CExpr> {
    let elem_bytes = elem_size.max(1);
    let elem_size = i64::from(elem_bytes);

    // The address is an integer expression; subscripting or dereferencing it
    // needs a pointer. `murmur3_32` renders `(arg0 + (arg1 & -0x4))[1]` without
    // this, and C reads that as indexing an integer. The element width is known
    // here, so the pointee is too.
    fn as_pointer(expr: CExpr, elem_bytes: u32) -> CExpr {
        if matches!(
            &expr,
            CExpr::Cast {
                ty: crate::ast::CType::Pointer(_),
                ..
            }
        ) {
            return expr;
        }
        CExpr::cast(
            crate::ast::CType::ptr(crate::ast::CType::Int {
                bits: elem_bytes.saturating_mul(8),
                signedness: r2types::Signedness::Unsigned,
            }),
            expr,
        )
    }

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
            prepared_load_access_expr_from_visible_addr(*inner, elem_size as u32, member_projected)
        }
        CExpr::Cast { expr: inner, .. } => {
            prepared_load_access_expr_from_visible_addr(*inner, elem_size as u32, member_projected)
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
                } else if offset >= 0
                    && member_projected.contains(&(offset as u64, elem_size as u32))
                {
                    // The capture projects this access onto a struct member, not
                    // an array element, so the offset reaches a field and its
                    // stride is not an element size. Leaving the address alone
                    // lets the layer holding the layout name it; inventing an
                    // index decided it first and `cur->next` rendered as `cur[1]`.
                    CExpr::deref(CExpr::binary(BinaryOp::Add, *left, *right))
                } else {
                    CExpr::subscript(as_pointer(*left, elem_bytes), CExpr::IntLit(index))
                });
            }
            if let Some(offset) = literal_i64(left.as_ref())
                && offset % elem_size == 0
            {
                let index = offset / elem_size;
                return Some(if index == 0 {
                    CExpr::deref(*right)
                } else {
                    CExpr::subscript(as_pointer(*right, elem_bytes), CExpr::IntLit(index))
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
                    CExpr::subscript(as_pointer(*left, elem_bytes), CExpr::IntLit(index))
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

fn populate_predicates(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &mut PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
) {
    view.predicate_expr_by_value.clear();

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
        let Some(lhs) = expr_for_compare_operand_with_width(
            symbols,
            inputs,
            lhs_var.clone(),
            view,
            compare_width,
        ) else {
            continue;
        };
        let Some(rhs) = expr_for_compare_operand_with_width(
            symbols,
            inputs,
            rhs_var.clone(),
            view,
            compare_width,
        ) else {
            continue;
        };
        let expr = CExpr::binary(binary_op_for_compare(compare.kind), lhs, rhs);
        let Some(cond_var) = prepared_var(inputs.prepared, predicate.condition) else {
            continue;
        };
        view.insert_predicate_expr(cond_var, expr.clone());
    }

    populate_derived_predicates(symbols, view, inputs);
}

fn populate_derived_predicates(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
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
                        boolean_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::And)
                    }
                    SSAOp::BoolOr { a, b, .. } => {
                        boolean_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::Or)
                    }
                    SSAOp::BoolXor { a, b, .. } => {
                        boolean_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::BitXor)
                    }
                    SSAOp::IntEqual { a, b, .. } => {
                        compare_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::Eq)
                    }
                    SSAOp::IntNotEqual { a, b, .. } => {
                        compare_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::Ne)
                    }
                    SSAOp::IntLess { a, b, .. } | SSAOp::IntSLess { a, b, .. } => {
                        compare_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::Lt)
                    }
                    SSAOp::IntLessEqual { a, b, .. } | SSAOp::IntSLessEqual { a, b, .. } => {
                        compare_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::Le)
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
}

fn boolean_expr_for_sources(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    lhs: &SSAVar,
    rhs: &SSAVar,
    op: BinaryOp,
) -> Option<CExpr> {
    let lhs = predicate_expr_for_operand(symbols, view, inputs, lhs)?;
    let rhs = predicate_expr_for_operand(symbols, view, inputs, rhs)?;
    Some(CExpr::binary(op, lhs, rhs))
}

fn compare_expr_for_sources(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    lhs: &SSAVar,
    rhs: &SSAVar,
    op: BinaryOp,
) -> Option<CExpr> {
    if let Some(expr) = reconstruct_zero_compare_from_def(symbols, view, inputs, lhs, rhs, op, 0) {
        return Some(expr);
    }
    if let Some(expr) = reconstruct_zero_compare_from_def(symbols, view, inputs, rhs, lhs, op, 0) {
        return Some(expr);
    }

    let compare_width = lhs.size.max(rhs.size);
    let lhs =
        expr_for_compare_operand_with_width(symbols, inputs, lhs.clone(), view, compare_width)?;
    let rhs =
        expr_for_compare_operand_with_width(symbols, inputs, rhs.clone(), view, compare_width)?;
    Some(CExpr::binary(op, lhs, rhs))
}

fn reconstruct_zero_compare_from_def(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
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

    let zero = compare_style_operand_expr(inputs.prepared, zero, candidate.size.max(zero.size))?;
    if !matches!(zero, CExpr::IntLit(0) | CExpr::UIntLit(0)) {
        return None;
    }

    reconstruct_zero_compare_from_nonzero_def(symbols, view, inputs, candidate, op, depth)
}

fn reconstruct_zero_compare_from_nonzero_def(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
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
            reconstruct_zero_compare_from_nonzero_def(symbols, view, inputs, src, op, depth + 1)
        }
        SSAOp::IntSub { a, b, .. } => {
            let compare_width = a.size.max(b.size);
            let lhs = expr_for_compare_operand_with_width(
                symbols,
                inputs,
                a.clone(),
                view,
                compare_width,
            )?;
            let rhs = expr_for_compare_operand_with_width(
                symbols,
                inputs,
                b.clone(),
                view,
                compare_width,
            )?;
            Some(CExpr::binary(op, lhs, rhs))
        }
        SSAOp::IntAnd { a, b, .. } if a == b => {
            let lhs =
                expr_for_compare_operand_with_width(symbols, inputs, a.clone(), view, a.size)?;
            Some(CExpr::binary(op, lhs, CExpr::IntLit(0)))
        }
        _ => None,
    }
}

fn predicate_expr_for_operand(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    var: &SSAVar,
) -> Option<CExpr> {
    predicate_expr_for_operand_with_depth(symbols, view, inputs, var, 0)
}

fn predicate_expr_for_operand_with_depth(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
    var: &SSAVar,
    depth: u32,
) -> Option<CExpr> {
    if depth > 8 {
        return None;
    }

    if let Some(expr) = view.predicate_expr_for_cond(var).cloned() {
        return Some(expr);
    }
    if let Some(expr) = compare_style_operand_expr(inputs.prepared, var, var.size) {
        return Some(expr);
    }
    if let Some(expr) =
        compare_def_expr_for_predicate_operand(symbols, view, inputs, var, depth + 1)
    {
        return Some(expr);
    }
    let expr = expr_for_compare_operand(symbols, inputs, var.clone(), view)?;
    let is_self = view
        .admitted_value_symbol(var)
        .is_some_and(|symbol| matches!(expr, CExpr::Var(candidate) if candidate == symbol));
    (!is_self).then_some(expr)
}

fn compare_def_expr_for_predicate_operand(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
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
            predicate_expr_for_operand_with_depth(symbols, view, inputs, src, depth + 1)
        }
        SSAOp::BoolNot { src, .. } => {
            predicate_expr_for_operand_with_depth(symbols, view, inputs, src, depth + 1)
                .map(|expr| CExpr::unary(UnaryOp::Not, expr))
        }
        SSAOp::BoolAnd { a, b, .. } => {
            let lhs = predicate_expr_for_operand_with_depth(symbols, view, inputs, a, depth + 1)?;
            let rhs = predicate_expr_for_operand_with_depth(symbols, view, inputs, b, depth + 1)?;
            Some(CExpr::binary(BinaryOp::And, lhs, rhs))
        }
        SSAOp::BoolOr { a, b, .. } => {
            let lhs = predicate_expr_for_operand_with_depth(symbols, view, inputs, a, depth + 1)?;
            let rhs = predicate_expr_for_operand_with_depth(symbols, view, inputs, b, depth + 1)?;
            Some(CExpr::binary(BinaryOp::Or, lhs, rhs))
        }
        SSAOp::BoolXor { a, b, .. } => {
            let lhs = predicate_expr_for_operand_with_depth(symbols, view, inputs, a, depth + 1)?;
            let rhs = predicate_expr_for_operand_with_depth(symbols, view, inputs, b, depth + 1)?;
            Some(CExpr::binary(BinaryOp::BitXor, lhs, rhs))
        }
        SSAOp::IntEqual { a, b, .. } => {
            compare_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::Eq)
        }
        SSAOp::IntNotEqual { a, b, .. } => {
            compare_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::Ne)
        }
        SSAOp::IntLess { a, b, .. } | SSAOp::IntSLess { a, b, .. } => {
            compare_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::Lt)
        }
        SSAOp::IntLessEqual { a, b, .. } | SSAOp::IntSLessEqual { a, b, .. } => {
            compare_expr_for_sources(symbols, view, inputs, a, b, BinaryOp::Le)
        }
        _ => {
            let _ = block;
            None
        }
    }
}

fn populate_calls(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &mut PreparedSemanticView,
    inputs: &PreparedSemanticViewInputs<'_>,
) {
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
        call_view.result_owner = certified_call_result_owner(
            symbols,
            site,
            inputs.prepared,
            view,
            inputs.call_result_facts(),
        );
        if let Some(owner) = call_view.result_owner.clone() {
            assign_certified_call_result_owner(
                site,
                inputs.prepared,
                view,
                inputs.call_result_facts(),
                &owner,
            );
        }
        let authoritative_args = canonical_call_authoritative_args(
            symbols,
            site,
            inputs.prepared.function(),
            inputs.prepared,
            view,
            inputs.callsite_facts(),
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

/// The arguments this call passes, in convention order.
///
/// How many there are is a fact about the call site, so the call site's own
/// certificate answers it and nothing else does. Asking the callee instead --
/// taking the arity off its recovered signature and truncating to it -- gives
/// one answer for every site that calls it, which is wrong the moment the
/// callee is variadic: `fprintf` declares two parameters and its three calls
/// in `bzip2recover`'s `tooManyBlocks` pass five, three and three. The cap
/// silently discarded the difference.
///
/// The sequence still has to be contiguous from index zero and every entry
/// still has to carry a location certificate, so a certificate with a gap in
/// it yields the prefix before the gap rather than a resequenced list.
fn canonical_call_authoritative_args(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    site: (u64, usize),
    function: &r2ssa::SSAFunction,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    callsite_facts: Option<&FunctionCallsiteFacts>,
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
    for argument in &call_facts.argument_values {
        if argument.index != args.len() {
            break;
        }
        if !call_arg_value_has_location_certificate(call_facts, argument.index, argument.value) {
            break;
        }
        if let Some(expr) =
            authoritative_expr_for_prepared_value(symbols, block, prepared, view, argument.value)
        {
            args.push((argument.value, expr));
        } else {
            break;
        }
    }

    // A stack-carried argument continues the same sequence, so it is admitted
    // only where its certificate says it does. The stack certificates are
    // numbered in their own space starting at zero, which is what a register
    // argument at the same index already claims, so the ones that do not
    // continue the register run stop the list rather than being renumbered
    // onto positions the machine never proved.
    for stack_arg in &call_facts.stack_argument_locations {
        if stack_arg.index != args.len() {
            break;
        }
        if let Some(expr) =
            authoritative_expr_for_prepared_value(symbols, block, prepared, view, stack_arg.value)
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
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    block: &r2ssa::FunctionSSABlock,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    value: ValueId,
) -> Option<CExpr> {
    let var = prepared.value_var(value)?;
    authoritative_scalar_expr_for_value(symbols, prepared, block, view, var, 0)
        .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, var, var.size))
        .or_else(|| view.owner_expr_for_var(var).cloned())
        .or_else(|| prepared_value_program_expr(symbols, view, var))
}

fn authoritative_scalar_expr_for_value(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    prepared: &SsaArtifact,
    block: &r2ssa::FunctionSSABlock,
    view: &PreparedSemanticView,
    var: &SSAVar,
    depth: u32,
) -> Option<CExpr> {
    if depth > 8 {
        return None;
    }

    if let Some(expr) = compare_style_operand_expr(prepared, var, var.size) {
        return Some(expr);
    }
    if let Some(expr) = view.predicate_expr_for_cond(var).cloned() {
        return Some(expr);
    }
    #[cfg(test)]
    if view.binding_names.is_none()
        && let Some(offset) = view.stack_offset_for_var(var)
        && let Some(alias) = preferred_stack_alias_name(view, offset)
    {
        return Some(crate::symbol::var_ref(symbols, alias));
    }
    if let Some(expr) = prepared_result_expr_for_var(symbols, view, var) {
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
            authoritative_scalar_expr_for_value(symbols, prepared, block, view, src, depth + 1)
                .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, src, src.size))
        }
        SSAOp::Load {
            space: r2il::SpaceId::Ram,
            addr,
            ..
        } => {
            #[cfg(test)]
            if view.binding_names.is_none()
                && let Some(expr) = view
                    .stack_offset_for_var(addr)
                    .and_then(|offset| preferred_stack_alias_name(view, offset))
                    .map(|name| crate::symbol::var_ref(symbols, name))
            {
                return Some(expr);
            }
            prepared_load_access_expr_for_addr(symbols, prepared, block, view, addr, var.size)
        }
        SSAOp::IntAdd { a, b, .. } => {
            authoritative_scalar_expr_for_value(symbols, prepared, block, view, a, depth + 1)
                .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, a, a.size))
                .zip(
                    authoritative_scalar_expr_for_value(
                        symbols,
                        prepared,
                        block,
                        view,
                        b,
                        depth + 1,
                    )
                    .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, b, b.size)),
                )
                .map(|(lhs, rhs)| CExpr::binary(BinaryOp::Add, lhs, rhs))
        }
        SSAOp::IntSub { a, b, .. } => {
            authoritative_scalar_expr_for_value(symbols, prepared, block, view, a, depth + 1)
                .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, a, a.size))
                .zip(
                    authoritative_scalar_expr_for_value(
                        symbols,
                        prepared,
                        block,
                        view,
                        b,
                        depth + 1,
                    )
                    .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, b, b.size)),
                )
                .map(|(lhs, rhs)| CExpr::binary(BinaryOp::Sub, lhs, rhs))
        }
        SSAOp::IntEqual { a, b, .. } => {
            authoritative_scalar_expr_for_value(symbols, prepared, block, view, a, depth + 1)
                .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, a, a.size))
                .zip(
                    authoritative_scalar_expr_for_value(
                        symbols,
                        prepared,
                        block,
                        view,
                        b,
                        depth + 1,
                    )
                    .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, b, b.size)),
                )
                .map(|(lhs, rhs)| CExpr::binary(BinaryOp::Eq, lhs, rhs))
        }
        SSAOp::IntNotEqual { a, b, .. } => {
            authoritative_scalar_expr_for_value(symbols, prepared, block, view, a, depth + 1)
                .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, a, a.size))
                .zip(
                    authoritative_scalar_expr_for_value(
                        symbols,
                        prepared,
                        block,
                        view,
                        b,
                        depth + 1,
                    )
                    .or_else(|| scalar_owner_expr_for_value(symbols, prepared, view, b, b.size)),
                )
                .map(|(lhs, rhs)| CExpr::binary(BinaryOp::Ne, lhs, rhs))
        }
        _ => None,
    }
}

fn prepared_result_expr_for_var(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    var: &SSAVar,
) -> Option<CExpr> {
    let site = view.call_result_source_for_var(var)?;
    let call_view = view.call_view_for_site(site)?;
    call_view
        .result_owner
        .clone()
        .or_else(|| prepared_call_expr_from_view(symbols, call_view))
}

fn certified_call_result_owner(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
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
        .filter_map(|cert| certified_call_result_owner_expr(symbols, cert, prepared, view))
        .next()
}

fn certified_call_result_owner_expr(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
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
            prepared_stack_program_expr_for_object_offset(symbols, view, *object, *offset)
        }
        Some(ValueOwner::Value(value)) if *value != cert.value => {
            let var = prepared.value_var(*value)?;
            (!var.is_register())
                .then(|| prepared_value_program_expr(symbols, view, var))
                .flatten()
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

fn stack_program_expr_for_memory_location(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    location: &MemoryLocation,
) -> Option<CExpr> {
    prepared_stack_program_expr_for_object_offset(
        symbols,
        view,
        location.object,
        location.address.exact_offset()?,
    )
}

#[cfg(test)]
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

#[cfg(test)]
fn prepared_stack_owner_offset_authorized(view: &PreparedSemanticView, offset: i64) -> bool {
    !view.certified_rendering_required
        || view
            .authorized_stack_owner_names
            .get(&offset)
            .is_some_and(|names| !names.is_empty())
}

#[cfg(test)]
fn prepared_stack_alias_name_for_object_offset(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    object: r2ssa::ObjectId,
    offset: i64,
) -> Option<String> {
    let authorized = view
        .authorized_stack_owner_names_by_object
        .get(&(object, offset))?;
    if view.binding_names.is_some() {
        return view
            .admitted_stack_symbol(object)
            .map(|symbol| crate::symbol::spelling(symbols, symbol).to_string());
    }
    #[cfg(test)]
    {
        preferred_stack_alias_name(view, offset)
            .filter(|alias| authorized.contains(&alias.to_ascii_lowercase()))
            .or_else(|| authorized.iter().next().cloned())
    }
    #[cfg(not(test))]
    {
        let _ = (symbols, authorized);
        None
    }
}

fn prepared_stack_program_expr_for_object_offset(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    object: r2ssa::ObjectId,
    offset: i64,
) -> Option<CExpr> {
    if view.binding_names.is_some() {
        return view.admitted_stack_symbol(object).map(CExpr::Var);
    }
    #[cfg(test)]
    {
        let _ = view
            .authorized_stack_owner_names_by_object
            .get(&(object, offset))?;
        prepared_stack_alias_name_for_object_offset(symbols, view, object, offset)
            .map(|name| crate::symbol::var_ref(symbols, name))
    }
    #[cfg(not(test))]
    {
        let _ = (symbols, offset);
        None
    }
}

fn prepared_stack_object_for_var(prepared: &SsaArtifact, var: &SSAVar) -> Option<r2ssa::ObjectId> {
    prepared
        .object_for_var(var, r2il::SpaceId::Ram)
        .or_else(|| {
            prepared
                .function()
                .decompile_prep_facts()
                .and_then(|facts| facts.canonical_root_of(var))
                .and_then(|root| prepared.object_for_var(root, r2il::SpaceId::Ram))
        })
}

fn prepared_stack_program_expr_for_var(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    prepared: &SsaArtifact,
    var: &SSAVar,
) -> Option<CExpr> {
    if view.binding_names.is_some() {
        return prepared_stack_object_for_var(prepared, var)
            .and_then(|object| view.admitted_stack_symbol(object))
            .map(CExpr::Var);
    }
    #[cfg(test)]
    {
        let offset = view
            .stack_offset_for_var(var)
            .or_else(|| stack_offset_for_value(prepared, var))?;
        prepared_stack_alias_expr_for_offset(symbols, view, offset)
    }
    #[cfg(not(test))]
    {
        let _ = symbols;
        None
    }
}

#[cfg(test)]
fn prepared_stack_alias_name_for_offset(
    view: &PreparedSemanticView,
    offset: i64,
) -> Option<String> {
    preferred_stack_alias_name(view, offset)
        .filter(|alias| !alias.is_empty())
        .filter(|alias| prepared_stack_owner_recovery_allowed(view, offset, alias))
}

fn prepared_stack_alias_expr_for_offset(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    offset: i64,
) -> Option<CExpr> {
    #[cfg(test)]
    {
        if view.binding_names.is_none() {
            return prepared_stack_alias_name_for_offset(view, offset)
                .map(|name| crate::symbol::var_ref(symbols, name));
        }
        None
    }
    #[cfg(not(test))]
    {
        let _ = (symbols, view, offset);
        None
    }
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

fn expr_for_compare_operand(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    inputs: &PreparedSemanticViewInputs<'_>,
    var: SSAVar,
    view: &PreparedSemanticView,
) -> Option<CExpr> {
    expr_for_compare_operand_with_width(symbols, inputs, var, view, 0)
}

fn expr_for_compare_operand_with_width(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    inputs: &PreparedSemanticViewInputs<'_>,
    var: SSAVar,
    view: &PreparedSemanticView,
    compare_width: u32,
) -> Option<CExpr> {
    if let Some(expr) = compare_style_operand_expr(inputs.prepared, &var, compare_width) {
        return Some(expr);
    }

    let root = inputs
        .prepared
        .function()
        .decompile_prep_facts()
        .and_then(|facts| facts.canonical_root_of(&var))
        .cloned()
        .unwrap_or_else(|| var.clone());
    if let Some(expr) = compare_style_operand_expr(inputs.prepared, &root, compare_width) {
        return Some(expr);
    }

    if let Some(expr) = prepared_parameter_program_expr(symbols, view, inputs.prepared, &root)
        .or_else(|| prepared_parameter_program_expr(symbols, view, inputs.prepared, &var))
    {
        return Some(expr);
    }

    if let Some(expr) = non_generic_prepared_owner_expr(symbols, view, &var)
        .or_else(|| non_generic_prepared_predicate_expr(symbols, view, &var))
        .or_else(|| non_generic_prepared_owner_expr(symbols, view, &root))
        .or_else(|| non_generic_prepared_predicate_expr(symbols, view, &root))
    {
        return Some(expr);
    }

    #[cfg(test)]
    if preferred_non_generic_stack_alias(view, &var).is_some()
        && let Some(expr) =
            prepared_stack_program_expr_for_var(symbols, view, inputs.prepared, &var)
    {
        return Some(expr);
    }
    #[cfg(test)]
    if preferred_non_generic_stack_alias(view, &root).is_some()
        && let Some(expr) =
            prepared_stack_program_expr_for_var(symbols, view, inputs.prepared, &root)
    {
        return Some(expr);
    }

    if let Some(expr) =
        generic_prepared_owner_expr(view, &var).or_else(|| generic_prepared_owner_expr(view, &root))
    {
        return Some(expr);
    }

    if view.stack_offset_for_var(&var).is_some()
        && let Some(expr) =
            prepared_stack_program_expr_for_var(symbols, view, inputs.prepared, &var)
    {
        return Some(expr);
    }
    if view.stack_offset_for_var(&root).is_some()
        && let Some(expr) =
            prepared_stack_program_expr_for_var(symbols, view, inputs.prepared, &root)
    {
        return Some(expr);
    }

    if let Some(expr) = prepared_fallback_visible_expr(symbols, view, &root)
        .or_else(|| prepared_fallback_visible_expr(symbols, view, &var))
    {
        return Some(expr);
    }

    prepared_value_program_expr(symbols, view, &var)
}

fn exact_prepared_constant_bits(prepared: &SsaArtifact, var: &SSAVar) -> Option<u64> {
    let bits = var.constant_bits()?;
    let value = prepared
        .graph()
        .value_id_for_var(var)
        .and_then(|value| prepared.graph().value(value))?;
    let storage = value.canonical_storage?;
    (storage.space == r2ssa::CanonicalStorageSpace::Constant
        && storage.offset == bits
        && storage.size == var.size)
        .then_some(bits)
}

fn compare_style_operand_expr(
    prepared: &SsaArtifact,
    var: &SSAVar,
    _compare_width: u32,
) -> Option<CExpr> {
    fn lit_for_u64(value: u64) -> CExpr {
        if value > 0x7fff_ffff {
            CExpr::UIntLit(value)
        } else {
            CExpr::IntLit(value as i64)
        }
    }

    exact_prepared_constant_bits(prepared, var).map(lit_for_u64)
}

fn binary_op_for_compare(kind: CompareKind) -> BinaryOp {
    match kind {
        CompareKind::Equal => BinaryOp::Eq,
        CompareKind::NotEqual => BinaryOp::Ne,
        CompareKind::Less | CompareKind::SignedLess => BinaryOp::Lt,
        CompareKind::LessEqual | CompareKind::SignedLessEqual => BinaryOp::Le,
    }
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
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    var: &SSAVar,
    compare_width: u32,
) -> Option<CExpr> {
    compare_style_operand_expr(prepared, var, compare_width)
        .or_else(|| prepared_value_program_expr(symbols, view, var))
        .or_else(|| non_generic_prepared_predicate_expr(symbols, view, var))
        .or_else(|| non_generic_prepared_owner_expr(symbols, view, var))
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
            #[cfg(test)]
            if view.binding_names.is_none() {
                return view
                    .stack_offset_for_var(var)
                    .and_then(|offset| preferred_stack_alias_name(view, offset))
                    .filter(|alias| {
                        !is_generic_prepared_stack_alias(alias) && !alias.ends_with("_home")
                    })
                    .map(|name| crate::symbol::var_ref(symbols, name));
            }
            None
        })
        .or_else(|| view.predicate_expr_for_cond(var).cloned())
        .or_else(|| generic_prepared_owner_expr(view, var))
}

fn prepared_binary_owner_expr(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    op: BinaryOp,
    a: &SSAVar,
    b: &SSAVar,
    compare_width: u32,
) -> Option<CExpr> {
    let lhs = scalar_owner_expr_for_value(symbols, prepared, view, a, compare_width)?;
    let rhs = scalar_owner_expr_for_value(symbols, prepared, view, b, compare_width)?;
    Some(prepared_simplify_binary_expr(symbols, view, op, lhs, rhs))
}

fn prepared_simplify_binary_expr(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    op: BinaryOp,
    mut lhs: CExpr,
    mut rhs: CExpr,
) -> CExpr {
    if prepared_binary_op_is_commutative(op)
        && prepared_expr_order_key(symbols, view, &rhs)
            < prepared_expr_order_key(symbols, view, &lhs)
    {
        std::mem::swap(&mut lhs, &mut rhs);
    }

    match op {
        BinaryOp::Add => {
            if prepared_expr_is_zero(&lhs) {
                rhs
            } else if prepared_expr_is_zero(&rhs) {
                lhs
            } else if let Some(expr) = prepared_simplify_linear_addition(symbols, view, &lhs, &rhs)
            {
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
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    left: &CExpr,
    right: &CExpr,
) -> Option<CExpr> {
    let mut terms = Vec::new();
    let mut constant = 0i64;
    prepared_collect_linear_add_terms(view, left, 1, &mut terms, &mut constant)?;
    prepared_collect_linear_add_terms(view, right, 1, &mut terms, &mut constant)?;
    terms.retain(|(_, coeff)| *coeff != 0);
    terms.sort_by_key(|(term, _)| prepared_expr_order_key(symbols, view, term));

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

fn prepared_parameter_rank(
    view: &PreparedSemanticView,
    symbol: crate::symbol::SymbolId,
) -> Option<usize> {
    view.binding_names
        .as_ref()?
        .parameters()
        .filter_map(Result::ok)
        .find_map(|parameter| {
            (parameter.symbol == symbol)
                .then(|| usize::try_from(parameter.slot).ok())
                .flatten()
        })
}

fn prepared_linear_atom_expr(view: &PreparedSemanticView, expr: &CExpr) -> Option<CExpr> {
    match expr {
        CExpr::Var(name) if prepared_parameter_rank(view, *name).is_some() => Some(expr.clone()),
        CExpr::Paren(inner) => prepared_linear_atom_expr(view, inner),
        CExpr::Cast {
            ty, expr: inner, ..
        } if ty.is_integer() && prepared_linear_atom_expr(view, inner).is_some() => {
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

fn prepared_expr_order_key(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    expr: &CExpr,
) -> (u8, usize, std::rc::Rc<str>) {
    match expr {
        CExpr::Var(name) => prepared_parameter_rank(view, *name)
            .map(|rank| (0, rank, crate::symbol::spelling(symbols, *name)))
            .unwrap_or_else(|| (1, usize::MAX, crate::symbol::spelling(symbols, *name))),
        CExpr::IntLit(value) => (
            2,
            usize::MAX,
            std::rc::Rc::from(format!("{value:020}").as_str()),
        ),
        CExpr::UIntLit(value) => (
            2,
            usize::MAX,
            std::rc::Rc::from(format!("{value:020}").as_str()),
        ),
        CExpr::Paren(inner) | CExpr::Cast { expr: inner, .. } => {
            prepared_expr_order_key(symbols, view, inner)
        }
        _ => (
            1,
            usize::MAX,
            std::rc::Rc::from(format!("{expr:?}").as_str()),
        ),
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
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    producer_by_dst: &HashMap<SSAVar, &SSAOp>,
    dividend: &SSAVar,
) -> Option<CExpr> {
    let dividend_value = prepared.graph().value_id_for_var(dividend)?;
    let certificate = prepared.certificates().expressions.get(&dividend_value)?;
    if certificate.value != dividend_value
        || certificate.width != dividend.size
        || !certificate.renderable
    {
        return None;
    }
    let SSAOp::IntOr {
        a: high_part,
        b: low_part,
        ..
    } = producer_by_dst.get(dividend).copied()?
    else {
        return None;
    };
    prepared_sign_extended_pair_low_root(prepared, producer_by_dst, high_part, low_part)
        .or_else(|| {
            prepared_sign_extended_pair_low_root(prepared, producer_by_dst, low_part, high_part)
        })
        .and_then(|root| scalar_owner_expr_for_value(symbols, prepared, view, root, root.size))
}

fn prepared_sign_extended_pair_low_root<'a>(
    prepared: &SsaArtifact,
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
        && prepared_shift_matches_signed_concat_width(prepared, shift, high, low, low_root)
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
    prepared: &SsaArtifact,
    shift: &SSAVar,
    high: &SSAVar,
    low: &SSAVar,
    low_root: &SSAVar,
) -> bool {
    let Some(shift_bits) = exact_prepared_constant_bits(prepared, shift) else {
        return false;
    };
    [low.size, low_root.size, high.size]
        .into_iter()
        .filter(|size| *size > 0)
        .any(|size| shift_bits == u64::from(size.saturating_mul(8)))
}

fn prepared_address_owner_expr_for_value(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    var: &SSAVar,
    compare_width: u32,
) -> Option<CExpr> {
    scalar_owner_expr_for_value(symbols, prepared, view, var, compare_width)
}

fn prepared_scaled_index_owner_expr(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    var: &SSAVar,
    compare_width: u32,
) -> Option<CExpr> {
    scalar_owner_expr_for_value(symbols, prepared, view, var, compare_width)
        .or_else(|| generic_prepared_owner_expr(view, var))
        .or_else(|| prepared_fallback_visible_expr(symbols, view, var))
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

#[cfg(test)]
fn preferred_non_generic_stack_alias(view: &PreparedSemanticView, var: &SSAVar) -> Option<String> {
    view.stack_offset_for_var(var)
        .and_then(|offset| preferred_stack_alias_name(view, offset))
        .filter(|alias| !is_generic_prepared_stack_alias(alias) && !alias.ends_with("_home"))
}

fn non_generic_prepared_owner_expr(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    var: &SSAVar,
) -> Option<CExpr> {
    view.owner_expr_for_var(var)
        .cloned()
        .filter(|expr| !matches!(expr, CExpr::AddrOf(_)))
        .filter(|expr| !prepared_expr_is_generic_scalar_alias(symbols, expr))
}

fn generic_prepared_owner_expr(view: &PreparedSemanticView, var: &SSAVar) -> Option<CExpr> {
    view.owner_expr_for_var(var)
        .cloned()
        .filter(|expr| !matches!(expr, CExpr::AddrOf(_)))
}

fn non_generic_prepared_predicate_expr(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    var: &SSAVar,
) -> Option<CExpr> {
    view.predicate_expr_for_cond(var)
        .cloned()
        .filter(|expr| !prepared_expr_is_generic_scalar_alias(symbols, expr))
}

fn prepared_fallback_visible_expr(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    var: &SSAVar,
) -> Option<CExpr> {
    if var.constant_bits().is_some() {
        return None;
    }

    // Writing the value's name here is a promise that something will define it,
    // and this pass is not in a position to make it: it runs over every block
    // before the fold decides which statements exist, so a value whose statement
    // the fold later leaves out keeps a name nothing writes. The name is then
    // frozen inside whatever definition embedded it, and no later resolution can
    // reach it -- `pearson` at x86-64 -O0 renders `local_19 = rcx_4[...]` that
    // way, while asking the fold about `RCX_4` answers `(int64_t)eax_3`.
    //
    // Declining for a computed value leaves it to the fold, which knows what it
    // emitted. Version zero is different and keeps its name: that is the value
    // the function was entered with, it has no defining statement to leave out,
    // and a parameter or an entry register is always spelled.
    //
    // The version is part of which value this is, and the definition side spells
    // it that way. Naming the storage alone made a use of `x19_3` print as
    // `x19`, which no longer matched the definition of `x19_3` -- so a
    // definition with eleven readers looked unread and was deleted, leaving the
    // readers naming nothing. Version zero stays bare, as it does everywhere:
    // that is the value the function was entered with.
    if var.version > 0 {
        return None;
    }
    prepared_value_program_expr(symbols, view, var)
}

#[cfg(test)]
fn local_store_owner_expr_for_offset(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    view: &PreparedSemanticView,
    prepared: &SsaArtifact,
    block: &r2ssa::FunctionSSABlock,
    before_idx: usize,
    offset: i64,
) -> Option<CExpr> {
    if !prepared_stack_owner_offset_authorized(view, offset) {
        return None;
    }
    let prefer_stack_object = preferred_stack_alias_name(view, offset)
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
        if let Some(expr) = scalar_owner_expr_for_value(symbols, prepared, view, val, val.size) {
            if prefer_stack_object
                && let Some(stack) =
                    prepared_stack_program_expr_for_var(symbols, view, prepared, addr)
            {
                return Some(stack);
            }
            if matches!(&expr, CExpr::Var(name) if !is_generic_prepared_stack_alias(&crate::symbol::spelling(symbols, *name)))
            {
                return Some(expr);
            }
            return Some(expr);
        }
    }
    prepared_stack_alias_expr_for_offset(symbols, view, offset)
}

#[cfg(not(test))]
fn local_store_owner_expr_for_offset(
    _symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    _view: &PreparedSemanticView,
    _prepared: &SsaArtifact,
    _block: &r2ssa::FunctionSSABlock,
    _before_idx: usize,
    _offset: i64,
) -> Option<CExpr> {
    None
}

#[cfg(test)]
fn preferred_stack_alias_name(view: &PreparedSemanticView, offset: i64) -> Option<String> {
    let alias = view.stack_alias_for_offset(offset)?;
    let visible = alias.visible_name.trim();
    (!visible.is_empty()).then(|| visible.to_string())
}

#[cfg(test)]
fn is_generic_prepared_stack_alias(name: &str) -> bool {
    name.starts_with("var_")
        || name.starts_with("local_")
        || name.starts_with("stack_")
        || name.starts_with("arg_")
}

#[cfg(test)]
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

#[cfg(test)]
fn synthetic_stack_name(offset: i64) -> String {
    if offset < 0 {
        format!("local_{:x}", (-offset) as u64)
    } else {
        format!("stack_{:x}", offset as u64)
    }
}

fn seed_prepared_stack_facts(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    use_info: &mut UseInfo,
    _stack_info: &mut StackInfo,
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) {
    #[cfg(not(test))]
    let _ = symbols;
    #[cfg(test)]
    for offset in view.stack_aliases_by_offset.keys() {
        if let Some(stack_expr) = prepared_stack_alias_expr_for_offset(symbols, view, *offset) {
            let CExpr::Var(stack_symbol) = stack_expr else {
                continue;
            };
            let name = crate::symbol::spelling(symbols, stack_symbol).to_string();
            _stack_info
                .stack_vars
                .entry(*offset)
                .or_insert(name.clone());
        }
    }

    for (key, object_id) in &prepared.objects().value_objects {
        if key.space != r2il::SpaceId::Ram {
            continue;
        }
        let Some(object) = prepared.objects().object(*object_id) else {
            continue;
        };
        let Some(_offset) = stack_offset_for_object_kind(&object.kind) else {
            continue;
        };
        let Some(value) = prepared_var(prepared, key.value) else {
            continue;
        };
        let value_id = key.value;
        if use_info.bind_value_id(value, value_id).is_none() {
            continue;
        }
        #[cfg(test)]
        let test_alias = preferred_stack_alias_name(view, _offset)
            .map(|name| crate::symbol::var_ref(symbols, name));
        #[cfg(not(test))]
        let test_alias = None;
        if let Some(_stack_expr) = view
            .admitted_stack_symbol(*object_id)
            .map(CExpr::Var)
            .or(test_alias)
        {
            #[cfg(test)]
            _stack_info
                .definition_overrides
                .entry(value.display_name())
                .or_insert_with(|| CExpr::AddrOf(Box::new(_stack_expr.clone())));
        }
    }
}

fn collect_prepared_runtime_facts(
    use_info: &mut UseInfo,
    blocks: &[SSABlock],
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
) {
    for block in blocks {
        for phi in &block.phis {
            let _ = bind_prepared_value_id(use_info, view, &phi.dst);
            for (_, src) in &phi.sources {
                // Bind first, then let the one helper write both halves.
                // Writing them here as well meant a second copy of the pairing
                // rule living beside the first.
                let _ = bind_prepared_value_id(use_info, view, src);
            }
            let _ = bind_prepared_value_id(use_info, view, &phi.dst);
        }

        for op in &block.ops {
            for src in op.sources() {
                let _ = bind_prepared_value_id(use_info, view, src);
            }
            // A value defined by adding or subtracting a constant is that
            // operand at an offset. This was the only fact the local-struct
            // overlay contributed here: measured over both fixtures it offered
            // 18, 252, 121 and 100 semantic values and none were taken, because
            // a prepared value already answered for every name, while every
            // pointer member it offered was taken because nothing else computes
            // them. So the rule moves here and the overlay goes.
            if let SSAOp::CBranch { cond, .. } = op {
                let _ = bind_prepared_value_id(use_info, view, cond);
            }

            if let Some(dst) = op.dst() {
                let _ = bind_prepared_value_id(use_info, view, dst);
            }

            match op {
                SSAOp::Copy { dst, src }
                | SSAOp::IntZExt { dst, src }
                | SSAOp::IntSExt { dst, src }
                | SSAOp::Trunc { dst, src }
                | SSAOp::Cast { dst, src, .. }
                | SSAOp::Subpiece { dst, src, .. } => {
                    let bound_copy = bind_prepared_copy_ids(use_info, view, dst, src);
                    let bound_dst_id = bound_copy.map(|(dst_id, _)| dst_id);
                    let bound_src_id = bound_copy.map(|(_, src_id)| src_id);
                    let source_stack_slot = use_info
                        .forwarded_value_for_var(src)
                        .and_then(|provenance| provenance.stack_slot)
                        .or_else(|| view.stack_offset_for_var(src))
                        .or_else(|| stack_offset_for_value(prepared, src));
                    // Forwarding a carrier member past its merge would restore the value it entered with.
                    let forwards = !bound_dst_id
                        .is_some_and(|value| view.certified_loop_carrier_values.contains(&value));
                    if forwards {
                        // One provenance, keyed by identity. There used to be
                        // two: this site wrote the end of the forwarding chain
                        // under the name and the immediate copy source under the
                        // value, and which one a caller got depended on which
                        // half it reached. The chained one is gone with the name
                        // half.
                        if let (Some(dst_id), Some(src_id)) = (bound_dst_id, bound_src_id) {
                            use_info.forwarded_values_by_value.insert(
                                dst_id,
                                exact_prepared_copy_provenance(src, src_id, source_stack_slot),
                            );
                        } else {
                            use_info
                                .dropped_unkeyed_fact
                                .get_or_insert("forwarded_values");
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

fn populate_prepared_call_runtime_facts(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    use_info: &mut UseInfo,
    blocks: &[SSABlock],
    prepared: &SsaArtifact,
    view: &PreparedSemanticView,
    origins: &crate::normalize::NormalizationOrigins,
) {
    for block in blocks {
        for (op_idx, op) in block.ops.iter().enumerate() {
            if !matches!(op, SSAOp::Call { .. } | SSAOp::CallInd { .. }) {
                continue;
            }
            let Some(block_id) = prepared.graph().block_id_for_addr(block.addr) else {
                continue;
            };
            let normalized_site = crate::normalize::NormalizedOpSite {
                block: block_id,
                op_idx,
            };
            let Some(crate::normalize::NormalizedOpOrigin::Original(inst)) =
                origins.origin(normalized_site)
            else {
                continue;
            };
            let Some(site) = prepared.inst_op_site(*inst) else {
                continue;
            };
            let Some(call_view) = view.call_view_for_site(site) else {
                continue;
            };
            if !prepared_call_render_authorized(call_view) {
                continue;
            }

            if let Some(call_expr) = prepared_call_expr(site, symbols, call_view) {
                use_info.call_result_exprs.insert(site, call_expr.clone());
            }
        }
    }
}

fn prepared_call_expr(
    site: (u64, usize),
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    call_view: &PreparedCallView,
) -> Option<CExpr> {
    if !prepared_call_render_authorized(call_view) {
        return None;
    }
    if !prepared_call_args_have_value_bijection(call_view) {
        return None;
    }
    let callee = prepared_call_callee_expr(symbols, call_view)?;
    let args = call_view
        .authoritative_args
        .iter()
        .map(|arg| normalize_prepared_inline_expr(arg.clone(), 0))
        .collect();
    Some(CExpr::call_at(site, callee, args))
}

fn prepared_call_callee_expr(
    _symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    call_view: &PreparedCallView,
) -> Option<CExpr> {
    let identity = call_view.callee_identity.as_ref()?;
    let name = identity
        .display_name
        .clone()
        .unwrap_or_else(|| identity.primary_key());
    let kind = match identity.class {
        r2types::CalleeClass::Imported => crate::symbol::ExternalKind::Import,
        r2types::CalleeClass::ExternalSymbol => crate::symbol::ExternalKind::Global,
        r2types::CalleeClass::Internal
        | r2types::CalleeClass::RawAddress
        | r2types::CalleeClass::Indirect
        | r2types::CalleeClass::Unknown => crate::symbol::ExternalKind::Function,
    };
    Some(CExpr::External { name, kind })
}

fn prepared_call_expr_from_view(
    symbols: &std::cell::RefCell<crate::symbol::SymbolTable>,
    call_view: &PreparedCallView,
) -> Option<CExpr> {
    if !prepared_call_render_authorized(call_view) {
        return None;
    }
    if !prepared_call_args_have_value_bijection(call_view) {
        return None;
    }
    let callee = prepared_call_callee_expr(symbols, call_view)?;
    Some(CExpr::call(callee, call_view.authoritative_args.clone()))
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

fn normalize_prepared_inline_expr(expr: CExpr, depth: u32) -> CExpr {
    if depth > 8 {
        return expr;
    }

    match expr {
        // SymbolId already is the exact rendered identity. No presentation
        // spelling is reversed to discover another value.
        CExpr::Var(name) => CExpr::Var(name),
        CExpr::Paren(inner) => {
            CExpr::Paren(Box::new(normalize_prepared_inline_expr(*inner, depth + 1)))
        }
        CExpr::Cast { ty, expr, .. } => {
            CExpr::cast(ty, normalize_prepared_inline_expr(*expr, depth + 1))
        }
        CExpr::AddrOf(inner) => {
            CExpr::AddrOf(Box::new(normalize_prepared_inline_expr(*inner, depth + 1)))
        }
        CExpr::Deref(inner) => {
            CExpr::Deref(Box::new(normalize_prepared_inline_expr(*inner, depth + 1)))
        }
        CExpr::Unary { op, operand } => {
            CExpr::unary(op, normalize_prepared_inline_expr(*operand, depth + 1))
        }
        CExpr::Binary { op, left, right } => CExpr::binary(
            op,
            normalize_prepared_inline_expr(*left, depth + 1),
            normalize_prepared_inline_expr(*right, depth + 1),
        ),
        CExpr::Subscript { base, index } => CExpr::Subscript {
            base: Box::new(normalize_prepared_inline_expr(*base, depth + 1)),
            index: Box::new(normalize_prepared_inline_expr(*index, depth + 1)),
        },
        CExpr::Member { base, member } => CExpr::Member {
            base: Box::new(normalize_prepared_inline_expr(*base, depth + 1)),
            member,
        },
        CExpr::PtrMember { base, member } => CExpr::PtrMember {
            base: Box::new(normalize_prepared_inline_expr(*base, depth + 1)),
            member,
        },
        CExpr::Call { func, args, site } => CExpr::Call {
            site,
            func: Box::new(normalize_prepared_inline_expr(*func, depth + 1)),
            args: args
                .into_iter()
                .map(|arg| normalize_prepared_inline_expr(arg, depth + 1))
                .collect(),
        },
        CExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => CExpr::Ternary {
            cond: Box::new(normalize_prepared_inline_expr(*cond, depth + 1)),
            then_expr: Box::new(normalize_prepared_inline_expr(*then_expr, depth + 1)),
            else_expr: Box::new(normalize_prepared_inline_expr(*else_expr, depth + 1)),
        },
        CExpr::Comma(items) => CExpr::Comma(
            items
                .into_iter()
                .map(|item| normalize_prepared_inline_expr(item, depth + 1))
                .collect(),
        ),
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::InterprocSummarySet;

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

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
        // The spoof's forwarding fact is filed under the spoof's identity. There
        // is no name-keyed half for it to be filed under any more, which is what
        // makes the collision this test was written for impossible rather than
        // merely avoided: `src` and `spoof` share a display name and differ as
        // values, and a store keyed by value cannot confuse them.
        info.forwarded_values_by_value.insert(
            ValueId(3),
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
    fn canonical_frame_pointer_slot_uses_runtime_offset() {
        let slot = StackSlotKey {
            base: ExternalStackBase::FramePointer,
            offset: 8,
        };
        assert_eq!(prepared_stack_slot_offset(&slot), -8);

        let legacy_slot = StackSlotKey {
            base: ExternalStackBase::FramePointer,
            offset: -8,
        };
        assert_eq!(prepared_stack_slot_offset(&legacy_slot), -8);
    }

    fn test_var(name: &str, version: u32, size: u32) -> SSAVar {
        SSAVar::new(name, version, size)
    }

    fn test_prepared_constant(value: u64) -> (SsaArtifact, SSAVar) {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x100, 8),
            src: Varnode::constant(value, 8),
        });
        let prepared = SsaArtifact::from_blocks(&[block], None).expect("prepared constant SSA");
        let constant = prepared
            .graph()
            .values
            .iter()
            .find(|candidate| candidate.var.constant_bits() == Some(value))
            .expect("exact graph constant")
            .var
            .clone();
        (prepared, constant)
    }

    #[test]
    fn prepared_constants_require_exact_graph_constant_storage() {
        let (prepared, constant) = test_prepared_constant(0x40);
        assert_eq!(
            compare_style_operand_expr(&prepared, &constant, 8),
            Some(CExpr::IntLit(0x40))
        );

        for spoof in ["0d64", "0x40", "40", "deadbeef", "const:40"] {
            assert_eq!(
                compare_style_operand_expr(&prepared, &test_var(spoof, 0, 8), 8),
                None,
                "presentation spelling {spoof:?} is not constant evidence"
            );
        }

        let mut foreign = constant.clone();
        foreign.name = "0x40".to_string();
        assert_eq!(foreign.constant_bits(), Some(0x40));
        assert_eq!(
            compare_style_operand_expr(&prepared, &foreign, 8),
            None,
            "typed bits without exact graph identity and Constant storage must fail closed"
        );
    }

    #[test]
    fn signed_dividend_shift_requires_exact_constant_identity() {
        let (prepared, shift) = test_prepared_constant(64);
        let limb = test_var("limb", 1, 8);
        assert!(prepared_shift_matches_signed_concat_width(
            &prepared, &shift, &limb, &limb, &limb
        ));
        assert!(!prepared_shift_matches_signed_concat_width(
            &prepared,
            &test_var("const:40", 0, 8),
            &limb,
            &limb,
            &limb
        ));
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
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
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
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let revision = b"prepared-semantic-two-arg-call";
        let function_interface = r2ssa::SourceFunctionInterface::new_exact(
            revision.to_vec(),
            "sysv64",
            [
                r2ssa::SourceAbiParameterSpec::new(0, storage(0x10)),
                r2ssa::SourceAbiParameterSpec::new(1, storage(0x18)),
            ],
            r2ssa::SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
        .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
        .expect("exact two-arg function interface");
        let call_target = Varnode::constant(0x401000, 8);
        let call_interface = r2ssa::SourceCallSiteInterface::new(
            revision.to_vec(),
            r2ssa::SourceCallSiteIdentity::new(
                0x1000,
                2,
                r2ssa::CanonicalStorageId::from_varnode(&call_target),
            ),
            true,
            "sysv64",
            [
                r2ssa::SourceCallArgumentSpec::new(0, storage(0x10)),
                r2ssa::SourceCallArgumentSpec::new(1, storage(0x18)),
            ],
            false,
            false,
            r2ssa::SourceCallResult::Void,
        )
        .expect("exact two-arg callsite interface");
        SsaArtifact::for_decompile_with_interfaces(
            &[block],
            Some(&arch),
            Some(function_interface),
            vec![call_interface],
        )
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
                        let r2ssa::CallArgumentLocation::Register { storage } = argument.location
                        else {
                            return None;
                        };
                        Some(r2types::RegisterCallArgumentLocationFact {
                            index: argument.index,
                            value: argument.value,
                            storage,
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
                        variadic: cert.variadic,
                        fixed_argument_count: cert.fixed_argument_count,
                        callee_signature: None,
                        variadic_argument_count_evidence: cert.variadic_argument_count_evidence,
                        variadic_argument_count_refusal: cert.variadic_argument_count_refusal,
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

    #[test]
    fn prepared_call_expr_requires_argument_value_bijection() {
        let symbols = test_table();
        let unproved = PreparedCallView {
            callee_identity: Some(CalleeIdentity::from_name("sym.helper")),
            authoritative_args: vec![CExpr::IntLit(7)],
            authoritative_arg_values: Vec::new(),
            ..PreparedCallView::default()
        };
        assert!(
            prepared_call_expr_from_view(&symbols, &unproved).is_none(),
            "prepared call expressions must not carry rendered args without ValueId proof"
        );

        let missing_render_fact = PreparedCallView {
            callee_identity: Some(CalleeIdentity::from_name("sym.helper")),
            authoritative_args: vec![CExpr::IntLit(7)],
            authoritative_arg_values: vec![ValueId(7)],
            ..PreparedCallView::default()
        };
        assert!(
            prepared_call_expr_from_view(&symbols, &missing_render_fact).is_none(),
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
            prepared_call_expr_from_view(&symbols, &proved),
            Some(CExpr::Call {
                func: Box::new(CExpr::External {
                    name: "sym.helper".to_string(),
                    kind: crate::symbol::ExternalKind::Function,
                }),
                args: vec![CExpr::IntLit(7)],
                site: None,
            })
        );
    }

    #[test]
    fn prepared_view_prefers_typed_callee_resolution_over_raw_name_maps() {
        let symbols = test_table();
        let prepared = test_prepared_call_artifact();
        let resolution_function_names = HashMap::from([(0x401000, "sym.imp.printf".to_string())]);
        let binary_symbols = HashMap::new();
        let callee_facts = BTreeMap::new();
        let known_function_signatures = HashMap::new();
        let resolution_ctx = r2types::CalleeIdentityContext {
            function_names: &resolution_function_names,
            symbols: &binary_symbols,
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
        let function_facts =
            FunctionFacts::default().with_callee_resolution(callee_resolution.clone());

        let view = PreparedSemanticView::build(
            &symbols,
            PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: &stack_slots,
                visible_bindings: &visible_bindings,
                function_facts: &function_facts,
                certified_rendering_required: false,
            },
        );

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
        let symbols = test_table();
        let prepared = test_prepared_call_artifact();
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
        let callsite_facts = test_callsite_facts(&prepared);
        let function_facts = FunctionFacts::default()
            .with_callee_resolution(callee_resolution.clone())
            .with_callsites(callsite_facts.clone());

        let view = PreparedSemanticView::build(
            &symbols,
            PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: &stack_slots,
                visible_bindings: &visible_bindings,
                function_facts: &function_facts,
                certified_rendering_required: false,
            },
        );

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
        let symbols = test_table();
        let prepared = test_prepared_call_artifact();
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
        let function_facts =
            FunctionFacts::default().with_callee_resolution(callee_resolution.clone());

        let view = PreparedSemanticView::build(
            &symbols,
            PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: &stack_slots,
                visible_bindings: &visible_bindings,
                function_facts: &function_facts,
                certified_rendering_required: false,
            },
        );

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
        let symbols = test_table();
        let prepared = test_prepared_call_artifact();
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();

        let view = PreparedSemanticView::build(
            &symbols,
            PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: &stack_slots,
                visible_bindings: &visible_bindings,
                function_facts: leak_function_facts(FunctionFacts::default()),
                certified_rendering_required: false,
            },
        );

        let call_view = view
            .call_view_for_site((0x1000, 0))
            .expect("direct callsite should have prepared call view");
        assert!(
            call_view.callee_identity.is_none(),
            "prepared semantic view must not certify raw callee names without typed resolution"
        );
        assert!(
            prepared_call_expr_from_view(&symbols, call_view).is_none(),
            "prepared calls must not fall back to fabricated sub_<addr> expressions"
        );
    }

    #[test]
    fn prepared_view_refuses_recursive_name_identity_without_typed_resolution() {
        let symbols = test_table();
        let prepared = test_prepared_recursive_call_artifact();
        assert_eq!(
            prepared.structured().recursive_calls.len(),
            1,
            "fixture should expose a structural recursive call"
        );
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();

        let view = PreparedSemanticView::build(
            &symbols,
            PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: &stack_slots,
                visible_bindings: &visible_bindings,
                function_facts: leak_function_facts(FunctionFacts::default()),
                certified_rendering_required: false,
            },
        );

        let call_view = view
            .call_view_for_site((0x1500, 0))
            .expect("recursive direct callsite should have prepared call view");
        assert!(
            call_view.callee_identity.is_none(),
            "recursive function names are not callee identity evidence"
        );
    }

    /// The callee's recovered signature names one parameter and the call site
    /// certificate carries two arguments. Two is the answer: how many
    /// arguments a call passes is a fact about the call, and cutting the list
    /// down to what the callee is declared to take is how every call to a
    /// variadic callee came out with the same arity.
    #[test]
    fn prepared_call_arity_comes_from_the_call_site_not_the_callee_signature() {
        let symbols = test_table();
        let prepared = test_prepared_two_arg_call_artifact();
        let typed_function_names = HashMap::from([(0x401000, "sym.imp.one_arg".to_string())]);
        let binary_symbols = HashMap::new();
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
            symbols: &binary_symbols,
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
        let callsite_facts = test_callsite_facts(&prepared);
        let function_facts = FunctionFacts::default()
            .with_callee_resolution(callee_resolution.clone())
            .with_callsites(callsite_facts.clone());

        let view = PreparedSemanticView::build(
            &symbols,
            PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: &stack_slots,
                visible_bindings: &visible_bindings,
                function_facts: &function_facts,
                certified_rendering_required: false,
            },
        );

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
        assert_eq!(
            call_view.authoritative_args,
            vec![CExpr::IntLit(7), CExpr::IntLit(9)]
        );
    }

    #[test]
    fn prepared_call_args_require_function_facts_callsite_contract() {
        let symbols = test_table();
        let prepared = test_prepared_two_arg_call_artifact();
        let mut summaries = InterprocSummarySet::default();
        let summary_id = r2ssa::InterprocFunctionId(0x401000);
        let mut summary =
            r2ssa::FunctionSemanticSummary::unknown(summary_id, Some("sym.local_two_arg".into()));
        summary.arg_count_hint = Some(1);
        summaries.summaries.insert(summary_id, summary);
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();

        let view = PreparedSemanticView::build(
            &symbols,
            PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: &stack_slots,
                visible_bindings: &visible_bindings,
                function_facts: leak_function_facts(FunctionFacts::default()),
                certified_rendering_required: false,
            },
        );

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
        let symbols = test_table();
        let prepared = test_prepared_two_arg_call_artifact();
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
        let function_facts = FunctionFacts::default().with_callsites(callsite_facts.clone());

        let view = PreparedSemanticView::build(
            &symbols,
            PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: &stack_slots,
                visible_bindings: &visible_bindings,
                function_facts: &function_facts,
                certified_rendering_required: false,
            },
        );

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
        let symbols = test_table();
        let prepared = test_prepared_two_arg_call_artifact();
        let callsite_facts = test_callsite_facts(&prepared);
        let stack_slots = BTreeMap::new();
        let visible_bindings = Vec::new();
        let function_facts = FunctionFacts::default().with_callsites(callsite_facts.clone());

        let view = PreparedSemanticView::build(
            &symbols,
            PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: &stack_slots,
                visible_bindings: &visible_bindings,
                function_facts: &function_facts,
                certified_rendering_required: false,
            },
        );

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
        let symbols = test_table();
        let prepared = test_prepared_stack_owned_call_result_artifact();
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

        let view = PreparedSemanticView::build(
            &symbols,
            PreparedSemanticViewInputs {
                prepared: &prepared,
                stack_slots: &stack_slots,
                visible_bindings: &visible_bindings,
                function_facts: leak_function_facts(FunctionFacts::default()),
                certified_rendering_required: false,
            },
        );

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

    /// Without a binding plan, nothing is spelled at all.
    ///
    /// This used to assert an ordering: that a storage spelling must not
    /// preempt the value projection. The ordering existed because an alias
    /// ladder could answer the same question, and every table it consulted had
    /// no writer, so it decided nothing while still being a second answerer.
    /// With the ladder gone the ordering question does not arise, and what is
    /// worth pinning is that the projection is the only source of a name.
    #[test]
    fn no_binding_plan_spells_nothing() {
        let symbols = test_table();
        let view = PreparedSemanticView::default();
        for var in [
            SSAVar::constant(1, 8),
            test_var("tmp:1", 0, 8),
            test_var("ram:401000", 0, 8),
            test_var("unique:1", 0, 8),
            test_var("const:40", 0, 8),
        ] {
            assert_eq!(
                prepared_fallback_visible_expr(&symbols, &view, &var),
                None,
                "an empty binding plan cannot name {var:?}"
            );
        }
    }
}
