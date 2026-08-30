use super::*;

#[derive(Debug)]
enum SealParameterCandidate {
    Exact {
        entity: SemanticId,
        width_bytes: u32,
        entry_values: BTreeSet<ValueId>,
    },
    Refused(ParameterRefusal),
}

/// Rebuild the formal-parameter evidence independently of construction.
fn seal_parameter_candidates(
    source_owned: &SourceOwnedFunctionFacts,
) -> Vec<Option<SealParameterCandidate>> {
    let mut result = Vec::new();
    if let Some(interface) = source_owned.source().machine_context().function_interface() {
        for parameter in interface.parameters() {
            let slot = parameter.index();
            let index = slot as usize;
            if index >= result.len() {
                result.resize_with(index.saturating_add(1), || None);
            }
            let entity = SemanticId::Parameter(slot);
            result[index] = Some(match &result[index] {
                None => SealParameterCandidate::Exact {
                    entity,
                    width_bytes: parameter.storage().size,
                    entry_values: BTreeSet::new(),
                },
                Some(SealParameterCandidate::Exact { entity: first, .. }) => {
                    SealParameterCandidate::Refused(ParameterRefusal::ConflictingSlotOwnership {
                        slot,
                        first: *first,
                        second: entity,
                    })
                }
                Some(SealParameterCandidate::Refused(reason)) => {
                    SealParameterCandidate::Refused(*reason)
                }
            });
        }
    }
    let Some(render) = source_owned.report().render() else {
        return result;
    };
    for (map_id, entity) in &render.certified_entities {
        let r2types::CertifiedEntity::Parameter {
            id,
            slot,
            entry_values,
            carrier_width,
            ..
        } = entity
        else {
            continue;
        };
        let index = *slot as usize;
        if index >= result.len() {
            result.resize_with(index.saturating_add(1), || None);
        }
        let expected = SemanticId::Parameter(*slot);
        if map_id != id || *id != expected {
            result[index] = Some(SealParameterCandidate::Refused(
                ParameterRefusal::ConflictingEntityOwnership {
                    entity: *id,
                    expected_slot: *slot,
                    claimed_slot: match *id {
                        SemanticId::Parameter(claimed) => claimed,
                        _ => u32::MAX,
                    },
                },
            ));
            continue;
        }
        match &result[index] {
            Some(SealParameterCandidate::Exact { entity: owner, .. }) if owner == id => {
                result[index] = Some(SealParameterCandidate::Exact {
                    entity: *id,
                    width_bytes: *carrier_width,
                    entry_values: entry_values.clone(),
                });
            }
            Some(SealParameterCandidate::Exact { entity: owner, .. }) => {
                result[index] = Some(SealParameterCandidate::Refused(
                    ParameterRefusal::ConflictingSlotOwnership {
                        slot: *slot,
                        first: *owner,
                        second: *id,
                    },
                ));
            }
            Some(SealParameterCandidate::Refused(_)) => {}
            None => {
                result[index] = Some(SealParameterCandidate::Exact {
                    entity: *id,
                    width_bytes: *carrier_width,
                    entry_values: entry_values.clone(),
                });
            }
        }
    }
    result
}

fn seal_parameter_width(
    entity: SemanticId,
    slot: u32,
    size_bytes: u32,
) -> Result<u32, ParameterRefusal> {
    if size_bytes == 0 {
        return Err(ParameterRefusal::MissingWidth { entity, slot });
    }
    let width_bits = size_bytes
        .checked_mul(8)
        .ok_or(ParameterRefusal::InvalidWidth {
            entity,
            slot,
            size_bytes,
        })?;
    declaration_width_is_supported(width_bits)
        .then_some(width_bits)
        .ok_or(ParameterRefusal::UnsupportedWidth {
            entity,
            slot,
            width_bits,
        })
}

fn binding_declaration_width(ty: &CType) -> Option<u32> {
    match ty {
        CType::UInt(bits) if *bits <= 128 => Some(*bits),
        CType::BitVector(bits) if *bits > 128 => Some(*bits),
        _ => None,
    }
}

/// Resolve the certificate relation independently of construction's union-find.
///
/// The graph is bipartite: values point to every exact upstream certificate that
/// contains them, and certificate identities point back to their resolved member
/// sets. A sorted BFS computes each transitive component without depending on the
/// construction representative, union schedule, or component accumulator.
pub(super) fn seal_binding_components(
    source_owned: &SourceOwnedFunctionFacts,
) -> Result<Vec<SealBindingComponent>, BindingPlanBuildError> {
    let source = source_owned.source();
    let graph = source.graph();
    let value_count = graph.values.len();
    let eligible = super::rules::component_eligible_values(source_owned)?;
    let mut members_by_source = BTreeMap::<BindingCertificateSource, BTreeSet<ValueId>>::new();

    let mut values_by_span = BTreeMap::<SpanId, BTreeSet<ValueId>>::new();
    for (index, value) in graph.values.iter().enumerate() {
        if value.id.0 as usize != index {
            return Err(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::ValueTopology {
                    index,
                    value: value.id,
                },
            ));
        }
        if !eligible[index] {
            continue;
        }
        let span = source
            .storage_spans()
            .span_of(value.id)
            .ok_or(BindingPlanBuildError::MissingStorageSpan { value: value.id })?;
        values_by_span.entry(span).or_default().insert(value.id);
    }
    for (span, members) in values_by_span {
        if members.len() > 1 {
            members_by_source.insert(BindingCertificateSource::StorageSpan(span), members);
        }
    }

    let read_together = super::rules::values_read_together(graph);

    if let Some(render) = source_owned.report().render() {
        for entity in render.certified_entities.values() {
            let Some(values) = entity.coalescing_values() else {
                continue;
            };
            let members = values
                .into_iter()
                .filter_map(|value| {
                    let index = value.0 as usize;
                    if index >= value_count {
                        return Some(Err(BindingPlanBuildError::InvalidCertifiedEntityValue {
                            entity: entity.id(),
                            value,
                        }));
                    }
                    eligible[index].then_some(Ok(value))
                })
                .collect::<Result<BTreeSet<_>, _>>()?;
            // What this certificate would put in one object: its own members
            // and everything already sharing a run with any of them.
            let mut merged = members.clone();
            for value in &members {
                if let Some(span) = source.storage_spans().span_of(*value)
                    && let Some(span_members) = source.storage_spans().members(span)
                {
                    merged.extend(span_members.iter().copied());
                }
            }
            let interferes = super::rules::set_interferes(&read_together, &merged)
                || super::rules::set_outlives_a_redefinition(graph, &members);
            if !members.is_empty() && !interferes {
                members_by_source
                    .entry(BindingCertificateSource::CertifiedEntity(entity.id()))
                    .or_default()
                    .extend(members);
            }
        }
    }

    let mut sources_by_value = vec![BTreeSet::<BindingCertificateSource>::new(); value_count];
    for (certificate, members) in &members_by_source {
        for value in members {
            sources_by_value[value.0 as usize].insert(*certificate);
        }
    }

    let mut visited = vec![false; value_count];
    let mut components = Vec::new();
    for (index, is_eligible) in eligible.iter().copied().enumerate() {
        if !is_eligible || visited[index] {
            continue;
        }
        let mut pending_values = BTreeSet::from([ValueId(index as u32)]);
        let mut pending_sources = BTreeSet::new();
        let mut members = BTreeSet::new();
        let mut sources = BTreeSet::new();
        while !pending_values.is_empty() || !pending_sources.is_empty() {
            if let Some(value) = pending_values.pop_first() {
                if !members.insert(value) {
                    continue;
                }
                visited[value.0 as usize] = true;
                pending_sources.extend(sources_by_value[value.0 as usize].iter().copied());
                continue;
            }
            let certificate = pending_sources
                .pop_first()
                .expect("non-empty certificate worklist");
            if !sources.insert(certificate) {
                continue;
            }
            pending_values.extend(
                members_by_source
                    .get(&certificate)
                    .expect("every queued certificate was resolved")
                    .iter()
                    .copied(),
            );
        }
        if sources.is_empty() {
            sources.insert(BindingCertificateSource::Singleton);
        }
        components.push(SealBindingComponent { members, sources });
    }
    Ok(components)
}

/// Collect declaration-width evidence independently of construction's maximum.
///
/// Validation later proves minimality by requiring the declaration to satisfy
/// every lower bound and equal at least one witness. That is equivalent to the
/// least upper bound without sharing construction's `max` implementation.
fn seal_width_evidence(
    source: &r2ssa::SsaArtifact,
    machine_projection: &MachineProjection,
    component: &SealBindingComponent,
) -> Result<SealWidthEvidence, BindingPlanBuildError> {
    let graph = source.graph();
    let mut lower_bounds = Vec::new();
    for value in &component.members {
        let graph_value = graph.value(*value).ok_or(BindingPlanBuildError::Seal(
            BindingPlanSourceMismatch::ValueTopology {
                index: value.0 as usize,
                value: *value,
            },
        ))?;
        let member_width_bits = graph_value
            .var
            .size
            .checked_mul(8)
            .filter(|bits| *bits > 0)
            .ok_or(BindingPlanBuildError::InvalidValueWidth {
                value: *value,
                size_bytes: graph_value.var.size,
            })?;
        lower_bounds.push(member_width_bits);

        for site in &graph.uses_of[value.0 as usize] {
            let Some(MachineUseDisposition::Exact(slice)) =
                machine_projection.use_disposition(*site)
            else {
                continue;
            };
            let carrier_width_bits = slice.carrier_width_bits();
            let valid_end = slice
                .bit_offset()
                .checked_add(slice.width_bits())
                .is_some_and(|end| end <= carrier_width_bits);
            if slice.width_bits() == 0 || carrier_width_bits < member_width_bits || !valid_end {
                return Ok(SealWidthEvidence::Refused(
                    ValueRefusal::IncoherentUseProjection { site: *site },
                ));
            }
            lower_bounds.push(carrier_width_bits);
        }

        let Some(definition) = graph.def_inst(*value) else {
            continue;
        };
        let Some(MachineWriteDisposition::Exact(write)) =
            machine_projection.write_disposition(definition)
        else {
            continue;
        };
        match *write {
            MachineWriteProjection::Full => lower_bounds.push(member_width_bits),
            MachineWriteProjection::Insert {
                bit_offset,
                width_bits,
                carrier_width_bits,
            } => {
                let valid_end = bit_offset
                    .checked_add(width_bits)
                    .is_some_and(|end| end <= carrier_width_bits);
                if width_bits == 0 || carrier_width_bits < member_width_bits || !valid_end {
                    return Ok(SealWidthEvidence::Refused(
                        ValueRefusal::IncoherentWriteProjection { value: *value },
                    ));
                }
                lower_bounds.push(carrier_width_bits);
            }
            MachineWriteProjection::ZeroExtend {
                from_width_bits,
                to_width_bits,
            } => {
                if from_width_bits == 0
                    || from_width_bits >= to_width_bits
                    || to_width_bits < member_width_bits
                {
                    return Ok(SealWidthEvidence::Refused(
                        ValueRefusal::IncoherentWriteProjection { value: *value },
                    ));
                }
                lower_bounds.push(to_width_bits);
            }
        }
    }
    let width_bits = lower_bounds.iter().copied().max().unwrap_or(0);
    if !declaration_width_is_supported(width_bits) {
        let value = component
            .members
            .first()
            .copied()
            .expect("seal binding components are non-empty");
        return Ok(SealWidthEvidence::Refused(
            ValueRefusal::UnsupportedDeclarationWidth { value, width_bits },
        ));
    }
    Ok(SealWidthEvidence::Exact { lower_bounds })
}

/// Recompute the Stage 4 comparison oracle directly from the exact source.
///
/// The candidate plan is intentionally not an input. This makes a wrong plan
/// disposition observable instead of validating the candidate against itself.
pub(crate) fn build_upstream_shadow_oracle(
    source_owned: &SourceOwnedFunctionFacts,
) -> Result<UpstreamShadowOracle, BindingPlanBuildError> {
    let source = source_owned.source();
    let graph = source.graph();
    let machine_projection = MachineProjection::from_artifact(source)
        .map_err(BindingPlanBuildError::MachineProjection)?;
    let return_controls = certified_return_control_values(source);
    let direct_control_targets = certified_direct_control_target_values(source);
    let stack_frame_values = certified_stack_frame_values(source);
    let stack_geometry_values = certified_stack_geometry_values(source);
    let unobserved_values = source.unobserved_values();
    let structural_unused =
        source
            .obligations()
            .structural_unused_values(graph)
            .ok_or(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::Authority,
            ))?;
    let resolved = seal_binding_components(source_owned)?;
    if u32::try_from(resolved.len()).is_err() {
        return Err(BindingPlanBuildError::TooManyBindings {
            count: resolved.len(),
        });
    }
    let width_evidence = resolved
        .iter()
        .map(|component| seal_width_evidence(source, &machine_projection, component))
        .collect::<Result<Vec<_>, _>>()?;

    let literal_values = machine_projection
        .arena()
        .iter()
        .filter_map(|(_, expr)| match expr.kind() {
            MachineExprKind::Constant { binding, .. } => Some(binding.value()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut values = vec![None; graph.values.len()];
    for graph_value in &graph.values {
        if return_controls.contains(&graph_value.id) {
            values[graph_value.id.0 as usize] = Some(UpstreamValueDisposition::Elided(
                r2ssa::ledger::ElisionReason::ReturnControl,
            ));
            continue;
        }
        if direct_control_targets.contains(&graph_value.id) {
            values[graph_value.id.0 as usize] = Some(UpstreamValueDisposition::Elided(
                r2ssa::ledger::ElisionReason::DirectControlTarget,
            ));
            continue;
        }
        if stack_frame_values.contains(&graph_value.id) {
            values[graph_value.id.0 as usize] = Some(UpstreamValueDisposition::Elided(
                r2ssa::ledger::ElisionReason::StackFrame,
            ));
            continue;
        }
        if stack_geometry_values.contains(&graph_value.id) {
            values[graph_value.id.0 as usize] = Some(UpstreamValueDisposition::Elided(
                r2ssa::ledger::ElisionReason::DeadStackBase,
            ));
            continue;
        }
        if source.unobserved_merges().contains(graph_value.id) {
            values[graph_value.id.0 as usize] = Some(UpstreamValueDisposition::Elided(
                r2ssa::ledger::ElisionReason::UnobservedMerge,
            ));
            continue;
        }
        if unobserved_values.contains(&graph_value.id) {
            values[graph_value.id.0 as usize] = Some(UpstreamValueDisposition::Elided(
                r2ssa::ledger::ElisionReason::UnobservedValue,
            ));
            continue;
        }
        if structural_unused.contains(&graph_value.id) {
            values[graph_value.id.0 as usize] = Some(UpstreamValueDisposition::Elided(
                r2ssa::ledger::ElisionReason::UnusedStructuralValue,
            ));
            continue;
        }
        if graph_value.var.constant_bits().is_none() {
            continue;
        }
        values[graph_value.id.0 as usize] = Some(if literal_values.contains(&graph_value.id) {
            UpstreamValueDisposition::InlineConstant
        } else {
            UpstreamValueDisposition::Refused(ValueRefusal::MissingLiteralProjection {
                value: graph_value.id,
            })
        });
    }

    let mut components = Vec::with_capacity(resolved.len());
    for (index, (component, width)) in resolved.iter().zip(width_evidence).enumerate() {
        let component_id = CanonicalComponentId(index as u32);
        let disposition = match width {
            SealWidthEvidence::Exact { .. } => UpstreamValueDisposition::Bound {
                component: component_id,
            },
            SealWidthEvidence::Refused(reason) => UpstreamValueDisposition::Refused(reason),
        };
        for value in &component.members {
            values[value.0 as usize] = Some(disposition);
        }
        components.push(
            component
                .members
                .iter()
                .copied()
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        );
    }

    let values = values
        .into_iter()
        .enumerate()
        .map(|(index, disposition)| {
            disposition.ok_or(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::UnexpectedValueDisposition {
                    value: ValueId(index as u32),
                },
            ))
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_boxed_slice();
    Ok(UpstreamShadowOracle {
        machine_projection,
        components: components.into_boxed_slice(),
        values,
    })
}

impl BindingPlan {
    pub(super) fn validate_seal(
        &self,
        source_owned: &SourceOwnedFunctionFacts,
    ) -> Result<(), BindingPlanBuildError> {
        let source = source_owned.source();
        self.validate_source(source)
            .map_err(BindingPlanBuildError::Seal)?;
        let graph = source.graph();
        if self.dispositions.len() != graph.values.len() {
            return Err(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::DispositionCount {
                    expected: graph.values.len(),
                    actual: self.dispositions.len(),
                },
            ));
        }

        let expected = seal_binding_components(source_owned)?;
        let unobserved_merges = source.unobserved_merges();
        let unobserved_values = source.unobserved_values();
        let return_controls = certified_return_control_values(source);
        let direct_control_targets = certified_direct_control_target_values(source);
        let stack_frame_values = certified_stack_frame_values(source);
        let stack_geometry_values = certified_stack_geometry_values(source);
        let structural_unused = source.obligations().structural_unused_values(graph).ok_or(
            BindingPlanBuildError::Seal(BindingPlanSourceMismatch::Authority),
        )?;
        for (index, graph_value) in graph.values.iter().enumerate() {
            if graph_value.id.0 as usize != index {
                return Err(BindingPlanBuildError::Seal(
                    BindingPlanSourceMismatch::ValueTopology {
                        index,
                        value: graph_value.id,
                    },
                ));
            }
        }
        let width_evidence = expected
            .iter()
            .map(|component| seal_width_evidence(source, &self.machine_projection, component))
            .collect::<Result<Vec<_>, _>>()?;
        let mut actual_by_binding = vec![BTreeSet::<ValueId>::new(); self.bindings.len()];
        for (index, disposition) in self.dispositions.iter().enumerate() {
            let value = ValueId(index as u32);
            let graph_value = &graph.values[index];
            match disposition {
                ValueDisposition::Bound { binding } => {
                    if graph_value.var.constant_bits().is_some() {
                        return Err(BindingPlanBuildError::Seal(
                            BindingPlanSourceMismatch::UnexpectedValueDisposition { value },
                        ));
                    }
                    let Some(members) = actual_by_binding.get_mut(binding.index()) else {
                        return Err(BindingPlanBuildError::Seal(
                            BindingPlanSourceMismatch::InvalidBindingReference {
                                value,
                                binding: *binding,
                            },
                        ));
                    };
                    members.insert(value);
                }
                ValueDisposition::Inline { expr, proof } => {
                    let exact_literal = proof.authority == *source.authority()
                        && proof.literal == *expr
                        && graph_value.var.constant_bits().is_some()
                        && matches!(
                            self.machine_projection.expr(*expr).map(|expr| expr.kind()),
                            Some(MachineExprKind::Constant { binding, .. })
                                if binding.value() == value
                        );
                    if !exact_literal {
                        return Err(BindingPlanBuildError::Seal(
                            BindingPlanSourceMismatch::InvalidLiteralInline { value },
                        ));
                    }
                }
                ValueDisposition::Refused {
                    reason: ValueRefusal::MissingLiteralProjection { value: refused },
                } if *refused == value && graph_value.var.constant_bits().is_some() => {}
                ValueDisposition::Refused { .. }
                    if graph_value.var.constant_bits().is_none()
                        && !unobserved_merges.contains(value)
                        && !unobserved_values.contains(&value)
                        && !return_controls.contains(&value)
                        && !direct_control_targets.contains(&value)
                        && !stack_frame_values.contains(&value)
                        && !stack_geometry_values.contains(&value)
                        && !structural_unused.contains(&value) => {}
                ValueDisposition::Elided { reason, proof }
                    if *reason == r2ssa::ledger::ElisionReason::UnobservedMerge
                        && proof.authority == *source.authority()
                        && proof.value == value
                        && unobserved_merges.contains(value) => {}
                ValueDisposition::Elided { reason, proof }
                    if *reason == r2ssa::ledger::ElisionReason::UnobservedValue
                        && proof.authority == *source.authority()
                        && proof.value == value
                        && unobserved_values.contains(&value)
                        && !unobserved_merges.contains(value) => {}
                ValueDisposition::Elided { reason, proof }
                    if *reason == r2ssa::ledger::ElisionReason::ReturnControl
                        && proof.authority == *source.authority()
                        && proof.value == value
                        && return_controls.contains(&value) => {}
                ValueDisposition::Elided { reason, proof }
                    if *reason == r2ssa::ledger::ElisionReason::DirectControlTarget
                        && proof.authority == *source.authority()
                        && proof.value == value
                        && direct_control_targets.contains(&value) => {}
                ValueDisposition::Elided { reason, proof }
                    if *reason == r2ssa::ledger::ElisionReason::StackFrame
                        && proof.authority == *source.authority()
                        && proof.value == value
                        && stack_frame_values.contains(&value) => {}
                ValueDisposition::Elided { reason, proof }
                    if *reason == r2ssa::ledger::ElisionReason::DeadStackBase
                        && proof.authority == *source.authority()
                        && proof.value == value
                        && stack_geometry_values.contains(&value) => {}
                ValueDisposition::Elided { reason, proof }
                    if *reason == r2ssa::ledger::ElisionReason::UnusedStructuralValue
                        && proof.authority == *source.authority()
                        && proof.value == value
                        && structural_unused.contains(&value) => {}
                ValueDisposition::Elided { .. } => {
                    return Err(BindingPlanBuildError::Seal(
                        BindingPlanSourceMismatch::InvalidElisionProof { value },
                    ));
                }
                ValueDisposition::Refused { .. } => {
                    return Err(BindingPlanBuildError::Seal(
                        BindingPlanSourceMismatch::UnexpectedValueDisposition { value },
                    ));
                }
            }
        }

        let mut binding_index = 0_usize;
        for (component, evidence) in expected.iter().zip(width_evidence) {
            match evidence {
                SealWidthEvidence::Exact { lower_bounds } => {
                    let binding_id = BindingId(binding_index as u32);
                    let binding = &self.bindings[binding_index];
                    let actual = &actual_by_binding[binding_index];
                    let expected_sources = component.sources.iter().copied().collect::<Vec<_>>();
                    // Re-derive whether the caller supplies a member rather
                    // than trusting the plan's own answer.
                    let expected_caller_supplied = component
                        .members
                        .iter()
                        .any(|value| graph.def_inst(*value).is_none());
                    if actual != &component.members
                        || binding.certificate.sources.as_ref() != expected_sources.as_slice()
                        || binding.caller_supplied != expected_caller_supplied
                    {
                        return Err(BindingPlanBuildError::Seal(
                            BindingPlanSourceMismatch::CertificateMembership {
                                binding: binding_id,
                            },
                        ));
                    }
                    let Some(width_bits) = binding_declaration_width(&binding.declaration_type)
                    else {
                        return Err(BindingPlanBuildError::Seal(
                            BindingPlanSourceMismatch::DeclarationWidth {
                                binding: binding_id,
                            },
                        ));
                    };
                    let satisfies_every_bound = lower_bounds
                        .iter()
                        .all(|lower_bound| *lower_bound <= width_bits);
                    let has_minimality_witness = lower_bounds.contains(&width_bits);
                    if width_bits == 0 || !satisfies_every_bound || !has_minimality_witness {
                        return Err(BindingPlanBuildError::Seal(
                            BindingPlanSourceMismatch::DeclarationWidth {
                                binding: binding_id,
                            },
                        ));
                    }
                    binding_index += 1;
                }
                SealWidthEvidence::Refused(reason) => {
                    for value in &component.members {
                        if self.disposition(*value) != Some(&ValueDisposition::Refused { reason }) {
                            return Err(BindingPlanBuildError::Seal(
                                BindingPlanSourceMismatch::UnexpectedValueDisposition {
                                    value: *value,
                                },
                            ));
                        }
                    }
                }
            }
        }

        let parameter_candidates = seal_parameter_candidates(source_owned);
        if self.parameters.len() != parameter_candidates.len() {
            return Err(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::ParameterCount {
                    expected: parameter_candidates.len(),
                    actual: self.parameters.len(),
                },
            ));
        }
        let mut slots_by_reused_binding = BTreeMap::<BindingId, Vec<u32>>::new();
        for (index, candidate) in parameter_candidates.iter().enumerate() {
            let Some(SealParameterCandidate::Exact {
                entity,
                width_bytes,
                entry_values,
            }) = candidate
            else {
                continue;
            };
            let slot = index as u32;
            if seal_parameter_width(*entity, slot, *width_bytes).is_err() || entry_values.is_empty()
            {
                continue;
            }
            let mut binding = None;
            if entry_values
                .iter()
                .all(|value| match self.disposition(*value) {
                    Some(ValueDisposition::Bound { binding: candidate })
                        if binding.is_none_or(|existing| existing == *candidate) =>
                    {
                        binding = Some(*candidate);
                        true
                    }
                    _ => false,
                })
                && let Some(binding) = binding
            {
                slots_by_reused_binding
                    .entry(binding)
                    .or_default()
                    .push(slot);
            }
        }

        for (index, candidate) in parameter_candidates.into_iter().enumerate() {
            let slot = index as u32;
            let expected_disposition = match candidate {
                None => {
                    if self.parameters[index].is_some() {
                        return Err(BindingPlanBuildError::Seal(
                            BindingPlanSourceMismatch::UnexpectedParameterDisposition { slot },
                        ));
                    }
                    continue;
                }
                Some(SealParameterCandidate::Refused(reason)) => {
                    ParameterDisposition::Refused { reason }
                }
                Some(SealParameterCandidate::Exact {
                    entity,
                    width_bytes,
                    entry_values,
                }) => match seal_parameter_width(entity, slot, width_bytes) {
                    Err(reason) => ParameterDisposition::Refused { reason },
                    Ok(width_bits) if entry_values.is_empty() => {
                        let binding = BindingId(binding_index as u32);
                        let planned =
                            self.bindings
                                .get(binding_index)
                                .ok_or(BindingPlanBuildError::Seal(
                                    BindingPlanSourceMismatch::UnexpectedParameterDisposition {
                                        slot,
                                    },
                                ))?;
                        if planned.certificate.sources.as_ref()
                            != [BindingCertificateSource::CertifiedEntity(entity)]
                            || !actual_by_binding[binding_index].is_empty()
                        {
                            return Err(BindingPlanBuildError::Seal(
                                BindingPlanSourceMismatch::ParameterCertificate { slot, binding },
                            ));
                        }
                        if planned.declaration_type != CType::machine_bits(width_bits) {
                            return Err(BindingPlanBuildError::Seal(
                                BindingPlanSourceMismatch::ParameterDeclarationWidth {
                                    slot,
                                    binding,
                                },
                            ));
                        }
                        binding_index += 1;
                        ParameterDisposition::Bound {
                            binding,
                            width_bits,
                        }
                    }
                    Ok(width_bits) => {
                        let mut binding = None;
                        let missing = entry_values.iter().copied().find(|value| {
                            match self.disposition(*value) {
                                Some(ValueDisposition::Bound { binding: candidate })
                                    if binding.is_none_or(|existing| existing == *candidate) =>
                                {
                                    binding = Some(*candidate);
                                    false
                                }
                                _ => true,
                            }
                        });
                        if let Some(value) = missing {
                            ParameterDisposition::Refused {
                                reason: ParameterRefusal::MissingValueBinding {
                                    entity,
                                    slot,
                                    value,
                                },
                            }
                        } else {
                            let binding = binding.expect("non-empty exact entry-value set");
                            let owners = &slots_by_reused_binding[&binding];
                            if owners.len() > 1 {
                                ParameterDisposition::Refused {
                                    reason: ParameterRefusal::ConflictingBindingOwnership {
                                        binding,
                                        first_slot: owners[0],
                                        second_slot: owners[1],
                                    },
                                }
                            } else {
                                ParameterDisposition::Bound {
                                    binding,
                                    width_bits,
                                }
                            }
                        }
                    }
                },
            };
            if self.parameter_disposition(slot) != Some(expected_disposition) {
                return Err(BindingPlanBuildError::Seal(
                    BindingPlanSourceMismatch::UnexpectedParameterDisposition { slot },
                ));
            }
        }

        let expected_stack_objects = source_owned
            .report()
            .render()
            .into_iter()
            .flat_map(|render| render.certified_entities.values())
            .filter_map(|entity| match entity {
                r2types::CertifiedEntity::StackSlot {
                    id,
                    object,
                    base,
                    offset,
                    size,
                    source_slot,
                    callee_allocation,
                } => Some((
                    *id,
                    *object,
                    *base,
                    *offset,
                    *size,
                    *source_slot,
                    callee_allocation.clone(),
                )),
                r2types::CertifiedEntity::Parameter { .. }
                | r2types::CertifiedEntity::LoopCarrier { .. } => None,
            })
            .collect::<Vec<_>>();
        if self.stack_objects.len() != expected_stack_objects.len() {
            return Err(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::StackObjectCount {
                    expected: expected_stack_objects.len(),
                    actual: self.stack_objects.len(),
                },
            ));
        }
        for (entity, object, base, offset, size, source_slot, callee_allocation) in
            expected_stack_objects
        {
            let exact_certificate = source.certificates().stack_slots.get(&object);
            if exact_certificate.is_none_or(|certificate| {
                certificate.object != object
                    || certificate.base != base
                    || certificate.offset != offset
                    || certificate.size != size
                    || certificate.source_slot != source_slot
                    || certificate.callee_allocation != callee_allocation
            }) {
                return Err(BindingPlanBuildError::Seal(
                    BindingPlanSourceMismatch::UnexpectedStackObjectDisposition { object },
                ));
            }
            if source
                .certificates()
                .stack_frame_round_trips
                .contains_key(&object)
            {
                let expected = StackObjectDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::StackFrame,
                };
                if self.stack_object_disposition(object) != Some(expected) {
                    return Err(BindingPlanBuildError::Seal(
                        BindingPlanSourceMismatch::UnexpectedStackObjectDisposition { object },
                    ));
                }
                continue;
            }
            let expected_disposition = match (source_slot, callee_allocation) {
                // Neither strong form answers, so the object is named by the
                // width its own accesses agree on. Without even that there is
                // no geometry to state and it stays refused.
                (None, None) if size.is_none() => StackObjectDisposition::Refused {
                    reason: StackObjectRefusal::MissingSourceIdentity { object },
                },
                (None, None) => {
                    let size_bytes = size.expect("the arm above covers a missing width");
                    let Some(width_bits) = size_bytes.checked_mul(8).filter(|width| *width > 0)
                    else {
                        let expected = StackObjectDisposition::Refused {
                            reason: StackObjectRefusal::InvalidWidth { object, size_bytes },
                        };
                        if self.stack_object_disposition(object) != Some(expected) {
                            return Err(BindingPlanBuildError::Seal(
                                BindingPlanSourceMismatch::UnexpectedStackObjectDisposition {
                                    object,
                                },
                            ));
                        }
                        continue;
                    };
                    let Some(binding) = BindingId::from_dense_index(binding_index) else {
                        return Err(BindingPlanBuildError::TooManyBindings {
                            count: binding_index.saturating_add(1),
                        });
                    };
                    let planned =
                        self.bindings
                            .get(binding_index)
                            .ok_or(BindingPlanBuildError::Seal(
                                BindingPlanSourceMismatch::UnexpectedStackObjectDisposition {
                                    object,
                                },
                            ))?;
                    if planned.certificate.sources.as_ref()
                        != [BindingCertificateSource::CertifiedEntity(entity)]
                        || !actual_by_binding[binding_index].is_empty()
                    {
                        return Err(BindingPlanBuildError::Seal(
                            BindingPlanSourceMismatch::StackObjectCertificate { object, binding },
                        ));
                    }
                    if planned.declaration_type != CType::machine_bits(width_bits) {
                        return Err(BindingPlanBuildError::Seal(
                            BindingPlanSourceMismatch::StackObjectDeclarationWidth {
                                object,
                                binding,
                            },
                        ));
                    }
                    binding_index += 1;
                    StackObjectDisposition::Bound { binding }
                }
                (None, Some(certificate)) => {
                    if certificate.object != object
                        || size != Some(certificate.size_bytes)
                        || certificate.accesses.is_empty()
                        || certificate.active_sp_offsets.is_empty()
                    {
                        StackObjectDisposition::Refused {
                            reason: StackObjectRefusal::MissingSourceIdentity { object },
                        }
                    } else {
                        let Some(binding) = BindingId::from_dense_index(binding_index) else {
                            return Err(BindingPlanBuildError::TooManyBindings {
                                count: binding_index.saturating_add(1),
                            });
                        };
                        let planned =
                            self.bindings
                                .get(binding_index)
                                .ok_or(BindingPlanBuildError::Seal(
                                    BindingPlanSourceMismatch::UnexpectedStackObjectDisposition {
                                        object,
                                    },
                                ))?;
                        let width_bits = certificate
                            .size_bytes
                            .checked_mul(8)
                            .filter(|width| *width > 0);
                        if planned.certificate.sources.as_ref()
                            != [BindingCertificateSource::CertifiedEntity(entity)]
                            || !actual_by_binding[binding_index].is_empty()
                        {
                            return Err(BindingPlanBuildError::Seal(
                                BindingPlanSourceMismatch::StackObjectCertificate {
                                    object,
                                    binding,
                                },
                            ));
                        }
                        if width_bits.is_none_or(|width_bits| {
                            planned.declaration_type != CType::machine_bits(width_bits)
                        }) {
                            return Err(BindingPlanBuildError::Seal(
                                BindingPlanSourceMismatch::StackObjectDeclarationWidth {
                                    object,
                                    binding,
                                },
                            ));
                        }
                        binding_index += 1;
                        StackObjectDisposition::Bound { binding }
                    }
                }
                (Some(_), Some(_)) => StackObjectDisposition::Refused {
                    reason: StackObjectRefusal::MissingSourceIdentity { object },
                },
                (Some(source_slot), None)
                    if source_slot.base() != base
                        || source_slot.offset() != offset
                        || size != Some(source_slot.size_bytes()) =>
                {
                    StackObjectDisposition::Refused {
                        reason: StackObjectRefusal::MissingSourceIdentity { object },
                    }
                }
                (Some(source_slot), None) => {
                    let size_bytes = source_slot.size_bytes();
                    let Some(width_bits) = size_bytes.checked_mul(8).filter(|width| *width > 0)
                    else {
                        let expected = StackObjectDisposition::Refused {
                            reason: StackObjectRefusal::InvalidWidth { object, size_bytes },
                        };
                        if self.stack_object_disposition(object) != Some(expected) {
                            return Err(BindingPlanBuildError::Seal(
                                BindingPlanSourceMismatch::UnexpectedStackObjectDisposition {
                                    object,
                                },
                            ));
                        }
                        continue;
                    };
                    match source_slot.role() {
                        r2ssa::SourceStackSlotRole::Local => {
                            let Some(binding) = BindingId::from_dense_index(binding_index) else {
                                return Err(BindingPlanBuildError::TooManyBindings {
                                    count: binding_index.saturating_add(1),
                                });
                            };
                            let planned =
                                self.bindings
                                    .get(binding_index)
                                    .ok_or(BindingPlanBuildError::Seal(
                                    BindingPlanSourceMismatch::UnexpectedStackObjectDisposition {
                                        object,
                                    },
                                ))?;
                            if planned.certificate.sources.as_ref()
                                != [BindingCertificateSource::CertifiedEntity(entity)]
                                || !actual_by_binding[binding_index].is_empty()
                            {
                                return Err(BindingPlanBuildError::Seal(
                                    BindingPlanSourceMismatch::StackObjectCertificate {
                                        object,
                                        binding,
                                    },
                                ));
                            }
                            if planned.declaration_type != CType::machine_bits(width_bits) {
                                return Err(BindingPlanBuildError::Seal(
                                    BindingPlanSourceMismatch::StackObjectDeclarationWidth {
                                        object,
                                        binding,
                                    },
                                ));
                            }
                            binding_index += 1;
                            StackObjectDisposition::Bound { binding }
                        }
                        r2ssa::SourceStackSlotRole::ParameterHome {
                            parameter_index, ..
                        } => match self.parameter_disposition(parameter_index) {
                            Some(ParameterDisposition::Bound {
                                binding,
                                width_bits: parameter_width_bits,
                            }) if parameter_width_bits == width_bits => {
                                StackObjectDisposition::Bound { binding }
                            }
                            Some(ParameterDisposition::Bound {
                                width_bits: parameter_width_bits,
                                ..
                            }) => StackObjectDisposition::Refused {
                                reason: StackObjectRefusal::ParameterHomeWidthMismatch {
                                    object,
                                    parameter_index,
                                    slot_width_bits: width_bits,
                                    parameter_width_bits,
                                },
                            },
                            _ => StackObjectDisposition::Refused {
                                reason: StackObjectRefusal::ParameterHomeUnavailable {
                                    object,
                                    parameter_index,
                                },
                            },
                        },
                        r2ssa::SourceStackSlotRole::UnclassifiedResource => {
                            StackObjectDisposition::Refused {
                                reason: StackObjectRefusal::UnclassifiedSourceRole { object },
                            }
                        }
                    }
                }
            };
            if self.stack_object_disposition(object) != Some(expected_disposition) {
                return Err(BindingPlanBuildError::Seal(
                    BindingPlanSourceMismatch::UnexpectedStackObjectDisposition { object },
                ));
            }
        }
        if binding_index != self.bindings.len() {
            return Err(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::BindingCount {
                    expected: binding_index,
                    actual: self.bindings.len(),
                },
            ));
        }
        Ok(())
    }
}
