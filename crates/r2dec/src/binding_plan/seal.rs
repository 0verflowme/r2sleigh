use super::*;

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
    let unobserved_merges = source.unobserved_merges();
    let eligible = graph
        .values
        .iter()
        .map(|value| value.var.constant_bits().is_none() && !unobserved_merges.contains(value.id))
        .collect::<Vec<_>>();
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
            if !members.is_empty() {
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
        if source.unobserved_merges().contains(graph_value.id) {
            values[graph_value.id.0 as usize] = Some(UpstreamValueDisposition::Elided(
                r2ssa::ledger::ElisionReason::UnobservedMerge,
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
        let expected_binding_count = width_evidence
            .iter()
            .filter(|evidence| matches!(evidence, SealWidthEvidence::Exact { .. }))
            .count()
            + source_owned
                .report()
                .render()
                .into_iter()
                .flat_map(|render| render.certified_entities.values())
                .filter(|entity| {
                    matches!(
                        entity,
                        r2types::CertifiedEntity::StackSlot {
                            size: Some(size),
                            ..
                        } if size.checked_mul(8).is_some_and(|width| width > 0)
                    )
                })
                .count();
        if self.bindings.len() != expected_binding_count {
            return Err(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::BindingCount {
                    expected: expected_binding_count,
                    actual: self.bindings.len(),
                },
            ));
        }

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
                        && !unobserved_merges.contains(value) => {}
                ValueDisposition::Elided { reason, proof }
                    if *reason == r2ssa::ledger::ElisionReason::UnobservedMerge
                        && proof.authority == *source.authority()
                        && proof.value == value
                        && unobserved_merges.contains(value) => {}
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
                    if actual != &component.members
                        || binding.certificate.sources.as_ref() != expected_sources.as_slice()
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

        let expected_stack_objects = source_owned
            .report()
            .render()
            .into_iter()
            .flat_map(|render| render.certified_entities.values())
            .filter_map(|entity| match entity {
                r2types::CertifiedEntity::StackSlot {
                    id, object, size, ..
                } => Some((*id, *object, *size)),
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
        for (entity, object, size) in expected_stack_objects {
            let expected_disposition = match size {
                None => StackObjectDisposition::Refused {
                    reason: StackObjectRefusal::MissingWidth { object },
                },
                Some(size_bytes) => match size_bytes.checked_mul(8).filter(|width| *width > 0) {
                    Some(width_bits) => {
                        let binding = BindingId(binding_index as u32);
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
                        if !actual_by_binding[binding_index].is_empty() {
                            return Err(BindingPlanBuildError::Seal(
                                BindingPlanSourceMismatch::StackObjectCertificate {
                                    object,
                                    binding,
                                },
                            ));
                        }
                        binding_index += 1;
                        StackObjectDisposition::Bound { binding }
                    }
                    None => StackObjectDisposition::Refused {
                        reason: StackObjectRefusal::InvalidWidth { object, size_bytes },
                    },
                },
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
