use super::*;

#[derive(Debug)]
enum ParameterCandidate {
    Exact {
        entity: SemanticId,
        width_bytes: u32,
        entry_values: BTreeSet<ValueId>,
    },
    Refused {
        entity: SemanticId,
        reason: ParameterRefusal,
    },
}

/// Collect the dense exact ABI-parameter domain without consulting names.
/// The source interface supplies unused formals; a matching render entity
/// supplies its exact entry-value membership and source-var carrier width.
fn parameter_candidates(
    source_owned: &SourceOwnedFunctionFacts,
) -> Vec<Option<ParameterCandidate>> {
    let interface = source_owned.source().machine_context().function_interface();
    let mut candidates = Vec::new();
    if let Some(interface) = interface {
        for parameter in interface.parameters() {
            insert_formal_parameter_candidate(
                &mut candidates,
                parameter.index(),
                parameter.storage().size,
            );
        }
    }
    let Some(render) = source_owned.report().render() else {
        return candidates;
    };

    for (key, certified) in &render.certified_entities {
        let r2types::CertifiedEntity::Parameter {
            id,
            slot,
            entry_values,
            carrier_width,
            ..
        } = certified
        else {
            continue;
        };
        let Ok(index) = usize::try_from(*slot) else {
            continue;
        };
        if index >= candidates.len() {
            candidates.resize_with(index.saturating_add(1), || None);
        }
        let canonical = SemanticId::Parameter(*slot);
        if *key != *id || *id != canonical {
            candidates[index] = Some(ParameterCandidate::Refused {
                entity: canonical,
                reason: ParameterRefusal::ConflictingEntityOwnership {
                    entity: *id,
                    expected_slot: *slot,
                    claimed_slot: match *id {
                        SemanticId::Parameter(claimed) => claimed,
                        _ => u32::MAX,
                    },
                },
            });
            continue;
        }
        match &candidates[index] {
            Some(ParameterCandidate::Exact {
                entity: existing, ..
            }) if *existing == *id => {
                candidates[index] = Some(ParameterCandidate::Exact {
                    entity: *id,
                    width_bytes: *carrier_width,
                    entry_values: entry_values.clone(),
                });
            }
            Some(ParameterCandidate::Exact {
                entity: existing, ..
            })
            | Some(ParameterCandidate::Refused {
                entity: existing, ..
            }) => {
                candidates[index] = Some(ParameterCandidate::Refused {
                    entity: canonical,
                    reason: ParameterRefusal::ConflictingSlotOwnership {
                        slot: *slot,
                        first: *existing,
                        second: *id,
                    },
                });
            }
            None => {
                candidates[index] = Some(ParameterCandidate::Exact {
                    entity: *id,
                    width_bytes: *carrier_width,
                    entry_values: entry_values.clone(),
                });
            }
        }
    }
    candidates
}

fn insert_formal_parameter_candidate(
    candidates: &mut Vec<Option<ParameterCandidate>>,
    slot: u32,
    width_bytes: u32,
) {
    let index = slot as usize;
    if index >= candidates.len() {
        candidates.resize_with(index.saturating_add(1), || None);
    }
    let entity = SemanticId::Parameter(slot);
    candidates[index] = Some(match &candidates[index] {
        None => ParameterCandidate::Exact {
            entity,
            width_bytes,
            entry_values: BTreeSet::new(),
        },
        Some(ParameterCandidate::Exact { entity: first, .. })
        | Some(ParameterCandidate::Refused { entity: first, .. }) => ParameterCandidate::Refused {
            entity,
            reason: ParameterRefusal::ConflictingSlotOwnership {
                slot,
                first: *first,
                second: entity,
            },
        },
    });
}

fn parameter_width(
    entity: SemanticId,
    slot: u32,
    width_bytes: u32,
) -> Result<u32, ParameterRefusal> {
    if width_bytes == 0 {
        return Err(ParameterRefusal::MissingWidth { entity, slot });
    }
    let Some(width_bits) = width_bytes.checked_mul(8) else {
        return Err(ParameterRefusal::InvalidWidth {
            entity,
            slot,
            size_bytes: width_bytes,
        });
    };
    if !declaration_width_is_supported(width_bits) {
        return Err(ParameterRefusal::UnsupportedWidth {
            entity,
            slot,
            width_bits,
        });
    }
    Ok(width_bits)
}

fn refuse_conflicting_parameter_bindings(parameters: &mut [Option<ParameterDisposition>]) {
    let mut parameter_slots_by_binding = BTreeMap::<BindingId, Vec<u32>>::new();
    for (index, disposition) in parameters.iter().enumerate() {
        let Some(ParameterDisposition::Bound { binding, .. }) = disposition else {
            continue;
        };
        parameter_slots_by_binding
            .entry(*binding)
            .or_default()
            .push(index as u32);
    }
    for (binding, slots) in parameter_slots_by_binding {
        if slots.len() < 2 {
            continue;
        }
        let reason = ParameterRefusal::ConflictingBindingOwnership {
            binding,
            first_slot: slots[0],
            second_slot: slots[1],
        };
        for slot in slots {
            parameters[slot as usize] = Some(ParameterDisposition::Refused { reason });
        }
    }
}

/// Compute the transitive closure of every exact upstream coalescing set.
///
/// Constants are deliberately outside the relation: they are expressions that
/// initialize or update an object, not C objects themselves. Certified sets are
/// filtered to the non-literal values they authorize before joining, and the
/// same filtering is used again when the completed plan is sealed.
pub(super) fn binding_components(
    source_owned: &SourceOwnedFunctionFacts,
) -> Result<Vec<BindingComponent>, BindingPlanBuildError> {
    let source = source_owned.source();
    let graph = source.graph();
    let value_count = graph.values.len();
    let eligible = super::rules::component_eligible_values(source_owned)?;
    let mut parent = (0..value_count).collect::<Vec<_>>();
    let mut rank = vec![0_u8; value_count];

    fn find(parent: &mut [usize], mut value: usize) -> usize {
        while parent[value] != value {
            let grandparent = parent[parent[value]];
            parent[value] = grandparent;
            value = grandparent;
        }
        value
    }

    fn union(parent: &mut [usize], rank: &mut [u8], left: ValueId, right: ValueId) {
        let left = find(parent, left.0 as usize);
        let right = find(parent, right.0 as usize);
        if left == right {
            return;
        }
        let (root, child) = match rank[left].cmp(&rank[right]) {
            std::cmp::Ordering::Greater => (left, right),
            std::cmp::Ordering::Less => (right, left),
            std::cmp::Ordering::Equal if left < right => {
                rank[left] += 1;
                (left, right)
            }
            std::cmp::Ordering::Equal => {
                rank[right] += 1;
                (right, left)
            }
        };
        parent[child] = root;
    }

    let mut certificate_sets = Vec::<(BindingCertificateSource, BTreeSet<ValueId>)>::new();
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
    let read_together = super::rules::values_read_together(source.graph());
    // Whether merging every one of these values into one object would put two
    // values that some instruction reads together into that object.
    let merge_would_interfere = |parent: &mut Vec<usize>, values: &BTreeSet<ValueId>| {
        let roots = values
            .iter()
            .map(|value| find(parent, value.0 as usize))
            .collect::<BTreeSet<_>>();
        let mut members = BTreeSet::new();
        for index in 0..parent.len() {
            if roots.contains(&find(parent, index)) {
                members.insert(ValueId(index as u32));
            }
        }
        super::rules::set_interferes(&read_together, &members)
    };

    for (span, values) in values_by_span {
        if values.len() > 1 {
            // A storage span says these values share a machine location. That
            // is not on its own a licence to share a C object, and this asked
            // nothing before unioning: the certificate path below has always
            // asked, and one instruction reading two members is exactly as
            // impossible whichever derivation proposed the merge. `crc32_bitwise`
            // at arm64 -O2 is the case -- one p-code temporary carries both
            // `w10` and `w11`, and `eor w10, w10, w11` reads two of its versions.
            if merge_would_interfere(&mut parent, &values) {
                continue;
            }
            let first = values.first().copied().expect("multi-member span");
            for value in values.iter().copied().skip(1) {
                union(&mut parent, &mut rank, first, value);
            }
            certificate_sets.push((BindingCertificateSource::StorageSpan(span), values));
        }
    }

    if let Some(render) = source_owned.report().render() {
        for entity in render.certified_entities.values() {
            let Some(values) = entity.coalescing_values() else {
                // StackSlot has object identity but no exact ValueId set.
                continue;
            };
            let values = values
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
            if values.is_empty() {
                continue;
            }
            // A certificate says these values are one object. It cannot say so
            // about two values that are read by one instruction, because that
            // instruction needs both at once. Where it does, the coalescing is
            // declined and the values keep their own objects, which costs an
            // assignment in the output and nothing in correctness.
            if let Some(first) = values.first().copied() {
                if merge_would_interfere(&mut parent, &values)
                    || super::rules::set_outlives_a_redefinition(graph, &values)
                {
                    continue;
                }
                for value in values.iter().copied().skip(1) {
                    union(&mut parent, &mut rank, first, value);
                }
            }
            certificate_sets.push((
                BindingCertificateSource::CertifiedEntity(entity.id()),
                values,
            ));
        }
    }

    let mut members_by_root = BTreeMap::<usize, BTreeSet<ValueId>>::new();
    for (index, is_eligible) in eligible.iter().copied().enumerate() {
        if !is_eligible {
            continue;
        }
        let root = find(&mut parent, index);
        members_by_root
            .entry(root)
            .or_default()
            .insert(ValueId(index as u32));
    }
    let mut sources_by_root = BTreeMap::<usize, BTreeSet<BindingCertificateSource>>::new();
    for (source, values) in certificate_sets {
        let Some(first) = values.first().copied() else {
            continue;
        };
        let root = find(&mut parent, first.0 as usize);
        if values
            .iter()
            .all(|value| find(&mut parent, value.0 as usize) == root)
        {
            sources_by_root.entry(root).or_default().insert(source);
        } else {
            return Err(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::CertificateMembership {
                    binding: BindingId(u32::MAX),
                },
            ));
        }
    }

    let mut components = members_by_root
        .into_iter()
        .map(|(root, members)| {
            let mut sources = sources_by_root.remove(&root).unwrap_or_default();
            if sources.is_empty() && members.len() == 1 {
                sources.insert(BindingCertificateSource::Singleton);
            }
            BindingComponent { members, sources }
        })
        .collect::<Vec<_>>();
    components.sort_by_key(|component| component.members.first().copied());
    Ok(components)
}

/// Compute the smallest unsigned C-object width proved by the graph and every
/// surviving exact machine projection. Refused projection cells are delegated
/// upstream and cannot survive the cutover, so they do not poison the object.
fn binding_width(
    source: &r2ssa::SsaArtifact,
    machine_projection: &MachineProjection,
    component: &BindingComponent,
) -> Result<BindingWidth, BindingPlanBuildError> {
    let graph = source.graph();
    let mut binding_width_bits = 0_u32;
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
        binding_width_bits = binding_width_bits.max(member_width_bits);

        for site in &graph.uses_of[value.0 as usize] {
            let Some(MachineUseDisposition::Exact(slice)) =
                machine_projection.use_disposition(*site)
            else {
                continue;
            };
            let valid_end = slice
                .bit_offset()
                .checked_add(slice.width_bits())
                .is_some_and(|end| end <= slice.carrier_width_bits());
            if slice.width_bits() == 0
                || slice.carrier_width_bits() < member_width_bits
                || !valid_end
            {
                return Ok(BindingWidth::Refused(
                    ValueRefusal::IncoherentUseProjection { site: *site },
                ));
            }
            binding_width_bits = binding_width_bits.max(slice.carrier_width_bits());
        }

        let Some(definition) = graph.def_inst(*value) else {
            continue;
        };
        let Some(MachineWriteDisposition::Exact(write)) =
            machine_projection.write_disposition(definition)
        else {
            continue;
        };
        let carrier_width_bits = match *write {
            MachineWriteProjection::Full => member_width_bits,
            // A lane write says nothing about the carrier, so it is no evidence
            // that the object is carrier-wide. Only the lane it assigns is.
            MachineWriteProjection::Lane {
                bit_offset,
                width_bits,
                carrier_width_bits,
            } => {
                let valid_end = bit_offset
                    .checked_add(width_bits)
                    .is_some_and(|end| end <= carrier_width_bits);
                if width_bits == 0 || !valid_end {
                    return Ok(BindingWidth::Refused(
                        ValueRefusal::IncoherentWriteProjection { value: *value },
                    ));
                }
                width_bits
            }
            MachineWriteProjection::Insert {
                bit_offset,
                width_bits,
                carrier_width_bits,
            } => {
                let valid_end = bit_offset
                    .checked_add(width_bits)
                    .is_some_and(|end| end <= carrier_width_bits);
                if width_bits == 0 || carrier_width_bits < member_width_bits || !valid_end {
                    return Ok(BindingWidth::Refused(
                        ValueRefusal::IncoherentWriteProjection { value: *value },
                    ));
                }
                carrier_width_bits
            }
            MachineWriteProjection::ZeroExtend {
                from_width_bits,
                to_width_bits,
            } => {
                if from_width_bits == 0
                    || from_width_bits >= to_width_bits
                    || to_width_bits < member_width_bits
                {
                    return Ok(BindingWidth::Refused(
                        ValueRefusal::IncoherentWriteProjection { value: *value },
                    ));
                }
                to_width_bits
            }
        };
        binding_width_bits = binding_width_bits.max(carrier_width_bits);
    }
    if !declaration_width_is_supported(binding_width_bits) {
        let value = component
            .members
            .first()
            .copied()
            .expect("binding components are non-empty");
        return Ok(BindingWidth::Refused(
            ValueRefusal::UnsupportedDeclarationWidth {
                value,
                width_bits: binding_width_bits,
            },
        ));
    }
    Ok(BindingWidth::Exact(binding_width_bits))
}

impl BindingPlan {
    /// Seal the conservative Stage 4 shadow partition for one exact source.
    ///
    /// Binding identity is the transitive closure of exact upstream storage-span
    /// and certified-entity membership. It never depends on a register location,
    /// renderer alias, or hash-map iteration order.
    pub(crate) fn build_shadow(
        source_owned: &SourceOwnedFunctionFacts,
    ) -> Result<Self, BindingPlanBuildError> {
        let source = source_owned.source();
        let machine_projection = MachineProjection::from_artifact(source)
            .map_err(BindingPlanBuildError::MachineProjection)?;
        let graph = source.graph();
        let return_controls = certified_return_control_values(source);
        let direct_control_targets = certified_direct_control_target_values(source);
        let direct_call_targets = super::certified_direct_call_target_values(source);
        let call_return_addresses = super::certified_call_return_address_values(source);
        let stack_frame_values = certified_stack_frame_values(source);
        let stack_geometry_values = certified_stack_geometry_values(source);
        let unobserved_values = source.unobserved_values();
        let structural_unused = source
            .obligations()
            .structural_unused_values(graph, source.unobserved_merges().unobserved_uses())
            .ok_or(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::Authority,
            ))?;
        let mut literal_by_value = BTreeMap::<ValueId, MachineExprId>::new();
        for (expr_id, expr) in machine_projection.arena().iter() {
            if let MachineExprKind::Constant { binding, .. } = expr.kind() {
                // Arena order is dense and stable. One constant may be interned
                // at more than one machine type; the first node is the stable
                // canonical literal expression for value disposition purposes.
                literal_by_value.entry(binding.value()).or_insert(expr_id);
            }
        }
        let mut expr_by_value = BTreeMap::<ValueId, MachineExprId>::new();
        for entity in machine_projection.entities() {
            expr_by_value.insert(entity.output().value(), entity.root());
        }
        let inlinable = super::rules::inlinable_values(source, &machine_projection);
        let mut dispositions = graph
            .values
            .iter()
            .map(|graph_value| ValueDisposition::Refused {
                reason: ValueRefusal::MissingBindingCertificate {
                    value: graph_value.id,
                },
            })
            .collect::<Vec<_>>();

        for (index, graph_value) in graph.values.iter().enumerate() {
            if graph_value.id.0 as usize != index {
                return Err(BindingPlanBuildError::Seal(
                    BindingPlanSourceMismatch::ValueTopology {
                        index,
                        value: graph_value.id,
                    },
                ));
            }
            if return_controls.contains(&graph_value.id) {
                dispositions[index] = ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::ReturnControl,
                    proof: ValueElisionProof {
                        authority: source.authority().clone(),
                        value: graph_value.id,
                    },
                };
            } else if direct_control_targets.contains(&graph_value.id) {
                dispositions[index] = ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::DirectControlTarget,
                    proof: ValueElisionProof {
                        authority: source.authority().clone(),
                        value: graph_value.id,
                    },
                };
            } else if direct_call_targets.contains(&graph_value.id) {
                dispositions[index] = ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::DirectCallTarget,
                    proof: ValueElisionProof {
                        authority: source.authority().clone(),
                        value: graph_value.id,
                    },
                };
            } else if stack_frame_values.contains(&graph_value.id) {
                dispositions[index] = ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::StackFrame,
                    proof: ValueElisionProof {
                        authority: source.authority().clone(),
                        value: graph_value.id,
                    },
                };
            } else if stack_geometry_values.contains(&graph_value.id) {
                dispositions[index] = ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::DeadStackBase,
                    proof: ValueElisionProof {
                        authority: source.authority().clone(),
                        value: graph_value.id,
                    },
                };
            } else if source.unobserved_merges().contains(graph_value.id) {
                dispositions[index] = ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::UnobservedMerge,
                    proof: ValueElisionProof {
                        authority: source.authority().clone(),
                        value: graph_value.id,
                    },
                };
            } else if unobserved_values.contains(&graph_value.id) {
                dispositions[index] = ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::UnobservedValue,
                    proof: ValueElisionProof {
                        authority: source.authority().clone(),
                        value: graph_value.id,
                    },
                };
            } else if structural_unused.contains(&graph_value.id) {
                dispositions[index] = ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::UnusedStructuralValue,
                    proof: ValueElisionProof {
                        authority: source.authority().clone(),
                        value: graph_value.id,
                    },
                };
            } else if call_return_addresses.contains(&graph_value.id) {
                dispositions[index] = ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::CallReturnAddress,
                    proof: ValueElisionProof {
                        authority: source.authority().clone(),
                        value: graph_value.id,
                    },
                };
            } else if graph_value.var.constant_bits().is_none()
                && inlinable.contains(&graph_value.id)
                && let Some(expr) = expr_by_value.get(&graph_value.id).copied()
            {
                dispositions[index] = ValueDisposition::Inline {
                    expr,
                    proof: InlineProof {
                        authority: source.authority().clone(),
                        literal: expr,
                    },
                };
            } else if graph_value.var.constant_bits().is_some() {
                dispositions[index] = match literal_by_value.get(&graph_value.id).copied() {
                    Some(expr) => ValueDisposition::Inline {
                        expr,
                        proof: InlineProof {
                            authority: source.authority().clone(),
                            literal: expr,
                        },
                    },
                    None => {
                        if std::env::var_os("R2DEC_TRACE_REFUSAL").is_some() {
                            eprintln!(
                                "missing literal projection {:?} bits={:?} name={:?} uses={} def={:?} users={users:?}",
                                graph_value.id,
                                graph_value.var.constant_bits(),
                                graph_value.var.name,
                                graph.use_sites(graph_value.id).len(),
                                graph
                                    .def_inst(graph_value.id)
                                    .and_then(|inst| graph.inst(inst))
                                    .map(|inst| format!("{:?}", inst.payload)
                                        .chars()
                                        .take(110)
                                        .collect::<String>()),
                                users = graph
                                    .use_sites(graph_value.id)
                                    .iter()
                                    .filter_map(|site| graph.inst(site.inst))
                                    .map(|inst| format!("{:?}", inst.payload)
                                        .chars()
                                        .take(90)
                                        .collect::<String>())
                                    .collect::<Vec<_>>(),
                            );
                        }
                        // A constant the arena never interned because the only
                        // thing that reads it is a user-operation the machine
                        // projection does not lower. Say that, rather than
                        // reporting a projection defect the arena does not have.
                        let unmodelled_userop = graph
                            .use_sites(graph_value.id)
                            .iter()
                            .filter_map(|site| graph.inst(site.inst))
                            .find_map(|inst| match &inst.payload {
                                r2ssa::InstPayload::Op(r2ssa::SSAOp::CallOther {
                                    userop, ..
                                }) => Some(*userop),
                                _ => None,
                            });
                        ValueDisposition::Refused {
                            reason: match unmodelled_userop {
                                Some(userop) => ValueRefusal::UnmodelledUserOperation {
                                    value: graph_value.id,
                                    userop,
                                },
                                None => ValueRefusal::MissingLiteralProjection {
                                    value: graph_value.id,
                                },
                            },
                        }
                    }
                };
            }
        }

        let components = binding_components(source_owned)?;
        if u32::try_from(components.len()).is_err() {
            return Err(BindingPlanBuildError::TooManyBindings {
                count: components.len(),
            });
        }

        let mut bindings = Vec::with_capacity(components.len());

        for component in components {
            let width_bits = match binding_width(source, &machine_projection, &component)? {
                BindingWidth::Exact(width_bits) => width_bits,
                BindingWidth::Refused(reason) => {
                    for value in component.members {
                        dispositions[value.0 as usize] = ValueDisposition::Refused { reason };
                    }
                    continue;
                }
            };
            let binding = BindingId(bindings.len() as u32);
            for value in &component.members {
                dispositions[value.0 as usize] = ValueDisposition::Bound { binding };
            }
            let first = component
                .members
                .first()
                .and_then(|value| graph.value(*value))
                .ok_or(BindingPlanBuildError::Seal(
                    BindingPlanSourceMismatch::CertificateMembership { binding },
                ))?;
            // A member with no defining instruction entered this function
            // already holding its value, so the object exists from entry.
            let caller_supplied = component
                .members
                .iter()
                .any(|value| graph.def_inst(*value).is_none());
            bindings.push(Binding {
                declaration_type: super::rules::declaration_type_for_binding(
                    source_owned,
                    component.members.iter().copied(),
                    width_bits,
                    source
                        .machine_context()
                        .memory_model()
                        .default_address_bits(),
                ),
                certificate: BindingCertificate {
                    sources: component
                        .sources
                        .into_iter()
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                },
                presentation_name_hint: Some(first.var.display_name()),
                caller_supplied,
            });
        }

        let candidates = parameter_candidates(source_owned);
        let mut parameters = vec![None; candidates.len()];
        for (index, candidate) in candidates.into_iter().enumerate() {
            let Some(candidate) = candidate else {
                continue;
            };
            let slot = u32::try_from(index).expect("dense parameter domain fits u32");
            let (entity, width_bytes, entry_values) = match candidate {
                ParameterCandidate::Exact {
                    entity,
                    width_bytes,
                    entry_values,
                } => (entity, width_bytes, entry_values),
                ParameterCandidate::Refused { reason, .. } => {
                    parameters[index] = Some(ParameterDisposition::Refused { reason });
                    continue;
                }
            };
            let width_bits = match parameter_width(entity, slot, width_bytes) {
                Ok(width_bits) => width_bits,
                Err(reason) => {
                    parameters[index] = Some(ParameterDisposition::Refused { reason });
                    continue;
                }
            };

            let mut value_binding = None;
            let mut missing_value = None;
            for value in entry_values {
                match dispositions.get(value.0 as usize) {
                    Some(ValueDisposition::Bound { binding })
                        if value_binding.is_none_or(|existing| existing == *binding) =>
                    {
                        value_binding = Some(*binding);
                    }
                    _ => {
                        missing_value = Some(value);
                        break;
                    }
                }
            }
            if let Some(value) = missing_value {
                parameters[index] = Some(ParameterDisposition::Refused {
                    reason: ParameterRefusal::MissingValueBinding {
                        entity,
                        slot,
                        value,
                    },
                });
                continue;
            }

            let binding = match value_binding {
                Some(binding) => binding,
                None => {
                    let Some(binding) = BindingId::from_dense_index(bindings.len()) else {
                        return Err(BindingPlanBuildError::TooManyBindings {
                            count: bindings.len().saturating_add(1),
                        });
                    };
                    bindings.push(Binding {
                        declaration_type: CType::machine_bits(width_bits),
                        certificate: BindingCertificate {
                            sources: Box::new([BindingCertificateSource::CertifiedEntity(entity)]),
                        },
                        presentation_name_hint: None,
                        caller_supplied: false,
                    });
                    binding
                }
            };

            parameters[index] = Some(ParameterDisposition::Bound {
                binding,
                width_bits,
            });
        }
        refuse_conflicting_parameter_bindings(&mut parameters);

        let mut stack_objects = BTreeMap::new();
        if let Some(render) = source_owned.report().render() {
            for entity in render.certified_entities.values() {
                let r2types::CertifiedEntity::StackSlot {
                    id,
                    object,
                    base,
                    offset,
                    size,
                    source_slot,
                    callee_allocation,
                } = entity
                else {
                    continue;
                };
                if source
                    .certificates()
                    .stack_frame_round_trips
                    .contains_key(object)
                    || super::certified_return_control_stack_objects(source).contains(object)
                {
                    stack_objects.insert(
                        *object,
                        StackObjectDisposition::Elided {
                            reason: r2ssa::ledger::ElisionReason::StackFrame,
                        },
                    );
                    continue;
                }
                // Identity needs a geometry, not an endorsement. A declared
                // slot and a callee allocation are the two strong forms and
                // still cannot both answer at once; where neither does, the
                // width the object's own accesses agree on is enough to name
                // it. Radare2 reports no stack variables at all for some
                // functions, and every local in them was refused for that
                // silence.
                if source_slot.is_none() && callee_allocation.is_none() && size.is_none()
                    || source_slot.is_some() && callee_allocation.is_some()
                {
                    stack_objects.insert(
                        *object,
                        StackObjectDisposition::Refused {
                            reason: StackObjectRefusal::MissingSourceIdentity { object: *object },
                        },
                    );
                    continue;
                }
                let Some(size_bytes) = *size else {
                    stack_objects.insert(
                        *object,
                        StackObjectDisposition::Refused {
                            reason: StackObjectRefusal::MissingWidth { object: *object },
                        },
                    );
                    continue;
                };
                let Some(width_bits) = size_bytes.checked_mul(8).filter(|width| *width > 0) else {
                    stack_objects.insert(
                        *object,
                        StackObjectDisposition::Refused {
                            reason: StackObjectRefusal::InvalidWidth {
                                object: *object,
                                size_bytes,
                            },
                        },
                    );
                    continue;
                };
                if let Some(certificate) = callee_allocation {
                    if source_slot.is_some()
                        || certificate.object != *object
                        || certificate.size_bytes != size_bytes
                        || certificate.accesses.is_empty()
                        || certificate.active_sp_offsets.is_empty()
                    {
                        stack_objects.insert(
                            *object,
                            StackObjectDisposition::Refused {
                                reason: StackObjectRefusal::MissingSourceIdentity {
                                    object: *object,
                                },
                            },
                        );
                        continue;
                    }
                    let Some(binding) = BindingId::from_dense_index(bindings.len()) else {
                        return Err(BindingPlanBuildError::TooManyBindings {
                            count: bindings.len().saturating_add(1),
                        });
                    };
                    bindings.push(Binding {
                        declaration_type: super::rules::declaration_type_for_stack_object(
                            source_owned,
                            *object,
                            width_bits,
                            source
                                .machine_context()
                                .memory_model()
                                .default_address_bits(),
                        ),
                        certificate: BindingCertificate {
                            sources: Box::new([BindingCertificateSource::CertifiedEntity(*id)]),
                        },
                        presentation_name_hint: Some(if certificate.entry_offset < 0 {
                            format!("stack_m{}", certificate.entry_offset.unsigned_abs())
                        } else {
                            format!("stack_p{}", certificate.entry_offset.unsigned_abs())
                        }),
                        caller_supplied: false,
                    });
                    stack_objects.insert(*object, StackObjectDisposition::Bound { binding });
                    continue;
                }
                let Some(source_slot) = *source_slot else {
                    // Named by the width its own accesses agree on, at the
                    // position the object model proved. A local like any other;
                    // only the origin of its geometry differs.
                    let Some(binding) = BindingId::from_dense_index(bindings.len()) else {
                        return Err(BindingPlanBuildError::TooManyBindings {
                            count: bindings.len().saturating_add(1),
                        });
                    };
                    bindings.push(Binding {
                        declaration_type: super::rules::declaration_type_for_stack_object(
                            source_owned,
                            *object,
                            width_bits,
                            source
                                .machine_context()
                                .memory_model()
                                .default_address_bits(),
                        ),
                        certificate: BindingCertificate {
                            sources: Box::new([BindingCertificateSource::CertifiedEntity(*id)]),
                        },
                        presentation_name_hint: Some(if *offset < 0 {
                            format!("stack_m{}", offset.unsigned_abs())
                        } else {
                            format!("stack_p{}", offset.unsigned_abs())
                        }),
                        caller_supplied: false,
                    });
                    stack_objects.insert(*object, StackObjectDisposition::Bound { binding });
                    continue;
                };
                if source_slot.base() != *base
                    || source_slot.offset() != *offset
                    || size_bytes != source_slot.size_bytes()
                {
                    stack_objects.insert(
                        *object,
                        StackObjectDisposition::Refused {
                            reason: StackObjectRefusal::MissingSourceIdentity { object: *object },
                        },
                    );
                    continue;
                }
                match source_slot.role() {
                    r2ssa::SourceStackSlotRole::Local => {
                        let Some(binding) = BindingId::from_dense_index(bindings.len()) else {
                            return Err(BindingPlanBuildError::TooManyBindings {
                                count: bindings.len().saturating_add(1),
                            });
                        };
                        bindings.push(Binding {
                            declaration_type: super::rules::declaration_type_for_stack_object(
                                source_owned,
                                *object,
                                width_bits,
                                source
                                    .machine_context()
                                    .memory_model()
                                    .default_address_bits(),
                            ),
                            certificate: BindingCertificate {
                                sources: Box::new([BindingCertificateSource::CertifiedEntity(*id)]),
                            },
                            presentation_name_hint: Some(if *offset < 0 {
                                format!("stack_m{}", offset.unsigned_abs())
                            } else {
                                format!("stack_p{}", offset.unsigned_abs())
                            }),
                            caller_supplied: false,
                        });
                        stack_objects.insert(*object, StackObjectDisposition::Bound { binding });
                    }
                    r2ssa::SourceStackSlotRole::ParameterHome {
                        parameter_index, ..
                    } => {
                        let Some(ParameterDisposition::Bound {
                            binding,
                            width_bits: parameter_width_bits,
                        }) = parameters.get(parameter_index as usize).copied().flatten()
                        else {
                            stack_objects.insert(
                                *object,
                                StackObjectDisposition::Refused {
                                    reason: StackObjectRefusal::ParameterHomeUnavailable {
                                        object: *object,
                                        parameter_index,
                                    },
                                },
                            );
                            continue;
                        };
                        if parameter_width_bits != width_bits {
                            stack_objects.insert(
                                *object,
                                StackObjectDisposition::Refused {
                                    reason: StackObjectRefusal::ParameterHomeWidthMismatch {
                                        object: *object,
                                        parameter_index,
                                        slot_width_bits: width_bits,
                                        parameter_width_bits,
                                    },
                                },
                            );
                            continue;
                        }
                        stack_objects.insert(*object, StackObjectDisposition::Bound { binding });
                    }
                    r2ssa::SourceStackSlotRole::UnclassifiedResource => {
                        stack_objects.insert(
                            *object,
                            StackObjectDisposition::Refused {
                                reason: StackObjectRefusal::UnclassifiedSourceRole {
                                    object: *object,
                                },
                            },
                        );
                    }
                }
            }
        }

        let plan = Self {
            authority: source.authority().clone(),
            machine_projection,
            bindings: bindings.into_boxed_slice(),
            dispositions: dispositions.into_boxed_slice(),
            parameters: parameters.into_boxed_slice(),
            stack_objects,
        };
        plan.validate_seal(source_owned)?;
        Ok(plan)
    }
}

#[cfg(test)]
mod parameter_tests {
    use super::*;

    #[test]
    fn sparse_out_of_order_slots_keep_their_exact_indices() {
        let mut candidates = Vec::new();
        insert_formal_parameter_candidate(&mut candidates, 3, 8);
        insert_formal_parameter_candidate(&mut candidates, 1, 4);

        assert_eq!(candidates.len(), 4);
        assert!(candidates[0].is_none());
        assert!(matches!(
            candidates[1],
            Some(ParameterCandidate::Exact {
                entity: SemanticId::Parameter(1),
                width_bytes: 4,
                ..
            })
        ));
        assert!(candidates[2].is_none());
        assert!(matches!(
            candidates[3],
            Some(ParameterCandidate::Exact {
                entity: SemanticId::Parameter(3),
                width_bytes: 8,
                ..
            })
        ));
    }

    #[test]
    fn three_slot_binding_conflict_has_one_deterministic_reason() {
        let binding = BindingId::from_dense_index(7).expect("binding");
        let mut parameters = vec![
            Some(ParameterDisposition::Bound {
                binding,
                width_bits: 64,
            });
            3
        ];
        refuse_conflicting_parameter_bindings(&mut parameters);

        let expected = Some(ParameterDisposition::Refused {
            reason: ParameterRefusal::ConflictingBindingOwnership {
                binding,
                first_slot: 0,
                second_slot: 1,
            },
        });
        assert!(
            parameters
                .iter()
                .all(|disposition| *disposition == expected)
        );
    }
}
