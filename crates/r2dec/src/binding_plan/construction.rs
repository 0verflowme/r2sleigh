use super::*;

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
    let eligible = graph
        .values
        .iter()
        .map(|value| value.var.constant_bits().is_none())
        .collect::<Vec<_>>();
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
    for (span, values) in values_by_span {
        if values.len() > 1 {
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
            if let Some(first) = values.first().copied() {
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
        let mut literal_by_value = BTreeMap::<ValueId, MachineExprId>::new();
        for (expr_id, expr) in machine_projection.arena().iter() {
            if let MachineExprKind::Constant { binding, .. } = expr.kind() {
                // Arena order is dense and stable. One constant may be interned
                // at more than one machine type; the first node is the stable
                // canonical literal expression for value disposition purposes.
                literal_by_value.entry(binding.value()).or_insert(expr_id);
            }
        }
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
            if graph_value.var.constant_bits().is_some() {
                dispositions[index] = match literal_by_value.get(&graph_value.id).copied() {
                    Some(expr) => ValueDisposition::Inline {
                        expr,
                        proof: InlineProof {
                            authority: source.authority().clone(),
                            literal: expr,
                        },
                    },
                    None => ValueDisposition::Refused {
                        reason: ValueRefusal::MissingLiteralProjection {
                            value: graph_value.id,
                        },
                    },
                };
                continue;
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
            bindings.push(Binding {
                declaration_type: CType::UInt(width_bits),
                certificate: BindingCertificate {
                    sources: component
                        .sources
                        .into_iter()
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                },
                presentation_name_hint: Some(first.var.display_name()),
            });
        }

        let mut stack_objects = BTreeMap::new();
        if let Some(render) = source_owned.report().render() {
            for entity in render.certified_entities.values() {
                let r2types::CertifiedEntity::StackSlot {
                    id,
                    object,
                    offset,
                    size,
                    ..
                } = entity
                else {
                    continue;
                };
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
                let binding = BindingId(bindings.len() as u32);
                bindings.push(Binding {
                    declaration_type: CType::UInt(width_bits),
                    certificate: BindingCertificate {
                        sources: Box::new([BindingCertificateSource::CertifiedEntity(*id)]),
                    },
                    presentation_name_hint: Some(if *offset < 0 {
                        format!("stack_m{}", offset.unsigned_abs())
                    } else {
                        format!("stack_p{}", offset.unsigned_abs())
                    }),
                });
                stack_objects.insert(*object, StackObjectDisposition::Bound { binding });
            }
        }

        let plan = Self {
            authority: source.authority().clone(),
            machine_projection,
            bindings: bindings.into_boxed_slice(),
            dispositions: dispositions.into_boxed_slice(),
            stack_objects,
        };
        plan.validate_seal(source_owned)?;
        Ok(plan)
    }
}
