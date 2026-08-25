use super::*;
use r2il::{
    AddressSpace, ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef, RegisterProjection,
    RegisterProjectionDisposition, RegisterStorage, SpaceId, Varnode,
};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, MachineUseDisposition, MachineWriteDisposition,
    SourceAbiParameterSpec, SourceFunctionInterface, SourceFunctionReturn, SsaArtifact,
};
use std::sync::Arc;

fn source_owned(ops: impl IntoIterator<Item = R2ILOp>) -> SourceOwnedFunctionFacts {
    let mut block = R2ILBlock::new(0x1000, 4);
    for op in ops {
        block.push(op);
    }
    let mut arch = ArchSpec::new("x86-64");
    arch.add_space(AddressSpace::ram(8));
    arch.add_register(RegisterDef::new("RAX", 0, 8));
    arch.add_register(RegisterDef::new("AH", 1, 1));
    arch.add_register(RegisterDef::new("RSP", 0x28, 8));
    arch.add_register(RegisterDef::new("RIP", 0x30, 8));
    arch.add_register(RegisterDef::new("RDI", 0x38, 8));
    arch.add_register(RegisterDef::new("EDI", 0x38, 4));
    arch.register_projections = vec![
        RegisterProjection {
            written: RegisterStorage { offset: 0, size: 8 },
            disposition: RegisterProjectionDisposition::Bound {
                carrier: RegisterStorage { offset: 0, size: 8 },
                slice: RegisterBitSlice {
                    lsb_bit_offset: 0,
                    size_bits: 64,
                },
            },
        },
        RegisterProjection {
            written: RegisterStorage { offset: 1, size: 1 },
            disposition: RegisterProjectionDisposition::Bound {
                carrier: RegisterStorage { offset: 0, size: 8 },
                slice: RegisterBitSlice {
                    lsb_bit_offset: 8,
                    size_bits: 8,
                },
            },
        },
        RegisterProjection {
            written: RegisterStorage {
                offset: 0x28,
                size: 8,
            },
            disposition: RegisterProjectionDisposition::Bound {
                carrier: RegisterStorage {
                    offset: 0x28,
                    size: 8,
                },
                slice: RegisterBitSlice {
                    lsb_bit_offset: 0,
                    size_bits: 64,
                },
            },
        },
        RegisterProjection {
            written: RegisterStorage {
                offset: 0x30,
                size: 8,
            },
            disposition: RegisterProjectionDisposition::Bound {
                carrier: RegisterStorage {
                    offset: 0x30,
                    size: 8,
                },
                slice: RegisterBitSlice {
                    lsb_bit_offset: 0,
                    size_bits: 64,
                },
            },
        },
        RegisterProjection {
            written: RegisterStorage {
                offset: 0x38,
                size: 4,
            },
            disposition: RegisterProjectionDisposition::Bound {
                carrier: RegisterStorage {
                    offset: 0x38,
                    size: 8,
                },
                slice: RegisterBitSlice {
                    lsb_bit_offset: 0,
                    size_bits: 32,
                },
            },
        },
        RegisterProjection {
            written: RegisterStorage {
                offset: 0x38,
                size: 8,
            },
            disposition: RegisterProjectionDisposition::Bound {
                carrier: RegisterStorage {
                    offset: 0x38,
                    size: 8,
                },
                slice: RegisterBitSlice {
                    lsb_bit_offset: 0,
                    size_bits: 64,
                },
            },
        },
    ];
    let storage = |offset| CanonicalStorageId {
        space: CanonicalStorageSpace::Register,
        offset,
        size: 8,
    };
    let interface = SourceFunctionInterface::new_exact(
        b"binding-plan-test-interface".to_vec(),
        "sysv64",
        [SourceAbiParameterSpec::new(0, storage(0x38))],
        SourceFunctionReturn::Register {
            storage: storage(0),
        },
        std::iter::empty(),
    )
    .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
    .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
    .expect("exact test source interface");
    let source = Arc::new(
        SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
            .expect("test SSA artifact"),
    );
    let request = r2types::TypeWritebackAnalysisRequest::new(
        Arc::clone(&source),
        r2types::ParsedExternalContext::default(),
    )
    .expect("source-owned request");
    r2types::build_source_owned_type_writeback_analysis(request)
        .expect("source-owned analysis")
        .finalize_for_decompile(r2types::DecompileFinalization {
            kind: r2types::DecompileRouteKind::Standard,
            reason: "binding-plan shadow test".to_string(),
            fallback_comment: None,
        })
        .expect("source-owned finalization")
}

#[test]
fn shadow_plan_groups_spans_and_inlines_only_upstream_literals() {
    let first = Varnode::unique(0x10, 8);
    let source_owned = source_owned([
        R2ILOp::Copy {
            dst: first.clone(),
            src: Varnode::constant(7, 8),
        },
        R2ILOp::IntAdd {
            dst: first,
            a: Varnode::unique(0x10, 8),
            b: Varnode::constant(1, 8),
        },
    ]);
    let source = source_owned.source();
    let plan = BindingPlan::build_shadow(&source_owned).expect("sealed shadow plan");
    let nonconstants = source
        .graph()
        .values
        .iter()
        .filter(|value| value.var.constant_bits().is_none())
        .map(|value| value.id)
        .collect::<Vec<_>>();
    assert_eq!(nonconstants.len(), 2);
    let binding = match plan.disposition(nonconstants[0]) {
        Some(ValueDisposition::Bound { binding }) => *binding,
        disposition => panic!("first storage value is not bound: {disposition:?}"),
    };
    assert_eq!(
        plan.disposition(nonconstants[1]),
        Some(&ValueDisposition::Bound { binding })
    );
    let binding_fact = plan.binding(binding).expect("dense binding");
    assert_eq!(binding_fact.declaration_type(), &CType::u64());
    assert!(binding_fact.presentation_name_hint().is_some());
    assert!(matches!(
        binding_fact.certificate.sources.as_ref(),
        [BindingCertificateSource::StorageSpan(_)]
    ));
    for constant in source
        .graph()
        .values
        .iter()
        .filter(|value| value.var.constant_bits().is_some())
    {
        assert!(matches!(
            plan.disposition(constant.id),
            Some(ValueDisposition::Inline { expr, proof })
                if expr == &proof.literal && proof.authority == *source.authority()
        ));
    }
    assert_eq!(plan.validate_source(source), Ok(()));
    assert!(plan.validate_seal(&source_owned).is_ok());
}

#[test]
fn use_and_write_dispositions_delegate_to_the_validated_projection() {
    let source_owned = source_owned([R2ILOp::Copy {
        dst: Varnode::unique(0x10, 8),
        src: Varnode::constant(7, 8),
    }]);
    let source = source_owned.source();
    let plan = BindingPlan::build_shadow(&source_owned).expect("sealed shadow plan");
    for inst in &source.graph().insts {
        for input_idx in 0..inst.inputs.len() {
            let site = UseSite {
                inst: inst.id,
                input_idx,
            };
            assert_eq!(
                plan.use_disposition(site),
                plan.machine_projection().use_disposition(site)
            );
            assert!(matches!(
                plan.use_disposition(site),
                Some(MachineUseDisposition::Exact(_))
            ));
        }
        assert_eq!(
            plan.write_disposition(inst.id),
            plan.machine_projection().write_disposition(inst.id)
        );
        if inst.output.is_some() {
            assert!(matches!(
                plan.write_disposition(inst.id),
                Some(MachineWriteDisposition::Exact(_))
            ));
        }
    }
}

#[test]
fn declaration_width_uses_exact_machine_carriers_not_register_view_widths() {
    let source_owned = source_owned([
        R2ILOp::Copy {
            dst: Varnode::unique(0x10, 1),
            src: Varnode::register(1, 1),
        },
        R2ILOp::Copy {
            dst: Varnode::register(1, 1),
            src: Varnode::constant(3, 1),
        },
    ]);
    let source = source_owned.source();
    let plan = BindingPlan::build_shadow(&source_owned).expect("sealed carrier-width plan");
    let register_values = source
        .graph()
        .values
        .iter()
        .filter(|value| {
            value.canonical_storage.is_some_and(|storage| {
                storage.space == CanonicalStorageSpace::Register
                    && storage.offset == 1
                    && storage.size == 1
            })
        })
        .map(|value| value.id)
        .collect::<Vec<_>>();
    assert!(!register_values.is_empty());
    let mut carrier_binding = None;
    for value in register_values {
        let binding = match plan.disposition(value) {
            Some(ValueDisposition::Bound { binding }) => *binding,
            disposition => panic!("AH value is not bound: {disposition:?}"),
        };
        carrier_binding.get_or_insert(binding);
        assert_eq!(
            plan.binding(binding).map(Binding::declaration_type),
            Some(&CType::u64())
        );
    }
    assert!(plan.validate_seal(&source_owned).is_ok());

    let carrier_binding = carrier_binding.expect("AH carrier binding");
    for forged_width in [32, 128] {
        let mut forged = plan.clone();
        forged.bindings[carrier_binding.index()].declaration_type = CType::UInt(forged_width);
        assert_eq!(
            forged.validate_seal(&source_owned),
            Err(BindingPlanBuildError::Seal(
                BindingPlanSourceMismatch::DeclarationWidth {
                    binding: carrier_binding,
                }
            ))
        );
    }
}

#[test]
fn refused_machine_use_leaves_its_constant_explicitly_refused() {
    let source_owned = source_owned([R2ILOp::CallOther {
        output: Some(Varnode::unique(0x10, 8)),
        userop: 7,
        inputs: vec![Varnode::constant(9, 8)],
    }]);
    let source = source_owned.source();
    let plan = BindingPlan::build_shadow(&source_owned).expect("partial shadow plan");
    let constant = source
        .graph()
        .values
        .iter()
        .find(|value| value.var.constant_bits() == Some(9))
        .expect("constant graph value");
    assert!(matches!(
        plan.disposition(constant.id),
        Some(ValueDisposition::Refused {
            reason: ValueRefusal::MissingLiteralProjection { value }
        }) if *value == constant.id
    ));
    let use_site = source.graph().uses_of[constant.id.0 as usize][0];
    assert!(matches!(
        plan.use_disposition(use_site),
        Some(MachineUseDisposition::Refused(_))
    ));
}

#[test]
fn seal_rejects_foreign_authority_and_inverse_membership_drift() {
    let ops = || {
        [
            R2ILOp::Copy {
                dst: Varnode::unique(0x10, 8),
                src: Varnode::constant(1, 8),
            },
            R2ILOp::Copy {
                dst: Varnode::unique(0x20, 4),
                src: Varnode::constant(2, 4),
            },
        ]
    };
    let first_source = source_owned(ops());
    let mut plan = BindingPlan::build_shadow(&first_source).expect("sealed shadow plan");
    let independent = source_owned(ops());
    assert_eq!(
        plan.validate_source(independent.source()),
        Err(BindingPlanSourceMismatch::Authority)
    );

    let bound_values = plan
        .dispositions
        .iter()
        .enumerate()
        .filter_map(|(index, disposition)| match disposition {
            ValueDisposition::Bound { binding } => Some((ValueId(index as u32), *binding)),
            _ => None,
        })
        .collect::<Vec<_>>();
    let (value, original) = bound_values[0];
    let foreign_binding = bound_values
        .iter()
        .find_map(|(_, binding)| (*binding != original).then_some(*binding))
        .expect("second independent storage binding");
    plan.dispositions[value.0 as usize] = ValueDisposition::Bound {
        binding: foreign_binding,
    };
    assert!(matches!(
        plan.validate_seal(&first_source),
        Err(BindingPlanBuildError::Seal(
            BindingPlanSourceMismatch::CertificateMembership { .. }
        ))
    ));
}

#[test]
fn seal_resolves_certificate_sources_instead_of_trusting_stored_witnesses() {
    let first = Varnode::unique(0x10, 8);
    let second = Varnode::unique(0x20, 8);
    let source_owned = source_owned([
        R2ILOp::Copy {
            dst: first.clone(),
            src: Varnode::constant(1, 8),
        },
        R2ILOp::IntAdd {
            dst: first,
            a: Varnode::unique(0x10, 8),
            b: Varnode::constant(1, 8),
        },
        R2ILOp::Copy {
            dst: second.clone(),
            src: Varnode::constant(2, 8),
        },
        R2ILOp::IntAdd {
            dst: second,
            a: Varnode::unique(0x20, 8),
            b: Varnode::constant(1, 8),
        },
    ]);
    let plan = BindingPlan::build_shadow(&source_owned).expect("sealed two-span plan");
    let certified = plan
        .bindings
        .iter()
        .enumerate()
        .filter_map(
            |(index, binding)| match binding.certificate.sources.as_ref() {
                [source @ BindingCertificateSource::StorageSpan(_)] => {
                    Some((BindingId(index as u32), *source))
                }
                _ => None,
            },
        )
        .collect::<Vec<_>>();
    assert!(
        certified.len() >= 2,
        "two independent span witnesses required"
    );
    let (binding, source) = certified[0];
    let foreign_source = certified[1].1;

    let mut missing = plan.clone();
    missing.bindings[binding.index()].certificate.sources = Box::new([]);
    assert!(matches!(
        missing.validate_seal(&source_owned),
        Err(BindingPlanBuildError::Seal(
            BindingPlanSourceMismatch::CertificateMembership { binding: rejected }
        )) if rejected == binding
    ));

    let mut foreign = plan.clone();
    foreign.bindings[binding.index()].certificate.sources = Box::new([foreign_source]);
    assert!(matches!(
        foreign.validate_seal(&source_owned),
        Err(BindingPlanBuildError::Seal(
            BindingPlanSourceMismatch::CertificateMembership { binding: rejected }
        )) if rejected == binding
    ));

    let mut redundant = plan;
    let mut sources = vec![source, foreign_source];
    sources.sort();
    redundant.bindings[binding.index()].certificate.sources = sources.into_boxed_slice();
    assert!(matches!(
        redundant.validate_seal(&source_owned),
        Err(BindingPlanBuildError::Seal(
            BindingPlanSourceMismatch::CertificateMembership { binding: rejected }
        )) if rejected == binding
    ));
}

#[test]
fn overlapping_parameter_and_span_certificates_close_transitively_in_canonical_order() {
    let source_owned = source_owned([
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
            val: Varnode::register(0x38, 4),
        },
        R2ILOp::IntAdd {
            dst: Varnode::register(0x38, 8),
            a: Varnode::register(0x38, 8),
            b: Varnode::constant(1, 8),
        },
        R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::register(0x38, 8),
        },
    ]);
    let parameter = BindingCertificateSource::CertifiedEntity(SemanticId::Parameter(0));
    let constructed = binding_components(&source_owned).expect("union-find components");
    let component = constructed
        .iter()
        .find(|component| component.sources.contains(&parameter))
        .expect("certified parameter component");
    assert!(component.members.len() >= 3);
    assert!(
        component
            .sources
            .iter()
            .any(|source| matches!(source, BindingCertificateSource::StorageSpan(_)))
    );

    let sealed = seal_binding_components(&source_owned).expect("independent BFS components");
    let sealed_component = sealed
        .iter()
        .find(|component| component.sources.contains(&parameter))
        .expect("independently resolved parameter component");
    assert_eq!(sealed_component.members, component.members);
    assert_eq!(sealed_component.sources, component.sources);

    let plan = BindingPlan::build_shadow(&source_owned).expect("sealed overlap plan");
    let binding = plan
        .bindings
        .iter()
        .enumerate()
        .find_map(|(index, binding)| {
            binding
                .certificate
                .sources
                .contains(&parameter)
                .then_some(BindingId(index as u32))
        })
        .expect("parameter binding");
    let actual_members = plan
        .dispositions
        .iter()
        .enumerate()
        .filter_map(|(index, disposition)| {
            (*disposition == ValueDisposition::Bound { binding }).then_some(ValueId(index as u32))
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(actual_members, component.members);

    let mut minima = vec![None::<ValueId>; plan.bindings.len()];
    for (index, disposition) in plan.dispositions.iter().enumerate() {
        let ValueDisposition::Bound { binding } = disposition else {
            continue;
        };
        let value = ValueId(index as u32);
        let minimum = &mut minima[binding.index()];
        *minimum = Some(minimum.map_or(value, |old| old.min(value)));
    }
    assert!(
        minima.iter().all(Option::is_some),
        "every dense binding must have a member"
    );
    assert!(
        minima.windows(2).all(|pair| pair[0] < pair[1]),
        "binding IDs must follow minimum stable ValueId order"
    );
    assert!(plan.validate_seal(&source_owned).is_ok());
}
