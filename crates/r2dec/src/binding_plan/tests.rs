use super::*;
use r2il::{
    AddressSpace, ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef, RegisterProjection,
    RegisterProjectionDisposition, RegisterStorage, SpaceId, Varnode,
};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, MachineUseDisposition, MachineWriteDisposition,
    SourceAbiParameterSpec, SourceFunctionInterface, SourceFunctionReturn, SourceMachineRoles,
    SourceStackAllocationContract, SourceStackGrowth, SsaArtifact,
};
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use crate::symbol::SymbolTable;

fn source_owned(ops: impl IntoIterator<Item = R2ILOp>) -> SourceOwnedFunctionFacts {
    let mut block = R2ILBlock::new(0x1000, 4);
    for op in ops {
        block.push(op);
    }
    source_owned_blocks(&[block])
}

fn source_owned_blocks(blocks: &[R2ILBlock]) -> SourceOwnedFunctionFacts {
    source_owned_blocks_with_stack_slots(blocks, Vec::new(), None)
}

fn source_owned_blocks_with_stack_slots(
    blocks: &[R2ILBlock],
    stack_slots: Vec<r2ssa::SourceStackSlotSpec>,
    stack_allocation: Option<SourceStackAllocationContract>,
) -> SourceOwnedFunctionFacts {
    let mut arch = ArchSpec::new("x86-64");
    arch.add_space(AddressSpace::ram(8));
    arch.add_register(RegisterDef::new("RAX", 0, 8));
    arch.add_register(RegisterDef::new("AH", 1, 1));
    arch.add_register(RegisterDef::new("RBP", 0x20, 8));
    arch.add_register(RegisterDef::new("RSP", 0x28, 8));
    arch.add_register(RegisterDef::new("RIP", 0x30, 8));
    arch.add_register(RegisterDef::new("RDI", 0x38, 8));
    arch.add_register(RegisterDef::new("EDI", 0x38, 4));
    arch.add_register(RegisterDef::new("CF", 0x40, 1));
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
                offset: 0x20,
                size: 8,
            },
            disposition: RegisterProjectionDisposition::Bound {
                carrier: RegisterStorage {
                    offset: 0x20,
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
        RegisterProjection {
            written: RegisterStorage {
                offset: 0x40,
                size: 1,
            },
            disposition: RegisterProjectionDisposition::Bound {
                carrier: RegisterStorage {
                    offset: 0x40,
                    size: 1,
                },
                slice: RegisterBitSlice {
                    lsb_bit_offset: 0,
                    size_bits: 8,
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
        stack_slots,
    )
    .and_then(|interface| interface.with_return_address_storage(storage(0x30)))
    .and_then(|interface| interface.with_stack_pointer_storage(storage(0x28)))
    .and_then(|interface| interface.with_frame_pointer_storage(storage(0x20)))
    .expect("exact test source interface");
    let mut machine_roles = SourceMachineRoles::new(Some(storage(0x30)), Some(storage(0x28)))
        .expect("exact test machine roles");
    if let Some(contract) = stack_allocation {
        machine_roles = machine_roles
            .with_stack_allocation_contract(contract)
            .expect("exact test allocation contract");
    }
    let source = Arc::new(
        SsaArtifact::for_decompile_with_interfaces_and_machine_roles(
            blocks,
            Some(&arch),
            Some(interface),
            machine_roles,
            Vec::new(),
        )
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

/// The projection the component builders now take, built here once per test.
///
/// Production shares one projection across the plan and its seal, because
/// deriving it again is the same answer at a cost rather than a second
/// opinion. A test that builds its own is exercising the same code path.
fn test_projection(source_owned: &SourceOwnedFunctionFacts) -> r2ssa::MachineProjection {
    r2ssa::MachineProjection::from_artifact(source_owned.source())
        .expect("machine projection for the fixture")
}

#[test]
fn shadow_plan_groups_spans_and_inlines_only_upstream_literals() {
    let first = Varnode::unique(0x10, 8);
    let source_owned = source_owned([
        R2ILOp::Copy {
            dst: first.clone(),
            src: Varnode::register(0, 8),
        },
        // Each version is read twice, and the span is seeded from a register.
        // A value with a single reader is folded into that reader and gets no
        // object; so does a value that reads nothing but literals, at every
        // reader it has. Either way a span made of them has nothing to group
        // and this test would have no subject.
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2010, 8),
            val: Varnode::unique(0x10, 8),
        },
        R2ILOp::IntAdd {
            dst: first,
            a: Varnode::unique(0x10, 8),
            b: Varnode::constant(1, 8),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
            val: Varnode::unique(0x10, 8),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2018, 8),
            val: Varnode::unique(0x10, 8),
        },
    ]);
    let source = source_owned.source();
    let plan = BindingPlan::build_shadow(&source_owned).expect("sealed shadow plan");
    // The two versions the span is made of. The register the chain is seeded
    // from is also a non-constant value, and it is not one of them: it has no
    // defining instruction, so it is not a version of anything this function
    // wrote.
    let nonconstants = source
        .graph()
        .values
        .iter()
        .filter(|value| value.var.constant_bits().is_none())
        .filter(|value| source.graph().def_inst(value.id).is_some())
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
fn unread_defined_value_is_elided_before_it_can_become_a_binding() {
    let source_owned = source_owned([
        R2ILOp::IntCarry {
            dst: Varnode::register(0x40, 1),
            a: Varnode::register(0x38, 8),
            b: Varnode::constant(1, 8),
        },
        R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        },
    ]);
    let source = source_owned.source();
    let graph = source.graph();
    let dead = graph
        .values
        .iter()
        .find(|value| {
            value.canonical_storage.is_some_and(|storage| {
                storage.space == CanonicalStorageSpace::Register
                    && storage.offset == 0x40
                    && storage.size == 1
            }) && graph.def_inst(value.id).is_some()
        })
        .expect("defined CF value")
        .id;
    assert!(graph.use_sites(dead).is_empty());
    assert!(rules::unread_defined_values(source, &test_projection(&source_owned)).contains(&dead));

    let plan = BindingPlan::build_shadow(&source_owned).expect("dead-value-aware plan");
    assert!(matches!(
        plan.disposition(dead),
        Some(ValueDisposition::Elided {
            reason: r2ssa::ledger::ElisionReason::DeadUnusedTemporary,
            proof,
        }) if proof.authority == *source.authority() && proof.value == dead
    ));
    assert!(
        binding_components(&source_owned, &test_projection(&source_owned))
            .expect("construction components")
            .iter()
            .all(|component| !component.members.contains(&dead))
    );
    assert!(
        seal_binding_components(&source_owned, &test_projection(&source_owned))
            .expect("independent components")
            .iter()
            .all(|component| !component.members.contains(&dead))
    );
    assert_eq!(
        build_upstream_shadow_oracle(&source_owned, &test_projection(&source_owned))
            .expect("upstream oracle")
            .value_disposition(dead),
        Some(UpstreamValueDisposition::Elided(
            r2ssa::ledger::ElisionReason::DeadUnusedTemporary
        ))
    );
    assert!(plan.validate_seal(&source_owned).is_ok());
}

#[test]
fn exact_source_return_address_fact_alone_authorizes_control_target_elision() {
    let source_owned = source_owned([
        R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(7, 8),
        },
        R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        },
    ]);
    let source = source_owned.source();
    let boundary = source
        .facts()
        .boundaries
        .returns
        .values()
        .next()
        .expect("return boundary");
    let return_control = boundary
        .return_address
        .expect("exact source return-address fact")
        .value;
    let plan = BindingPlan::build_shadow(&source_owned).expect("return-control-aware plan");

    assert!(matches!(
        plan.disposition(return_control),
        Some(ValueDisposition::Elided {
            reason: r2ssa::ledger::ElisionReason::ReturnControl,
            proof,
        }) if proof.authority == *source.authority() && proof.value == return_control
    ));
    assert!(
        binding_components(&source_owned, &test_projection(&source_owned))
            .expect("construction components")
            .iter()
            .all(|component| !component.members.contains(&return_control))
    );
    assert!(
        seal_binding_components(&source_owned, &test_projection(&source_owned))
            .expect("independent components")
            .iter()
            .all(|component| !component.members.contains(&return_control))
    );
    assert_eq!(
        build_upstream_shadow_oracle(&source_owned, &test_projection(&source_owned))
            .expect("upstream oracle")
            .value_disposition(return_control),
        Some(UpstreamValueDisposition::Elided(
            r2ssa::ledger::ElisionReason::ReturnControl
        ))
    );

    let semantic_return_certificate = source
        .facts()
        .certificates
        .returns_by_inst
        .values()
        .next()
        .and_then(|index| source.facts().certificates.returns.get(*index))
        .expect("semantic return certificate");
    let semantic_return = semantic_return_certificate.value;
    assert!(source.graph().use_sites(semantic_return).is_empty());
    assert!(certified_boundary_read(
        source,
        semantic_return,
        semantic_return_certificate.at
    ));
    assert!(
        !rules::unread_defined_values(source, &test_projection(&source_owned))
            .contains(&semantic_return)
    );
    let mut forged = plan;
    forged.dispositions[semantic_return.0 as usize] = ValueDisposition::Elided {
        reason: r2ssa::ledger::ElisionReason::ReturnControl,
        proof: ValueElisionProof {
            authority: source.authority().clone(),
            value: semantic_return,
        },
    };
    assert_eq!(
        forged.validate_seal(&source_owned),
        Err(BindingPlanBuildError::Seal(
            BindingPlanSourceMismatch::InvalidElisionProof {
                value: semantic_return
            }
        ))
    );
}

#[test]
fn direct_cfg_target_is_elided_only_when_every_use_is_control_topology() {
    let target = Varnode::constant(0x1020, 8);
    let mut entry = R2ILBlock::new(0x1000, 0x10);
    entry.push(R2ILOp::CBranch {
        target: target.clone(),
        cond: Varnode::register(0x38, 8),
    });
    let mut fallthrough = R2ILBlock::new(0x1010, 0x10);
    fallthrough.push(R2ILOp::Branch {
        target: Varnode::constant(0x1030, 8),
    });
    let mut taken = R2ILBlock::new(0x1020, 0x10);
    taken.push(R2ILOp::Branch {
        target: Varnode::constant(0x1030, 8),
    });
    let mut exit = R2ILBlock::new(0x1030, 4);
    exit.push(R2ILOp::Return {
        target: Varnode::register(0x30, 8),
    });
    let source_owned = source_owned_blocks(&[entry, fallthrough, taken, exit]);
    let source = source_owned.source();
    let control_site = certified_direct_control_target_sites(source)
        .into_iter()
        .find(|site| {
            source.graph().inst(site.inst).is_some_and(|inst| {
                inst.inputs.first().is_some_and(|value| {
                    source
                        .graph()
                        .value(*value)
                        .is_some_and(|value| value.var.constant_bits() == Some(target.offset))
                })
            })
        })
        .expect("exact conditional target site");
    let target_value = source
        .graph()
        .inst(control_site.inst)
        .expect("target op")
        .inputs[0];
    let plan = BindingPlan::build_shadow(&source_owned).expect("direct-control-aware plan");

    assert!(matches!(
        plan.disposition(target_value),
        Some(ValueDisposition::Elided {
            reason: r2ssa::ledger::ElisionReason::DirectControlTarget,
            proof,
        }) if proof.authority == *source.authority() && proof.value == target_value
    ));
    assert_eq!(
        build_upstream_shadow_oracle(&source_owned, &test_projection(&source_owned))
            .expect("independent direct-control oracle")
            .value_disposition(target_value),
        Some(UpstreamValueDisposition::Elided(
            r2ssa::ledger::ElisionReason::DirectControlTarget
        ))
    );

    let mut mixed_entry = R2ILBlock::new(0x1000, 0x10);
    // The literal is added to a register, not to another literal. Adding two
    // constants folds to their sum before the plan is built, and the literal
    // then has only its control use left, which is not the mixed use this
    // fixture exists to describe.
    mixed_entry.push(R2ILOp::IntAdd {
        dst: Varnode::unique(0x80, 8),
        a: target.clone(),
        b: Varnode::register(0x38, 8),
    });
    mixed_entry.push(R2ILOp::CBranch {
        target,
        cond: Varnode::register(0x38, 8),
    });
    let mixed = source_owned_blocks(&[
        mixed_entry,
        R2ILBlock::new(0x1010, 0x10),
        R2ILBlock::new(0x1020, 0x10),
    ]);
    let mixed_value = mixed
        .source()
        .graph()
        .values
        .iter()
        .find(|value| value.var.constant_bits() == Some(0x1020))
        .expect("shared target literal")
        .id;
    assert!(
        mixed.source().graph().use_sites(mixed_value).len() > 1,
        "fixture must share the literal between control and ordinary use"
    );
    assert!(matches!(
        BindingPlan::build_shadow(&mixed)
            .expect("mixed-use plan")
            .disposition(mixed_value),
        Some(ValueDisposition::Inline { .. })
    ));
}

#[test]
fn unobserved_merge_is_elided_by_its_source_certificate_not_bound() {
    let mut entry = R2ILBlock::new(0x1000, 4);
    entry.push(R2ILOp::CBranch {
        cond: Varnode::constant(1, 1),
        target: Varnode::constant(0x1008, 8),
    });
    let mut left = R2ILBlock::new(0x1004, 4);
    left.push(R2ILOp::Copy {
        dst: Varnode::register(0, 8),
        src: Varnode::constant(1, 8),
    });
    left.push(R2ILOp::Copy {
        dst: Varnode::register(0x38, 8),
        src: Varnode::constant(11, 8),
    });
    left.push(R2ILOp::Branch {
        target: Varnode::constant(0x100c, 8),
    });
    let mut right = R2ILBlock::new(0x1008, 4);
    right.push(R2ILOp::Copy {
        dst: Varnode::register(0, 8),
        src: Varnode::constant(2, 8),
    });
    right.push(R2ILOp::Copy {
        dst: Varnode::register(0x38, 8),
        src: Varnode::constant(12, 8),
    });
    right.push(R2ILOp::Branch {
        target: Varnode::constant(0x100c, 8),
    });
    let mut join = R2ILBlock::new(0x100c, 4);
    join.push(R2ILOp::Return {
        target: Varnode::register(0x30, 8),
    });

    let source_owned = source_owned_blocks(&[entry, left, right, join]);
    let source = source_owned.source();
    let graph = source.graph();
    let dead = source
        .unobserved_merges()
        .iter()
        .find(|value| {
            graph.value(*value).is_some_and(|value| {
                value.canonical_storage.is_some_and(|storage| {
                    storage.space == CanonicalStorageSpace::Register
                        && storage.offset == 0x38
                        && storage.size == 8
                })
            })
        })
        .expect("unused RDI merge has an upstream dead-phi certificate");
    let live = graph
        .insts
        .iter()
        .filter(|inst| matches!(inst.payload, r2ssa::InstPayload::Phi { .. }))
        .filter_map(|inst| inst.output)
        .find(|value| {
            graph.value(*value).is_some_and(|value| {
                value.canonical_storage.is_some_and(|storage| {
                    storage.space == CanonicalStorageSpace::Register
                        && storage.offset == 0
                        && storage.size == 8
                })
            })
        })
        .expect("returned RAX merge");
    assert!(!source.unobserved_merges().contains(live));
    let dead_support = graph
        .def_inst(dead)
        .and_then(|inst| graph.inst(inst))
        .and_then(|inst| inst.inputs.first())
        .copied()
        .expect("dead merge has an entry support value");
    assert!(source.unobserved_values().contains(&dead_support));

    let plan = BindingPlan::build_shadow(&source_owned).expect("dead-merge-aware plan");
    assert!(matches!(
        plan.disposition(dead),
        Some(ValueDisposition::Elided {
            reason: r2ssa::ledger::ElisionReason::UnobservedMerge,
            proof,
        }) if proof.authority == *source.authority() && proof.value == dead
    ));
    assert!(matches!(
        plan.disposition(live),
        Some(ValueDisposition::Bound { .. })
    ));
    assert!(matches!(
        plan.disposition(dead_support),
        Some(ValueDisposition::Elided {
            reason: r2ssa::ledger::ElisionReason::UnobservedValue,
            proof,
        }) if proof.authority == *source.authority() && proof.value == dead_support
    ));
    assert!(
        binding_components(&source_owned, &test_projection(&source_owned))
            .expect("construction components")
            .iter()
            .all(|component| !component.members.contains(&dead))
    );
    assert!(
        seal_binding_components(&source_owned, &test_projection(&source_owned))
            .expect("independent components")
            .iter()
            .all(|component| !component.members.contains(&dead))
    );
    let projection = test_projection(&source_owned);
    let oracle = build_upstream_shadow_oracle(&source_owned, &projection).expect("upstream oracle");
    assert_eq!(
        oracle.value_disposition(dead),
        Some(UpstreamValueDisposition::Elided(
            r2ssa::ledger::ElisionReason::UnobservedMerge
        ))
    );

    let mut forged = plan;
    forged.dispositions[dead.0 as usize] = ValueDisposition::Elided {
        reason: r2ssa::ledger::ElisionReason::UnobservedMerge,
        proof: ValueElisionProof {
            authority: source.authority().clone(),
            value: live,
        },
    };
    assert_eq!(
        forged.validate_seal(&source_owned),
        Err(BindingPlanBuildError::Seal(
            BindingPlanSourceMismatch::InvalidElisionProof { value: dead }
        ))
    );
}

#[test]
fn use_and_write_dispositions_delegate_to_the_validated_projection() {
    let source_owned = source_owned([R2ILOp::Copy {
        dst: Varnode::unique(0x10, 8),
        src: Varnode::constant(7, 8),
    }]);
    let source = source_owned.source();
    let plan = Rc::new(BindingPlan::build_shadow(&source_owned).expect("sealed shadow plan"));
    let resolution = BindingNameResolution::build(
        &source_owned,
        Rc::clone(&plan),
        Rc::new(RefCell::new(SymbolTable::new())),
    )
    .expect("exact projection resolution");
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
            assert!(std::ptr::eq(
                resolution.require_use(site).expect("required exact use"),
                plan.machine_projection()
                    .use_disposition(site)
                    .expect("projection use"),
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
            assert!(std::ptr::eq(
                resolution
                    .require_write(inst.id)
                    .expect("required exact write"),
                plan.machine_projection()
                    .write_disposition(inst.id)
                    .expect("projection write"),
            ));
        }
    }
    let missing_site = UseSite {
        inst: r2ssa::InstId(u32::MAX),
        input_idx: 0,
    };
    assert_eq!(
        resolution.require_use(missing_site),
        Err(RenderedIdentityRefusal::MissingUseDisposition { site: missing_site })
    );
    assert_eq!(
        resolution.require_write(r2ssa::InstId(u32::MAX)),
        Err(RenderedIdentityRefusal::MissingWriteDisposition {
            inst: r2ssa::InstId(u32::MAX)
        })
    );
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
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
            val: Varnode::unique(0x10, 1),
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
        let Some(ValueDisposition::Bound { binding }) = plan.disposition(value) else {
            continue;
        };
        let binding = *binding;
        carrier_binding.get_or_insert(binding);
        assert_eq!(
            plan.binding(binding).map(Binding::declaration_type),
            Some(&CType::u64())
        );
    }
    assert!(plan.validate_seal(&source_owned).is_ok());

    let carrier_binding = carrier_binding.expect("at least one observed AH value has a binding");
    for forged_width in [32, 128] {
        let mut forged = plan.clone();
        forged.bindings[carrier_binding.index()].declaration_type = CType::Int {
            bits: forged_width,
            signedness: r2types::Signedness::Unsigned,
        };
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
    let plan = Rc::new(BindingPlan::build_shadow(&source_owned).expect("partial shadow plan"));
    let resolution = BindingNameResolution::build(
        &source_owned,
        Rc::clone(&plan),
        Rc::new(RefCell::new(SymbolTable::new())),
    )
    .expect("refused projection resolution");
    let constant = source
        .graph()
        .values
        .iter()
        .find(|value| value.var.constant_bits() == Some(9))
        .expect("constant graph value");
    // The constant is projected, and only its *reader* is refused. Whether a
    // value is a constant is a fact about the value; it does not depend on
    // whether the operation reading it could be lowered. This used to refuse
    // the constant as well, which reported a missing literal projection where
    // the truth was an operation with no model -- on `/bin/ls`, `brk 0xc471`
    // refusing on its own immediate.
    assert!(matches!(
        plan.disposition(constant.id),
        Some(ValueDisposition::Inline { .. })
    ));
    let use_site = source.graph().uses_of[constant.id.0 as usize][0];
    assert!(matches!(
        plan.use_disposition(use_site),
        Some(MachineUseDisposition::Refused(_))
    ));
    let use_reason = match plan.machine_projection().use_disposition(use_site) {
        Some(MachineUseDisposition::Refused(reason)) => *reason,
        other => panic!("expected canonical use refusal, got {other:?}"),
    };
    assert_eq!(
        resolution.require_use(use_site),
        Err(RenderedIdentityRefusal::MachineUse {
            site: use_site,
            reason: use_reason,
        })
    );

    let producer = source
        .graph()
        .insts
        .iter()
        .find(|inst| {
            matches!(
                &inst.payload,
                r2ssa::InstPayload::Op(r2ssa::SSAOp::CallOther { .. })
            )
        })
        .map(|inst| inst.id)
        .expect("opaque operation instruction");
    let write_reason = match plan.machine_projection().write_disposition(producer) {
        Some(MachineWriteDisposition::Refused(reason)) => *reason,
        other => panic!("expected canonical write refusal, got {other:?}"),
    };
    assert_eq!(
        resolution.require_write(producer),
        Err(RenderedIdentityRefusal::MachineWrite {
            inst: producer,
            reason: write_reason,
        })
    );
}

#[test]
fn unsupported_c_scalar_width_is_a_typed_value_refusal() {
    let source_owned = source_owned([
        R2ILOp::Copy {
            dst: Varnode::unique(0x10, 3),
            src: Varnode::register(0, 3),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
            val: Varnode::unique(0x10, 3),
        },
        // Read twice and taken from a register, so the value needs a
        // declaration of its own. A value read once is folded into its reader,
        // and one that reads nothing but literals is spelled at every reader;
        // either way it is never declared, and an undeclarable width is only a
        // refusal for something being declared.
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2008, 8),
            val: Varnode::unique(0x10, 3),
        },
    ]);
    let output = source_owned
        .source()
        .graph()
        .insts
        .iter()
        .find_map(|inst| inst.output)
        .expect("copy output");
    let plan = BindingPlan::build_shadow(&source_owned).expect("typed refusal plan");

    assert!(matches!(
        plan.disposition(output),
        Some(ValueDisposition::Refused {
            reason: ValueRefusal::UnsupportedDeclarationWidth {
                value,
                width_bits: 24,
            },
        }) if *value == output
    ));
    assert!(plan.validate_seal(&source_owned).is_ok());
}

#[test]
fn seal_rejects_foreign_authority_and_inverse_membership_drift() {
    let ops = || {
        [
            R2ILOp::Copy {
                dst: Varnode::unique(0x10, 8),
                src: Varnode::register(0, 8),
            },
            R2ILOp::Copy {
                dst: Varnode::unique(0x20, 4),
                src: Varnode::register(8, 4),
            },
            R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::constant(0x2000, 8),
                val: Varnode::unique(0x10, 8),
            },
            R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::constant(0x2008, 8),
                val: Varnode::unique(0x20, 4),
            },
            // Second readers, and the values come from registers. A value read
            // once is folded into its reader, and one that reads nothing but
            // literals is spelled at every reader; either way it is bound to
            // nothing, and this test needs two independent storage bindings to
            // move a value between.
            R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::constant(0x2010, 8),
                val: Varnode::unique(0x10, 8),
            },
            R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::constant(0x2018, 8),
                val: Varnode::unique(0x20, 4),
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
    // Both spans start from a register: a value reading nothing but literals
    // is spelled at each reader rather than bound, and this test needs
    // bindings whose certificate sources it can resolve.
    let source_owned = source_owned([
        R2ILOp::Copy {
            dst: first.clone(),
            src: Varnode::register(0, 8),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2020, 8),
            val: Varnode::unique(0x10, 8),
        },
        R2ILOp::IntAdd {
            dst: first,
            a: Varnode::unique(0x10, 8),
            b: Varnode::constant(1, 8),
        },
        R2ILOp::Copy {
            dst: second.clone(),
            src: Varnode::register(8, 8),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2028, 8),
            val: Varnode::unique(0x20, 8),
        },
        R2ILOp::IntAdd {
            dst: second,
            a: Varnode::unique(0x20, 8),
            b: Varnode::constant(1, 8),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
            val: Varnode::unique(0x10, 8),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2008, 8),
            val: Varnode::unique(0x20, 8),
        },
        // Second readers, so each span holds an object rather than being
        // folded away into its one reader.
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2010, 8),
            val: Varnode::unique(0x10, 8),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2018, 8),
            val: Varnode::unique(0x20, 8),
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
        // A second reader for the middle version. With one reader it is
        // folded into that reader and leaves the span, and the component this
        // test closes transitively would have two members instead of three.
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2010, 8),
            val: Varnode::register(0x38, 8),
        },
        R2ILOp::IntAdd {
            dst: Varnode::register(0x38, 8),
            a: Varnode::register(0x38, 8),
            b: Varnode::constant(2, 8),
        },
        R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::register(0x38, 8),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2008, 8),
            val: Varnode::register(0x38, 8),
        },
        // And a second rendered reader for the last version. The copy above
        // is never read, so it is unobserved and its read does not count:
        // the single-reader rule counts the readers that render, and with
        // one store the last version would fold into it and leave the span.
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x2018, 8),
            val: Varnode::register(0x38, 8),
        },
    ]);
    let parameter = BindingCertificateSource::CertifiedEntity(SemanticId::Parameter(0));
    let constructed = binding_components(&source_owned, &test_projection(&source_owned))
        .expect("union-find components");
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

    let sealed = seal_binding_components(&source_owned, &test_projection(&source_owned))
        .expect("independent BFS components");
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

#[test]
fn certified_stack_objects_get_bindings_without_invented_value_membership() {
    let address = Varnode::unique(0x80, 8);
    let mut block = R2ILBlock::new(0x1000, 4);
    for op in [
        R2ILOp::IntSub {
            dst: address.clone(),
            a: Varnode::register(0x28, 8),
            b: Varnode::constant(8, 8),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: address.clone(),
            val: Varnode::constant(7, 8),
        },
        R2ILOp::Load {
            dst: Varnode::unique(0x88, 8),
            space: SpaceId::Ram,
            addr: address,
        },
    ] {
        block.push(op);
    }
    let source_owned = source_owned_blocks_with_stack_slots(
        &[block],
        vec![r2ssa::SourceStackSlotSpec::new_local(
            r2ssa::StackAddressBase::StackPointer,
            CanonicalStorageId {
                space: CanonicalStorageSpace::Register,
                offset: 0x28,
                size: 8,
            },
            -8,
            8,
        )],
        None,
    );
    let stack_slots = source_owned
        .report()
        .render()
        .expect("render facts")
        .stack_slots()
        .collect::<Vec<_>>();
    assert!(
        !stack_slots.is_empty(),
        "source must certify a stack object"
    );

    let plan = BindingPlan::build_shadow(&source_owned).expect("stack-aware plan");
    let resolution = BindingNameResolution::build(
        &source_owned,
        Rc::new(plan.clone()),
        Rc::new(RefCell::new(SymbolTable::new())),
    )
    .expect("stack resolution");
    let mut bound_stack_objects = 0;
    for (object, _, _, size) in stack_slots {
        match (size, plan.stack_object_disposition(object)) {
            (Some(size), Some(StackObjectDisposition::Bound { binding })) if size > 0 => {
                bound_stack_objects += 1;
                assert_eq!(
                    plan.binding(binding).map(Binding::declaration_type),
                    Some(&CType::Int {
                        bits: size * 8,
                        signedness: r2types::Signedness::Unsigned
                    })
                );
                assert!(matches!(
                    plan.binding(binding)
                        .map(|binding| binding.certificate.sources.as_ref()),
                    Some([BindingCertificateSource::CertifiedEntity(
                        SemanticId::StackSlot(certified)
                    )]) if *certified == object
                ));
                assert_eq!(
                    resolution.require_stack(object),
                    Ok(PlannedStackSymbol::Bound(
                        resolution
                            .symbol_for_binding(binding)
                            .expect("stack binding symbol")
                    ))
                );
            }
            (
                None,
                Some(StackObjectDisposition::Refused {
                    reason: StackObjectRefusal::MissingWidth { object: refused },
                }),
            ) if refused == object => {
                assert_eq!(
                    resolution.require_stack(object),
                    Err(RenderedIdentityRefusal::StackObject {
                        object,
                        reason: StackObjectRefusal::MissingWidth { object }
                    })
                );
            }
            (
                None,
                Some(StackObjectDisposition::Refused {
                    reason: StackObjectRefusal::MissingSourceIdentity { object: refused },
                }),
            ) if refused == object => {
                assert_eq!(
                    resolution.require_stack(object),
                    Err(RenderedIdentityRefusal::StackObject {
                        object,
                        reason: StackObjectRefusal::MissingSourceIdentity { object }
                    })
                );
            }
            other => panic!("unexpected stack object disposition: {other:?}"),
        }
    }
    assert_eq!(
        bound_stack_objects, 1,
        "only the exact source-declared stack slot may become a C binding"
    );
    assert_eq!(
        resolution.require_stack(r2ssa::ObjectId(u32::MAX)),
        Err(RenderedIdentityRefusal::MissingStackDisposition {
            object: r2ssa::ObjectId(u32::MAX)
        })
    );
    assert!(plan.validate_seal(&source_owned).is_ok());
}

#[test]
fn exact_callee_allocation_binds_anonymous_stack_object_without_source_identity() {
    let address = Varnode::unique(0x80, 8);
    let loaded = Varnode::unique(0x88, 8);
    let mut block = R2ILBlock::new(0x1000, 4);
    for op in [
        R2ILOp::IntSub {
            dst: Varnode::register(0x28, 8),
            a: Varnode::register(0x28, 8),
            b: Varnode::constant(8, 8),
        },
        R2ILOp::Copy {
            dst: address.clone(),
            src: Varnode::register(0x28, 8),
        },
        R2ILOp::Store {
            space: SpaceId::Ram,
            addr: address.clone(),
            val: Varnode::constant(7, 8),
        },
        R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: address,
        },
        R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: loaded,
        },
        R2ILOp::Return {
            target: Varnode::register(0x30, 8),
        },
    ] {
        block.push(op);
    }
    let source_owned = source_owned_blocks_with_stack_slots(
        &[block],
        Vec::new(),
        Some(SourceStackAllocationContract::new(
            SourceStackGrowth::LowerAddresses,
        )),
    );
    let allocation = source_owned
        .source()
        .certificates()
        .stack_slots
        .values()
        .find_map(|slot| slot.callee_allocation.as_ref())
        .expect("upstream allocation certificate");
    let object = allocation.object;

    let plan = BindingPlan::build_shadow(&source_owned).expect("allocation-aware plan");
    let Some(StackObjectDisposition::Bound { binding }) = plan.stack_object_disposition(object)
    else {
        panic!("certified anonymous object was not bound");
    };
    assert_eq!(
        plan.binding(binding).map(Binding::declaration_type),
        Some(&CType::u64())
    );
    assert!(matches!(
        plan.binding(binding)
            .map(|binding| binding.certificate.sources.as_ref()),
        Some([BindingCertificateSource::CertifiedEntity(
            SemanticId::StackSlot(certified)
        )]) if *certified == object
    ));
    assert!(plan.validate_seal(&source_owned).is_ok());
}

#[test]
fn exact_frame_round_trip_is_elided_without_a_program_binding() {
    let saved = Varnode::unique(0x90, 8);
    let loaded = Varnode::unique(0x98, 8);
    let sp = Varnode::register(0x28, 8);
    let fp = Varnode::register(0x20, 8);
    let source_owned = source_owned_blocks_with_stack_slots(
        &[R2ILBlock {
            addr: 0x1000,
            size: 4,
            ops: vec![
                R2ILOp::Copy {
                    dst: saved.clone(),
                    src: fp.clone(),
                },
                R2ILOp::IntSub {
                    dst: sp.clone(),
                    a: sp.clone(),
                    b: Varnode::constant(8, 8),
                },
                R2ILOp::Store {
                    space: SpaceId::Ram,
                    addr: sp.clone(),
                    val: saved,
                },
                R2ILOp::Copy {
                    dst: fp.clone(),
                    src: sp.clone(),
                },
                R2ILOp::Load {
                    dst: loaded.clone(),
                    space: SpaceId::Ram,
                    addr: sp.clone(),
                },
                R2ILOp::IntAdd {
                    dst: sp.clone(),
                    a: sp,
                    b: Varnode::constant(8, 8),
                },
                R2ILOp::Copy {
                    dst: fp,
                    src: loaded,
                },
                R2ILOp::Return {
                    target: Varnode::register(0x30, 8),
                },
            ],
            switch_info: None,
            op_metadata: Default::default(),
        }],
        Vec::new(),
        Some(SourceStackAllocationContract::new(
            SourceStackGrowth::LowerAddresses,
        )),
    );
    let certificate = source_owned
        .source()
        .certificates()
        .stack_frame_round_trips
        .values()
        .next()
        .expect("upstream frame round-trip certificate");
    let object = certificate.object;
    let plan = Rc::new(BindingPlan::build_shadow(&source_owned).expect("frame-aware plan"));
    assert_eq!(
        plan.stack_object_disposition(object),
        Some(StackObjectDisposition::Elided {
            reason: r2ssa::ledger::ElisionReason::StackFrame,
        })
    );
    assert!(certificate.values.iter().all(|value| {
        matches!(
            plan.disposition(*value),
            Some(ValueDisposition::Elided {
                reason: r2ssa::ledger::ElisionReason::StackFrame,
                ..
            })
        )
    }));
    assert!(
        source_owned
            .source()
            .certificates()
            .stack_geometry
            .values
            .iter()
            .all(|value| matches!(
                plan.disposition(*value),
                Some(ValueDisposition::Elided {
                    reason: r2ssa::ledger::ElisionReason::DeadStackBase,
                    ..
                })
            ))
    );
    let resolution = BindingNameResolution::build(
        &source_owned,
        Rc::clone(&plan),
        Rc::new(RefCell::new(SymbolTable::new())),
    )
    .expect("frame-aware name resolution");
    assert_eq!(
        resolution.require_stack(object),
        Err(RenderedIdentityRefusal::StackObjectElided {
            object,
            reason: r2ssa::ledger::ElisionReason::StackFrame,
        })
    );
    assert!(plan.validate_seal(&source_owned).is_ok());
}
