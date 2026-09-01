use std::sync::Arc;

use r2il::{
    AddressSpace, ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef, RegisterProjection,
    RegisterProjectionDisposition, RegisterStorage, Varnode,
};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, SourceFunctionInterface, SourceFunctionReturn,
    SsaArtifact,
};

use super::*;

fn source_owned(ops: impl IntoIterator<Item = R2ILOp>) -> SourceOwnedFunctionFacts {
    let mut block = R2ILBlock::new(0x1000, 4);
    for op in ops {
        block.push(op);
    }
    let mut arch = ArchSpec::new("x86-64");
    arch.add_space(AddressSpace::ram(8));
    arch.add_register(RegisterDef::new("RAX", 0, 8));
    arch.add_register(RegisterDef::new("RSP", 0x28, 8));
    arch.add_register(RegisterDef::new("RIP", 0x30, 8));
    arch.register_projections = [(0, 8, 0, 64), (0x28, 8, 0, 64), (0x30, 8, 0, 64)]
        .into_iter()
        .map(
            |(offset, size, lsb_bit_offset, size_bits)| RegisterProjection {
                written: RegisterStorage { offset, size },
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: RegisterStorage { offset, size },
                    slice: RegisterBitSlice {
                        lsb_bit_offset,
                        size_bits,
                    },
                },
            },
        )
        .collect();
    let storage = |offset| CanonicalStorageId {
        space: CanonicalStorageSpace::Register,
        offset,
        size: 8,
    };
    let interface = SourceFunctionInterface::new_exact(
        b"shadow-report-test-interface".to_vec(),
        "sysv64",
        std::iter::empty(),
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
            reason: "shadow report test".to_string(),
            fallback_comment: None,
        })
        .expect("source-owned finalization")
}

fn matching_value_cells(
    source: &SourceOwnedFunctionFacts,
    plan: &BindingPlan,
    class_bias: u32,
) -> Box<[LegacyValueCell]> {
    source
        .source()
        .graph()
        .values
        .iter()
        .map(|value| {
            let observation = match plan.disposition(value.id).expect("dense plan") {
                ValueDisposition::Bound { binding } => LegacyValueObservation::Bound {
                    binding: LegacyBindingId(binding.index() as u32 + class_bias),
                },
                ValueDisposition::Inline { .. } => LegacyValueObservation::InlineConstant,
                ValueDisposition::Elided { reason, .. } => LegacyValueObservation::Elided(*reason),
                ValueDisposition::Refused { reason } => LegacyValueObservation::Refused(*reason),
            };
            LegacyValueCell {
                value: value.id,
                observation,
            }
        })
        .collect::<Vec<_>>()
        .into_boxed_slice()
}

fn matching_snapshot(
    source: &SourceOwnedFunctionFacts,
    plan: &BindingPlan,
    class_bias: u32,
) -> LegacyAnalysisSnapshot {
    let mut snapshot = LegacyAnalysisSnapshot::with_absent_machine_observations(
        source,
        matching_value_cells(source, plan, class_bias),
    );
    for row in &mut snapshot.uses {
        for cell in row {
            cell.observation = match plan.use_disposition(cell.site).expect("dense use") {
                MachineUseDisposition::Exact(slice) => LegacyUseObservation::Exact(*slice),
                MachineUseDisposition::MemoryAddress(address) => {
                    LegacyUseObservation::MemoryAddress(*address)
                }
                MachineUseDisposition::Refused(reason) => LegacyUseObservation::Refused(*reason),
            };
        }
    }
    for cell in snapshot.writes.iter_mut().flatten() {
        cell.observation = match plan.write_disposition(cell.inst).expect("dense write") {
            MachineWriteDisposition::Exact(write) => LegacyWriteObservation::Exact(*write),
            MachineWriteDisposition::Refused(reason) => LegacyWriteObservation::Refused(*reason),
        };
    }
    snapshot
}

#[test]
fn classification_truth_table_includes_equal_and_different_both_wrong() {
    let correct = SideJudgment::Correct;
    let wrong = SideJudgment::Wrong(WrongReason::DispositionMismatch);
    assert_eq!(
        classify_sides(correct, correct, true),
        ShadowClassification::AgreeCorrect
    );
    assert_eq!(
        classify_sides(wrong, correct, false),
        ShadowClassification::OldWrong
    );
    assert_eq!(
        classify_sides(correct, wrong, false),
        ShadowClassification::ShadowWrong
    );
    assert_eq!(
        classify_sides(wrong, wrong, true),
        ShadowClassification::BothWrong(BothWrongRelation::Equal)
    );
    assert_eq!(
        classify_sides(wrong, wrong, false),
        ShadowClassification::BothWrong(BothWrongRelation::Different)
    );
}

#[test]
fn dense_domains_balance_and_detect_snapshot_and_report_corruption() {
    let source = source_owned([R2ILOp::Copy {
        dst: Varnode::unique(0x10, 8),
        src: Varnode::constant(7, 8),
    }]);
    let plan = BindingPlan::build_shadow(&source).expect("sealed plan");
    let snapshot = matching_snapshot(&source, &plan, 0);
    let report = ShadowReport::build(&plan, &source, &snapshot).expect("shadow report");
    let ledger = report.ledger(&source);
    assert!(ledger.equations_hold());
    assert!(ledger.passes_stage4());
    assert!(ledger.passes_quality());
    assert_eq!(ledger.values.total, source.source().graph().values.len());
    assert_eq!(
        ledger.uses.total,
        source
            .source()
            .graph()
            .insts
            .iter()
            .map(|inst| inst.inputs.len())
            .sum::<usize>()
    );
    assert_eq!(
        ledger.writes.total,
        source
            .source()
            .graph()
            .insts
            .iter()
            .filter(|inst| inst.output.is_some())
            .count()
    );

    let mut missing = snapshot.clone();
    missing.values = missing.values[..missing.values.len() - 1]
        .to_vec()
        .into_boxed_slice();
    assert!(matches!(
        ShadowReport::build(&plan, &source, &missing),
        Err(ShadowReportError::LegacyValueCount { .. })
    ));

    let mut missing_report = report.clone();
    missing_report.values = missing_report.values[..missing_report.values.len() - 1]
        .to_vec()
        .into_boxed_slice();
    let missing_ledger = missing_report.ledger(&source);
    assert_eq!(missing_ledger.values.total, ledger.values.total);
    assert_eq!(
        missing_ledger.values.observed + 1,
        missing_ledger.values.total
    );
    assert!(!missing_ledger.values.equations_hold());

    let mut corrupt = report;
    corrupt.values[0].key = ValueId(u32::MAX);
    assert!(matches!(
        corrupt.validate_against(&plan, &source, &snapshot),
        Err(ShadowReportError::ReportCellMismatch {
            field: ReportCellField::Key,
            ..
        })
    ));
}

#[test]
fn refusal_is_exact_and_legacy_absence_is_not_refusal() {
    let source = source_owned([R2ILOp::CallOther {
        output: Some(Varnode::unique(0x10, 8)),
        userop: 7,
        inputs: vec![Varnode::constant(9, 8)],
    }]);
    let plan = BindingPlan::build_shadow(&source).expect("partial sealed plan");
    let exact_snapshot = matching_snapshot(&source, &plan, 0);
    let exact = ShadowReport::build(&plan, &source, &exact_snapshot).expect("exact report");
    assert!(exact.ledger(&source).passes_stage4());
    assert!(!exact.ledger(&source).passes_quality());
    assert!(exact.ledger(&source).uses.refused > 0 || exact.ledger(&source).writes.refused > 0);

    let absent = LegacyAnalysisSnapshot::with_absent_machine_observations(
        &source,
        matching_value_cells(&source, &plan, 0),
    );
    let absent_report = ShadowReport::build(&plan, &source, &absent).expect("absent report");
    let refused_use = absent_report
        .uses
        .iter()
        .flatten()
        .find(|cell| cell.canonical_kind == CanonicalDispositionKind::Refused)
        .expect("canonical refused use");
    assert_eq!(refused_use.classification, ShadowClassification::OldWrong);
    assert_eq!(
        refused_use.old,
        SideJudgment::Wrong(WrongReason::LegacyAbsent)
    );
}

#[test]
fn contextual_memory_use_is_not_equal_to_an_integer_slice_observation() {
    let source = source_owned([R2ILOp::Store {
        space: r2il::SpaceId::Ram,
        addr: Varnode::register(0x28, 8),
        val: Varnode::constant(7, 8),
    }]);
    let plan = BindingPlan::build_shadow(&source).expect("sealed memory plan");
    let inst = source
        .source()
        .graph()
        .inst_id_for_op_site(0x1000, 0)
        .expect("store instruction");
    let address_site = UseSite { inst, input_idx: 0 };
    let value_site = UseSite { inst, input_idx: 1 };
    assert!(matches!(
        plan.use_disposition(address_site),
        Some(MachineUseDisposition::MemoryAddress(_))
    ));
    let wrong_slice = match plan.use_disposition(value_site) {
        Some(MachineUseDisposition::Exact(slice)) => *slice,
        other => panic!("store value must have an integer slice: {other:?}"),
    };

    let mut snapshot = matching_snapshot(&source, &plan, 0);
    snapshot.uses[inst.0 as usize][0].observation = LegacyUseObservation::Exact(wrong_slice);
    let report = ShadowReport::build(&plan, &source, &snapshot).expect("classified report");
    let address = &report.uses()[inst.0 as usize][0];
    assert_eq!(address.key(), address_site);
    assert_eq!(address.classification(), ShadowClassification::OldWrong);
    assert_eq!(
        address.old_judgment(),
        SideJudgment::Wrong(WrongReason::DispositionMismatch),
        "a contextual memory projection must never be reported as an exact bit slice"
    );
    assert_eq!(address.shadow_judgment(), SideJudgment::Correct);
}

#[test]
fn exact_source_authority_is_required() {
    let ops = || {
        [R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(7, 8),
        }]
    };
    let first = source_owned(ops());
    let foreign = source_owned(ops());
    let plan = BindingPlan::build_shadow(&first).expect("sealed first plan");
    let foreign_plan = BindingPlan::build_shadow(&foreign).expect("sealed foreign plan");
    let snapshot = matching_snapshot(&foreign, &foreign_plan, 0);
    assert_eq!(
        ShadowReport::build(&plan, &foreign, &snapshot),
        Err(ShadowReportError::SourceMismatch(
            BindingPlanSourceMismatch::Authority
        ))
    );
}

#[test]
fn legacy_snapshot_rejects_same_topology_from_foreign_authority() {
    let ops = || {
        [R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(7, 8),
        }]
    };
    let source = source_owned(ops());
    let foreign = source_owned(ops());
    let plan = BindingPlan::build_shadow(&source).expect("sealed source plan");
    let foreign_plan = BindingPlan::build_shadow(&foreign).expect("sealed foreign plan");
    let foreign_snapshot = matching_snapshot(&foreign, &foreign_plan, 0);
    assert_eq!(
        ShadowReport::build(&plan, &source, &foreign_snapshot),
        Err(ShadowReportError::LegacyAuthority)
    );
}

#[test]
fn independently_forged_candidate_is_classified_shadow_wrong() {
    let source = source_owned([
        R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(1, 8),
        },
        R2ILOp::Copy {
            dst: Varnode::unique(0x20, 8),
            src: Varnode::constant(2, 8),
        },
        R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: Varnode::constant(0x2000, 8),
            val: Varnode::unique(0x10, 8),
        },
        R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: Varnode::constant(0x2008, 8),
            val: Varnode::unique(0x20, 8),
        },
        // Second readers. A value read once is folded into its reader and is
        // bound to nothing, and this test needs two bindings to forge one
        // against the other.
        R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: Varnode::constant(0x2010, 8),
            val: Varnode::unique(0x10, 8),
        },
        R2ILOp::Store {
            space: r2il::SpaceId::Ram,
            addr: Varnode::constant(0x2018, 8),
            val: Varnode::unique(0x20, 8),
        },
    ]);
    let original = BindingPlan::build_shadow(&source).expect("sealed plan");
    let snapshot = matching_snapshot(&source, &original, 0);
    let bound = source
        .source()
        .graph()
        .values
        .iter()
        .filter_map(|value| match original.disposition(value.id) {
            Some(ValueDisposition::Bound { binding }) => Some((value.id, *binding)),
            _ => None,
        })
        .collect::<Vec<_>>();
    let (value, original_binding) = bound[0];
    let foreign_binding = bound
        .iter()
        .find_map(|(_, binding)| (*binding != original_binding).then_some(*binding))
        .expect("second binding component");

    let mut forged = original;
    forged.replace_value_disposition_for_shadow_test(
        value,
        ValueDisposition::Bound {
            binding: foreign_binding,
        },
    );
    let report = ShadowReport::build(&forged, &source, &snapshot).expect("classified report");
    assert_eq!(
        report.values[value.0 as usize].classification,
        ShadowClassification::ShadowWrong
    );
    assert_eq!(report.values[value.0 as usize].old, SideJudgment::Correct);
    assert!(matches!(
        report.values[value.0 as usize].shadow,
        SideJudgment::Wrong(WrongReason::EquivalenceClassMismatch)
    ));
    assert!(report.validate_against(&forged, &source, &snapshot).is_ok());
    assert!(report.ledger(&source).values.shadow_wrong > 0);
    assert!(!report.ledger(&source).passes_stage4());
}

#[test]
fn validation_rederives_every_stored_cell_field() {
    let source = source_owned([R2ILOp::Copy {
        dst: Varnode::unique(0x10, 8),
        src: Varnode::constant(7, 8),
    }]);
    let plan = BindingPlan::build_shadow(&source).expect("sealed plan");
    let snapshot = matching_snapshot(&source, &plan, 0);
    let report = ShadowReport::build(&plan, &source, &snapshot).expect("report");

    let assert_mutation = |field, mutate: fn(&mut ShadowCell<ValueId>)| {
        let mut corrupt = report.clone();
        mutate(&mut corrupt.values[0]);
        assert!(matches!(
            corrupt.validate_against(&plan, &source, &snapshot),
            Err(ShadowReportError::ReportCellMismatch {
                field: actual,
                ..
            }) if actual == field
        ));
    };

    assert_mutation(ReportCellField::Key, |cell| cell.key = ValueId(u32::MAX));
    assert_mutation(ReportCellField::Evidence, |cell| {
        cell.evidence = ShadowEvidenceKey::MachineUse {
            site: UseSite {
                inst: InstId(u32::MAX),
                input_idx: usize::MAX,
            },
        }
    });
    assert_mutation(ReportCellField::CanonicalKind, |cell| {
        cell.canonical_kind = match cell.canonical_kind {
            CanonicalDispositionKind::Representable => CanonicalDispositionKind::Refused,
            CanonicalDispositionKind::Refused => CanonicalDispositionKind::Representable,
        }
    });
    assert_mutation(ReportCellField::OldJudgment, |cell| {
        cell.old = SideJudgment::Wrong(WrongReason::EquivalenceClassMismatch)
    });
    assert_mutation(ReportCellField::ShadowJudgment, |cell| {
        cell.shadow = SideJudgment::Wrong(WrongReason::DispositionMismatch)
    });
    assert_mutation(ReportCellField::ObservationEquality, |cell| {
        cell.observations_equal = !cell.observations_equal
    });
    assert_mutation(ReportCellField::Classification, |cell| {
        cell.classification = ShadowClassification::ShadowWrong
    });
}

#[test]
fn legacy_binding_numbers_do_not_affect_report_identity() {
    let source = source_owned([
        R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(7, 8),
        },
        R2ILOp::IntAdd {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::unique(0x10, 8),
            b: Varnode::constant(1, 8),
        },
    ]);
    let plan = BindingPlan::build_shadow(&source).expect("sealed plan");
    let low_ids = matching_snapshot(&source, &plan, 0);
    let high_ids = matching_snapshot(&source, &plan, 10_000);
    let low = ShadowReport::build(&plan, &source, &low_ids).expect("low-id report");
    let high = ShadowReport::build(&plan, &source, &high_ids).expect("high-id report");
    assert_eq!(low, high);
}
