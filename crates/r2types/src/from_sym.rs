use crate::facts::{
    SymbolicBranchFact, SymbolicCompiledCondition, SymbolicConditionPrecision, SymbolicControlFact,
    SymbolicControlIsland, SymbolicControlIslandKind, SymbolicFactDiagnostics,
    SymbolicInterpreterDispatch, SymbolicInterpreterKind, SymbolicMemoryCondition,
    SymbolicMemoryIsland, SymbolicMemoryIslandKind, SymbolicMemoryRegion, SymbolicMemoryRegionKind,
    SymbolicMemoryRegionRef, SymbolicReachabilityStatus, SymbolicSemanticCapability,
    SymbolicSemanticConfidence, SymbolicSemanticEvidence, SymbolicSemanticEvidenceAmbiguity,
    SymbolicSemanticEvidenceCoverage, SymbolicSemanticEvidenceProvenance,
    SymbolicSemanticEvidenceReason, SymbolicSemanticEvidenceSoundness, SymbolicSemanticFacts,
    SymbolicSemanticMode, SymbolicSemanticResidualReason, SymbolicSemanticSliceClass,
    SymbolicVmBinaryOp, SymbolicVmGuardCondition, SymbolicVmGuardedExit, SymbolicVmStateUpdate,
    SymbolicVmStepSummary, SymbolicVmTransferArm, SymbolicVmUnaryOp, SymbolicVmValueExpr,
    SymbolicWorkerIsland,
};

fn symbolic_reachability_status_from_sym(
    status: r2sym::SymbolicReachabilityStatus,
) -> SymbolicReachabilityStatus {
    match status {
        r2sym::SymbolicReachabilityStatus::Reachable => SymbolicReachabilityStatus::Reachable,
        r2sym::SymbolicReachabilityStatus::Unreachable => SymbolicReachabilityStatus::Unreachable,
        r2sym::SymbolicReachabilityStatus::Unknown => SymbolicReachabilityStatus::Unknown,
    }
}

fn symbolic_condition_precision_from_sym(
    precision: r2sym::BackwardConditionPrecision,
) -> SymbolicConditionPrecision {
    match precision {
        r2sym::BackwardConditionPrecision::Exact => SymbolicConditionPrecision::Exact,
        r2sym::BackwardConditionPrecision::OverApprox => SymbolicConditionPrecision::OverApprox,
        r2sym::BackwardConditionPrecision::ResidualSearchRequired => {
            SymbolicConditionPrecision::ResidualSearchRequired
        }
        r2sym::BackwardConditionPrecision::Unsupported => SymbolicConditionPrecision::Unsupported,
    }
}

fn symbolic_memory_region_kind_from_sym(
    kind: &r2sym::MemoryRegionKind,
) -> SymbolicMemoryRegionKind {
    match kind {
        r2sym::MemoryRegionKind::Stack => SymbolicMemoryRegionKind::Stack,
        r2sym::MemoryRegionKind::Global => SymbolicMemoryRegionKind::Global,
        r2sym::MemoryRegionKind::Input => SymbolicMemoryRegionKind::Input,
        r2sym::MemoryRegionKind::Heap => SymbolicMemoryRegionKind::Heap,
        r2sym::MemoryRegionKind::Replay => SymbolicMemoryRegionKind::Replay,
        r2sym::MemoryRegionKind::EscapedUnknown => SymbolicMemoryRegionKind::EscapedUnknown,
    }
}

fn symbolic_memory_region_from_sym(region: &r2sym::BackwardMemoryRegion) -> SymbolicMemoryRegion {
    match region {
        r2sym::BackwardMemoryRegion::Argument { index } => {
            SymbolicMemoryRegion::Argument { index: *index }
        }
        r2sym::BackwardMemoryRegion::Region(region) => {
            SymbolicMemoryRegion::Region(SymbolicMemoryRegionRef {
                id: region.id.0,
                kind: symbolic_memory_region_kind_from_sym(&region.kind),
                name: region.name.clone(),
            })
        }
    }
}

fn symbolic_confidence_from_sym(
    confidence: r2sym::SemanticConfidence,
) -> SymbolicSemanticConfidence {
    match confidence {
        r2sym::SemanticConfidence::Exact => SymbolicSemanticConfidence::Exact,
        r2sym::SemanticConfidence::Likely => SymbolicSemanticConfidence::Likely,
        r2sym::SemanticConfidence::Heuristic => SymbolicSemanticConfidence::Heuristic,
        r2sym::SemanticConfidence::Residual => SymbolicSemanticConfidence::Residual,
    }
}

fn symbolic_evidence_reason_from_sym(
    reason: r2sym::SemanticEvidenceReason,
) -> SymbolicSemanticEvidenceReason {
    match reason {
        r2sym::SemanticEvidenceReason::LargeCfg => SymbolicSemanticEvidenceReason::LargeCfg,
        r2sym::SemanticEvidenceReason::SummaryBudget => {
            SymbolicSemanticEvidenceReason::SummaryBudget
        }
        r2sym::SemanticEvidenceReason::AliasAmbiguity => {
            SymbolicSemanticEvidenceReason::AliasAmbiguity
        }
        r2sym::SemanticEvidenceReason::ReplayOverlap => {
            SymbolicSemanticEvidenceReason::ReplayOverlap
        }
        r2sym::SemanticEvidenceReason::HeapIdentityWeak => {
            SymbolicSemanticEvidenceReason::HeapIdentityWeak
        }
        r2sym::SemanticEvidenceReason::GuardOpaque => SymbolicSemanticEvidenceReason::GuardOpaque,
        r2sym::SemanticEvidenceReason::ValueOpaque => SymbolicSemanticEvidenceReason::ValueOpaque,
        r2sym::SemanticEvidenceReason::TruncatedTransfer => {
            SymbolicSemanticEvidenceReason::TruncatedTransfer
        }
        r2sym::SemanticEvidenceReason::DerivedFromRanking => {
            SymbolicSemanticEvidenceReason::DerivedFromRanking
        }
        r2sym::SemanticEvidenceReason::PartialPathCoverage => {
            SymbolicSemanticEvidenceReason::PartialPathCoverage
        }
        r2sym::SemanticEvidenceReason::ResidualSearchRequired => {
            SymbolicSemanticEvidenceReason::ResidualSearchRequired
        }
    }
}

fn symbolic_evidence_from_sym(evidence: &r2sym::SemanticEvidence) -> SymbolicSemanticEvidence {
    SymbolicSemanticEvidence {
        tier: symbolic_confidence_from_sym(evidence.tier),
        soundness: match evidence.soundness {
            r2sym::SemanticEvidenceSoundness::Proven => SymbolicSemanticEvidenceSoundness::Proven,
            r2sym::SemanticEvidenceSoundness::OverApprox => {
                SymbolicSemanticEvidenceSoundness::OverApprox
            }
            r2sym::SemanticEvidenceSoundness::Ranked => SymbolicSemanticEvidenceSoundness::Ranked,
            r2sym::SemanticEvidenceSoundness::Unknown => SymbolicSemanticEvidenceSoundness::Unknown,
        },
        coverage: match evidence.coverage {
            r2sym::SemanticEvidenceCoverage::Full => SymbolicSemanticEvidenceCoverage::Full,
            r2sym::SemanticEvidenceCoverage::Partial => SymbolicSemanticEvidenceCoverage::Partial,
            r2sym::SemanticEvidenceCoverage::Bounded => SymbolicSemanticEvidenceCoverage::Bounded,
        },
        provenance: match evidence.provenance {
            r2sym::SemanticEvidenceProvenance::Stable => SymbolicSemanticEvidenceProvenance::Stable,
            r2sym::SemanticEvidenceProvenance::Normalized => {
                SymbolicSemanticEvidenceProvenance::Normalized
            }
            r2sym::SemanticEvidenceProvenance::Ranked => SymbolicSemanticEvidenceProvenance::Ranked,
            r2sym::SemanticEvidenceProvenance::Unstable => {
                SymbolicSemanticEvidenceProvenance::Unstable
            }
        },
        ambiguity: match evidence.ambiguity {
            r2sym::SemanticEvidenceAmbiguity::Single => SymbolicSemanticEvidenceAmbiguity::Single,
            r2sym::SemanticEvidenceAmbiguity::Bounded => SymbolicSemanticEvidenceAmbiguity::Bounded,
            r2sym::SemanticEvidenceAmbiguity::Ranked => SymbolicSemanticEvidenceAmbiguity::Ranked,
            r2sym::SemanticEvidenceAmbiguity::Multiple => {
                SymbolicSemanticEvidenceAmbiguity::Multiple
            }
        },
        budget_limited: evidence.budget_limited,
        reasons: evidence
            .reasons
            .iter()
            .copied()
            .map(symbolic_evidence_reason_from_sym)
            .collect(),
    }
}

fn symbolic_compiled_condition_from_sym(
    summary: &r2sym::BackwardConditionSummary,
) -> SymbolicCompiledCondition {
    let evidence = summary.evidence();
    SymbolicCompiledCondition {
        simplified: summary.simplified.clone(),
        terms: summary.terms.clone(),
        memory_terms: summary
            .memory_terms
            .iter()
            .map(|term| SymbolicMemoryCondition {
                region: symbolic_memory_region_from_sym(&term.region),
                offset_lo: term.offset_lo,
                offset_hi: term.offset_hi,
                size: term.size,
                exact_offset: term.exact_offset,
                evidence: symbolic_evidence_from_sym(&term.evidence()),
                confidence: symbolic_confidence_from_sym(term.confidence()),
                binding: term.binding.clone(),
                expr: term.expr.clone(),
                value_expr: term.value_expr.clone(),
                exact_value: term.exact_value,
            })
            .collect(),
        backward_memory_substitutions: summary.backward_memory_substitutions,
        backward_memory_candidate_enumerations: summary.backward_memory_candidate_enumerations,
        backward_memory_residual_fallbacks: summary.backward_memory_residual_fallbacks,
        precision: symbolic_condition_precision_from_sym(summary.precision),
        evidence: symbolic_evidence_from_sym(&evidence),
        confidence: symbolic_confidence_from_sym(evidence.tier),
        supported_paths: summary.supported_paths,
        total_paths: summary.total_paths,
    }
}

fn symbolic_control_island_kind_from_sym(
    kind: r2sym::SymbolicControlIslandKind,
) -> SymbolicControlIslandKind {
    match kind {
        r2sym::SymbolicControlIslandKind::BranchFrontier => {
            SymbolicControlIslandKind::BranchFrontier
        }
        r2sym::SymbolicControlIslandKind::LargeCfgBranchFrontier => {
            SymbolicControlIslandKind::LargeCfgBranchFrontier
        }
    }
}

fn symbolic_control_fact_from_sym(fact: &r2sym::SymbolicControlFact) -> SymbolicControlFact {
    SymbolicControlFact {
        target: fact.target,
        status: symbolic_reachability_status_from_sym(fact.status),
        condition: fact.condition.clone(),
        compiled: fact
            .compiled
            .as_ref()
            .map(symbolic_compiled_condition_from_sym),
        evidence: symbolic_evidence_from_sym(&fact.evidence),
        confidence: symbolic_confidence_from_sym(fact.evidence.tier),
    }
}

fn symbolic_memory_island_kind_from_sym(
    kind: r2sym::SymbolicMemoryIslandKind,
) -> SymbolicMemoryIslandKind {
    match kind {
        r2sym::SymbolicMemoryIslandKind::ConditionFrontier => {
            SymbolicMemoryIslandKind::ConditionFrontier
        }
        r2sym::SymbolicMemoryIslandKind::LargeCfgConditionFrontier => {
            SymbolicMemoryIslandKind::LargeCfgConditionFrontier
        }
    }
}

fn symbolic_control_island_from_sym(
    island: &r2sym::SymbolicControlIsland,
) -> SymbolicControlIsland {
    SymbolicControlIsland {
        kind: symbolic_control_island_kind_from_sym(island.kind),
        anchor_block: island.anchor_block,
        frontier_targets: island.frontier_targets.clone(),
        facts: island
            .facts
            .iter()
            .map(symbolic_control_fact_from_sym)
            .collect(),
        evidence: symbolic_evidence_from_sym(&island.evidence),
        confidence: symbolic_confidence_from_sym(island.evidence.tier),
    }
}

fn symbolic_memory_island_from_sym(island: &r2sym::SymbolicMemoryIsland) -> SymbolicMemoryIsland {
    SymbolicMemoryIsland {
        kind: symbolic_memory_island_kind_from_sym(island.kind),
        anchor_block: island.anchor_block,
        terms: island
            .terms
            .iter()
            .map(|term| SymbolicMemoryCondition {
                region: symbolic_memory_region_from_sym(&term.region),
                offset_lo: term.offset_lo,
                offset_hi: term.offset_hi,
                size: term.size,
                exact_offset: term.exact_offset,
                evidence: symbolic_evidence_from_sym(&term.evidence()),
                confidence: symbolic_confidence_from_sym(term.confidence()),
                binding: term.binding.clone(),
                expr: term.expr.clone(),
                value_expr: term.value_expr.clone(),
                exact_value: term.exact_value,
            })
            .collect(),
        evidence: symbolic_evidence_from_sym(&island.evidence),
        confidence: symbolic_confidence_from_sym(island.evidence.tier),
    }
}

fn symbolic_worker_island_from_sym(island: &r2sym::SymbolicWorkerIsland) -> SymbolicWorkerIsland {
    SymbolicWorkerIsland {
        anchor_block: island.anchor_block,
        control_kind: island
            .control_kind
            .map(symbolic_control_island_kind_from_sym),
        memory_kind: island.memory_kind.map(symbolic_memory_island_kind_from_sym),
        frontier_targets: island.frontier_targets.clone(),
        control_facts: island
            .control_facts
            .iter()
            .map(symbolic_control_fact_from_sym)
            .collect(),
        memory_terms: island
            .memory_terms
            .iter()
            .map(|term| SymbolicMemoryCondition {
                region: symbolic_memory_region_from_sym(&term.region),
                offset_lo: term.offset_lo,
                offset_hi: term.offset_hi,
                size: term.size,
                exact_offset: term.exact_offset,
                evidence: symbolic_evidence_from_sym(&term.evidence()),
                confidence: symbolic_confidence_from_sym(term.confidence()),
                binding: term.binding.clone(),
                expr: term.expr.clone(),
                value_expr: term.value_expr.clone(),
                exact_value: term.exact_value,
            })
            .collect(),
        evidence: symbolic_evidence_from_sym(&island.evidence),
        confidence: symbolic_confidence_from_sym(island.evidence.tier),
    }
}

fn symbolic_interpreter_kind_from_sym(kind: r2sym::InterpreterKind) -> SymbolicInterpreterKind {
    match kind {
        r2sym::InterpreterKind::SwitchDispatch => SymbolicInterpreterKind::SwitchDispatch,
        r2sym::InterpreterKind::IndirectDispatch => SymbolicInterpreterKind::IndirectDispatch,
    }
}

pub fn symbolic_vm_value_expr_from_sym(value: &r2sym::VmValueExpr) -> SymbolicVmValueExpr {
    value.into()
}

impl From<&r2sym::VmValueExpr> for SymbolicVmValueExpr {
    fn from(value: &r2sym::VmValueExpr) -> Self {
        match value {
            r2sym::VmValueExpr::Const(value) => SymbolicVmValueExpr::Const(*value),
            r2sym::VmValueExpr::Var(name) => SymbolicVmValueExpr::Var(name.clone()),
            r2sym::VmValueExpr::Unary { op, arg } => SymbolicVmValueExpr::Unary {
                op: match op {
                    r2sym::VmUnaryOp::Neg => SymbolicVmUnaryOp::Neg,
                    r2sym::VmUnaryOp::BitNot => SymbolicVmUnaryOp::Not,
                    r2sym::VmUnaryOp::BoolNot => SymbolicVmUnaryOp::BoolNot,
                },
                expr: Box::new(SymbolicVmValueExpr::from(arg.as_ref())),
            },
            r2sym::VmValueExpr::Binary { op, lhs, rhs } => SymbolicVmValueExpr::Binary {
                op: match op {
                    r2sym::VmBinaryOp::Add => SymbolicVmBinaryOp::Add,
                    r2sym::VmBinaryOp::Sub => SymbolicVmBinaryOp::Sub,
                    r2sym::VmBinaryOp::Mul => SymbolicVmBinaryOp::Mul,
                    r2sym::VmBinaryOp::Div => SymbolicVmBinaryOp::Div,
                    r2sym::VmBinaryOp::Rem => SymbolicVmBinaryOp::Rem,
                    r2sym::VmBinaryOp::And => SymbolicVmBinaryOp::And,
                    r2sym::VmBinaryOp::Or => SymbolicVmBinaryOp::Or,
                    r2sym::VmBinaryOp::Xor => SymbolicVmBinaryOp::Xor,
                    r2sym::VmBinaryOp::Shl => SymbolicVmBinaryOp::Shl,
                    r2sym::VmBinaryOp::LShr | r2sym::VmBinaryOp::AShr => SymbolicVmBinaryOp::Shr,
                    r2sym::VmBinaryOp::Eq => SymbolicVmBinaryOp::Eq,
                    r2sym::VmBinaryOp::Ne => SymbolicVmBinaryOp::Ne,
                    r2sym::VmBinaryOp::Lt | r2sym::VmBinaryOp::SLt => SymbolicVmBinaryOp::Lt,
                    r2sym::VmBinaryOp::Le | r2sym::VmBinaryOp::SLe => SymbolicVmBinaryOp::Le,
                    r2sym::VmBinaryOp::BoolAnd => SymbolicVmBinaryOp::And,
                    r2sym::VmBinaryOp::BoolOr => SymbolicVmBinaryOp::Or,
                },
                left: Box::new(SymbolicVmValueExpr::from(lhs.as_ref())),
                right: Box::new(SymbolicVmValueExpr::from(rhs.as_ref())),
            },
            r2sym::VmValueExpr::Expr(expr) => SymbolicVmValueExpr::Expr(expr.clone()),
        }
    }
}

fn symbolic_vm_state_update_from_sym(update: &r2sym::VmStateUpdate) -> SymbolicVmStateUpdate {
    let evidence = update.evidence();
    SymbolicVmStateUpdate {
        output: update.output.clone(),
        expr: update.expr.clone(),
        value: SymbolicVmValueExpr::from(&update.value),
        exact: update.exact,
        evidence: symbolic_evidence_from_sym(&evidence),
        confidence: symbolic_confidence_from_sym(evidence.tier),
    }
}

fn symbolic_vm_guard_condition_from_sym(
    guard: &r2sym::VmGuardCondition,
) -> SymbolicVmGuardCondition {
    let evidence = guard.evidence();
    SymbolicVmGuardCondition {
        expr: guard.expr.clone(),
        value: SymbolicVmValueExpr::from(&guard.value),
        expect_nonzero: guard.expect_nonzero,
        exact: guard.exact,
        evidence: symbolic_evidence_from_sym(&evidence),
        confidence: symbolic_confidence_from_sym(evidence.tier),
    }
}

fn symbolic_vm_guarded_exit_from_sym(guarded: &r2sym::VmGuardedExit) -> SymbolicVmGuardedExit {
    SymbolicVmGuardedExit {
        target: guarded.target,
        guard: symbolic_vm_guard_condition_from_sym(&guarded.guard),
    }
}

fn symbolic_vm_memory_condition_from_sym(
    condition: &r2sym::VmMemoryCondition,
) -> SymbolicMemoryCondition {
    let evidence = condition.evidence();
    SymbolicMemoryCondition {
        region: SymbolicMemoryRegion::Region(SymbolicMemoryRegionRef {
            id: condition.region.id,
            kind: symbolic_memory_region_kind_from_sym(&condition.region.kind),
            name: condition.region.name.clone(),
        }),
        offset_lo: condition.offset_lo,
        offset_hi: condition.offset_hi,
        size: condition.size,
        exact_offset: condition.exact_offset,
        evidence: symbolic_evidence_from_sym(&evidence),
        confidence: symbolic_confidence_from_sym(evidence.tier),
        binding: condition.binding.clone(),
        expr: condition.expr.clone(),
        value_expr: condition.value_expr.clone(),
        exact_value: condition.exact_value,
    }
}

fn symbolic_vm_transfer_arm_from_sym(transfer: &r2sym::VmTransferArm) -> SymbolicVmTransferArm {
    let evidence = transfer.evidence();
    SymbolicVmTransferArm {
        handler_target: transfer.handler_target,
        case_values: transfer.case_values.clone(),
        region_blocks: transfer.region_blocks.clone(),
        exit_targets: transfer.exit_targets.clone(),
        exit_guards: transfer
            .exit_guards
            .iter()
            .map(symbolic_vm_guarded_exit_from_sym)
            .collect(),
        state_updates: transfer
            .state_updates
            .iter()
            .map(symbolic_vm_state_update_from_sym)
            .collect(),
        selector_update: transfer
            .selector_update
            .as_ref()
            .map(symbolic_vm_state_update_from_sym),
        memory_reads: transfer
            .memory_reads
            .iter()
            .map(symbolic_vm_memory_condition_from_sym)
            .collect(),
        memory_writes: transfer
            .memory_writes
            .iter()
            .map(symbolic_vm_memory_condition_from_sym)
            .collect(),
        residual_guards: transfer.residual_guards,
        residual_memory_effects: transfer.residual_memory_effects,
        exact: transfer.exact,
        evidence: symbolic_evidence_from_sym(&evidence),
        confidence: symbolic_confidence_from_sym(evidence.tier),
        redispatch: transfer.redispatch,
        may_return: transfer.may_return,
        truncated: transfer.truncated,
    }
}

fn symbolic_vm_step_summary_from_sym(vm_step: &r2sym::VmStepSummary) -> SymbolicVmStepSummary {
    SymbolicVmStepSummary {
        kind: symbolic_interpreter_kind_from_sym(vm_step.kind),
        loop_header: vm_step.loop_header,
        dispatch_header: vm_step.dispatch_header,
        selector: vm_step.selector.clone(),
        dispatch_targets: vm_step.dispatch_targets.clone(),
        default_target: vm_step.default_target,
        case_values_by_target: vm_step.case_values_by_target.clone(),
        loop_latches: vm_step.loop_latches.clone(),
        state_inputs: vm_step.state_inputs.clone(),
        state_outputs: vm_step.state_outputs.clone(),
        step_blocks: vm_step.step_blocks.clone(),
        handler_regions: vm_step.handler_regions.clone(),
        handler_state_inputs: vm_step.handler_state_inputs.clone(),
        handler_state_outputs: vm_step.handler_state_outputs.clone(),
        handler_state_updates: vm_step
            .handler_state_updates
            .iter()
            .map(|(target, updates)| {
                (
                    *target,
                    updates
                        .iter()
                        .map(symbolic_vm_state_update_from_sym)
                        .collect(),
                )
            })
            .collect(),
        handler_exit_guards: vm_step
            .handler_exit_guards
            .iter()
            .map(|(target, guards)| {
                (
                    *target,
                    guards
                        .iter()
                        .map(symbolic_vm_guarded_exit_from_sym)
                        .collect(),
                )
            })
            .collect(),
        handler_memory_read_effects: vm_step
            .handler_memory_read_effects
            .iter()
            .map(|(target, effects)| {
                (
                    *target,
                    effects
                        .iter()
                        .map(symbolic_vm_memory_condition_from_sym)
                        .collect(),
                )
            })
            .collect(),
        handler_memory_write_effects: vm_step
            .handler_memory_write_effects
            .iter()
            .map(|(target, effects)| {
                (
                    *target,
                    effects
                        .iter()
                        .map(symbolic_vm_memory_condition_from_sym)
                        .collect(),
                )
            })
            .collect(),
        handler_memory_reads: vm_step.handler_memory_reads.clone(),
        handler_memory_writes: vm_step.handler_memory_writes.clone(),
        handler_calls: vm_step.handler_calls.clone(),
        handler_conditional_branches: vm_step.handler_conditional_branches.clone(),
        handler_exit_targets: vm_step.handler_exit_targets.clone(),
        redispatch_handlers: vm_step.redispatch_handlers.clone(),
        returning_handlers: vm_step.returning_handlers.clone(),
        truncated_handlers: vm_step.truncated_handlers.clone(),
        transfers: vm_step
            .transfers
            .iter()
            .map(symbolic_vm_transfer_arm_from_sym)
            .collect(),
    }
}

pub fn symbolic_semantic_facts_from_artifact(
    compiled: &r2sym::CompiledSemanticArtifact,
) -> SymbolicSemanticFacts {
    compiled.into()
}

impl From<&r2sym::CompiledSemanticArtifact> for SymbolicSemanticFacts {
    fn from(compiled: &r2sym::CompiledSemanticArtifact) -> Self {
        let facts = &compiled.symbolic_facts;
        SymbolicSemanticFacts {
            branch_facts: facts
                .branch_facts
                .iter()
                .map(|fact| SymbolicBranchFact {
                    block_addr: fact.block_addr,
                    true_target: fact.true_target,
                    false_target: fact.false_target,
                    true_status: symbolic_reachability_status_from_sym(fact.true_status),
                    false_status: symbolic_reachability_status_from_sym(fact.false_status),
                    true_condition: fact.true_condition.clone(),
                    false_condition: fact.false_condition.clone(),
                    true_compiled: fact
                        .true_compiled
                        .as_ref()
                        .map(symbolic_compiled_condition_from_sym),
                    false_compiled: fact
                        .false_compiled
                        .as_ref()
                        .map(symbolic_compiled_condition_from_sym),
                })
                .collect(),
            worker_islands: facts
                .worker_islands
                .iter()
                .map(symbolic_worker_island_from_sym)
                .collect(),
            control_islands: facts
                .control_islands
                .iter()
                .map(symbolic_control_island_from_sym)
                .collect(),
            memory_islands: facts
                .memory_islands
                .iter()
                .map(symbolic_memory_island_from_sym)
                .collect(),
            diagnostics: SymbolicFactDiagnostics {
                branches_evaluated: facts.diagnostics.branches_evaluated,
                branches_pruned: facts.diagnostics.branches_pruned,
                branches_unknown: facts.diagnostics.branches_unknown,
                skipped_missing_arch: facts.diagnostics.skipped_missing_arch,
                skipped_large_cfg: facts.diagnostics.skipped_large_cfg,
                cache_hit: compiled.cache_hit,
                semantic_mode: Some(match compiled.mode {
                    r2sym::SemanticMode::Raw => SymbolicSemanticMode::Raw,
                    r2sym::SemanticMode::Compiled => SymbolicSemanticMode::Compiled,
                    r2sym::SemanticMode::IslandCompiled => SymbolicSemanticMode::IslandCompiled,
                    r2sym::SemanticMode::Residual => SymbolicSemanticMode::Residual,
                    r2sym::SemanticMode::VmSummary => SymbolicSemanticMode::VmSummary,
                }),
                semantic_capability: Some(SymbolicSemanticCapability {
                    query_ready: compiled.capability.query_ready,
                    type_ready: compiled.capability.type_ready,
                    decompile_ready: compiled.capability.decompile_ready,
                }),
                slice_class: Some(match compiled.slice_class {
                    r2sym::SliceClass::Wrapper => SymbolicSemanticSliceClass::Wrapper,
                    r2sym::SliceClass::Worker => SymbolicSemanticSliceClass::Worker,
                    r2sym::SliceClass::RecursiveGroup => SymbolicSemanticSliceClass::RecursiveGroup,
                    r2sym::SliceClass::InterpreterSwitch => {
                        SymbolicSemanticSliceClass::InterpreterSwitch
                    }
                    r2sym::SliceClass::InterpreterIndirect => {
                        SymbolicSemanticSliceClass::InterpreterIndirect
                    }
                    r2sym::SliceClass::GenericLarge => SymbolicSemanticSliceClass::GenericLarge,
                }),
                residual_reasons: compiled
                    .residual_reasons
                    .iter()
                    .map(|reason| match reason {
                        r2sym::ResidualReason::MissingArch => {
                            SymbolicSemanticResidualReason::MissingArch
                        }
                        r2sym::ResidualReason::LargeCfg => SymbolicSemanticResidualReason::LargeCfg,
                        r2sym::ResidualReason::SummaryBudgetExhausted => {
                            SymbolicSemanticResidualReason::SummaryBudgetExhausted
                        }
                        r2sym::ResidualReason::SccBudgetExhausted => {
                            SymbolicSemanticResidualReason::SccBudgetExhausted
                        }
                        r2sym::ResidualReason::InterpreterRequiresStepSummary => {
                            SymbolicSemanticResidualReason::InterpreterRequiresStepSummary
                        }
                    })
                    .collect(),
                closure_functions: compiled.closure_functions,
                helper_functions: compiled.helper_functions,
                derived_summaries: compiled.derived_summaries,
                summary_attempted: compiled.derived_diagnostics.attempted,
                summary_budget_exhausted: compiled.derived_diagnostics.budget_exhausted
                    + compiled.derived_diagnostics.scc_budget_exhausted,
                summary_scc_count: compiled.derived_diagnostics.scc_count,
            },
            interpreter: compiled.interpreter.as_ref().map(|interpreter| {
                SymbolicInterpreterDispatch {
                    kind: symbolic_interpreter_kind_from_sym(interpreter.kind),
                    dispatch_header: interpreter.dispatch_header,
                    dispatch_targets: interpreter.dispatch_targets,
                    selector: interpreter.selector.clone(),
                    back_edges: interpreter.back_edges,
                    score: interpreter.score,
                }
            }),
            vm_step: compiled
                .vm_step
                .as_ref()
                .map(symbolic_vm_step_summary_from_sym),
            vm_transfer: compiled
                .vm_transfer
                .as_ref()
                .map(symbolic_vm_step_summary_from_sym),
        }
    }
}
