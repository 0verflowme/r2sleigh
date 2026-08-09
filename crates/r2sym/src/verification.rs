//! Canonical solve verification and replay policy.
//!
//! Query exploration can prove that a target is reachable under the current
//! semantic model. This module decides whether that reachability is strong
//! enough to report a concrete solve.

use r2ssa::SsaArtifact;

use crate::constraints::{FinalConstraintGraph, FinalConstraintPrecision};
use crate::kernel::FactPrecision;
use crate::loops::{
    ExactLoopFoldEvidence, ExactLoopRecurrenceEvidence, ExactLoopRecurrenceKind, LoopFoldOperation,
    LoopMemoryTermKind, exact_fold_evidence_from_recurrences,
};
use crate::path::{ExploreStats, PathExplorer, SolvedPath, SolvedPathGeneration};
use crate::query::QueryCompletion;
use crate::semantics::TargetQueryExecutionRoute;
use crate::{PreparedFunctionScope, SymState};

/// Result status for concrete target solving.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveStatus {
    Solved,
    Candidate,
    ResidualReachable,
    Unverified,
    Unsat,
    Unknown,
    BudgetExhausted,
}

/// Concrete/model validation state for a reported solve candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelValidation {
    /// Pure symbolic semantics were exact enough; no external replay is required.
    NotRequired,
    /// A concrete replay/oracle accepted the candidate.
    Verified,
    /// A concrete replay/oracle rejected the candidate.
    Failed { reason: String },
    /// Validation was required by residual/runtime evidence but no backend was available.
    Unavailable { reason: String },
}

/// Truthfulness metadata for target solving.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolveVerification {
    pub target_reached_under_model: bool,
    pub candidate_solution_verified: bool,
    pub residual_reasons: Vec<String>,
    pub model_validation: ModelValidation,
}

/// Shape of the concrete candidate extracted from a path model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolveCandidateShape {
    pub input_scalars: usize,
    pub input_buffers: usize,
    pub registers: usize,
    pub memory_regions: usize,
    pub concrete_assignments: usize,
    pub final_pc: u64,
    pub num_constraints: usize,
    pub generation: Option<SolvedPathGeneration>,
}

impl SolveCandidateShape {
    pub fn from_solution(solution: &SolvedPath) -> Self {
        let concrete_assignments = solution.inputs.len()
            + solution.input_buffers.values().map(Vec::len).sum::<usize>()
            + solution.memory.values().map(Vec::len).sum::<usize>();
        Self {
            input_scalars: solution.inputs.len(),
            input_buffers: solution.input_buffers.len(),
            registers: solution.registers.len(),
            memory_regions: solution.memory.len(),
            concrete_assignments,
            final_pc: solution.final_pc,
            num_constraints: solution.num_constraints,
            generation: solution.generation.clone(),
        }
    }

    pub fn has_replayable_assignments(&self) -> bool {
        self.concrete_assignments > 0
    }
}

/// Compact precision summary for route/query evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceSummary {
    pub precision: FactPrecision,
    pub reasons: Vec<String>,
    pub requires_replay: bool,
    pub final_constraint_precision: FinalConstraintPrecision,
    pub exact_final_constraints: usize,
    pub model_conditioned_final_constraints: usize,
    pub exact_loop_recurrences: Vec<ExactLoopRecurrenceEvidence>,
    pub exact_loop_folds: Vec<ExactLoopFoldEvidence>,
    pub tactics: Vec<SolveTacticEvidence>,
}

impl EvidenceSummary {
    pub fn exact() -> Self {
        Self {
            precision: FactPrecision::Exact,
            reasons: Vec::new(),
            requires_replay: false,
            final_constraint_precision: FinalConstraintPrecision::Unknown,
            exact_final_constraints: 0,
            model_conditioned_final_constraints: 0,
            exact_loop_recurrences: Vec::new(),
            exact_loop_folds: Vec::new(),
            tactics: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveTacticKind {
    XorFoldPreimage,
    AddFoldPreimage,
    RotateXorRecurrence,
    RotateAddRecurrence,
    ConcreteTableFold,
    RuntimeBlobFold,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveTacticStatus {
    Available,
    EvidenceOnly,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolveTacticEvidence {
    pub kind: SolveTacticKind,
    pub status: SolveTacticStatus,
    pub reason: String,
    pub recurrence: ExactLoopRecurrenceEvidence,
}

/// Replay requirement derived from route precision and runtime evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationRequirement {
    NotRequired,
    Required { reasons: Vec<String> },
    Refused { reasons: Vec<String> },
}

/// Canonical witness for a target solve result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolveWitness {
    pub target_addr: u64,
    pub selected_path_index: Option<usize>,
    pub final_pc: Option<u64>,
    pub candidate: Option<SolveCandidateShape>,
    pub evidence: EvidenceSummary,
    pub verification_requirement: VerificationRequirement,
    pub verification: SolveVerification,
}

impl SolveWitness {
    pub fn is_proven(&self) -> bool {
        self.verification.target_reached_under_model
            && (self.verification.candidate_solution_verified
                || (self
                    .candidate
                    .as_ref()
                    .is_some_and(|candidate| !candidate.has_replayable_assignments())
                    && self.evidence.reasons.is_empty()
                    && matches!(
                        self.verification.model_validation,
                        ModelValidation::NotRequired
                    )))
    }
}

/// Input required to replay a candidate model against concrete/lifted semantics.
pub struct CandidateReplayRequest<'a, 'ctx> {
    pub func: &'a SsaArtifact,
    pub scope: Option<&'a PreparedFunctionScope>,
    pub initial_state: SymState<'ctx>,
    pub target_addr: u64,
    pub solution: &'a SolvedPath,
}

/// Backend-neutral candidate replay interface.
pub trait CandidateReplayBackend<'ctx> {
    fn replay_candidate<'a>(
        &mut self,
        request: CandidateReplayRequest<'a, 'ctx>,
    ) -> ModelValidation;
}

/// Lifted-semantics replay backend used as the default verifier.
pub struct LiftedReplayBackend<'a, 'ctx> {
    explorer: &'a mut PathExplorer<'ctx>,
}

impl<'a, 'ctx> LiftedReplayBackend<'a, 'ctx> {
    pub fn new(explorer: &'a mut PathExplorer<'ctx>) -> Self {
        Self { explorer }
    }
}

impl<'ctx> CandidateReplayBackend<'ctx> for LiftedReplayBackend<'_, 'ctx> {
    fn replay_candidate<'a>(
        &mut self,
        request: CandidateReplayRequest<'a, 'ctx>,
    ) -> ModelValidation {
        validate_solution_with_lifted_semantics(
            self.explorer,
            request.func,
            request.scope,
            request.initial_state,
            request.target_addr,
            request.solution,
        )
    }
}

/// Explicit no-backend verifier for tests and future external integrations.
#[derive(Debug, Clone)]
pub struct UnavailableReplayBackend {
    reason: String,
}

impl UnavailableReplayBackend {
    pub fn new(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
        }
    }
}

impl<'ctx> CandidateReplayBackend<'ctx> for UnavailableReplayBackend {
    fn replay_candidate<'a>(
        &mut self,
        _request: CandidateReplayRequest<'a, 'ctx>,
    ) -> ModelValidation {
        ModelValidation::Unavailable {
            reason: self.reason.clone(),
        }
    }
}

/// Full verifier input for a target solve result.
pub struct SolveVerificationRequest<'a, 'ctx> {
    pub func: &'a SsaArtifact,
    pub scope: Option<&'a PreparedFunctionScope>,
    pub selected_route: &'a crate::TargetQueryRoutePlan,
    pub stats: &'a ExploreStats,
    pub validation_initial_state: SymState<'ctx>,
    pub target_addr: u64,
    pub exact_unsat: bool,
    pub selected_path_index: Option<usize>,
    pub solution: Option<&'a SolvedPath>,
    pub constraint_graph: &'a FinalConstraintGraph,
}

/// Verify the target solve result and decide its final user-visible status.
pub fn verify_solve_result<'a, 'ctx, B>(
    request: SolveVerificationRequest<'a, 'ctx>,
    replay_backend: &mut B,
) -> (SolveStatus, SolveVerification, SolveWitness)
where
    B: CandidateReplayBackend<'ctx>,
{
    let residual_reasons = solve_residual_reasons(request.selected_route, request.stats);
    let evidence = evidence_summary_for_route_and_stats(
        request.selected_route,
        request.stats,
        Some(request.constraint_graph),
    );
    let verification_requirement = verification_requirement_for_route_and_stats(
        request.selected_route,
        request.stats,
        Some(request.constraint_graph),
    );
    let candidate = request.solution.map(SolveCandidateShape::from_solution);
    let final_pc = request.solution.map(|solution| solution.final_pc);

    let model_validation = if let Some(solution) = request.solution {
        let candidate_has_replayable_assignments = candidate
            .as_ref()
            .is_some_and(SolveCandidateShape::has_replayable_assignments);
        if candidate_has_replayable_assignments {
            replay_backend.replay_candidate(CandidateReplayRequest {
                func: request.func,
                scope: request.scope,
                initial_state: request.validation_initial_state,
                target_addr: request.target_addr,
                solution,
            })
        } else if residual_reasons.is_empty() {
            ModelValidation::NotRequired
        } else {
            ModelValidation::Unavailable {
                reason: "residual/runtime evidence produced no concrete replay candidate"
                    .to_string(),
            }
        }
    } else if residual_reasons.is_empty() {
        ModelValidation::NotRequired
    } else {
        ModelValidation::Unavailable {
            reason: "residual/runtime evidence requires concrete replay validation".to_string(),
        }
    };

    let verification = solve_verification(
        request.selected_path_index.is_some(),
        request.solution.is_some(),
        residual_reasons,
        model_validation,
    );
    let status = classify_solve_status(
        request.exact_unsat,
        request.selected_path_index,
        request.solution.is_some(),
        completion_from_stats(request.stats),
        &verification,
        request.constraint_graph,
    );
    let witness = SolveWitness {
        target_addr: request.target_addr,
        selected_path_index: request.selected_path_index,
        final_pc,
        candidate,
        evidence,
        verification_requirement,
        verification: verification.clone(),
    };
    (status, verification, witness)
}

pub fn solution_extraction_allowed(
    route: &crate::TargetQueryRoutePlan,
    stats: &ExploreStats,
) -> bool {
    let residual_reasons = solve_residual_reasons(route, stats);
    !residual_summary_blocks_solution_extraction(stats, &residual_reasons)
}

pub fn evidence_summary_for_route_and_stats(
    route: &crate::TargetQueryRoutePlan,
    stats: &ExploreStats,
    constraint_graph: Option<&FinalConstraintGraph>,
) -> EvidenceSummary {
    let mut reasons = solve_residual_reasons(route, stats);
    if let Some(graph) = constraint_graph {
        for reason in &graph.refusals {
            push_unique_reason(&mut reasons, reason.clone());
        }
        if graph.constraints.is_empty() {
            push_unique_reason(&mut reasons, "final_constraint_missing");
        } else if graph.exact_constraint_count() == 0
            && graph.model_conditioned_constraint_count() > 0
        {
            push_unique_reason(&mut reasons, "final_constraint_model_conditioned");
        }
    }
    let exact_loop_folds =
        exact_fold_evidence_from_recurrences(&stats.runtime_loop_exact_recurrences);
    let exact_loop_recurrences = stats.runtime_loop_exact_recurrences.clone();
    let tactics = solve_tactics_for_exact_recurrences(&stats.runtime_loop_exact_recurrences);
    let final_constraint_precision = constraint_graph
        .map(FinalConstraintGraph::strongest_precision)
        .unwrap_or(FinalConstraintPrecision::Unknown);
    let exact_final_constraints = constraint_graph
        .map(FinalConstraintGraph::exact_constraint_count)
        .unwrap_or(0);
    let model_conditioned_final_constraints = constraint_graph
        .map(FinalConstraintGraph::model_conditioned_constraint_count)
        .unwrap_or(0);
    if reasons.is_empty() {
        return EvidenceSummary {
            precision: FactPrecision::Exact,
            reasons,
            requires_replay: false,
            final_constraint_precision,
            exact_final_constraints,
            model_conditioned_final_constraints,
            exact_loop_recurrences,
            exact_loop_folds,
            tactics,
        };
    }
    EvidenceSummary {
        precision: FactPrecision::Residual,
        requires_replay: true,
        reasons,
        final_constraint_precision,
        exact_final_constraints,
        model_conditioned_final_constraints,
        exact_loop_recurrences,
        exact_loop_folds,
        tactics,
    }
}

pub fn solve_tactics_for_exact_recurrences(
    recurrences: &[ExactLoopRecurrenceEvidence],
) -> Vec<SolveTacticEvidence> {
    let mut tactics = recurrences
        .iter()
        .filter_map(|recurrence| match &recurrence.kind {
            ExactLoopRecurrenceKind::Fold { operation, term } => {
                tactic_for_fold_recurrence(recurrence, *operation, term)
            }
            ExactLoopRecurrenceKind::RotateMix {
                operation, term, ..
            } => Some(SolveTacticEvidence {
                kind: match operation {
                    LoopFoldOperation::Xor => SolveTacticKind::RotateXorRecurrence,
                    LoopFoldOperation::Add => SolveTacticKind::RotateAddRecurrence,
                },
                status: SolveTacticStatus::Available,
                reason: rotate_recurrence_reason(*operation, term.kind),
                recurrence: recurrence.clone(),
            }),
            _ => None,
        })
        .collect::<Vec<_>>();
    tactics.sort_by(|lhs, rhs| {
        (
            lhs.recurrence.header,
            lhs.recurrence.exit_target,
            lhs.recurrence.accumulator.as_str(),
            format!("{:?}", lhs.recurrence.kind),
            lhs.reason.as_str(),
        )
            .cmp(&(
                rhs.recurrence.header,
                rhs.recurrence.exit_target,
                rhs.recurrence.accumulator.as_str(),
                format!("{:?}", rhs.recurrence.kind),
                rhs.reason.as_str(),
            ))
    });
    tactics
}

pub fn solve_tactics_for_exact_folds(folds: &[ExactLoopFoldEvidence]) -> Vec<SolveTacticEvidence> {
    let recurrences = folds
        .iter()
        .cloned()
        .map(ExactLoopRecurrenceEvidence::from)
        .collect::<Vec<_>>();
    solve_tactics_for_exact_recurrences(&recurrences)
}

fn tactic_for_fold_recurrence(
    recurrence: &ExactLoopRecurrenceEvidence,
    operation: LoopFoldOperation,
    term: &crate::LoopMemoryTerm,
) -> Option<SolveTacticEvidence> {
    match (operation, term.kind) {
        (LoopFoldOperation::Xor, LoopMemoryTermKind::InputRead) => Some(SolveTacticEvidence {
            kind: SolveTacticKind::XorFoldPreimage,
            status: SolveTacticStatus::Available,
            reason: "exact symbolic input xor-fold can feed bounded preimage solving".to_string(),
            recurrence: recurrence.clone(),
        }),
        (LoopFoldOperation::Add, LoopMemoryTermKind::InputRead) => Some(SolveTacticEvidence {
            kind: SolveTacticKind::AddFoldPreimage,
            status: SolveTacticStatus::Available,
            reason: "exact symbolic input add-fold can feed bounded preimage solving".to_string(),
            recurrence: recurrence.clone(),
        }),
        (_, LoopMemoryTermKind::TableRead) => Some(SolveTacticEvidence {
            kind: SolveTacticKind::ConcreteTableFold,
            status: SolveTacticStatus::EvidenceOnly,
            reason: "exact concrete table fold is available as constraint evidence".to_string(),
            recurrence: recurrence.clone(),
        }),
        (_, LoopMemoryTermKind::RuntimeBlobRead) => Some(SolveTacticEvidence {
            kind: SolveTacticKind::RuntimeBlobFold,
            status: SolveTacticStatus::EvidenceOnly,
            reason: "exact runtime-blob fold is available as constraint evidence".to_string(),
            recurrence: recurrence.clone(),
        }),
        (_, LoopMemoryTermKind::Unknown) => None,
    }
}

fn rotate_recurrence_reason(operation: LoopFoldOperation, term_kind: LoopMemoryTermKind) -> String {
    let operation = match operation {
        LoopFoldOperation::Add => "rotate-add",
        LoopFoldOperation::Xor => "rotate-xor",
    };
    match term_kind {
        LoopMemoryTermKind::InputRead => {
            format!(
                "exact symbolic input {operation} recurrence can feed bounded preimage solving when initial state is concrete"
            )
        }
        LoopMemoryTermKind::TableRead => {
            format!(
                "exact concrete-table {operation} recurrence is available as constraint evidence"
            )
        }
        LoopMemoryTermKind::RuntimeBlobRead => {
            format!("exact runtime-blob {operation} recurrence is available as constraint evidence")
        }
        LoopMemoryTermKind::Unknown => {
            format!("exact {operation} recurrence has unknown memory provenance")
        }
    }
}

pub fn verification_requirement_for_route_and_stats(
    route: &crate::TargetQueryRoutePlan,
    stats: &ExploreStats,
    constraint_graph: Option<&FinalConstraintGraph>,
) -> VerificationRequirement {
    let summary = evidence_summary_for_route_and_stats(route, stats, constraint_graph);
    if summary.reasons.is_empty() {
        return VerificationRequirement::NotRequired;
    }
    if matches!(route.target_plan, crate::TargetQueryPlan::Refuse { .. })
        || matches!(route.execution, TargetQueryExecutionRoute::Refuse { .. })
    {
        return VerificationRequirement::Refused {
            reasons: summary.reasons,
        };
    }
    if summary.requires_replay {
        VerificationRequirement::Required {
            reasons: summary.reasons,
        }
    } else {
        VerificationRequirement::NotRequired
    }
}

pub(crate) fn completion_from_stats(stats: &ExploreStats) -> QueryCompletion {
    if matches!(
        stats.execution_stop,
        Some(crate::SymExecutionStopReason::Cancelled)
    ) {
        QueryCompletion::Cancelled
    } else if matches!(
        stats.execution_stop,
        Some(crate::SymExecutionStopReason::DeadlineExceeded)
    ) {
        QueryCompletion::DeadlineExceeded
    } else if stats.timed_out || stats.max_states_exhausted {
        QueryCompletion::BudgetExhausted
    } else {
        QueryCompletion::Complete
    }
}

pub(crate) fn push_unique_reason(reasons: &mut Vec<String>, reason: impl Into<String>) {
    let reason = reason.into();
    if !reasons.iter().any(|existing| existing == &reason) {
        reasons.push(reason);
    }
}

pub(crate) fn collect_route_residual_reasons(
    route: &TargetQueryExecutionRoute,
    reasons: &mut Vec<String>,
) {
    match route {
        TargetQueryExecutionRoute::ContinuationSeeded { route, .. } => {
            push_unique_reason(reasons, "continuation_seeded_unverified");
            collect_route_residual_reasons(route, reasons);
        }
        TargetQueryExecutionRoute::ResidualOnly {
            reasons: route_reasons,
        } => {
            for reason in route_reasons {
                push_unique_reason(reasons, reason.clone());
            }
        }
        TargetQueryExecutionRoute::Refuse { reason } => {
            push_unique_reason(reasons, format!("refused: {reason}"));
        }
        TargetQueryExecutionRoute::ArtifactCondition { .. }
        | TargetQueryExecutionRoute::ArtifactMemoryOnly
        | TargetQueryExecutionRoute::DynamicTargetCompile { .. }
        | TargetQueryExecutionRoute::VmTargetCompile { .. } => {}
    }
}

pub(crate) fn solve_residual_reasons(
    route: &crate::TargetQueryRoutePlan,
    stats: &ExploreStats,
) -> Vec<String> {
    let mut reasons = Vec::new();
    match &route.target_plan {
        crate::TargetQueryPlan::Residual {
            reasons: plan_reasons,
        } => {
            for reason in plan_reasons {
                push_unique_reason(&mut reasons, reason.clone());
            }
        }
        crate::TargetQueryPlan::Refuse { reason } => {
            push_unique_reason(&mut reasons, format!("target refused: {reason}"));
        }
        crate::TargetQueryPlan::Ready { .. } | crate::TargetQueryPlan::Fallback { .. } => {}
    }
    collect_route_residual_reasons(&route.execution, &mut reasons);
    if stats.runtime_breakpoint_loop_summaries > 0 {
        push_unique_reason(&mut reasons, "runtime_breakpoint_loop_summary_residual");
    }
    if stats.runtime_loop_unknown_carried_state > 0 {
        push_unique_reason(&mut reasons, "runtime_loop_unknown_carried_state");
    }
    if stats.runtime_loop_budget_residuals > 0 {
        push_unique_reason(&mut reasons, "runtime_loop_iteration_budget");
    }
    if stats.runtime_loop_refusals > 0 {
        push_unique_reason(&mut reasons, "runtime_loop_refused");
    }
    if stats.runtime_missing_materialized_code > 0 {
        push_unique_reason(&mut reasons, "missing_runtime_materialized_code");
    }
    if stats.runtime_region_provenance_unknown > 0 {
        push_unique_reason(&mut reasons, "runtime_region_provenance_unknown");
    }
    reasons
}

pub(crate) fn residual_summary_blocks_solution_extraction(
    stats: &ExploreStats,
    residual_reasons: &[String],
) -> bool {
    stats.runtime_breakpoint_loop_summaries > 0
        && residual_reasons
            .iter()
            .any(|reason| reason == "runtime_breakpoint_loop_summary_residual")
}

pub(crate) fn solve_verification(
    target_reached_under_model: bool,
    solution_present: bool,
    residual_reasons: Vec<String>,
    model_validation: ModelValidation,
) -> SolveVerification {
    let candidate_solution_verified =
        solution_present && matches!(model_validation, ModelValidation::Verified);
    SolveVerification {
        target_reached_under_model,
        candidate_solution_verified,
        residual_reasons,
        model_validation,
    }
}

pub(crate) fn classify_solve_status(
    exact_unsat: bool,
    selected_path_index: Option<usize>,
    solution_present: bool,
    completion: QueryCompletion,
    verification: &SolveVerification,
    constraint_graph: &FinalConstraintGraph,
) -> SolveStatus {
    if exact_unsat {
        return SolveStatus::Unsat;
    }
    let has_exact_final_constraints = constraint_graph.has_exact_constraints();
    let has_model_conditioned_final_constraints =
        constraint_graph.model_conditioned_constraint_count() > 0;
    if selected_path_index.is_some()
        && !verification.residual_reasons.is_empty()
        && !verification.candidate_solution_verified
    {
        if has_exact_final_constraints
            && !matches!(
                verification.model_validation,
                ModelValidation::Failed { .. }
            )
        {
            return SolveStatus::Candidate;
        }
        return match verification.model_validation {
            ModelValidation::Failed { .. } => SolveStatus::Unverified,
            ModelValidation::NotRequired | ModelValidation::Unavailable { .. } => {
                SolveStatus::ResidualReachable
            }
            ModelValidation::Verified => SolveStatus::Solved,
        };
    }
    match (
        selected_path_index,
        solution_present,
        completion,
        &verification.model_validation,
    ) {
        (Some(_), true, _, ModelValidation::Unavailable { .. }) if has_exact_final_constraints => {
            SolveStatus::Candidate
        }
        (
            Some(_),
            true,
            _,
            ModelValidation::Failed { .. } | ModelValidation::Unavailable { .. },
        ) => SolveStatus::Unverified,
        (Some(_), true, _, ModelValidation::NotRequired | ModelValidation::Verified) => {
            if has_model_conditioned_final_constraints && !has_exact_final_constraints {
                SolveStatus::Unverified
            } else {
                SolveStatus::Solved
            }
        }
        (_, _, QueryCompletion::Cancelled | QueryCompletion::DeadlineExceeded, _) => {
            SolveStatus::Unknown
        }
        (None, _, QueryCompletion::BudgetExhausted, _) => SolveStatus::BudgetExhausted,
        (None, _, QueryCompletion::Complete, _) => SolveStatus::Unsat,
        (Some(_), false, QueryCompletion::BudgetExhausted, _) => SolveStatus::BudgetExhausted,
        (Some(_), false, _, _) => SolveStatus::Unknown,
    }
}

fn concrete_value_to_width(value: u64, bits: u32) -> u64 {
    if bits >= 64 {
        value
    } else if bits == 0 {
        0
    } else {
        value & ((1u64 << bits) - 1)
    }
}

fn little_endian_bytes_to_u64(bytes: &[u8]) -> Option<u64> {
    if bytes.len() > 8 {
        return None;
    }
    let mut value = 0u64;
    for (index, byte) in bytes.iter().enumerate() {
        value |= (*byte as u64) << (index * 8);
    }
    Some(value)
}

fn solution_constraints_for_state<'ctx>(
    state: &SymState<'ctx>,
    solution: &SolvedPath,
) -> Vec<(crate::SymValue<'ctx>, u64)> {
    let mut constraints = Vec::new();
    for (name, value) in &solution.inputs {
        if let Some(symbolic) = state.symbolic_inputs().get(name) {
            constraints.push((
                symbolic.clone(),
                concrete_value_to_width(*value, symbolic.bits()),
            ));
        }
    }
    for (input_name, bytes) in &solution.input_buffers {
        for input in state.symbolic_fd_inputs().values() {
            if input.name != *input_name {
                continue;
            }
            for (byte, value) in input.bytes.iter().zip(bytes.iter()) {
                constraints.push((byte.clone(), *value as u64));
            }
        }
    }
    for (region_name, bytes) in &solution.memory {
        let Some(value) = little_endian_bytes_to_u64(bytes) else {
            continue;
        };
        if let Some(region) = state
            .symbolic_memory()
            .iter()
            .find(|region| region.name == *region_name)
        {
            constraints.push((
                region.value.clone(),
                concrete_value_to_width(value, region.value.bits()),
            ));
        }
    }
    constraints
}

fn apply_solution_constraints<'ctx>(
    state: &mut SymState<'ctx>,
    solution: &SolvedPath,
) -> Result<usize, String> {
    let constraints = solution_constraints_for_state(state, solution);
    if constraints.is_empty()
        && (!solution.inputs.is_empty()
            || !solution.input_buffers.is_empty()
            || !solution.memory.is_empty())
    {
        return Err("candidate model did not match validation seed inputs".to_string());
    }
    let count = constraints.len();
    for (value, concrete) in constraints {
        state.constrain_eq(&value, concrete);
    }
    Ok(count)
}

fn validate_solution_with_lifted_semantics<'ctx>(
    explorer: &mut PathExplorer<'ctx>,
    func: &SsaArtifact,
    scope: Option<&PreparedFunctionScope>,
    mut initial_state: SymState<'ctx>,
    target_addr: u64,
    solution: &SolvedPath,
) -> ModelValidation {
    match apply_solution_constraints(&mut initial_state, solution) {
        Ok(_) => {}
        Err(reason) => return ModelValidation::Unavailable { reason },
    }

    let (found, replay_stats) = explorer.with_isolated_stats(|explorer| {
        let previous_target_guided = explorer.target_guided_queries_enabled();
        explorer.set_target_guided_queries(true);
        let found = explorer.with_residual_runtime_loop_summaries(false, |explorer| {
            explorer.find_path_to_in_scope(func, scope, initial_state, target_addr)
        });
        explorer.set_target_guided_queries(previous_target_guided);
        found
    });

    match found {
        Some(path) if path.final_pc() == target_addr => ModelValidation::Verified,
        Some(path) => ModelValidation::Failed {
            reason: format!(
                "lifted replay stopped at 0x{:x} instead of 0x{:x}",
                path.final_pc(),
                target_addr
            ),
        },
        None if replay_stats.timed_out || replay_stats.max_states_exhausted => {
            ModelValidation::Unavailable {
                reason: "lifted replay validation exhausted budget".to_string(),
            }
        }
        None => ModelValidation::Failed {
            reason: "lifted replay did not reach target with candidate model".to_string(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ModelValidation, SolveTacticKind, SolveTacticStatus, classify_solve_status,
        evidence_summary_for_route_and_stats, residual_summary_blocks_solution_extraction,
        solve_residual_reasons, solve_tactics_for_exact_folds, solve_tactics_for_exact_recurrences,
        solve_verification,
    };
    use crate::{
        ExactLoopFoldEvidence, ExactLoopRecurrenceEvidence, FinalConstraint, FinalConstraintGraph,
        FinalConstraintPrecision, FinalConstraintSource, LoopFoldOperation, LoopMemoryTerm,
        LoopMemoryTermKind, LoopRotateDirection, QueryCompletion, QueryGuidanceMode,
        RecurrenceAggregateConstraint, SolveStatus, TargetQueryExecutionRoute, TargetQueryPlan,
        TargetQueryRoutePlan,
    };

    fn exact_graph() -> FinalConstraintGraph {
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 4,
            accumulator: "RBX_2".to_string(),
            bits: 64,
            operation: LoopFoldOperation::Xor,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_2".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(4),
            },
        };
        FinalConstraintGraph {
            constraints: vec![FinalConstraint::RecurrenceEquals(
                RecurrenceAggregateConstraint {
                    recurrence: fold.into(),
                    target: 0x41,
                    bits: 64,
                    source: FinalConstraintSource::TerminalCompareExact,
                    precision: FinalConstraintPrecision::Exact,
                    reasons: Vec::new(),
                },
            )],
            input_byte_constraints: Vec::new(),
            input_length_constraints: Vec::new(),
            refusals: Vec::new(),
        }
    }

    #[test]
    fn residual_runtime_loop_summary_cannot_be_solved() {
        let route = TargetQueryRoutePlan {
            target_plan: TargetQueryPlan::Ready {
                mode: QueryGuidanceMode::NarrowOnly,
            },
            execution: TargetQueryExecutionRoute::DynamicTargetCompile {
                reason: "large cfg".to_string(),
                mode: QueryGuidanceMode::NarrowOnly,
            },
        };
        let stats = crate::path::ExploreStats {
            runtime_breakpoint_loop_summaries: 1,
            ..crate::path::ExploreStats::default()
        };
        let reasons = solve_residual_reasons(&route, &stats);
        assert_eq!(
            reasons,
            vec!["runtime_breakpoint_loop_summary_residual".to_string()]
        );
        assert!(residual_summary_blocks_solution_extraction(
            &stats, &reasons
        ));
        let verification = solve_verification(
            true,
            true,
            reasons,
            ModelValidation::Unavailable {
                reason: "residual/runtime evidence requires concrete replay validation".to_string(),
            },
        );

        assert_eq!(
            classify_solve_status(
                false,
                Some(0),
                true,
                QueryCompletion::Complete,
                &verification,
                &FinalConstraintGraph::default(),
            ),
            SolveStatus::ResidualReachable
        );
        assert!(!verification.candidate_solution_verified);
        assert!(matches!(
            verification.model_validation,
            ModelValidation::Unavailable { .. }
        ));
    }

    #[test]
    fn residual_route_cannot_be_solved() {
        let route = TargetQueryRoutePlan {
            target_plan: TargetQueryPlan::Residual {
                reasons: vec!["LargeCfg".to_string()],
            },
            execution: TargetQueryExecutionRoute::ResidualOnly {
                reasons: vec!["continuation-seeded runtime execution".to_string()],
            },
        };
        let reasons = solve_residual_reasons(&route, &crate::path::ExploreStats::default());
        let verification = solve_verification(
            true,
            true,
            reasons,
            ModelValidation::Unavailable {
                reason: "residual/runtime evidence requires concrete replay validation".to_string(),
            },
        );

        assert_eq!(
            classify_solve_status(
                false,
                Some(0),
                true,
                QueryCompletion::Complete,
                &verification,
                &FinalConstraintGraph::default(),
            ),
            SolveStatus::ResidualReachable
        );
    }

    #[test]
    fn verified_residual_route_can_be_solved() {
        let verification = solve_verification(
            true,
            true,
            vec!["continuation_seeded_unverified".to_string()],
            ModelValidation::Verified,
        );

        assert_eq!(
            classify_solve_status(
                false,
                Some(0),
                true,
                QueryCompletion::Complete,
                &verification,
                &exact_graph(),
            ),
            SolveStatus::Solved
        );
        assert!(verification.candidate_solution_verified);
    }

    #[test]
    fn failed_residual_replay_is_unverified() {
        let verification = solve_verification(
            true,
            true,
            vec!["continuation_seeded_unverified".to_string()],
            ModelValidation::Failed {
                reason: "candidate rejected".to_string(),
            },
        );

        assert_eq!(
            classify_solve_status(
                false,
                Some(0),
                true,
                QueryCompletion::Complete,
                &verification,
                &exact_graph(),
            ),
            SolveStatus::Unverified
        );
        assert!(!verification.candidate_solution_verified);
    }

    #[test]
    fn exact_final_constraint_without_replay_proof_is_candidate() {
        let verification = solve_verification(
            true,
            true,
            Vec::new(),
            ModelValidation::Unavailable {
                reason: "lifted replay validation exhausted budget".to_string(),
            },
        );

        assert_eq!(
            classify_solve_status(
                false,
                Some(0),
                true,
                QueryCompletion::Complete,
                &verification,
                &exact_graph(),
            ),
            SolveStatus::Candidate
        );
    }

    #[test]
    fn exact_input_fold_evidence_enables_preimage_tactic_without_downgrade() {
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 4,
            accumulator: "RBX_2".to_string(),
            bits: 64,
            operation: LoopFoldOperation::Xor,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_2".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(4),
            },
        };
        let tactics = solve_tactics_for_exact_folds(std::slice::from_ref(&fold));
        assert_eq!(tactics.len(), 1);
        assert_eq!(tactics[0].kind, SolveTacticKind::XorFoldPreimage);
        assert_eq!(tactics[0].status, SolveTacticStatus::Available);
        assert_eq!(
            tactics[0].recurrence,
            ExactLoopRecurrenceEvidence::from(fold.clone())
        );

        let route = TargetQueryRoutePlan {
            target_plan: TargetQueryPlan::Ready {
                mode: QueryGuidanceMode::NarrowOnly,
            },
            execution: TargetQueryExecutionRoute::DynamicTargetCompile {
                reason: "test".to_string(),
                mode: QueryGuidanceMode::NarrowOnly,
            },
        };
        let stats = crate::path::ExploreStats {
            runtime_loop_exact_recurrences: vec![ExactLoopRecurrenceEvidence::from(fold.clone())],
            runtime_loop_exact_folds: vec![fold],
            ..crate::path::ExploreStats::default()
        };
        let evidence = evidence_summary_for_route_and_stats(&route, &stats, None);
        assert_eq!(evidence.precision, crate::FactPrecision::Exact);
        assert!(!evidence.requires_replay);
        assert!(evidence.reasons.is_empty());
        assert_eq!(evidence.exact_loop_recurrences.len(), 1);
        assert_eq!(evidence.exact_loop_folds.len(), 1);
        assert_eq!(evidence.tactics.len(), 1);
    }

    #[test]
    fn exact_rotate_input_recurrence_is_reported_as_available_tactic() {
        let recurrence = ExactLoopRecurrenceEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 4,
            accumulator: "RBX_2".to_string(),
            initial: "RBX_1".to_string(),
            bits: 8,
            kind: crate::ExactLoopRecurrenceKind::RotateMix {
                direction: LoopRotateDirection::Left,
                amount: 3,
                operation: LoopFoldOperation::Xor,
                term: LoopMemoryTerm {
                    kind: LoopMemoryTermKind::InputRead,
                    addr: "RDI_2".to_string(),
                    bytes: 1,
                    base: Some(0x7000),
                    stride: Some(1),
                    region: Some("argv1".to_string()),
                    region_base: Some(0x7000),
                    region_size: Some(4),
                },
            },
        };
        let tactics = solve_tactics_for_exact_recurrences(std::slice::from_ref(&recurrence));
        assert_eq!(tactics.len(), 1);
        assert_eq!(tactics[0].kind, SolveTacticKind::RotateXorRecurrence);
        assert_eq!(tactics[0].status, SolveTacticStatus::Available);
        assert_eq!(tactics[0].recurrence, recurrence);
    }
}
