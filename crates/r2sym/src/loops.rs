//! Runtime loop recognition and summary construction.
//!
//! This module owns loop-shape policy for symex. Path exploration executes
//! summaries, while verification decides whether summarized evidence can prove
//! a solve.

use std::collections::{HashMap, HashSet};

use r2il::SpaceId;
use r2ssa::{FunctionSSABlock, SSAOp, SSAVar, SsaArtifact};
use z3::Context;

use crate::{SymState, SymValue};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopSummaryKind {
    Exact,
    BoundedExact,
    Residual,
    Refused,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopVarRole {
    InductionCounter,
    Accumulator,
    Pointer,
    MemoryEffect,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopCarriedVar {
    pub name: String,
    pub bits: u32,
    pub role: LoopVarRole,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopTransitionExpr {
    Identity(String),
    AddConst {
        var: String,
        value: u64,
    },
    AffineConst {
        var: String,
        multiplier: u64,
        addend: u64,
    },
    XorConst {
        var: String,
        value: u64,
    },
    XorVar {
        lhs: String,
        rhs: String,
    },
    AddVar {
        lhs: String,
        rhs: String,
    },
    Load {
        addr: String,
        bytes: u32,
    },
    TableRead(LoopMemoryTerm),
    RotateMix {
        var: String,
        direction: LoopRotateDirection,
        amount: u32,
        operation: LoopFoldOperation,
        term: LoopMemoryTerm,
    },
    Store {
        addr: String,
        value: String,
    },
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopMemoryTermKind {
    TableRead,
    InputRead,
    RuntimeBlobRead,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopMemoryTerm {
    pub kind: LoopMemoryTermKind,
    pub addr: String,
    pub bytes: u32,
    pub base: Option<u64>,
    pub stride: Option<u64>,
    pub region: Option<String>,
    pub region_base: Option<u64>,
    pub region_size: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopRecurrenceKind {
    Identity,
    AddConst(u64),
    SubConst(u64),
    AffineConst {
        multiplier: u64,
        addend: u64,
    },
    XorConst(u64),
    AddMemoryFold(LoopMemoryTerm),
    XorMemoryFold(LoopMemoryTerm),
    RotateMix {
        direction: LoopRotateDirection,
        amount: u32,
        operation: LoopFoldOperation,
        term: LoopMemoryTerm,
    },
    Unsupported(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopFoldOperation {
    Add,
    Xor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopRotateDirection {
    Left,
    Right,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExactLoopRecurrenceKind {
    AddConst(u64),
    SubConst(u64),
    AffineConst {
        multiplier: u64,
        addend: u64,
    },
    XorConst(u64),
    Fold {
        operation: LoopFoldOperation,
        term: LoopMemoryTerm,
    },
    RotateMix {
        direction: LoopRotateDirection,
        amount: u32,
        operation: LoopFoldOperation,
        term: LoopMemoryTerm,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactLoopRecurrenceEvidence {
    pub header: u64,
    pub exit_target: u64,
    pub iterations: u64,
    pub accumulator: String,
    pub initial: String,
    pub bits: u32,
    pub kind: ExactLoopRecurrenceKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExactLoopFoldEvidence {
    pub header: u64,
    pub exit_target: u64,
    pub iterations: u64,
    pub accumulator: String,
    pub bits: u32,
    pub operation: LoopFoldOperation,
    pub term: LoopMemoryTerm,
}

impl ExactLoopRecurrenceEvidence {
    pub fn as_fold(&self) -> Option<ExactLoopFoldEvidence> {
        let ExactLoopRecurrenceKind::Fold { operation, term } = &self.kind else {
            return None;
        };
        Some(ExactLoopFoldEvidence {
            header: self.header,
            exit_target: self.exit_target,
            iterations: self.iterations,
            accumulator: self.accumulator.clone(),
            bits: self.bits,
            operation: *operation,
            term: term.clone(),
        })
    }
}

impl From<ExactLoopFoldEvidence> for ExactLoopRecurrenceEvidence {
    fn from(value: ExactLoopFoldEvidence) -> Self {
        Self {
            header: value.header,
            exit_target: value.exit_target,
            iterations: value.iterations,
            accumulator: value.accumulator,
            initial: String::new(),
            bits: value.bits,
            kind: ExactLoopRecurrenceKind::Fold {
                operation: value.operation,
                term: value.term,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopRecurrence {
    pub phi: String,
    pub initial: String,
    pub latch: String,
    pub bits: u32,
    pub role: LoopVarRole,
    pub kind: LoopRecurrenceKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopTransitionSystem {
    pub header: u64,
    pub exit_target: u64,
    pub iterations: u64,
    pub counter: String,
    pub counter_start: u64,
    pub carried_state: Vec<LoopCarriedVar>,
    pub recurrences: Vec<LoopRecurrence>,
    pub reasons: Vec<String>,
}

impl LoopTransitionSystem {
    pub fn is_exact(&self) -> bool {
        self.reasons.is_empty()
            && self
                .recurrences
                .iter()
                .all(|recurrence| !matches!(recurrence.kind, LoopRecurrenceKind::Unsupported(_)))
    }
}

#[derive(Debug)]
pub struct LoopSummary<'ctx> {
    pub kind: LoopSummaryKind,
    pub header: u64,
    pub exit_target: Option<u64>,
    pub iterations: Option<u64>,
    pub carried_state: Vec<LoopCarriedVar>,
    pub transitions: Vec<LoopTransitionExpr>,
    pub exact_recurrences: Vec<ExactLoopRecurrenceEvidence>,
    pub exact_folds: Vec<ExactLoopFoldEvidence>,
    pub reasons: Vec<String>,
    pub resulting_state: Option<SymState<'ctx>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeLoopBranch {
    pub counter: SSAVar,
    pub threshold: u64,
    pub target: u64,
}

pub fn bounded_exact_summary<'ctx>(
    header: u64,
    branch: &RuntimeLoopBranch,
    iterations: u64,
    resulting_state: SymState<'ctx>,
) -> LoopSummary<'ctx> {
    LoopSummary {
        kind: LoopSummaryKind::BoundedExact,
        header,
        exit_target: Some(branch.target),
        iterations: Some(iterations),
        carried_state: Vec::new(),
        transitions: Vec::new(),
        exact_recurrences: Vec::new(),
        exact_folds: Vec::new(),
        reasons: Vec::new(),
        resulting_state: Some(resulting_state),
    }
}

pub fn summarize_residual_runtime_loop<'ctx>(
    ctx: &'ctx Context,
    block_func: &SsaArtifact,
    block: &FunctionSSABlock,
    state: &SymState<'ctx>,
    branch: &RuntimeLoopBranch,
    residual_enabled: bool,
) -> LoopSummary<'ctx> {
    if state.pending_exception().is_none() {
        return refused(block.addr, Some(branch.target), "no_pending_exception");
    }
    if !residual_enabled {
        return refused(block.addr, Some(branch.target), "residual_disabled");
    }
    if state.runtime().runtime_regions.is_empty() {
        return residual(
            block.addr,
            Some(branch.target),
            "runtime_loop_missing_materialized_region",
        );
    }
    if block_func.get_block(branch.target).is_none() {
        return residual(
            block.addr,
            Some(branch.target),
            "runtime_loop_missing_exit_target",
        );
    }

    let counter_bits = branch.counter.size.saturating_mul(8).max(1);
    let counter_key = branch.counter.display_name();
    let Some(counter) = concrete_state_var_at_block_entry(state, block, &branch.counter) else {
        return residual(
            block.addr,
            Some(branch.target),
            "runtime_loop_unknown_counter",
        );
    };
    if counter >= branch.threshold {
        return refused(
            block.addr,
            Some(branch.target),
            "runtime_loop_counter_past_threshold",
        );
    }
    let Some(iterations) = branch.threshold.checked_sub(counter) else {
        return refused(
            block.addr,
            Some(branch.target),
            "runtime_loop_counter_past_threshold",
        );
    };
    if iterations < 8 {
        return refused(
            block.addr,
            Some(branch.target),
            "runtime_loop_too_small_to_summarize",
        );
    }

    let transition_system =
        derive_loop_transition_system(block_func, block, state, branch, counter, iterations);
    if transition_system.is_exact()
        && let Some(summary) = apply_exact_transition_system(ctx, state, &transition_system)
    {
        return summary;
    }

    let carried_state = discover_loop_carried_state(block, Some(&branch.counter));
    if carried_state
        .iter()
        .all(|var| var.role == LoopVarRole::InductionCounter)
    {
        return residual(
            block.addr,
            Some(branch.target),
            "runtime_loop_unknown_carried_state",
        );
    }
    if carried_state
        .iter()
        .any(|var| var.role == LoopVarRole::Unknown)
    {
        let mut summary = residual(
            block.addr,
            Some(branch.target),
            "runtime_loop_unknown_carried_state",
        );
        summary.carried_state = carried_state;
        summary.transitions = discover_loop_transitions(block, &summary.carried_state);
        return summary;
    }

    let transitions = discover_loop_transitions(block, &carried_state);
    let mut summarized = state.fork();
    summarized.set_register(
        &counter_key,
        SymValue::concrete(branch.threshold, counter_bits),
    );
    for carried in &carried_state {
        if carried.role == LoopVarRole::InductionCounter {
            continue;
        }
        let summary_name = format!(
            "runtime_loop_summary_{:x}_{:x}_{:x}_{}",
            block.addr, counter, branch.threshold, carried.name
        );
        summarized.set_register(
            &carried.name,
            SymValue::new_symbolic(ctx, &summary_name, carried.bits),
        );
    }
    if !summarized.set_loop_summary_exit(block.addr, branch.target) {
        return refused(
            block.addr,
            Some(branch.target),
            "runtime_loop_execution_domain_unresolved",
        );
    }

    LoopSummary {
        kind: LoopSummaryKind::Residual,
        header: block.addr,
        exit_target: Some(branch.target),
        iterations: Some(iterations),
        carried_state,
        transitions,
        exact_recurrences: Vec::new(),
        exact_folds: Vec::new(),
        reasons: vec!["runtime_loop_summary_residual".to_string()],
        resulting_state: Some(summarized),
    }
}

pub fn derive_loop_transition_system<'ctx>(
    artifact: &SsaArtifact,
    block: &FunctionSSABlock,
    state: &SymState<'ctx>,
    branch: &RuntimeLoopBranch,
    counter: u64,
    iterations: u64,
) -> LoopTransitionSystem {
    let carried_state = discover_loop_carried_state(block, Some(&branch.counter));
    let mut reasons = Vec::new();
    let mut recurrences = Vec::new();

    if block_has_memory_writes(block) {
        push_unique_reason(
            &mut reasons,
            "runtime_loop_memory_write_transition_unsupported",
        );
    }
    if block_has_non_ram_memory(block) {
        push_unique_reason(&mut reasons, "runtime_loop_non_ram_memory_unsupported");
    }

    if state_value_at_block_entry(state, block, &branch.counter).is_none() {
        push_unique_reason(&mut reasons, "runtime_loop_unknown_counter");
    }

    if counter.saturating_add(iterations) != branch.threshold {
        push_unique_reason(&mut reasons, "runtime_loop_non_affine_exit_count");
    }

    for carried in &carried_state {
        let Some(phi) = block
            .phis
            .iter()
            .find(|phi| phi.dst.display_name() == carried.name)
        else {
            push_unique_reason(
                &mut reasons,
                format!("runtime_loop_missing_phi:{}", carried.name),
            );
            continue;
        };
        let Some(initial_source) = selected_phi_source(phi, state.prev_pc()) else {
            push_unique_reason(
                &mut reasons,
                format!("runtime_loop_missing_initial_source:{}", carried.name),
            );
            continue;
        };
        let Some(latch_source) = latch_source_for_phi(phi, state.prev_pc()) else {
            push_unique_reason(
                &mut reasons,
                format!("runtime_loop_missing_latch_source:{}", carried.name),
            );
            continue;
        };
        if state_value_at_block_entry(state, block, &phi.dst).is_none() {
            push_unique_reason(
                &mut reasons,
                format!("runtime_loop_unknown_initial:{}", carried.name),
            );
            continue;
        }
        let recurrence =
            recurrence_for_latch(artifact, block, state, &phi.dst, latch_source, carried.role);
        let recurrence = LoopRecurrence {
            initial: initial_source.display_name(),
            ..recurrence
        };
        if matches!(recurrence.kind, LoopRecurrenceKind::Unsupported(_)) {
            push_unique_reason(
                &mut reasons,
                format!("runtime_loop_unsupported_recurrence:{}", carried.name),
            );
        }
        if let Some(term) = recurrence_memory_term(&recurrence.kind) {
            if term.base.is_none() || term.stride.is_none() {
                push_unique_reason(
                    &mut reasons,
                    format!("runtime_loop_unknown_memory_term:{}", carried.name),
                );
            }
            if term.kind == LoopMemoryTermKind::Unknown {
                push_unique_reason(
                    &mut reasons,
                    format!("runtime_loop_unknown_memory_provenance:{}", carried.name),
                );
            }
            if !memory_term_has_exact_bounds(state, term, iterations) {
                push_unique_reason(
                    &mut reasons,
                    format!("runtime_loop_memory_bounds_unknown:{}", carried.name),
                );
            }
        }
        recurrences.push(recurrence);
    }

    recurrences.sort_by(|lhs, rhs| lhs.phi.cmp(&rhs.phi));
    LoopTransitionSystem {
        header: block.addr,
        exit_target: branch.target,
        iterations,
        counter: branch.counter.display_name(),
        counter_start: counter,
        carried_state,
        recurrences,
        reasons,
    }
}

pub fn runtime_counter_threshold_branch(block: &FunctionSSABlock) -> Option<RuntimeLoopBranch> {
    let mut copies: HashMap<String, SSAVar> = HashMap::new();
    let mut unsigned_less_defs: HashMap<String, (SSAVar, u64)> = HashMap::new();
    let mut inverted_less_defs: HashMap<String, (SSAVar, u64)> = HashMap::new();

    for op in &block.ops {
        match op {
            SSAOp::Copy { dst, src } => {
                copies.insert(dst.display_name(), resolve_copy_source(src, &copies));
            }
            SSAOp::IntLess { dst, a, b } => {
                if let Some(threshold) = parse_const_var(b) {
                    unsigned_less_defs.insert(
                        dst.display_name(),
                        (resolve_copy_source(a, &copies), threshold),
                    );
                }
            }
            SSAOp::BoolNot { dst, src } => {
                if let Some((counter, threshold)) = unsigned_less_defs.get(&src.display_name()) {
                    inverted_less_defs.insert(dst.display_name(), (counter.clone(), *threshold));
                }
            }
            SSAOp::CBranch { target, cond } => {
                let target = parse_address_var(target)?;
                if target <= block.addr.saturating_add(block.size as u64) {
                    return None;
                }
                let (counter, threshold) = inverted_less_defs.get(&cond.display_name())?;
                return Some(RuntimeLoopBranch {
                    counter: counter.clone(),
                    threshold: *threshold,
                    target,
                });
            }
            _ => {}
        }
    }

    None
}

pub fn exact_recurrence_evidence_from_system(
    system: &LoopTransitionSystem,
) -> Vec<ExactLoopRecurrenceEvidence> {
    if !system.is_exact() {
        return Vec::new();
    }
    let mut evidence = system
        .recurrences
        .iter()
        .filter_map(|recurrence| match &recurrence.kind {
            LoopRecurrenceKind::AddConst(value) => Some(ExactLoopRecurrenceEvidence {
                header: system.header,
                exit_target: system.exit_target,
                iterations: system.iterations,
                accumulator: recurrence.phi.clone(),
                initial: recurrence.initial.clone(),
                bits: recurrence.bits,
                kind: ExactLoopRecurrenceKind::AddConst(*value),
            }),
            LoopRecurrenceKind::SubConst(value) => Some(ExactLoopRecurrenceEvidence {
                header: system.header,
                exit_target: system.exit_target,
                iterations: system.iterations,
                accumulator: recurrence.phi.clone(),
                initial: recurrence.initial.clone(),
                bits: recurrence.bits,
                kind: ExactLoopRecurrenceKind::SubConst(*value),
            }),
            LoopRecurrenceKind::AffineConst { multiplier, addend } => {
                Some(ExactLoopRecurrenceEvidence {
                    header: system.header,
                    exit_target: system.exit_target,
                    iterations: system.iterations,
                    accumulator: recurrence.phi.clone(),
                    initial: recurrence.initial.clone(),
                    bits: recurrence.bits,
                    kind: ExactLoopRecurrenceKind::AffineConst {
                        multiplier: *multiplier,
                        addend: *addend,
                    },
                })
            }
            LoopRecurrenceKind::XorConst(value) => Some(ExactLoopRecurrenceEvidence {
                header: system.header,
                exit_target: system.exit_target,
                iterations: system.iterations,
                accumulator: recurrence.phi.clone(),
                initial: recurrence.initial.clone(),
                bits: recurrence.bits,
                kind: ExactLoopRecurrenceKind::XorConst(*value),
            }),
            LoopRecurrenceKind::AddMemoryFold(term) => Some(ExactLoopRecurrenceEvidence {
                header: system.header,
                exit_target: system.exit_target,
                iterations: system.iterations,
                accumulator: recurrence.phi.clone(),
                initial: recurrence.initial.clone(),
                bits: recurrence.bits,
                kind: ExactLoopRecurrenceKind::Fold {
                    operation: LoopFoldOperation::Add,
                    term: term.clone(),
                },
            }),
            LoopRecurrenceKind::XorMemoryFold(term) => Some(ExactLoopRecurrenceEvidence {
                header: system.header,
                exit_target: system.exit_target,
                iterations: system.iterations,
                accumulator: recurrence.phi.clone(),
                initial: recurrence.initial.clone(),
                bits: recurrence.bits,
                kind: ExactLoopRecurrenceKind::Fold {
                    operation: LoopFoldOperation::Xor,
                    term: term.clone(),
                },
            }),
            LoopRecurrenceKind::RotateMix {
                direction,
                amount,
                operation,
                term,
            } => Some(ExactLoopRecurrenceEvidence {
                header: system.header,
                exit_target: system.exit_target,
                iterations: system.iterations,
                accumulator: recurrence.phi.clone(),
                initial: recurrence.initial.clone(),
                bits: recurrence.bits,
                kind: ExactLoopRecurrenceKind::RotateMix {
                    direction: *direction,
                    amount: *amount,
                    operation: *operation,
                    term: term.clone(),
                },
            }),
            _ => None,
        })
        .collect::<Vec<_>>();
    evidence.sort_by(|lhs, rhs| {
        (
            lhs.header,
            lhs.exit_target,
            lhs.accumulator.as_str(),
            recurrence_sort_key(&lhs.kind),
        )
            .cmp(&(
                rhs.header,
                rhs.exit_target,
                rhs.accumulator.as_str(),
                recurrence_sort_key(&rhs.kind),
            ))
    });
    evidence
}

fn recurrence_sort_key(kind: &ExactLoopRecurrenceKind) -> String {
    match kind {
        ExactLoopRecurrenceKind::AddConst(value) => format!("add_const:{value:x}"),
        ExactLoopRecurrenceKind::SubConst(value) => format!("sub_const:{value:x}"),
        ExactLoopRecurrenceKind::AffineConst { multiplier, addend } => {
            format!("affine:{multiplier:x}:{addend:x}")
        }
        ExactLoopRecurrenceKind::XorConst(value) => format!("xor_const:{value:x}"),
        ExactLoopRecurrenceKind::Fold { operation, term } => {
            format!("fold:{operation:?}:{}", term.addr)
        }
        ExactLoopRecurrenceKind::RotateMix {
            direction,
            amount,
            operation,
            term,
        } => format!(
            "rotate_mix:{direction:?}:{amount}:{operation:?}:{}",
            term.addr
        ),
    }
}

fn recurrence_memory_term(kind: &LoopRecurrenceKind) -> Option<&LoopMemoryTerm> {
    match kind {
        LoopRecurrenceKind::AddMemoryFold(term)
        | LoopRecurrenceKind::XorMemoryFold(term)
        | LoopRecurrenceKind::RotateMix { term, .. } => Some(term),
        _ => None,
    }
}

pub fn exact_fold_evidence_from_recurrences(
    recurrences: &[ExactLoopRecurrenceEvidence],
) -> Vec<ExactLoopFoldEvidence> {
    let mut folds = recurrences
        .iter()
        .filter_map(ExactLoopRecurrenceEvidence::as_fold)
        .collect::<Vec<_>>();
    folds.sort_by(|lhs, rhs| {
        (
            lhs.header,
            lhs.exit_target,
            lhs.accumulator.as_str(),
            lhs.term.addr.as_str(),
        )
            .cmp(&(
                rhs.header,
                rhs.exit_target,
                rhs.accumulator.as_str(),
                rhs.term.addr.as_str(),
            ))
    });
    folds
}

pub fn discover_loop_carried_state(
    block: &FunctionSSABlock,
    counter: Option<&SSAVar>,
) -> Vec<LoopCarriedVar> {
    let mut vars = Vec::new();
    let counter_name = counter.map(SSAVar::display_name);
    for phi in &block.phis {
        let phi_name = phi.dst.display_name();
        let latch_sources = phi
            .sources
            .iter()
            .map(|(_, source)| source)
            .filter(|source| source.display_name() != phi_name)
            .collect::<Vec<_>>();
        if latch_sources.is_empty() {
            continue;
        }
        let role = if counter_name.as_deref() == Some(phi_name.as_str())
            || latch_sources
                .iter()
                .any(|source| counter_name.as_deref() == Some(source.display_name().as_str()))
        {
            LoopVarRole::InductionCounter
        } else if used_as_memory_value(block, &phi.dst, &latch_sources) {
            LoopVarRole::MemoryEffect
        } else if used_as_memory_addr(block, &phi.dst, &latch_sources) {
            LoopVarRole::Pointer
        } else if latch_update_depends_on_phi(block, &phi.dst, &latch_sources) {
            LoopVarRole::Accumulator
        } else {
            LoopVarRole::Unknown
        };
        vars.push(LoopCarriedVar {
            name: phi_name,
            bits: phi.dst.size.saturating_mul(8).max(1),
            role,
        });
    }
    vars.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
    vars
}

pub fn concrete_state_var_at_block_entry<'ctx>(
    state: &SymState<'ctx>,
    block: &FunctionSSABlock,
    var: &SSAVar,
) -> Option<u64> {
    let phi = block
        .phis
        .iter()
        .find(|phi| phi.dst.display_name() == var.display_name());
    if let Some(phi) = phi {
        let prev_pc = state.prev_pc()?;
        return phi
            .sources
            .iter()
            .find(|(pred, _)| *pred == prev_pc)
            .and_then(|(_, source)| concrete_state_var(state, source));
    }

    concrete_state_var(state, var)
}

fn refused<'ctx>(header: u64, exit_target: Option<u64>, reason: &str) -> LoopSummary<'ctx> {
    LoopSummary {
        kind: LoopSummaryKind::Refused,
        header,
        exit_target,
        iterations: None,
        carried_state: Vec::new(),
        transitions: Vec::new(),
        exact_recurrences: Vec::new(),
        exact_folds: Vec::new(),
        reasons: vec![reason.to_string()],
        resulting_state: None,
    }
}

fn residual<'ctx>(header: u64, exit_target: Option<u64>, reason: &str) -> LoopSummary<'ctx> {
    LoopSummary {
        kind: LoopSummaryKind::Residual,
        header,
        exit_target,
        iterations: None,
        carried_state: Vec::new(),
        transitions: Vec::new(),
        exact_recurrences: Vec::new(),
        exact_folds: Vec::new(),
        reasons: vec![reason.to_string()],
        resulting_state: None,
    }
}

fn apply_exact_transition_system<'ctx>(
    ctx: &'ctx Context,
    state: &SymState<'ctx>,
    system: &LoopTransitionSystem,
) -> Option<LoopSummary<'ctx>> {
    let mut summarized = state.fork();
    let counter_bits = state.get_register_sized(&system.counter, 64).bits().max(1);
    summarized.set_register(
        &system.counter,
        SymValue::concrete(
            system.iterations.saturating_add(system.counter_start),
            counter_bits,
        ),
    );

    for recurrence in &system.recurrences {
        let initial = value_for_name(state, &recurrence.initial, recurrence.bits)?;
        let value = apply_recurrence(ctx, state, initial, recurrence, system.iterations)?;
        summarized.set_register(&recurrence.phi, value);
        summarized.set_register(
            &recurrence.latch,
            summarized.get_register_sized(&recurrence.phi, recurrence.bits),
        );
    }
    if !summarized.set_loop_summary_exit(system.header, system.exit_target) {
        return None;
    }
    let exact_recurrences = exact_recurrence_evidence_from_system(system);
    let exact_folds = exact_fold_evidence_from_recurrences(&exact_recurrences);

    Some(LoopSummary {
        kind: LoopSummaryKind::Exact,
        header: system.header,
        exit_target: Some(system.exit_target),
        iterations: Some(system.iterations),
        carried_state: system.carried_state.clone(),
        transitions: system
            .recurrences
            .iter()
            .map(recurrence_to_transition)
            .collect(),
        exact_recurrences,
        exact_folds,
        reasons: Vec::new(),
        resulting_state: Some(summarized),
    })
}

fn apply_recurrence<'ctx>(
    ctx: &'ctx Context,
    state: &SymState<'ctx>,
    initial: SymValue<'ctx>,
    recurrence: &LoopRecurrence,
    iterations: u64,
) -> Option<SymValue<'ctx>> {
    let bits = recurrence.bits.max(1);
    match recurrence.kind {
        LoopRecurrenceKind::Identity => Some(initial),
        LoopRecurrenceKind::AddConst(value) => {
            let delta = mul_mod_width(value, iterations, bits);
            Some(initial.add(ctx, &SymValue::concrete(delta, bits)))
        }
        LoopRecurrenceKind::SubConst(value) => {
            let delta = mul_mod_width(value, iterations, bits);
            Some(initial.sub(ctx, &SymValue::concrete(delta, bits)))
        }
        LoopRecurrenceKind::AffineConst { multiplier, addend } => {
            let (scale, bias) = affine_transform_pow(multiplier, addend, iterations, bits);
            let scaled = initial.mul(ctx, &SymValue::concrete(scale, bits));
            Some(if bias == 0 {
                scaled
            } else {
                scaled.add(ctx, &SymValue::concrete(bias, bits))
            })
        }
        LoopRecurrenceKind::XorConst(value) => {
            if iterations.is_multiple_of(2) {
                Some(initial)
            } else {
                Some(initial.xor(ctx, &SymValue::concrete(value, bits)))
            }
        }
        LoopRecurrenceKind::AddMemoryFold(ref term) => {
            let folded = fold_memory_term(ctx, state, term, iterations, bits, true)?;
            Some(initial.add(ctx, &folded))
        }
        LoopRecurrenceKind::XorMemoryFold(ref term) => {
            let folded = fold_memory_term(ctx, state, term, iterations, bits, false)?;
            Some(initial.xor(ctx, &folded))
        }
        LoopRecurrenceKind::RotateMix {
            direction,
            amount,
            operation,
            ref term,
        } => apply_rotate_mix_recurrence(
            ctx,
            state,
            initial,
            term,
            iterations,
            bits,
            RotateMixSpec {
                direction,
                amount,
                operation,
            },
        ),
        LoopRecurrenceKind::Unsupported(_) => None,
    }
}

fn recurrence_to_transition(recurrence: &LoopRecurrence) -> LoopTransitionExpr {
    match recurrence.kind {
        LoopRecurrenceKind::Identity => LoopTransitionExpr::Identity(recurrence.phi.clone()),
        LoopRecurrenceKind::AddConst(value) => LoopTransitionExpr::AddConst {
            var: recurrence.phi.clone(),
            value,
        },
        LoopRecurrenceKind::SubConst(value) => LoopTransitionExpr::AddConst {
            var: recurrence.phi.clone(),
            value: value.wrapping_neg(),
        },
        LoopRecurrenceKind::AffineConst { multiplier, addend } => LoopTransitionExpr::AffineConst {
            var: recurrence.phi.clone(),
            multiplier,
            addend,
        },
        LoopRecurrenceKind::XorConst(value) => LoopTransitionExpr::XorConst {
            var: recurrence.phi.clone(),
            value,
        },
        LoopRecurrenceKind::AddMemoryFold(ref term)
        | LoopRecurrenceKind::XorMemoryFold(ref term) => {
            LoopTransitionExpr::TableRead(term.clone())
        }
        LoopRecurrenceKind::RotateMix {
            direction,
            amount,
            operation,
            ref term,
        } => LoopTransitionExpr::RotateMix {
            var: recurrence.phi.clone(),
            direction,
            amount,
            operation,
            term: term.clone(),
        },
        LoopRecurrenceKind::Unsupported(_) => LoopTransitionExpr::Unknown,
    }
}

fn discover_loop_transitions(
    block: &FunctionSSABlock,
    carried_state: &[LoopCarriedVar],
) -> Vec<LoopTransitionExpr> {
    let carried = carried_state
        .iter()
        .map(|var| var.name.as_str())
        .collect::<HashSet<_>>();
    let mut transitions = Vec::new();
    for op in &block.ops {
        match op {
            SSAOp::IntAdd { dst, a, b } if carried.contains(dst.display_name().as_str()) => {
                transitions.push(binary_transition(
                    LoopTransitionExpr::AddVar {
                        lhs: a.display_name(),
                        rhs: b.display_name(),
                    },
                    a,
                    b,
                    |var, value| LoopTransitionExpr::AddConst { var, value },
                ));
            }
            SSAOp::IntXor { dst, a, b } if carried.contains(dst.display_name().as_str()) => {
                transitions.push(binary_transition(
                    LoopTransitionExpr::XorVar {
                        lhs: a.display_name(),
                        rhs: b.display_name(),
                    },
                    a,
                    b,
                    |var, value| LoopTransitionExpr::XorConst { var, value },
                ));
            }
            SSAOp::Load {
                dst,
                addr,
                space: SpaceId::Ram,
            } if carried.contains(dst.display_name().as_str()) => {
                transitions.push(LoopTransitionExpr::Load {
                    addr: addr.display_name(),
                    bytes: dst.size,
                });
            }
            SSAOp::Store {
                addr,
                val,
                space: SpaceId::Ram,
            } => {
                transitions.push(LoopTransitionExpr::Store {
                    addr: addr.display_name(),
                    value: val.display_name(),
                });
            }
            SSAOp::Load { space, .. }
            | SSAOp::LoadLinked { space, .. }
            | SSAOp::StoreConditional { space, .. }
            | SSAOp::AtomicCAS { space, .. }
            | SSAOp::LoadGuarded { space, .. }
            | SSAOp::StoreGuarded { space, .. }
                if *space != SpaceId::Ram =>
            {
                transitions.push(LoopTransitionExpr::Unknown);
            }
            SSAOp::Store { space, .. } if *space != SpaceId::Ram => {
                transitions.push(LoopTransitionExpr::Unknown);
            }
            _ => {}
        }
    }
    if transitions.is_empty() && !carried_state.is_empty() {
        transitions.push(LoopTransitionExpr::Unknown);
    }
    transitions
}

fn binary_transition<F>(
    fallback: LoopTransitionExpr,
    a: &SSAVar,
    b: &SSAVar,
    make_const: F,
) -> LoopTransitionExpr
where
    F: Fn(String, u64) -> LoopTransitionExpr,
{
    if let Some(value) = parse_const_var(a) {
        make_const(b.display_name(), value)
    } else if let Some(value) = parse_const_var(b) {
        make_const(a.display_name(), value)
    } else {
        fallback
    }
}

fn recurrence_for_latch(
    artifact: &SsaArtifact,
    block: &FunctionSSABlock,
    state: &SymState<'_>,
    phi: &SSAVar,
    latch: &SSAVar,
    role: LoopVarRole,
) -> LoopRecurrence {
    let phi_name = phi.display_name();
    let latch_name = latch.display_name();
    let bits = phi.size.saturating_mul(8).max(1);
    let kind = if phi_name == latch_name {
        LoopRecurrenceKind::Identity
    } else {
        block
            .ops
            .iter()
            .find(|op| op.dst().is_some_and(|dst| dst.display_name() == latch_name))
            .map(|op| recurrence_kind_for_op(artifact, block, state, op, phi, &phi_name))
            .unwrap_or_else(|| {
                LoopRecurrenceKind::Unsupported("missing_latch_definition".to_string())
            })
    };

    LoopRecurrence {
        phi: phi_name,
        initial: String::new(),
        latch: latch_name,
        bits,
        role,
        kind,
    }
}

fn recurrence_kind_for_op(
    artifact: &SsaArtifact,
    block: &FunctionSSABlock,
    state: &SymState<'_>,
    op: &SSAOp,
    phi: &SSAVar,
    phi_name: &str,
) -> LoopRecurrenceKind {
    let bits = op
        .dst()
        .map(|dst| dst.size.saturating_mul(8).max(1))
        .unwrap_or(64);
    // The add, subtract and affine family is `r2ssa`'s answer, not this
    // crate's. It recognises them on the prepared graph keyed by `ValueId` and
    // validates each against that graph, so recognising them again here from
    // SSA variable spellings would be a second answer to a question that
    // already has an owner -- and the one that stops being right first,
    // because a name changes where a value identity does not.
    if let Some(kind) = induction_recurrence_kind(artifact, phi) {
        return kind;
    }
    match op {
        SSAOp::Copy { src, .. } if src.display_name() == phi_name => LoopRecurrenceKind::Identity,
        SSAOp::IntAdd { a, b, .. } => rotate_mix_recurrence_kind_for_op(
            block,
            state,
            a,
            b,
            phi_name,
            bits,
            LoopFoldOperation::Add,
        )
        .unwrap_or_else(|| recurrence_memory_or_const_fold(block, state, a, b, phi_name, true)),
        SSAOp::IntSub { a, b, .. } if a.display_name() == phi_name => parse_const_var(b)
            .map(LoopRecurrenceKind::SubConst)
            .unwrap_or_else(|| LoopRecurrenceKind::Unsupported("sub_non_const".to_string())),
        SSAOp::IntXor { a, b, .. } => rotate_mix_recurrence_kind_for_op(
            block,
            state,
            a,
            b,
            phi_name,
            bits,
            LoopFoldOperation::Xor,
        )
        .unwrap_or_else(|| recurrence_memory_or_const_fold(block, state, a, b, phi_name, false)),
        _ => LoopRecurrenceKind::Unsupported("unsupported_latch_op".to_string()),
    }
}

/// The step `r2ssa` recovered for this merge, in this crate's spelling.
///
/// Purely an adapter. Every judgement about whether a value moves and by how
/// much was made and validated in `r2ssa::semantic`; a step this crate cannot
/// spell would be a gap in the mapping to fix rather than a reason to
/// recognise the shape a second time here.
fn induction_recurrence_kind(artifact: &SsaArtifact, phi: &SSAVar) -> Option<LoopRecurrenceKind> {
    let value = artifact.graph().value_id_for_var(phi)?;
    let fact = artifact.facts().structured.inductions.get(&value)?;
    Some(match fact.step {
        r2ssa::InductionStep::AddConst(value) => LoopRecurrenceKind::AddConst(value),
        r2ssa::InductionStep::SubConst(value) => LoopRecurrenceKind::SubConst(value),
        r2ssa::InductionStep::Affine { multiplier, addend } => {
            LoopRecurrenceKind::AffineConst { multiplier, addend }
        }
    })
}

fn rotate_mix_recurrence_kind_for_op(
    block: &FunctionSSABlock,
    state: &SymState<'_>,
    a: &SSAVar,
    b: &SSAVar,
    phi_name: &str,
    bits: u32,
    operation: LoopFoldOperation,
) -> Option<LoopRecurrenceKind> {
    rotate_mix_kind_from_operands(block, state, a, b, phi_name, bits, operation)
        .or_else(|| rotate_mix_kind_from_operands(block, state, b, a, phi_name, bits, operation))
}

fn rotate_mix_kind_from_operands(
    block: &FunctionSSABlock,
    state: &SymState<'_>,
    rotate_operand: &SSAVar,
    mix_operand: &SSAVar,
    phi_name: &str,
    bits: u32,
    operation: LoopFoldOperation,
) -> Option<LoopRecurrenceKind> {
    let mut visited = HashSet::new();
    let (direction, amount) =
        parse_rotate_source_for_var(block, rotate_operand, phi_name, bits, 8, &mut visited)?;
    let term = memory_term_for_var(block, state, mix_operand)?;
    Some(LoopRecurrenceKind::RotateMix {
        direction,
        amount,
        operation,
        term,
    })
}

fn parse_rotate_source_for_var(
    block: &FunctionSSABlock,
    value: &SSAVar,
    phi_name: &str,
    bits: u32,
    depth: u8,
    visited: &mut HashSet<String>,
) -> Option<(LoopRotateDirection, u32)> {
    if depth == 0 {
        return None;
    }
    let name = value.display_name();
    let op = lookup_def_op_by_name(block, &name)?;
    if !visited.insert(name.clone()) {
        return None;
    }
    let result = match op {
        SSAOp::Copy { src, .. } => {
            parse_rotate_source_for_var(block, src, phi_name, bits, depth - 1, visited)
        }
        SSAOp::IntOr { dst, a, b } if dst.size.saturating_mul(8).max(1) == bits => {
            parse_rotate_or_term(block, a, b, phi_name, bits, depth - 1)
        }
        _ => None,
    };
    visited.remove(&name);
    result
}

fn parse_rotate_or_term(
    block: &FunctionSSABlock,
    a: &SSAVar,
    b: &SSAVar,
    phi_name: &str,
    bits: u32,
    depth: u8,
) -> Option<(LoopRotateDirection, u32)> {
    let lhs = parse_rotate_shift_term(block, a, phi_name, bits, depth)?;
    let rhs = parse_rotate_shift_term(block, b, phi_name, bits, depth)?;
    if lhs.shift == 0 || rhs.shift == 0 || lhs.shift.saturating_add(rhs.shift) != bits {
        return None;
    }
    match (lhs.direction, rhs.direction) {
        (LoopRotateDirection::Left, LoopRotateDirection::Right) => {
            Some((LoopRotateDirection::Left, lhs.shift))
        }
        (LoopRotateDirection::Right, LoopRotateDirection::Left) => {
            Some((LoopRotateDirection::Right, lhs.shift))
        }
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RotateShiftTerm {
    direction: LoopRotateDirection,
    shift: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RotateMixSpec {
    direction: LoopRotateDirection,
    amount: u32,
    operation: LoopFoldOperation,
}

fn parse_rotate_shift_term(
    block: &FunctionSSABlock,
    value: &SSAVar,
    phi_name: &str,
    bits: u32,
    depth: u8,
) -> Option<RotateShiftTerm> {
    if depth == 0 {
        return None;
    }
    let op = lookup_def_op_by_name(block, &value.display_name())?;
    match op {
        SSAOp::IntLeft { dst, a, b } if dst.size.saturating_mul(8).max(1) == bits => {
            let shift = normalize_rotate_amount(parse_const_var(b)? as u32, bits);
            let mut inner_visited = HashSet::new();
            value_matches_phi_source(block, a, phi_name, depth - 1, &mut inner_visited).then_some(
                RotateShiftTerm {
                    direction: LoopRotateDirection::Left,
                    shift,
                },
            )
        }
        SSAOp::IntRight { dst, a, b } if dst.size.saturating_mul(8).max(1) == bits => {
            let shift = normalize_rotate_amount(parse_const_var(b)? as u32, bits);
            let mut inner_visited = HashSet::new();
            value_matches_phi_source(block, a, phi_name, depth - 1, &mut inner_visited).then_some(
                RotateShiftTerm {
                    direction: LoopRotateDirection::Right,
                    shift,
                },
            )
        }
        SSAOp::Copy { src, .. } => parse_rotate_shift_term(block, src, phi_name, bits, depth - 1),
        _ => None,
    }
}

fn value_matches_phi_source(
    block: &FunctionSSABlock,
    value: &SSAVar,
    phi_name: &str,
    depth: u8,
    visited: &mut HashSet<String>,
) -> bool {
    if depth == 0 {
        return false;
    }
    if value.display_name() == phi_name {
        return true;
    }
    let name = value.display_name();
    let Some(op) = lookup_def_op_by_name(block, &name) else {
        return false;
    };
    if !visited.insert(name.clone()) {
        return false;
    }
    let result = match op {
        SSAOp::Copy { src, .. } => {
            value_matches_phi_source(block, src, phi_name, depth - 1, visited)
        }
        _ => false,
    };
    visited.remove(&name);
    result
}

fn lookup_def_op_by_name<'a>(block: &'a FunctionSSABlock, name: &str) -> Option<&'a SSAOp> {
    block
        .ops
        .iter()
        .find(|op| op.dst().is_some_and(|dst| dst.display_name() == name))
}

fn recurrence_memory_or_const_fold(
    block: &FunctionSSABlock,
    state: &SymState<'_>,
    a: &SSAVar,
    b: &SSAVar,
    phi_name: &str,
    additive: bool,
) -> LoopRecurrenceKind {
    let other = if a.display_name() == phi_name {
        b
    } else if b.display_name() == phi_name {
        a
    } else {
        return LoopRecurrenceKind::Unsupported("fold_missing_accumulator".to_string());
    };

    if let Some(value) = parse_const_var(other) {
        return if additive {
            LoopRecurrenceKind::AddConst(value)
        } else {
            LoopRecurrenceKind::XorConst(value)
        };
    }

    let Some(term) = memory_term_for_var(block, state, other) else {
        return LoopRecurrenceKind::Unsupported("fold_operand_not_memory_term".to_string());
    };
    if additive {
        LoopRecurrenceKind::AddMemoryFold(term)
    } else {
        LoopRecurrenceKind::XorMemoryFold(term)
    }
}

fn memory_term_for_var(
    block: &FunctionSSABlock,
    state: &SymState<'_>,
    value: &SSAVar,
) -> Option<LoopMemoryTerm> {
    let (addr, bytes) = block.ops.iter().find_map(|op| match op {
        SSAOp::Load {
            dst,
            addr,
            space: SpaceId::Ram,
        } if dst == value => Some((addr, dst.size)),
        _ => None,
    })?;
    let base = state_value_at_block_entry(state, block, addr).and_then(|value| value.as_concrete());
    let addr_is_loop_carried = block.phis.iter().any(|phi| phi.dst == *addr);
    let stride = if addr_is_loop_carried {
        memory_stride_for_addr_var(block, state, addr)
    } else {
        Some(bytes as u64)
    };
    let provenance = base.and_then(|base| classify_memory_term_provenance(state, base));
    Some(LoopMemoryTerm {
        kind: provenance
            .as_ref()
            .map(|provenance| provenance.kind)
            .unwrap_or(LoopMemoryTermKind::Unknown),
        addr: addr.display_name(),
        bytes,
        base,
        stride,
        region: provenance
            .as_ref()
            .map(|provenance| provenance.name.clone()),
        region_base: provenance.as_ref().map(|provenance| provenance.base),
        region_size: provenance.as_ref().map(|provenance| provenance.size),
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LoopMemoryProvenance {
    kind: LoopMemoryTermKind,
    name: String,
    base: u64,
    size: u64,
}

fn classify_memory_term_provenance(
    state: &SymState<'_>,
    base: u64,
) -> Option<LoopMemoryProvenance> {
    if let Some(region) = state
        .symbolic_memory()
        .iter()
        .find(|region| base >= region.addr && base < region.addr.saturating_add(region.size as u64))
    {
        let kind = if region.name.contains("argv")
            || region.name.contains("stdin")
            || region.name.contains("input")
        {
            LoopMemoryTermKind::InputRead
        } else {
            LoopMemoryTermKind::TableRead
        };
        return Some(LoopMemoryProvenance {
            kind,
            name: region.name.clone(),
            base: region.addr,
            size: region.size as u64,
        });
    };

    if let Some(region) = state.runtime_region_for_pc(base) {
        return Some(LoopMemoryProvenance {
            kind: LoopMemoryTermKind::RuntimeBlobRead,
            name: format!("runtime:{:x}", region.runtime_base),
            base: region.runtime_base,
            size: region.size,
        });
    }

    if state.is_concrete_memory_range(base, 1) {
        return Some(LoopMemoryProvenance {
            kind: LoopMemoryTermKind::TableRead,
            name: format!("concrete:{base:x}"),
            base,
            size: 0,
        });
    }

    None
}

fn memory_stride_for_addr_var(
    block: &FunctionSSABlock,
    state: &SymState<'_>,
    addr: &SSAVar,
) -> Option<u64> {
    let phi = block
        .phis
        .iter()
        .find(|phi| phi.dst.display_name() == addr.display_name())?;
    let latch = latch_source_for_phi(phi, state.prev_pc())?;
    let latch_name = latch.display_name();
    block
        .ops
        .iter()
        .find(|op| op.dst().is_some_and(|dst| dst.display_name() == latch_name))
        .and_then(|op| match op {
            SSAOp::IntAdd { a, b, .. } if a.display_name() == addr.display_name() => {
                parse_const_var(b)
            }
            SSAOp::IntAdd { a, b, .. } if b.display_name() == addr.display_name() => {
                parse_const_var(a)
            }
            _ => None,
        })
}

fn memory_term_has_exact_bounds(
    state: &SymState<'_>,
    term: &LoopMemoryTerm,
    iterations: u64,
) -> bool {
    let (Some(base), Some(stride)) = (term.base, term.stride) else {
        return false;
    };
    if iterations == 0 {
        return true;
    }
    let Some(last_offset) = (iterations - 1).checked_mul(stride) else {
        return false;
    };
    let Some(last_addr) = base.checked_add(last_offset) else {
        return false;
    };
    let Some(last_end) = last_addr.checked_add(term.bytes as u64) else {
        return false;
    };

    match term.kind {
        LoopMemoryTermKind::InputRead | LoopMemoryTermKind::RuntimeBlobRead => {
            let (Some(region_base), Some(region_size)) = (term.region_base, term.region_size)
            else {
                return false;
            };
            let Some(region_end) = region_base.checked_add(region_size) else {
                return false;
            };
            base >= region_base && last_end <= region_end
        }
        LoopMemoryTermKind::TableRead => (0..iterations).all(|iteration| {
            let Some(offset) = iteration.checked_mul(stride) else {
                return false;
            };
            let Some(addr) = base.checked_add(offset) else {
                return false;
            };
            state.is_concrete_memory_range(addr, term.bytes)
        }),
        LoopMemoryTermKind::Unknown => false,
    }
}

fn selected_phi_source(phi: &r2ssa::PhiNode, prev_pc: Option<u64>) -> Option<&SSAVar> {
    let prev_pc = prev_pc?;
    phi.sources
        .iter()
        .find(|(pred, _)| *pred == prev_pc)
        .map(|(_, source)| source)
}

fn latch_source_for_phi(phi: &r2ssa::PhiNode, selected_prev_pc: Option<u64>) -> Option<&SSAVar> {
    phi.sources
        .iter()
        .rev()
        .find(|(pred, source)| {
            Some(*pred) != selected_prev_pc && source.display_name() != phi.dst.display_name()
        })
        .map(|(_, source)| source)
        .or_else(|| {
            phi.sources
                .iter()
                .rev()
                .find(|(_, source)| source.display_name() != phi.dst.display_name())
                .map(|(_, source)| source)
        })
}

fn block_has_memory_writes(block: &FunctionSSABlock) -> bool {
    block.ops.iter().any(|op| {
        matches!(
            op,
            SSAOp::Store { .. }
                | SSAOp::StoreConditional { .. }
                | SSAOp::AtomicCAS { .. }
                | SSAOp::StoreGuarded { .. }
        )
    })
}

fn block_has_non_ram_memory(block: &FunctionSSABlock) -> bool {
    block.ops.iter().any(|op| match op {
        SSAOp::Load { space, .. }
        | SSAOp::Store { space, .. }
        | SSAOp::LoadLinked { space, .. }
        | SSAOp::StoreConditional { space, .. }
        | SSAOp::AtomicCAS { space, .. }
        | SSAOp::LoadGuarded { space, .. }
        | SSAOp::StoreGuarded { space, .. } => *space != SpaceId::Ram,
        _ => false,
    })
}

fn fold_memory_term<'ctx>(
    ctx: &'ctx Context,
    state: &SymState<'ctx>,
    term: &LoopMemoryTerm,
    iterations: u64,
    bits: u32,
    additive: bool,
) -> Option<SymValue<'ctx>> {
    let base = term.base?;
    let stride = term.stride?;
    let mut concrete: u64 = 0;
    let mut symbolic: Option<SymValue<'ctx>> = None;
    for iteration in 0..iterations {
        let offset = iteration.checked_mul(stride)?;
        let addr = base.checked_add(offset)?;
        let value = state.mem_read(&SymValue::concrete(addr, 64), term.bytes);
        if let Some(item) = value.as_concrete() {
            concrete = if additive {
                concrete.wrapping_add(item)
            } else {
                concrete ^ item
            };
            continue;
        }
        symbolic = Some(match symbolic {
            Some(acc) if additive => acc.add(ctx, &value),
            Some(acc) => acc.xor(ctx, &value),
            None => value,
        });
    }
    let concrete_value = SymValue::concrete(concrete & mask_for_bits(bits), bits);
    Some(match symbolic {
        Some(value) if additive => value.add(ctx, &concrete_value),
        Some(value) => value.xor(ctx, &concrete_value),
        None => concrete_value,
    })
}

fn apply_rotate_mix_recurrence<'ctx>(
    ctx: &'ctx Context,
    state: &SymState<'ctx>,
    initial: SymValue<'ctx>,
    term: &LoopMemoryTerm,
    iterations: u64,
    bits: u32,
    spec: RotateMixSpec,
) -> Option<SymValue<'ctx>> {
    let base = term.base?;
    let stride = term.stride?;
    let bits = bits.max(1);
    let mut acc = normalize_value_bits(ctx, &initial, bits);
    for iteration in 0..iterations {
        acc = rotate_value(ctx, &acc, spec.amount, bits, spec.direction);
        let offset = iteration.checked_mul(stride)?;
        let addr = base.checked_add(offset)?;
        let value = state.mem_read(&SymValue::concrete(addr, 64), term.bytes);
        acc = match spec.operation {
            LoopFoldOperation::Add => acc.add(ctx, &value),
            LoopFoldOperation::Xor => acc.xor(ctx, &value),
        };
        acc = normalize_value_bits(ctx, &acc, bits);
    }
    Some(acc)
}

fn normalize_value_bits<'ctx>(
    ctx: &'ctx Context,
    value: &SymValue<'ctx>,
    bits: u32,
) -> SymValue<'ctx> {
    let bits = bits.max(1);
    match value.bits().cmp(&bits) {
        std::cmp::Ordering::Equal => value.clone(),
        std::cmp::Ordering::Less => value.zero_extend(ctx, bits),
        std::cmp::Ordering::Greater => value.extract(ctx, bits - 1, 0),
    }
}

fn rotate_value<'ctx>(
    ctx: &'ctx Context,
    value: &SymValue<'ctx>,
    amount: u32,
    bits: u32,
    direction: LoopRotateDirection,
) -> SymValue<'ctx> {
    let bits = bits.max(1);
    let amount = normalize_rotate_amount(amount, bits);
    let value = normalize_value_bits(ctx, value, bits);
    if amount == 0 {
        return value;
    }
    if let Some(concrete) = value.as_concrete() {
        return SymValue::concrete(
            rotate_concrete_bits(concrete, amount, bits, direction),
            bits,
        );
    }
    let head = match direction {
        LoopRotateDirection::Left => value.shl(ctx, &SymValue::concrete(amount as u64, bits)),
        LoopRotateDirection::Right => value.lshr(ctx, &SymValue::concrete(amount as u64, bits)),
    };
    let tail_amount = bits - amount;
    let tail = match direction {
        LoopRotateDirection::Left => value.lshr(ctx, &SymValue::concrete(tail_amount as u64, bits)),
        LoopRotateDirection::Right => value.shl(ctx, &SymValue::concrete(tail_amount as u64, bits)),
    };
    normalize_value_bits(ctx, &head.or(ctx, &tail), bits)
}

fn rotate_concrete_bits(value: u64, amount: u32, bits: u32, direction: LoopRotateDirection) -> u64 {
    let bits = bits.clamp(1, 64);
    let value = value & mask_for_bits(bits);
    let amount = normalize_rotate_amount(amount, bits);
    if amount == 0 {
        return value;
    }
    if bits == 64 {
        return match direction {
            LoopRotateDirection::Left => value.rotate_left(amount),
            LoopRotateDirection::Right => value.rotate_right(amount),
        };
    }
    let lhs = match direction {
        LoopRotateDirection::Left => value.wrapping_shl(amount),
        LoopRotateDirection::Right => value >> amount,
    } & mask_for_bits(bits);
    let rhs = match direction {
        LoopRotateDirection::Left => value >> (bits - amount),
        LoopRotateDirection::Right => value.wrapping_shl(bits - amount),
    } & mask_for_bits(bits);
    (lhs | rhs) & mask_for_bits(bits)
}

fn value_for_name<'ctx>(state: &SymState<'ctx>, name: &str, bits: u32) -> Option<SymValue<'ctx>> {
    if let Some(value) = name
        .strip_prefix("const:")
        .and_then(|value| u64::from_str_radix(value, 16).ok())
    {
        return Some(SymValue::concrete(value, bits.max(1)));
    }
    let value = state.get_register_sized(name, bits.max(1));
    if value.is_unknown() {
        None
    } else {
        Some(value)
    }
}

fn state_value_at_block_entry<'ctx>(
    state: &SymState<'ctx>,
    block: &FunctionSSABlock,
    var: &SSAVar,
) -> Option<SymValue<'ctx>> {
    let phi = block
        .phis
        .iter()
        .find(|phi| phi.dst.display_name() == var.display_name());
    if let Some(phi) = phi {
        return selected_phi_source(phi, state.prev_pc())
            .and_then(|source| value_for_name(state, &source.display_name(), source.size * 8));
    }

    value_for_name(
        state,
        &var.display_name(),
        var.size.saturating_mul(8).max(1),
    )
}

fn mul_mod_width(value: u64, iterations: u64, bits: u32) -> u64 {
    let mask = mask_for_bits(bits);
    value.wrapping_mul(iterations) & mask
}

fn compose_affine_transform(outer: (u64, u64), inner: (u64, u64), bits: u32) -> (u64, u64) {
    let mask = mask_for_bits(bits);
    let multiplier = outer.0.wrapping_mul(inner.0) & mask;
    let addend = outer.0.wrapping_mul(inner.1).wrapping_add(outer.1) & mask;
    (multiplier, addend)
}

fn affine_transform_pow(multiplier: u64, addend: u64, iterations: u64, bits: u32) -> (u64, u64) {
    let mask = mask_for_bits(bits);
    let mut result = (1u64, 0u64);
    let mut base = (multiplier & mask, addend & mask);
    let mut exp = iterations;

    while exp != 0 {
        if exp & 1 == 1 {
            result = compose_affine_transform(base, result, bits);
        }
        exp >>= 1;
        if exp != 0 {
            base = compose_affine_transform(base, base, bits);
        }
    }

    result
}

fn normalize_rotate_amount(amount: u32, bits: u32) -> u32 {
    let bits = bits.min(64);
    if bits == 0 { 0 } else { amount % bits }
}

fn mask_for_bits(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits.max(1)) - 1
    }
}

fn push_unique_reason(reasons: &mut Vec<String>, reason: impl Into<String>) {
    let reason = reason.into();
    if !reasons.iter().any(|existing| existing == &reason) {
        reasons.push(reason);
    }
}

fn used_as_memory_addr(block: &FunctionSSABlock, phi: &SSAVar, latch_sources: &[&SSAVar]) -> bool {
    let names = related_names(phi, latch_sources);
    block.ops.iter().any(|op| match op {
        SSAOp::Load { addr, .. }
        | SSAOp::Store { addr, .. }
        | SSAOp::LoadLinked { addr, .. }
        | SSAOp::StoreConditional { addr, .. }
        | SSAOp::LoadGuarded { addr, .. }
        | SSAOp::StoreGuarded { addr, .. } => names.contains(addr.display_name().as_str()),
        _ => false,
    })
}

fn used_as_memory_value(block: &FunctionSSABlock, phi: &SSAVar, latch_sources: &[&SSAVar]) -> bool {
    let names = related_names(phi, latch_sources);
    block.ops.iter().any(|op| match op {
        SSAOp::Store { val, .. }
        | SSAOp::StoreConditional { val, .. }
        | SSAOp::StoreGuarded { val, .. } => names.contains(val.display_name().as_str()),
        _ => false,
    })
}

fn latch_update_depends_on_phi(
    block: &FunctionSSABlock,
    phi: &SSAVar,
    latch_sources: &[&SSAVar],
) -> bool {
    let phi_name = phi.display_name();
    latch_sources.iter().any(|source| {
        let source_name = source.display_name();
        block.ops.iter().any(|op| {
            op.dst()
                .is_some_and(|dst| dst.display_name() == source_name)
                && op_sources_include(op, &phi_name)
        })
    })
}

fn op_sources_include(op: &SSAOp, needle: &str) -> bool {
    let mut found = false;
    op.for_each_source(|source| {
        if source.display_name() == needle {
            found = true;
        }
    });
    found
}

fn related_names<'a>(phi: &'a SSAVar, latch_sources: &[&'a SSAVar]) -> HashSet<String> {
    let mut names = HashSet::new();
    names.insert(phi.display_name());
    for source in latch_sources {
        names.insert(source.display_name());
    }
    names
}

fn parse_hex_prefixed_var(var: &SSAVar, prefix: &str) -> Option<u64> {
    var.name
        .strip_prefix(prefix)
        .and_then(|value| u64::from_str_radix(value, 16).ok())
}

fn parse_const_var(var: &SSAVar) -> Option<u64> {
    parse_hex_prefixed_var(var, "const:")
}

pub(crate) fn parse_address_var(var: &SSAVar) -> Option<u64> {
    parse_hex_prefixed_var(var, "ram:").or_else(|| parse_const_var(var))
}

fn resolve_copy_source(var: &SSAVar, copies: &HashMap<String, SSAVar>) -> SSAVar {
    let mut current = var.clone();
    for _ in 0..8 {
        let Some(next) = copies.get(&current.display_name()) else {
            break;
        };
        if next.display_name() == current.display_name() {
            break;
        }
        current = next.clone();
    }
    current
}

fn concrete_state_var<'ctx>(state: &SymState<'ctx>, var: &SSAVar) -> Option<u64> {
    parse_const_var(var).or_else(|| {
        state
            .get_register_sized(&var.display_name(), var.size.saturating_mul(8).max(1))
            .as_concrete()
    })
}

#[cfg(test)]
mod tests {
    use r2ssa::{FunctionSSABlock, PhiNode, SSAOp, SSAVar};
    use z3::Context;

    use super::{
        LoopMemoryTermKind, LoopRecurrenceKind, LoopSummaryKind, LoopVarRole,
        apply_exact_transition_system, concrete_state_var_at_block_entry,
        derive_loop_transition_system, discover_loop_carried_state,
        exact_recurrence_evidence_from_system, runtime_counter_threshold_branch,
    };
    use crate::{SymState, SymValue};

    fn var(name: &str, version: u32, size: u32) -> SSAVar {
        SSAVar::new(name, version, size)
    }

    fn const_var(value: u64, size: u32) -> SSAVar {
        SSAVar::new(format!("const:{value:x}"), 0, size)
    }

    #[test]
    fn detects_counter_threshold_exit_branch() {
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 4,
            phis: Vec::new(),
            ops: vec![
                SSAOp::IntLess {
                    dst: var("tmp", 0, 1),
                    a: var("i", 1, 8),
                    b: const_var(0x10, 8),
                },
                SSAOp::BoolNot {
                    dst: var("done", 0, 1),
                    src: var("tmp", 0, 1),
                },
                SSAOp::CBranch {
                    target: const_var(0x2000, 8),
                    cond: var("done", 0, 1),
                },
            ],
        };
        let branch = runtime_counter_threshold_branch(&block).expect("branch");
        assert_eq!(branch.counter.display_name(), "I_1");
        assert_eq!(branch.threshold, 0x10);
        assert_eq!(branch.target, 0x2000);
    }

    #[test]
    fn block_entry_concrete_lookup_uses_selected_phi_source() {
        let counter = var("RCX", 2, 8);
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 4,
            phis: vec![PhiNode {
                dst: counter.clone(),
                sources: vec![(0x900, var("RCX", 0, 8)), (0x1008, var("RCX", 1, 8))],
                canonical_storage: None,
            }],
            ops: Vec::new(),
        };
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.set_prev_pc(Some(0x1008));
        state.set_register("RCX_0", SymValue::concrete(1, 64));
        state.set_register("RCX_1", SymValue::concrete(7, 64));
        assert_eq!(
            concrete_state_var_at_block_entry(&state, &block, &counter),
            Some(7)
        );
    }

    #[test]
    fn discovers_non_rax_loop_accumulator() {
        let acc_phi = var("RBX", 2, 8);
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 4,
            phis: vec![
                PhiNode {
                    dst: var("RCX", 2, 8),
                    sources: vec![(0x900, var("RCX", 0, 8)), (0x1008, var("RCX", 1, 8))],
                    canonical_storage: None,
                },
                PhiNode {
                    dst: acc_phi.clone(),
                    sources: vec![(0x900, var("RBX", 0, 8)), (0x1008, var("RBX", 1, 8))],
                    canonical_storage: None,
                },
            ],
            ops: vec![SSAOp::IntXor {
                dst: var("RBX", 1, 8),
                a: acc_phi,
                b: var("input", 0, 8),
            }],
        };
        let carried = discover_loop_carried_state(&block, Some(&var("RCX", 2, 8)));
        assert!(
            carried
                .iter()
                .any(|var| { var.name == "RBX_2" && var.role == LoopVarRole::Accumulator })
        );
    }

    /// An artifact with no loop, for the fixtures that still forge their own
    /// blocks to exercise the fold and rotate shapes `r2ssa` does not model.
    ///
    /// Passing one with facts in it would be misleading: those fixtures' SSA
    /// names belong to no real graph, so no fact could match them, and a
    /// reader should be able to see that the recurrence under test came from
    /// this crate's own recognisers.
    fn artifact_without_inductions() -> r2ssa::SsaArtifact {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        let mut only = R2ILBlock::new(0x1000, 4);
        only.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        r2ssa::SsaArtifact::for_decompile(&[only], None).expect("straight-line artifact")
    }

    /// A real two-carrier loop artifact: a counter stepped by one and an
    /// accumulator stepped by `acc_step`.
    ///
    /// The fixtures below used to forge `FunctionSSABlock` values by hand,
    /// which let them describe SSA the builder never produces. The add,
    /// subtract and affine recurrences now come from `r2ssa`'s induction
    /// facts, which are keyed by `ValueId` against a real graph, so a forged
    /// block has no facts to find and these have to be real.
    fn real_loop_artifact(acc_multiplier: u64, acc_addend: u64) -> r2ssa::SsaArtifact {
        use r2il::{R2ILBlock, R2ILOp, Varnode};
        let counter = Varnode::register(40, 8);
        let accumulator = Varnode::register(48, 8);
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Copy {
            dst: counter.clone(),
            src: Varnode::constant(0, 8),
        });
        entry.push(R2ILOp::Copy {
            dst: accumulator.clone(),
            src: Varnode::constant(0, 8),
        });
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x1010, 8),
        });
        let mut header = R2ILBlock::new(0x1010, 4);
        header.push(R2ILOp::IntAdd {
            dst: counter.clone(),
            a: counter,
            b: Varnode::constant(1, 8),
        });
        if acc_multiplier != 1 {
            // Scale in place rather than through a temporary. A unique written
            // in the header and read there is discovered as loop-carried state
            // with no value on the entry edge, which makes the whole system
            // inexact for a reason that is an artifact of the fixture.
            header.push(R2ILOp::IntMult {
                dst: accumulator.clone(),
                a: accumulator.clone(),
                b: Varnode::constant(acc_multiplier, 8),
            });
            header.push(R2ILOp::IntAdd {
                dst: accumulator.clone(),
                a: accumulator.clone(),
                b: Varnode::constant(acc_addend, 8),
            });
        } else {
            header.push(R2ILOp::IntAdd {
                dst: accumulator.clone(),
                a: accumulator.clone(),
                b: Varnode::constant(acc_addend, 8),
            });
        }
        header.push(R2ILOp::CBranch {
            target: Varnode::ram(0x1010, 8),
            cond: Varnode::register(24, 1),
        });
        let mut exit = R2ILBlock::new(0x1014, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        r2ssa::SsaArtifact::for_decompile(&[entry, header, exit], None).expect("real loop artifact")
    }

    #[test]
    fn derives_exact_add_const_recurrence_summary() {
        // Real SSA rather than a forged block: the add, subtract and affine
        // recurrences come from `r2ssa`'s induction facts, which are keyed by
        // `ValueId` against a real graph, so a hand-built block has no facts
        // to find. The accumulator is register 0x30 and steps by three.
        let artifact = real_loop_artifact(1, 3);
        let block = artifact
            .function()
            .get_block(0x1010)
            .expect("loop header")
            .clone();
        let counter_phi = block.phis[0].dst.clone();
        let accumulator = block.phis[1].dst.display_name();
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1010);
        state.set_prev_pc(Some(0x1000));
        // The state holds the values on the edge into the loop, which is what
        // `state_value_at_block_entry` resolves a phi to, not the phi outputs.
        let entry_source = |phi: &r2ssa::PhiNode| {
            phi.sources
                .iter()
                .find(|(pred, _)| *pred == 0x1000)
                .map(|(_, var)| var.display_name())
                .expect("entry edge source")
        };
        state.set_register(&entry_source(&block.phis[0]), SymValue::concrete(0, 64));
        state.set_register(&entry_source(&block.phis[1]), SymValue::concrete(0, 64));
        let branch = super::RuntimeLoopBranch {
            counter: counter_phi,
            threshold: 10,
            target: 0x2000,
        };

        let system = derive_loop_transition_system(&artifact, &block, &state, &branch, 0, 10);
        assert!(
            system.recurrences.iter().any(|recurrence| {
                recurrence.phi == accumulator && recurrence.kind == LoopRecurrenceKind::AddConst(3)
            }),
            "recurrences={:?} reasons={:?} carried={:?}",
            system.recurrences,
            system.reasons,
            system.carried_state
        );
        let exact_recurrences = exact_recurrence_evidence_from_system(&system);
        assert!(
            exact_recurrences.iter().any(|recurrence| {
                recurrence.accumulator == accumulator
                    && recurrence.kind == super::ExactLoopRecurrenceKind::AddConst(3)
            }),
            "{exact_recurrences:?}"
        );
        let summary = apply_exact_transition_system(&ctx, &state, &system).expect("summary");
        assert_eq!(summary.kind, LoopSummaryKind::Exact);
        assert_eq!(summary.exact_recurrences, exact_recurrences);
        let summarized = summary.resulting_state.expect("state");
        assert_eq!(summarized.pc(), 0x2000);
        // Ten trips of three from zero.
        assert_eq!(
            summarized
                .get_register_sized(&accumulator, 64)
                .as_concrete(),
            Some(30)
        );
    }

    #[test]
    fn derives_exact_affine_const_recurrence_summary() {
        // `x = x * 3 + 1`, recovered as one affine step rather than as a
        // multiply followed by an add.
        let artifact = real_loop_artifact(3, 1);
        let block = artifact
            .function()
            .get_block(0x1010)
            .expect("loop header")
            .clone();
        let counter_phi = block.phis[0].dst.clone();
        let accumulator = block.phis[1].dst.display_name();
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1010);
        state.set_prev_pc(Some(0x1000));
        let entry_source = |phi: &r2ssa::PhiNode| {
            phi.sources
                .iter()
                .find(|(pred, _)| *pred == 0x1000)
                .map(|(_, var)| var.display_name())
                .expect("entry edge source")
        };
        state.set_register(&entry_source(&block.phis[0]), SymValue::concrete(0, 64));
        state.set_register(&entry_source(&block.phis[1]), SymValue::concrete(2, 64));
        let branch = super::RuntimeLoopBranch {
            counter: counter_phi,
            threshold: 4,
            target: 0x2000,
        };

        let system = derive_loop_transition_system(&artifact, &block, &state, &branch, 0, 4);
        assert!(
            system.recurrences.iter().any(|recurrence| {
                recurrence.phi == accumulator
                    && recurrence.kind
                        == LoopRecurrenceKind::AffineConst {
                            multiplier: 3,
                            addend: 1,
                        }
            }),
            "recurrences={:?} reasons={:?} carried={:?}",
            system.recurrences,
            system.reasons,
            system.carried_state
        );
        let exact_recurrences = exact_recurrence_evidence_from_system(&system);
        assert!(system.is_exact(), "reasons={:?}", system.reasons);
        assert!(
            exact_recurrences.iter().any(|recurrence| {
                recurrence.accumulator == accumulator
                    && recurrence.kind
                        == super::ExactLoopRecurrenceKind::AffineConst {
                            multiplier: 3,
                            addend: 1,
                        }
            }),
            "{exact_recurrences:?}"
        );
        let summary = apply_exact_transition_system(&ctx, &state, &system).expect("summary");
        assert_eq!(summary.kind, LoopSummaryKind::Exact);
        let summarized = summary.resulting_state.expect("state");
        // Four trips of `x = x * 3 + 1` from two: 7, 22, 67, 202.
        assert_eq!(
            summarized
                .get_register_sized(&accumulator, 64)
                .as_concrete(),
            Some(202)
        );
    }

    #[test]
    fn refuses_exact_recurrence_when_loop_has_memory_effects() {
        let counter_phi = var("RCX", 2, 8);
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 4,
            phis: vec![PhiNode {
                dst: counter_phi.clone(),
                sources: vec![(0x900, var("RCX", 0, 8)), (0x1008, var("RCX", 1, 8))],
                canonical_storage: None,
            }],
            ops: vec![
                SSAOp::IntAdd {
                    dst: var("RCX", 1, 8),
                    a: counter_phi.clone(),
                    b: const_var(1, 8),
                },
                SSAOp::Store {
                    space: r2il::SpaceId::Ram,
                    addr: var("RAX", 0, 8),
                    val: var("RCX", 1, 8),
                },
            ],
        };
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.set_prev_pc(Some(0x900));
        state.set_register("RCX_0", SymValue::concrete(0, 64));
        let branch = super::RuntimeLoopBranch {
            counter: counter_phi,
            threshold: 10,
            target: 0x2000,
        };

        let system = derive_loop_transition_system(
            &artifact_without_inductions(),
            &block,
            &state,
            &branch,
            0,
            10,
        );
        assert!(!system.is_exact());
        assert!(
            system
                .reasons
                .contains(&"runtime_loop_memory_write_transition_unsupported".to_string())
        );
    }

    #[test]
    fn refuses_custom_space_fold_even_when_ram_exists_at_the_same_address() {
        let counter_phi = var("RCX", 2, 8);
        let ptr_phi = var("RDI", 2, 8);
        let acc_phi = var("RBX", 2, 8);
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 4,
            phis: vec![
                PhiNode {
                    dst: counter_phi.clone(),
                    sources: vec![(0x900, var("RCX", 0, 8)), (0x1008, var("RCX", 1, 8))],
                    canonical_storage: None,
                },
                PhiNode {
                    dst: ptr_phi.clone(),
                    sources: vec![(0x900, var("RDI", 0, 8)), (0x1008, var("RDI", 1, 8))],
                    canonical_storage: None,
                },
                PhiNode {
                    dst: acc_phi.clone(),
                    sources: vec![(0x900, var("RBX", 0, 8)), (0x1008, var("RBX", 1, 8))],
                    canonical_storage: None,
                },
            ],
            ops: vec![
                SSAOp::IntAdd {
                    dst: var("RCX", 1, 8),
                    a: counter_phi.clone(),
                    b: const_var(1, 8),
                },
                SSAOp::IntAdd {
                    dst: var("RDI", 1, 8),
                    a: ptr_phi.clone(),
                    b: const_var(1, 8),
                },
                SSAOp::Load {
                    dst: var("TMP", 0, 1),
                    space: r2il::SpaceId::Custom(7),
                    addr: ptr_phi,
                },
                SSAOp::IntXor {
                    dst: var("RBX", 1, 8),
                    a: acc_phi,
                    b: var("TMP", 0, 1),
                },
            ],
        };
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.set_prev_pc(Some(0x900));
        state.set_register("RCX_0", SymValue::concrete(0, 64));
        state.set_register("RDI_0", SymValue::concrete(0x5000, 64));
        state.set_register("RBX_0", SymValue::concrete(0xaa, 64));
        state.mem_write(
            &SymValue::concrete(0x5000, 64),
            &SymValue::concrete(1, 8),
            1,
        );
        state.mem_write(
            &SymValue::concrete(0x5001, 64),
            &SymValue::concrete(2, 8),
            1,
        );
        state.mem_write(
            &SymValue::concrete(0x5002, 64),
            &SymValue::concrete(3, 8),
            1,
        );
        let branch = super::RuntimeLoopBranch {
            counter: counter_phi,
            threshold: 3,
            target: 0x2000,
        };

        let system = derive_loop_transition_system(
            &artifact_without_inductions(),
            &block,
            &state,
            &branch,
            0,
            3,
        );
        assert!(!system.is_exact());
        assert!(
            system
                .reasons
                .contains(&"runtime_loop_non_ram_memory_unsupported".to_string())
        );
        assert!(system.recurrences.iter().any(|recurrence| {
            recurrence.phi == "RBX_2"
                && matches!(
                    &recurrence.kind,
                    LoopRecurrenceKind::Unsupported(reason)
                        if reason == "fold_operand_not_memory_term"
                )
        }));
        assert!(apply_exact_transition_system(&ctx, &state, &system).is_none());
    }

    #[test]
    fn derives_exact_add_runtime_blob_fold_summary() {
        let counter_phi = var("RCX", 2, 8);
        let ptr_phi = var("RDI", 2, 8);
        let acc_phi = var("RBX", 2, 8);
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 4,
            phis: vec![
                PhiNode {
                    dst: counter_phi.clone(),
                    sources: vec![(0x900, var("RCX", 0, 8)), (0x1008, var("RCX", 1, 8))],
                    canonical_storage: None,
                },
                PhiNode {
                    dst: ptr_phi.clone(),
                    sources: vec![(0x900, var("RDI", 0, 8)), (0x1008, var("RDI", 1, 8))],
                    canonical_storage: None,
                },
                PhiNode {
                    dst: acc_phi.clone(),
                    sources: vec![(0x900, var("RBX", 0, 8)), (0x1008, var("RBX", 1, 8))],
                    canonical_storage: None,
                },
            ],
            ops: vec![
                SSAOp::IntAdd {
                    dst: var("RCX", 1, 8),
                    a: counter_phi.clone(),
                    b: const_var(1, 8),
                },
                SSAOp::IntAdd {
                    dst: var("RDI", 1, 8),
                    a: ptr_phi.clone(),
                    b: const_var(1, 8),
                },
                SSAOp::Load {
                    dst: var("TMP", 0, 1),
                    space: r2il::SpaceId::Ram,
                    addr: ptr_phi,
                },
                SSAOp::IntAdd {
                    dst: var("RBX", 1, 8),
                    a: acc_phi,
                    b: var("TMP", 0, 1),
                },
            ],
        };
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.set_prev_pc(Some(0x900));
        state.set_register("RCX_0", SymValue::concrete(0, 64));
        state.set_register("RDI_0", SymValue::concrete(0x6000_0000, 64));
        state.set_register("RBX_0", SymValue::concrete(10, 64));
        let region = state.define_runtime_region("jit_blob", 0x6000_0000, 3, true);
        state.seed_region_bytes(region, 0, &[1, 2, 3]);
        let branch = super::RuntimeLoopBranch {
            counter: counter_phi,
            threshold: 3,
            target: 0x2000,
        };

        let system = derive_loop_transition_system(
            &artifact_without_inductions(),
            &block,
            &state,
            &branch,
            0,
            3,
        );
        assert!(system.is_exact(), "{:?}", system.reasons);
        assert!(system.recurrences.iter().any(|recurrence| {
            matches!(
                &recurrence.kind,
                LoopRecurrenceKind::AddMemoryFold(term)
                    if term.kind == LoopMemoryTermKind::RuntimeBlobRead
                        && term.base == Some(0x6000_0000)
                        && term.region_base == Some(0x6000_0000)
                        && term.region_size == Some(3)
            )
        }));
        let summary = apply_exact_transition_system(&ctx, &state, &system).expect("summary");
        let summarized = summary.resulting_state.expect("state");
        assert_eq!(
            summarized.get_register_sized("RBX_2", 64).as_concrete(),
            Some(16)
        );
    }

    #[test]
    fn refuses_exact_symbolic_input_fold_when_bounds_are_unknown() {
        let counter_phi = var("RCX", 2, 8);
        let ptr_phi = var("RDI", 2, 8);
        let acc_phi = var("RBX", 2, 8);
        let block = FunctionSSABlock {
            addr: 0x1000,
            size: 4,
            phis: vec![
                PhiNode {
                    dst: counter_phi.clone(),
                    sources: vec![(0x900, var("RCX", 0, 8)), (0x1008, var("RCX", 1, 8))],
                    canonical_storage: None,
                },
                PhiNode {
                    dst: ptr_phi.clone(),
                    sources: vec![(0x900, var("RDI", 0, 8)), (0x1008, var("RDI", 1, 8))],
                    canonical_storage: None,
                },
                PhiNode {
                    dst: acc_phi.clone(),
                    sources: vec![(0x900, var("RBX", 0, 8)), (0x1008, var("RBX", 1, 8))],
                    canonical_storage: None,
                },
            ],
            ops: vec![
                SSAOp::IntAdd {
                    dst: var("RCX", 1, 8),
                    a: counter_phi.clone(),
                    b: const_var(1, 8),
                },
                SSAOp::IntAdd {
                    dst: var("RDI", 1, 8),
                    a: ptr_phi.clone(),
                    b: const_var(1, 8),
                },
                SSAOp::Load {
                    dst: var("TMP", 0, 1),
                    space: r2il::SpaceId::Ram,
                    addr: ptr_phi,
                },
                SSAOp::IntXor {
                    dst: var("RBX", 1, 8),
                    a: acc_phi,
                    b: var("TMP", 0, 1),
                },
            ],
        };
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.set_prev_pc(Some(0x900));
        state.set_register("RCX_0", SymValue::concrete(0, 64));
        state.set_register("RDI_0", SymValue::concrete(0x7000, 64));
        state.set_register("RBX_0", SymValue::concrete(0, 64));
        state.make_symbolic_memory(0x7000, 2, "argv1");
        let branch = super::RuntimeLoopBranch {
            counter: counter_phi,
            threshold: 3,
            target: 0x2000,
        };

        let system = derive_loop_transition_system(
            &artifact_without_inductions(),
            &block,
            &state,
            &branch,
            0,
            3,
        );
        assert!(!system.is_exact());
        assert!(
            system
                .reasons
                .contains(&"runtime_loop_memory_bounds_unknown:RBX_2".to_string())
        );
    }
}
