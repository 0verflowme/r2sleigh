//! Solver tactics over canonical semantic evidence.
//!
//! Tactics must not claim proof. They only add typed constraints that bias
//! model extraction toward useful candidates; replay/verification remains the
//! authority for `solved`.

use std::collections::{BTreeMap, BTreeSet};

use z3::ast::{BV, Bool};

use crate::constraints::{
    FinalConstraintGraph, RecurrenceAggregateConstraint, RecurrenceAggregateRangeConstraint,
};
use crate::loops::{
    ExactLoopFoldEvidence, ExactLoopRecurrenceEvidence, ExactLoopRecurrenceKind, LoopFoldOperation,
    LoopMemoryTerm, LoopMemoryTermKind, LoopRotateDirection,
};
use crate::{SymState, SymValue, aggregate_exact_fold_bytes};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputByteDomain {
    Any,
    PrintableAscii,
    AlphaNum,
    Ranges(Vec<(u8, u8)>),
    Bytes(Vec<u8>),
}

impl InputByteDomain {
    pub fn printable_ascii() -> Self {
        Self::PrintableAscii
    }

    pub fn ranges(&self) -> Vec<(u8, u8)> {
        match self {
            Self::Any => vec![(0x00, 0xff)],
            Self::PrintableAscii => vec![(0x20, 0x7e)],
            Self::AlphaNum => vec![(b'0', b'9'), (b'A', b'Z'), (b'a', b'z')],
            Self::Ranges(ranges) => normalize_ranges(ranges.iter().copied()),
            Self::Bytes(bytes) => normalize_ranges(bytes.iter().copied().map(|byte| (byte, byte))),
        }
    }

    fn is_any(&self) -> bool {
        matches!(self, Self::Any)
    }

    pub fn allowed_bytes(&self) -> Vec<u8> {
        self.ranges()
            .into_iter()
            .flat_map(|(start, end)| start..=end)
            .collect()
    }

    pub fn contains(&self, byte: u8) -> bool {
        self.ranges()
            .into_iter()
            .any(|(start, end)| byte >= start && byte <= end)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolveTacticConfig {
    pub enabled: bool,
    pub preferred_domains: Vec<InputByteDomain>,
    pub max_constrained_bytes: usize,
    pub max_candidates: usize,
    pub max_mitm_table: usize,
    pub max_target_enumeration: usize,
}

impl Default for SolveTacticConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            preferred_domains: vec![InputByteDomain::PrintableAscii, InputByteDomain::Any],
            max_constrained_bytes: 256,
            max_candidates: 32,
            max_mitm_table: 32_768,
            max_target_enumeration: 256,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstraintCandidateStrategy {
    Algebraic,
    Mitm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TacticConstraintReport {
    pub constrained_bytes: usize,
    pub skipped_reasons: Vec<String>,
}

impl TacticConstraintReport {
    fn new(constrained_bytes: usize, skipped_reasons: Vec<String>) -> Self {
        Self {
            constrained_bytes,
            skipped_reasons,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolveTacticCandidate {
    pub recurrence: ExactLoopRecurrenceEvidence,
    pub domain: InputByteDomain,
    pub bytes: Vec<u8>,
    pub target: u64,
    pub used_mitm: bool,
    pub reason: String,
}

pub fn constrain_exact_fold_inputs<'ctx>(
    state: &mut SymState<'ctx>,
    folds: &[ExactLoopFoldEvidence],
    domain: &InputByteDomain,
    max_constrained_bytes: usize,
) -> TacticConstraintReport {
    if domain.is_any() {
        return TacticConstraintReport::new(0, Vec::new());
    }

    let mut addresses = BTreeSet::new();
    let mut skipped_reasons = Vec::new();
    for fold in folds {
        if fold.term.kind != LoopMemoryTermKind::InputRead {
            continue;
        }
        if fold.term.bytes != 1 {
            push_unique(
                &mut skipped_reasons,
                format!("unsupported_fold_read_width:{}", fold.term.bytes),
            );
            continue;
        }
        let (Some(base), Some(stride)) = (fold.term.base, fold.term.stride) else {
            push_unique(&mut skipped_reasons, "missing_fold_input_address");
            continue;
        };
        for iteration in 0..fold.iterations {
            if addresses.len() >= max_constrained_bytes {
                push_unique(&mut skipped_reasons, "tactic_input_byte_budget");
                break;
            }
            let Some(offset) = iteration.checked_mul(stride) else {
                push_unique(&mut skipped_reasons, "fold_input_address_overflow");
                break;
            };
            let Some(addr) = base.checked_add(offset) else {
                push_unique(&mut skipped_reasons, "fold_input_address_overflow");
                break;
            };
            addresses.insert(addr);
        }
    }

    let constrained_bytes = addresses.len();
    for addr in addresses {
        let value = state.mem_read(&SymValue::concrete(addr, 64), 1);
        constrain_byte_to_domain(state, &value, domain);
    }

    TacticConstraintReport::new(constrained_bytes, skipped_reasons)
}

pub fn constrain_exact_fold_candidate<'ctx>(
    state: &mut SymState<'ctx>,
    fold: &ExactLoopFoldEvidence,
    bytes: &[u8],
) -> TacticConstraintReport {
    let mut skipped_reasons = Vec::new();
    if fold.term.kind != LoopMemoryTermKind::InputRead {
        return TacticConstraintReport::new(0, skipped_reasons);
    }
    if fold.term.bytes != 1 {
        push_unique(
            &mut skipped_reasons,
            format!("unsupported_fold_read_width:{}", fold.term.bytes),
        );
        return TacticConstraintReport::new(0, skipped_reasons);
    }
    if bytes.len() != fold.iterations as usize {
        push_unique(&mut skipped_reasons, "candidate_length_mismatch");
        return TacticConstraintReport::new(0, skipped_reasons);
    }
    let (Some(base), Some(stride)) = (fold.term.base, fold.term.stride) else {
        push_unique(&mut skipped_reasons, "missing_fold_input_address");
        return TacticConstraintReport::new(0, skipped_reasons);
    };
    for (iteration, byte) in bytes.iter().copied().enumerate() {
        let Some(offset) = (iteration as u64).checked_mul(stride) else {
            push_unique(&mut skipped_reasons, "fold_input_address_overflow");
            continue;
        };
        let Some(addr) = base.checked_add(offset) else {
            push_unique(&mut skipped_reasons, "fold_input_address_overflow");
            continue;
        };
        let value = state.mem_read(&SymValue::concrete(addr, 64), 1);
        state.constrain_eq(&value, byte as u64);
    }
    TacticConstraintReport::new(bytes.len(), skipped_reasons)
}

fn constrain_input_term_candidate<'ctx>(
    state: &mut SymState<'ctx>,
    term: &LoopMemoryTerm,
    iterations: u64,
    bytes: &[u8],
) -> TacticConstraintReport {
    let mut skipped_reasons = Vec::new();
    if term.kind != LoopMemoryTermKind::InputRead {
        return TacticConstraintReport::new(0, skipped_reasons);
    }
    if term.bytes != 1 {
        push_unique(
            &mut skipped_reasons,
            format!("unsupported_recurrence_read_width:{}", term.bytes),
        );
        return TacticConstraintReport::new(0, skipped_reasons);
    }
    if bytes.len() != iterations as usize {
        push_unique(&mut skipped_reasons, "candidate_length_mismatch");
        return TacticConstraintReport::new(0, skipped_reasons);
    }
    let (Some(base), Some(stride)) = (term.base, term.stride) else {
        push_unique(&mut skipped_reasons, "missing_recurrence_input_address");
        return TacticConstraintReport::new(0, skipped_reasons);
    };
    for (iteration, byte) in bytes.iter().copied().enumerate() {
        let Some(offset) = (iteration as u64).checked_mul(stride) else {
            push_unique(&mut skipped_reasons, "recurrence_input_address_overflow");
            continue;
        };
        let Some(addr) = base.checked_add(offset) else {
            push_unique(&mut skipped_reasons, "recurrence_input_address_overflow");
            continue;
        };
        let value = state.mem_read(&SymValue::concrete(addr, 64), 1);
        state.constrain_eq(&value, byte as u64);
    }
    TacticConstraintReport::new(bytes.len(), skipped_reasons)
}

fn recurrence_input_term(recurrence: &ExactLoopRecurrenceEvidence) -> Option<&LoopMemoryTerm> {
    match &recurrence.kind {
        ExactLoopRecurrenceKind::Fold { term, .. }
        | ExactLoopRecurrenceKind::RotateMix { term, .. } => Some(term),
        _ => None,
    }
}

pub fn constrain_exact_recurrence_candidate<'ctx>(
    state: &mut SymState<'ctx>,
    recurrence: &ExactLoopRecurrenceEvidence,
    bytes: &[u8],
) -> TacticConstraintReport {
    let Some(term) = recurrence_input_term(recurrence) else {
        return TacticConstraintReport::new(
            0,
            vec!["unsupported_recurrence_candidate".to_string()],
        );
    };
    constrain_input_term_candidate(state, term, recurrence.iterations, bytes)
}

pub fn algebraic_preimage_candidate(
    fold: &ExactLoopFoldEvidence,
    model_bytes: &[u8],
    domain: &InputByteDomain,
) -> Option<Vec<u8>> {
    if fold.term.kind != LoopMemoryTermKind::InputRead || fold.term.bytes != 1 {
        return None;
    }
    if model_bytes.len() != fold.iterations as usize || model_bytes.is_empty() {
        return None;
    }
    match fold.operation {
        LoopFoldOperation::Xor => xor_preimage_candidate(model_bytes, domain),
        LoopFoldOperation::Add => add_preimage_candidate(model_bytes, domain, fold.bits),
    }
}

pub fn algebraic_preimage_for_target(
    fold: &ExactLoopFoldEvidence,
    target: u64,
    domain: &InputByteDomain,
) -> Option<Vec<u8>> {
    if fold.term.kind != LoopMemoryTermKind::InputRead || fold.term.bytes != 1 {
        return None;
    }
    if fold.iterations == 0 {
        return None;
    }
    match fold.operation {
        LoopFoldOperation::Xor => xor_preimage_for_target(fold.iterations as usize, target, domain),
        LoopFoldOperation::Add => {
            add_preimage_for_target(fold.iterations as usize, target, domain, fold.bits)
        }
    }
}

pub fn tactic_candidates_for_constraint_graph<'ctx>(
    graph: &FinalConstraintGraph,
    state: Option<&SymState<'ctx>>,
    config: &SolveTacticConfig,
) -> Vec<SolveTacticCandidate> {
    if !config.enabled || graph.is_empty() {
        return Vec::new();
    }
    let mut candidates = Vec::new();
    for constraint in graph.recurrence_aggregate_constraints() {
        for domain in &config.preferred_domains {
            if candidates.len() >= config.max_candidates {
                return candidates;
            }
            if let Some(candidate) =
                tactic_candidate_for_recurrence_constraint(constraint, graph, state, domain, config)
            {
                candidates.push(candidate);
            }
        }
    }
    for constraint in graph.recurrence_aggregate_range_constraints() {
        for domain in &config.preferred_domains {
            if candidates.len() >= config.max_candidates {
                return candidates;
            }
            if let Some(candidate) = tactic_candidate_for_recurrence_range_constraint(
                constraint, graph, state, domain, config,
            ) {
                candidates.push(candidate);
            }
        }
    }
    candidates
}

fn xor_preimage_candidate(model_bytes: &[u8], domain: &InputByteDomain) -> Option<Vec<u8>> {
    let target = model_bytes.iter().fold(0u8, |acc, byte| acc ^ byte);
    xor_preimage_for_target(model_bytes.len(), target as u64, domain)
}

fn xor_preimage_for_target(count: usize, target: u64, domain: &InputByteDomain) -> Option<Vec<u8>> {
    let allowed = domain.allowed_bytes();
    if allowed.is_empty() {
        return None;
    }
    let target = target as u8;
    if count == 1 {
        return domain.contains(target).then_some(vec![target]);
    }

    let preferred = preferred_byte(&allowed);
    let mut candidate = vec![preferred; count];
    let prefix_xor = candidate
        .iter()
        .take(candidate.len().saturating_sub(2))
        .fold(0u8, |acc, byte| acc ^ byte);
    let pair_target = target ^ prefix_xor;
    for &lhs in &allowed {
        let rhs = lhs ^ pair_target;
        if domain.contains(rhs) {
            let last = candidate.len() - 1;
            candidate[last - 1] = lhs;
            candidate[last] = rhs;
            return Some(candidate);
        }
    }
    None
}

fn add_preimage_candidate(
    model_bytes: &[u8],
    domain: &InputByteDomain,
    bits: u32,
) -> Option<Vec<u8>> {
    let target = model_bytes
        .iter()
        .fold(0u128, |acc, byte| acc.saturating_add(*byte as u128));
    add_preimage_for_target(model_bytes.len(), target as u64, domain, bits)
}

fn add_preimage_for_target(
    count: usize,
    target: u64,
    domain: &InputByteDomain,
    bits: u32,
) -> Option<Vec<u8>> {
    let allowed = domain.allowed_bytes();
    if allowed.is_empty() {
        return None;
    }
    let modulus = if bits >= 64 {
        None
    } else {
        Some(1u128 << bits.max(1))
    };
    let target = target as u128;
    let target_mod = modulus.map_or(target, |modulus| target % modulus);
    let min_byte = *allowed.first()? as u128;
    let max_byte = *allowed.last()? as u128;
    let min_sum = min_byte.saturating_mul(count as u128);
    let max_sum = max_byte.saturating_mul(count as u128);
    let target_sum = match modulus {
        Some(modulus) => {
            let mut candidate = target_mod;
            while candidate < min_sum {
                candidate = candidate.saturating_add(modulus);
            }
            if candidate > max_sum {
                return None;
            }
            candidate
        }
        None if target_mod >= min_sum && target_mod <= max_sum => target_mod,
        None => return None,
    };

    let mut remaining = target_sum;
    let mut candidate = Vec::with_capacity(count);
    for index in 0..count {
        let slots_left = count - index - 1;
        let min_tail = min_byte.saturating_mul(slots_left as u128);
        let max_tail = max_byte.saturating_mul(slots_left as u128);
        let byte = allowed.iter().copied().find(|byte| {
            let value = *byte as u128;
            value <= remaining
                && remaining.saturating_sub(value) >= min_tail
                && remaining.saturating_sub(value) <= max_tail
        })?;
        candidate.push(byte);
        remaining = remaining.saturating_sub(byte as u128);
    }
    (remaining == 0).then_some(candidate)
}

fn tactic_candidate_for_recurrence_constraint(
    constraint: &RecurrenceAggregateConstraint,
    graph: &FinalConstraintGraph,
    state: Option<&SymState<'_>>,
    domain: &InputByteDomain,
    config: &SolveTacticConfig,
) -> Option<SolveTacticCandidate> {
    let allowed = allowed_bytes_for_recurrence(graph, &constraint.recurrence, domain)?;
    let (bytes, strategy) = candidate_for_recurrence_target_with_allowed(
        &constraint.recurrence,
        state,
        constraint.target,
        &allowed,
        config,
    )?;
    Some(SolveTacticCandidate {
        recurrence: constraint.recurrence.clone(),
        domain: domain.clone(),
        bytes,
        target: constraint.target,
        used_mitm: strategy == ConstraintCandidateStrategy::Mitm,
        reason: tactic_reason_for_recurrence(&constraint.recurrence, graph, "exact", strategy),
    })
}

fn tactic_candidate_for_recurrence_range_constraint(
    constraint: &RecurrenceAggregateRangeConstraint,
    graph: &FinalConstraintGraph,
    state: Option<&SymState<'_>>,
    domain: &InputByteDomain,
    config: &SolveTacticConfig,
) -> Option<SolveTacticCandidate> {
    let allowed = allowed_bytes_for_recurrence(graph, &constraint.recurrence, domain)?;
    let (target, bytes, strategy) = select_target_for_range_constraint(
        &constraint.recurrence,
        state,
        &allowed,
        constraint,
        config,
    )?;
    Some(SolveTacticCandidate {
        recurrence: constraint.recurrence.clone(),
        domain: domain.clone(),
        bytes,
        target,
        used_mitm: strategy == ConstraintCandidateStrategy::Mitm,
        reason: tactic_reason_for_recurrence(&constraint.recurrence, graph, "range", strategy),
    })
}

fn tactic_reason_for_recurrence(
    recurrence: &ExactLoopRecurrenceEvidence,
    graph: &FinalConstraintGraph,
    prefix: &str,
    strategy: ConstraintCandidateStrategy,
) -> String {
    let strategy = match strategy {
        ConstraintCandidateStrategy::Algebraic => "algebraic",
        ConstraintCandidateStrategy::Mitm => "mitm",
    };
    let base = match &recurrence.kind {
        ExactLoopRecurrenceKind::Fold { operation, .. } => match operation {
            LoopFoldOperation::Xor => {
                format!("{prefix} {strategy} xor-fold preimage from constraint graph")
            }
            LoopFoldOperation::Add => {
                format!("{prefix} {strategy} add-fold preimage from constraint graph")
            }
        },
        ExactLoopRecurrenceKind::RotateMix { operation, .. } => match operation {
            LoopFoldOperation::Xor => {
                format!("{prefix} {strategy} rotate-xor recurrence preimage from constraint graph")
            }
            LoopFoldOperation::Add => {
                format!("{prefix} {strategy} rotate-add recurrence preimage from constraint graph")
            }
        },
        _ => format!("{prefix} {strategy} exact recurrence candidate from constraint graph"),
    };
    if graph.input_byte_constraints.is_empty() {
        base
    } else {
        format!("{base}; input assumptions applied")
    }
}

fn select_target_for_range_constraint(
    recurrence: &ExactLoopRecurrenceEvidence,
    state: Option<&SymState<'_>>,
    allowed: &[Vec<u8>],
    constraint: &RecurrenceAggregateRangeConstraint,
    config: &SolveTacticConfig,
) -> Option<(u64, Vec<u8>, ConstraintCandidateStrategy)> {
    let preferred = preferred_candidate_bytes(allowed)?;
    let preferred_target = recurrence_target_for_bytes(recurrence, state, &preferred)?;
    if preferred_target >= constraint.min
        && preferred_target <= constraint.max
        && let Some((bytes, strategy)) = candidate_for_recurrence_target_with_allowed(
            recurrence,
            state,
            preferred_target,
            allowed,
            config,
        )
    {
        return Some((preferred_target, bytes, strategy));
    }
    let budget = config.max_target_enumeration.max(1) as u64;
    let upper = constraint
        .max
        .min(constraint.min.saturating_add(budget.saturating_sub(1)));
    (constraint.min..=upper).find_map(|target| {
        candidate_for_recurrence_target_with_allowed(recurrence, state, target, allowed, config)
            .map(|(bytes, strategy)| (target, bytes, strategy))
    })
}

fn preferred_candidate_bytes(allowed: &[Vec<u8>]) -> Option<Vec<u8>> {
    let mut out = Vec::with_capacity(allowed.len());
    for choices in allowed {
        out.push(preferred_byte(choices));
    }
    Some(out)
}

fn allowed_bytes_for_recurrence(
    graph: &FinalConstraintGraph,
    recurrence: &ExactLoopRecurrenceEvidence,
    default_domain: &InputByteDomain,
) -> Option<Vec<Vec<u8>>> {
    let term = recurrence_input_term(recurrence)?;
    if term.kind != LoopMemoryTermKind::InputRead || term.bytes != 1 {
        return None;
    }
    let (Some(base), Some(stride)) = (term.base, term.stride) else {
        return None;
    };
    if stride == 0 {
        return None;
    }
    if let Some(length) = graph
        .input_length_constraints
        .iter()
        .find(|constraint| constraint.base_addr == base)
        && length.len != recurrence.iterations as u32
    {
        return None;
    }

    let mut allowed = vec![default_domain.allowed_bytes(); recurrence.iterations as usize];
    let by_addr = graph.input_byte_constraints.iter().fold(
        BTreeMap::<u64, Vec<u8>>::new(),
        |mut acc, constraint| {
            let mut next = constraint.allowed.clone();
            next.sort_unstable();
            next.dedup();
            acc.entry(constraint.addr)
                .and_modify(|existing| {
                    let existing_set = existing.iter().copied().collect::<BTreeSet<_>>();
                    let next_set = next.iter().copied().collect::<BTreeSet<_>>();
                    *existing = existing_set
                        .intersection(&next_set)
                        .copied()
                        .collect::<Vec<_>>();
                })
                .or_insert(next);
            acc
        },
    );

    for (index, bytes) in allowed.iter_mut().enumerate() {
        let addr = base.checked_add((index as u64).checked_mul(stride)?)?;
        if let Some(constrained) = by_addr.get(&addr) {
            let constrained_set = constrained.iter().copied().collect::<BTreeSet<_>>();
            *bytes = bytes
                .iter()
                .copied()
                .filter(|byte| constrained_set.contains(byte))
                .collect();
        }
        bytes.sort_unstable();
        bytes.dedup();
        if bytes.is_empty() {
            return None;
        }
    }
    Some(allowed)
}

fn candidate_for_recurrence_target_with_allowed(
    recurrence: &ExactLoopRecurrenceEvidence,
    state: Option<&SymState<'_>>,
    target: u64,
    allowed: &[Vec<u8>],
    config: &SolveTacticConfig,
) -> Option<(Vec<u8>, ConstraintCandidateStrategy)> {
    if let Some(fold) = recurrence.as_fold() {
        return candidate_for_target_with_allowed(&fold, target, allowed, config);
    }
    let initial = concrete_initial_for_recurrence(state, recurrence)?;
    if let Some(bytes) =
        rotate_mix_preimage_for_target_with_allowed(recurrence, initial, target, allowed)
    {
        return Some((bytes, ConstraintCandidateStrategy::Algebraic));
    }
    rotate_mix_mitm_preimage_for_target_with_allowed(recurrence, initial, target, allowed, config)
        .map(|bytes| (bytes, ConstraintCandidateStrategy::Mitm))
}

fn recurrence_target_for_bytes(
    recurrence: &ExactLoopRecurrenceEvidence,
    state: Option<&SymState<'_>>,
    bytes: &[u8],
) -> Option<u64> {
    if let Some(fold) = recurrence.as_fold() {
        return aggregate_exact_fold_bytes(&fold, bytes);
    }
    let initial = concrete_initial_for_recurrence(state, recurrence)?;
    rotate_mix_apply_bytes(recurrence, initial, bytes)
}

fn concrete_initial_for_recurrence(
    state: Option<&SymState<'_>>,
    recurrence: &ExactLoopRecurrenceEvidence,
) -> Option<u64> {
    let initial_name = recurrence.initial.as_str();
    if initial_name.is_empty() {
        return None;
    }
    let value = state?.get_register_sized(initial_name, recurrence.bits.max(1));
    value
        .as_concrete()
        .map(|value| mask_to_bits(value, recurrence.bits))
}

fn candidate_for_target_with_allowed(
    fold: &ExactLoopFoldEvidence,
    target: u64,
    allowed: &[Vec<u8>],
    config: &SolveTacticConfig,
) -> Option<(Vec<u8>, ConstraintCandidateStrategy)> {
    if let Some(bytes) = algebraic_preimage_for_target_with_allowed(fold, target, allowed) {
        return Some((bytes, ConstraintCandidateStrategy::Algebraic));
    }
    mitm_preimage_for_target_with_allowed(fold, target, allowed, config)
        .map(|bytes| (bytes, ConstraintCandidateStrategy::Mitm))
}

fn algebraic_preimage_for_target_with_allowed(
    fold: &ExactLoopFoldEvidence,
    target: u64,
    allowed: &[Vec<u8>],
) -> Option<Vec<u8>> {
    if fold.iterations as usize != allowed.len() {
        return None;
    }
    match fold.operation {
        LoopFoldOperation::Xor => xor_preimage_for_target_with_allowed(allowed, target),
        LoopFoldOperation::Add => add_preimage_for_target_with_allowed(allowed, target, fold.bits),
    }
}

fn xor_preimage_for_target_with_allowed(allowed: &[Vec<u8>], target: u64) -> Option<Vec<u8>> {
    if allowed.is_empty() {
        return None;
    }
    if allowed.len() == 1 {
        let target = target as u8;
        return allowed[0].contains(&target).then_some(vec![target]);
    }
    let mut candidate = preferred_candidate_bytes(allowed)?;
    let prefix_xor = candidate
        .iter()
        .take(candidate.len().saturating_sub(2))
        .fold(0u8, |acc, byte| acc ^ byte);
    let pair_target = (target as u8) ^ prefix_xor;
    let penultimate = candidate.len() - 2;
    let last = candidate.len() - 1;
    let final_allowed = allowed[last].iter().copied().collect::<BTreeSet<_>>();
    for &lhs in &allowed[penultimate] {
        let rhs = lhs ^ pair_target;
        if final_allowed.contains(&rhs) {
            candidate[penultimate] = lhs;
            candidate[last] = rhs;
            return Some(candidate);
        }
    }
    None
}

fn add_preimage_for_target_with_allowed(
    allowed: &[Vec<u8>],
    target: u64,
    bits: u32,
) -> Option<Vec<u8>> {
    if allowed.is_empty() {
        return None;
    }
    let modulus = if bits >= 64 {
        None
    } else {
        Some(1u128 << bits.max(1))
    };
    let target = target as u128;
    let target_mod = modulus.map_or(target, |modulus| target % modulus);
    let min_sum = allowed
        .iter()
        .map(|bytes| *bytes.first().unwrap_or(&0) as u128)
        .sum::<u128>();
    let max_sum = allowed
        .iter()
        .map(|bytes| *bytes.last().unwrap_or(&0) as u128)
        .sum::<u128>();
    let target_sum = match modulus {
        Some(modulus) => {
            let mut candidate = target_mod;
            while candidate < min_sum {
                candidate = candidate.saturating_add(modulus);
            }
            if candidate > max_sum {
                return None;
            }
            candidate
        }
        None if target_mod >= min_sum && target_mod <= max_sum => target_mod,
        None => return None,
    };
    let mut min_suffix = vec![0u128; allowed.len() + 1];
    let mut max_suffix = vec![0u128; allowed.len() + 1];
    for index in (0..allowed.len()).rev() {
        min_suffix[index] = min_suffix[index + 1] + *allowed[index].first()? as u128;
        max_suffix[index] = max_suffix[index + 1] + *allowed[index].last()? as u128;
    }
    let mut remaining = target_sum;
    let mut candidate = Vec::with_capacity(allowed.len());
    for (index, bytes) in allowed.iter().enumerate() {
        let min_tail = min_suffix[index + 1];
        let max_tail = max_suffix[index + 1];
        let byte = bytes.iter().copied().find(|byte| {
            let value = *byte as u128;
            value <= remaining
                && remaining.saturating_sub(value) >= min_tail
                && remaining.saturating_sub(value) <= max_tail
        })?;
        candidate.push(byte);
        remaining = remaining.saturating_sub(byte as u128);
    }
    (remaining == 0).then_some(candidate)
}

fn rotate_mix_preimage_for_target_with_allowed(
    recurrence: &ExactLoopRecurrenceEvidence,
    initial: u64,
    target: u64,
    allowed: &[Vec<u8>],
) -> Option<Vec<u8>> {
    let spec = rotate_mix_spec(recurrence)?;
    if allowed.len() != recurrence.iterations as usize || allowed.is_empty() {
        return None;
    }
    let mut candidate = preferred_candidate_bytes(allowed)?;
    let last = candidate.len() - 1;
    let prefix_acc = rotate_mix_apply_prefix(initial, &candidate[..last], recurrence.bits, spec)?;
    if let Some(byte) = rotate_mix_required_final_byte(prefix_acc, target, recurrence.bits, spec)
        && allowed[last].contains(&byte)
    {
        candidate[last] = byte;
        return Some(candidate);
    }
    if candidate.len() < 2 {
        return None;
    }
    let penultimate = candidate.len() - 2;
    let prefix_acc =
        rotate_mix_apply_prefix(initial, &candidate[..penultimate], recurrence.bits, spec)?;
    let last_allowed = allowed[last].iter().copied().collect::<BTreeSet<_>>();
    for &byte in &allowed[penultimate] {
        let after_penultimate = rotate_mix_apply_step(prefix_acc, byte, recurrence.bits, spec);
        let Some(last_byte) =
            rotate_mix_required_final_byte(after_penultimate, target, recurrence.bits, spec)
        else {
            continue;
        };
        if last_allowed.contains(&last_byte) {
            candidate[penultimate] = byte;
            candidate[last] = last_byte;
            return Some(candidate);
        }
    }
    None
}

fn mitm_preimage_for_target_with_allowed(
    fold: &ExactLoopFoldEvidence,
    target: u64,
    allowed: &[Vec<u8>],
    config: &SolveTacticConfig,
) -> Option<Vec<u8>> {
    if allowed.len() < 2 || config.max_mitm_table == 0 {
        return None;
    }
    match fold.operation {
        LoopFoldOperation::Xor => {
            xor_mitm_preimage_for_target_with_allowed(allowed, target, config.max_mitm_table)
        }
        LoopFoldOperation::Add => {
            add_mitm_preimage_for_target_with_allowed(allowed, target, fold.bits, config)
        }
    }
}

fn rotate_mix_mitm_preimage_for_target_with_allowed(
    recurrence: &ExactLoopRecurrenceEvidence,
    initial: u64,
    target: u64,
    allowed: &[Vec<u8>],
    config: &SolveTacticConfig,
) -> Option<Vec<u8>> {
    if allowed.len() < 2 || config.max_mitm_table == 0 {
        return None;
    }
    let spec = rotate_mix_spec(recurrence)?;
    let split = allowed.len() / 2;
    let (left, right) = allowed.split_at(split);
    if left.is_empty() || right.is_empty() {
        return None;
    }
    let left_table =
        build_rotate_mix_half_table(left, initial, recurrence.bits, spec, config.max_mitm_table)?;
    search_rotate_mix_half_table(right, target, recurrence.bits, spec, &left_table)
}

fn xor_mitm_preimage_for_target_with_allowed(
    allowed: &[Vec<u8>],
    target: u64,
    max_table: usize,
) -> Option<Vec<u8>> {
    let split = allowed.len() / 2;
    let (left, right) = allowed.split_at(split);
    if left.is_empty() || right.is_empty() {
        return None;
    }
    let left_table = build_xor_half_table(left, max_table)?;
    search_xor_half_table(right, target as u8, &left_table)
}

fn build_xor_half_table(allowed: &[Vec<u8>], max_table: usize) -> Option<BTreeMap<u8, Vec<u8>>> {
    fn recurse(
        allowed: &[Vec<u8>],
        index: usize,
        aggregate: u8,
        current: &mut Vec<u8>,
        table: &mut BTreeMap<u8, Vec<u8>>,
        max_table: usize,
    ) -> bool {
        if index == allowed.len() {
            table.entry(aggregate).or_insert_with(|| current.clone());
            return table.len() <= max_table;
        }
        for &byte in &allowed[index] {
            current.push(byte);
            if !recurse(
                allowed,
                index + 1,
                aggregate ^ byte,
                current,
                table,
                max_table,
            ) {
                current.pop();
                return false;
            }
            current.pop();
        }
        true
    }

    let mut table = BTreeMap::new();
    let mut current = Vec::with_capacity(allowed.len());
    recurse(allowed, 0, 0, &mut current, &mut table, max_table).then_some(table)
}

fn search_xor_half_table(
    allowed: &[Vec<u8>],
    target: u8,
    left_table: &BTreeMap<u8, Vec<u8>>,
) -> Option<Vec<u8>> {
    fn recurse(
        allowed: &[Vec<u8>],
        index: usize,
        aggregate: u8,
        target: u8,
        current: &mut Vec<u8>,
        left_table: &BTreeMap<u8, Vec<u8>>,
    ) -> Option<Vec<u8>> {
        if index == allowed.len() {
            let needed = target ^ aggregate;
            let mut candidate = left_table.get(&needed)?.clone();
            candidate.extend_from_slice(current);
            return Some(candidate);
        }
        for &byte in &allowed[index] {
            current.push(byte);
            if let Some(candidate) = recurse(
                allowed,
                index + 1,
                aggregate ^ byte,
                target,
                current,
                left_table,
            ) {
                return Some(candidate);
            }
            current.pop();
        }
        None
    }

    let mut current = Vec::with_capacity(allowed.len());
    recurse(allowed, 0, 0, target, &mut current, left_table)
}

fn add_mitm_preimage_for_target_with_allowed(
    allowed: &[Vec<u8>],
    target: u64,
    bits: u32,
    config: &SolveTacticConfig,
) -> Option<Vec<u8>> {
    let split = allowed.len() / 2;
    let (left, right) = allowed.split_at(split);
    if left.is_empty() || right.is_empty() {
        return None;
    }
    let modulus = add_fold_modulus(bits);
    let target = modulus.map_or(target as u128, |modulus| (target as u128) % modulus);
    let left_table = build_add_half_table(left, modulus, config.max_mitm_table)?;
    search_add_half_table(right, target, modulus, &left_table)
}

fn add_fold_modulus(bits: u32) -> Option<u128> {
    if bits >= 64 {
        None
    } else {
        Some(1u128 << bits.max(1))
    }
}

fn add_fold_step(aggregate: u128, byte: u8, modulus: Option<u128>) -> u128 {
    let next = aggregate + byte as u128;
    modulus.map_or(next, |modulus| next % modulus)
}

fn build_add_half_table(
    allowed: &[Vec<u8>],
    modulus: Option<u128>,
    max_table: usize,
) -> Option<BTreeMap<u128, Vec<u8>>> {
    fn recurse(
        allowed: &[Vec<u8>],
        index: usize,
        aggregate: u128,
        modulus: Option<u128>,
        current: &mut Vec<u8>,
        table: &mut BTreeMap<u128, Vec<u8>>,
        max_table: usize,
    ) -> bool {
        if index == allowed.len() {
            table.entry(aggregate).or_insert_with(|| current.clone());
            return table.len() <= max_table;
        }
        for &byte in &allowed[index] {
            current.push(byte);
            let next = add_fold_step(aggregate, byte, modulus);
            if !recurse(allowed, index + 1, next, modulus, current, table, max_table) {
                current.pop();
                return false;
            }
            current.pop();
        }
        true
    }

    let mut table = BTreeMap::new();
    let mut current = Vec::with_capacity(allowed.len());
    recurse(allowed, 0, 0, modulus, &mut current, &mut table, max_table).then_some(table)
}

fn search_add_half_table(
    allowed: &[Vec<u8>],
    target: u128,
    modulus: Option<u128>,
    left_table: &BTreeMap<u128, Vec<u8>>,
) -> Option<Vec<u8>> {
    fn recurse(
        allowed: &[Vec<u8>],
        index: usize,
        aggregate: u128,
        target: u128,
        modulus: Option<u128>,
        current: &mut Vec<u8>,
        left_table: &BTreeMap<u128, Vec<u8>>,
    ) -> Option<Vec<u8>> {
        if index == allowed.len() {
            let needed = match modulus {
                Some(modulus) => (target + modulus - (aggregate % modulus)) % modulus,
                None if aggregate <= target => target - aggregate,
                None => return None,
            };
            let mut candidate = left_table.get(&needed)?.clone();
            candidate.extend_from_slice(current);
            return Some(candidate);
        }
        for &byte in &allowed[index] {
            current.push(byte);
            let next = add_fold_step(aggregate, byte, modulus);
            if let Some(candidate) = recurse(
                allowed,
                index + 1,
                next,
                target,
                modulus,
                current,
                left_table,
            ) {
                return Some(candidate);
            }
            current.pop();
        }
        None
    }

    let mut current = Vec::with_capacity(allowed.len());
    recurse(allowed, 0, 0, target, modulus, &mut current, left_table)
}

#[derive(Clone, Copy)]
struct RotateMixSpec {
    direction: LoopRotateDirection,
    amount: u32,
    operation: LoopFoldOperation,
}

fn rotate_mix_spec(recurrence: &ExactLoopRecurrenceEvidence) -> Option<RotateMixSpec> {
    let ExactLoopRecurrenceKind::RotateMix {
        direction,
        amount,
        operation,
        ..
    } = &recurrence.kind
    else {
        return None;
    };
    Some(RotateMixSpec {
        direction: *direction,
        amount: *amount,
        operation: *operation,
    })
}

fn rotate_mix_apply_bytes(
    recurrence: &ExactLoopRecurrenceEvidence,
    initial: u64,
    bytes: &[u8],
) -> Option<u64> {
    let spec = rotate_mix_spec(recurrence)?;
    rotate_mix_apply_prefix(initial, bytes, recurrence.bits, spec)
}

fn rotate_mix_apply_prefix(
    initial: u64,
    bytes: &[u8],
    bits: u32,
    spec: RotateMixSpec,
) -> Option<u64> {
    let mut acc = mask_to_bits(initial, bits);
    for &byte in bytes {
        acc = rotate_mix_apply_step(acc, byte, bits, spec);
    }
    Some(acc)
}

fn rotate_mix_apply_step(acc: u64, byte: u8, bits: u32, spec: RotateMixSpec) -> u64 {
    let rotated = rotate_bits(acc, spec.amount, bits, spec.direction);
    let byte = u64::from(byte);
    match spec.operation {
        LoopFoldOperation::Xor => mask_to_bits(rotated ^ byte, bits),
        LoopFoldOperation::Add => mask_to_bits(rotated.wrapping_add(byte), bits),
    }
}

fn rotate_mix_required_final_byte(
    acc_before_final: u64,
    target: u64,
    bits: u32,
    spec: RotateMixSpec,
) -> Option<u8> {
    let rotated = rotate_bits(acc_before_final, spec.amount, bits, spec.direction);
    let needed = match spec.operation {
        LoopFoldOperation::Xor => mask_to_bits(target ^ rotated, bits),
        LoopFoldOperation::Add => mask_to_bits(target.wrapping_sub(rotated), bits),
    };
    (needed <= u8::MAX as u64).then_some(needed as u8)
}

fn rotate_mix_reverse_step(acc_after: u64, byte: u8, bits: u32, spec: RotateMixSpec) -> u64 {
    let unrotated = match spec.operation {
        LoopFoldOperation::Xor => mask_to_bits(acc_after ^ u64::from(byte), bits),
        LoopFoldOperation::Add => mask_to_bits(acc_after.wrapping_sub(u64::from(byte)), bits),
    };
    rotate_bits(
        unrotated,
        spec.amount,
        bits,
        match spec.direction {
            LoopRotateDirection::Left => LoopRotateDirection::Right,
            LoopRotateDirection::Right => LoopRotateDirection::Left,
        },
    )
}

fn build_rotate_mix_half_table(
    allowed: &[Vec<u8>],
    initial: u64,
    bits: u32,
    spec: RotateMixSpec,
    max_table: usize,
) -> Option<BTreeMap<u64, Vec<u8>>> {
    struct Env<'a> {
        allowed: &'a [Vec<u8>],
        bits: u32,
        spec: RotateMixSpec,
        max_table: usize,
    }

    fn recurse(
        env: &Env<'_>,
        index: usize,
        acc: u64,
        current: &mut Vec<u8>,
        table: &mut BTreeMap<u64, Vec<u8>>,
    ) -> bool {
        if index == env.allowed.len() {
            table.entry(acc).or_insert_with(|| current.clone());
            return table.len() <= env.max_table;
        }
        for &byte in &env.allowed[index] {
            current.push(byte);
            let next = rotate_mix_apply_step(acc, byte, env.bits, env.spec);
            if !recurse(env, index + 1, next, current, table) {
                current.pop();
                return false;
            }
            current.pop();
        }
        true
    }

    let env = Env {
        allowed,
        bits,
        spec,
        max_table,
    };
    let mut table = BTreeMap::new();
    let mut current = Vec::with_capacity(allowed.len());
    recurse(
        &env,
        0,
        mask_to_bits(initial, bits),
        &mut current,
        &mut table,
    )
    .then_some(table)
}

fn search_rotate_mix_half_table(
    allowed: &[Vec<u8>],
    target: u64,
    bits: u32,
    spec: RotateMixSpec,
    left_table: &BTreeMap<u64, Vec<u8>>,
) -> Option<Vec<u8>> {
    fn recurse(
        allowed: &[Vec<u8>],
        index: usize,
        acc_after: u64,
        bits: u32,
        spec: RotateMixSpec,
        current_rev: &mut Vec<u8>,
        left_table: &BTreeMap<u64, Vec<u8>>,
    ) -> Option<Vec<u8>> {
        if index == 0 {
            let mut candidate = left_table.get(&acc_after)?.clone();
            current_rev.reverse();
            candidate.extend_from_slice(current_rev);
            current_rev.reverse();
            return Some(candidate);
        }
        let choices = &allowed[index - 1];
        for &byte in choices {
            current_rev.push(byte);
            let prev = rotate_mix_reverse_step(acc_after, byte, bits, spec);
            if let Some(candidate) = recurse(
                allowed,
                index - 1,
                prev,
                bits,
                spec,
                current_rev,
                left_table,
            ) {
                return Some(candidate);
            }
            current_rev.pop();
        }
        None
    }

    let mut current_rev = Vec::with_capacity(allowed.len());
    recurse(
        allowed,
        allowed.len(),
        mask_to_bits(target, bits),
        bits,
        spec,
        &mut current_rev,
        left_table,
    )
}

fn rotate_bits(value: u64, amount: u32, bits: u32, direction: LoopRotateDirection) -> u64 {
    let bits = bits.clamp(1, 64);
    let value = mask_to_bits(value, bits);
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
    };
    let rhs = match direction {
        LoopRotateDirection::Left => value >> (bits - amount),
        LoopRotateDirection::Right => value.wrapping_shl(bits - amount),
    };
    mask_to_bits(lhs | rhs, bits)
}

fn normalize_rotate_amount(amount: u32, bits: u32) -> u32 {
    if bits == 0 { 0 } else { amount % bits.min(64) }
}

fn mask_to_bits(value: u64, bits: u32) -> u64 {
    if bits >= 64 {
        value
    } else if bits == 0 {
        0
    } else {
        value & ((1u64 << bits) - 1)
    }
}

fn preferred_byte(allowed: &[u8]) -> u8 {
    for preferred in [b'A', b'a', b'0', b' '] {
        if allowed.binary_search(&preferred).is_ok() {
            return preferred;
        }
    }
    allowed[0]
}

fn constrain_byte_to_domain<'ctx>(
    state: &mut SymState<'ctx>,
    value: &SymValue<'ctx>,
    domain: &InputByteDomain,
) {
    let ranges = domain.ranges();
    if ranges.len() == 1 && ranges[0] == (0, u8::MAX) {
        return;
    }
    let ctx = state.context();
    let byte = value.extract(ctx, 7, 0).to_bv(ctx);
    let mut range_predicates = Vec::new();
    for (start, end) in ranges {
        if start == end {
            range_predicates.push(byte.eq(BV::from_u64(start as u64, 8)));
        } else {
            let ge = byte.bvuge(BV::from_u64(start as u64, 8));
            let le = byte.bvule(BV::from_u64(end as u64, 8));
            range_predicates.push(ge & le);
        }
    }
    if range_predicates.is_empty() {
        return;
    }
    let predicate = if range_predicates.len() == 1 {
        range_predicates.remove(0)
    } else {
        Bool::or(&range_predicates.iter().collect::<Vec<_>>())
    };
    state.add_constraint(predicate);
}

fn normalize_ranges(ranges: impl IntoIterator<Item = (u8, u8)>) -> Vec<(u8, u8)> {
    let mut ranges = ranges
        .into_iter()
        .map(|(start, end)| {
            if start <= end {
                (start, end)
            } else {
                (end, start)
            }
        })
        .collect::<Vec<_>>();
    ranges.sort_unstable();
    let mut out: Vec<(u8, u8)> = Vec::new();
    for (start, end) in ranges {
        if let Some(last) = out.last_mut()
            && start <= last.1.saturating_add(1)
        {
            last.1 = last.1.max(end);
            continue;
        }
        out.push((start, end));
    }
    out
}

fn push_unique(reasons: &mut Vec<String>, reason: impl Into<String>) {
    let reason = reason.into();
    if !reasons.iter().any(|existing| existing == &reason) {
        reasons.push(reason);
    }
}

#[cfg(test)]
mod tests {
    use z3::Context;

    use super::{
        InputByteDomain, SolveTacticConfig, algebraic_preimage_candidate,
        algebraic_preimage_for_target, constrain_exact_fold_inputs,
        constrain_exact_recurrence_candidate, recurrence_target_for_bytes,
        tactic_candidates_for_constraint_graph,
    };
    use crate::constraints::{
        FinalConstraint, FinalConstraintGraph, FinalConstraintPrecision, FinalConstraintSource,
        RecurrenceAggregateConstraint, RecurrenceAggregateRangeConstraint,
    };
    use crate::{
        ExactLoopFoldEvidence, ExactLoopRecurrenceEvidence, ExactLoopRecurrenceKind,
        LoopFoldOperation, LoopMemoryTerm, LoopMemoryTermKind, LoopRotateDirection, SymSolver,
        SymState, SymValue,
    };

    #[test]
    fn exact_input_fold_constraints_bias_model_to_printable_bytes() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic_memory(0x7000, 2, "argv1");
        let lhs = state.mem_read(&SymValue::concrete(0x7000, 64), 1);
        let rhs = state.mem_read(&SymValue::concrete(0x7001, 64), 1);
        let folded = lhs.xor(&ctx, &rhs);
        state.constrain_eq(&folded, 0);

        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 2,
            accumulator: "RBX_2".to_string(),
            bits: 8,
            operation: LoopFoldOperation::Xor,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_2".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(2),
            },
        };

        let report =
            constrain_exact_fold_inputs(&mut state, &[fold], &InputByteDomain::PrintableAscii, 16);
        assert_eq!(report.constrained_bytes, 2);
        assert!(report.skipped_reasons.is_empty());

        let solver = SymSolver::new(&ctx);
        let model = solver.solve(&state).expect("model");
        let bytes = model
            .eval_bytes(&state.symbolic_memory()[0].value, 2)
            .expect("bytes");
        assert!(bytes.iter().all(|byte| (0x20..=0x7e).contains(byte)));
        assert_eq!(bytes[0] ^ bytes[1], 0);
    }

    #[test]
    fn xor_preimage_rewrites_nonprintable_model_to_printable_equivalent() {
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 4,
            accumulator: "RBX_2".to_string(),
            bits: 8,
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
        let model = [0x00, 0x01, 0x02, 0x03];
        let candidate =
            algebraic_preimage_candidate(&fold, &model, &InputByteDomain::PrintableAscii)
                .expect("candidate");
        assert_eq!(candidate.len(), model.len());
        assert!(candidate.iter().all(|byte| (0x20..=0x7e).contains(byte)));
        assert_eq!(
            candidate.iter().fold(0u8, |acc, byte| acc ^ byte),
            model.iter().fold(0u8, |acc, byte| acc ^ byte)
        );
    }

    #[test]
    fn add_preimage_rewrites_sum_to_printable_equivalent() {
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 3,
            accumulator: "RBX_2".to_string(),
            bits: 16,
            operation: LoopFoldOperation::Add,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_2".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(3),
            },
        };
        let model = [1, 100, 100];
        let candidate =
            algebraic_preimage_candidate(&fold, &model, &InputByteDomain::PrintableAscii)
                .expect("candidate");
        assert_eq!(candidate.len(), model.len());
        assert!(candidate.iter().all(|byte| (0x20..=0x7e).contains(byte)));
        assert_eq!(
            candidate.iter().map(|byte| *byte as u16).sum::<u16>(),
            model.iter().map(|byte| *byte as u16).sum::<u16>()
        );
    }

    #[test]
    fn xor_preimage_for_target_solves_constraint_directly() {
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 5,
            accumulator: "RBX_2".to_string(),
            bits: 8,
            operation: LoopFoldOperation::Xor,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_2".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(5),
            },
        };
        let candidate =
            algebraic_preimage_for_target(&fold, 0x42, &InputByteDomain::PrintableAscii)
                .expect("candidate");
        assert_eq!(candidate.len(), 5);
        assert!(candidate.iter().all(|byte| (0x20..=0x7e).contains(byte)));
        assert_eq!(candidate.iter().fold(0u8, |acc, byte| acc ^ byte), 0x42);
    }

    #[test]
    fn constraint_graph_scheduler_returns_bounded_candidates() {
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 3,
            accumulator: "RBX_2".to_string(),
            bits: 16,
            operation: LoopFoldOperation::Add,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_2".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(3),
            },
        };
        let graph = FinalConstraintGraph {
            constraints: vec![FinalConstraint::RecurrenceEquals(
                RecurrenceAggregateConstraint {
                    recurrence: ExactLoopRecurrenceEvidence::from(fold),
                    target: 201,
                    bits: 16,
                    source: FinalConstraintSource::ExactRecurrenceAggregateModel,
                    precision: FinalConstraintPrecision::ModelConditioned,
                    reasons: Vec::new(),
                },
            )],
            input_byte_constraints: Vec::new(),
            input_length_constraints: Vec::new(),
            refusals: Vec::new(),
        };
        let config = SolveTacticConfig {
            max_candidates: 1,
            ..SolveTacticConfig::default()
        };
        let candidates = tactic_candidates_for_constraint_graph(&graph, None, &config);
        assert_eq!(candidates.len(), 1);
        assert_eq!(
            candidates[0]
                .bytes
                .iter()
                .map(|byte| *byte as u16)
                .sum::<u16>(),
            201
        );
    }

    #[test]
    fn range_constraint_scheduler_honors_input_byte_constraints() {
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 3,
            accumulator: "RBX_2".to_string(),
            bits: 8,
            operation: LoopFoldOperation::Xor,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_2".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(3),
            },
        };
        let graph = FinalConstraintGraph {
            constraints: vec![FinalConstraint::RecurrenceRange(
                RecurrenceAggregateRangeConstraint {
                    recurrence: ExactLoopRecurrenceEvidence::from(fold.clone()),
                    min: 0x40,
                    max: 0x4f,
                    bits: 8,
                    source: FinalConstraintSource::TerminalCompareExact,
                    precision: FinalConstraintPrecision::Exact,
                    reasons: Vec::new(),
                },
            )],
            input_byte_constraints: vec![crate::InputByteConstraint {
                addr: 0x7000,
                allowed: vec![b'K'],
                precision: FinalConstraintPrecision::Exact,
                source: FinalConstraintSource::MemoryWindowAssumption,
                reasons: Vec::new(),
            }],
            input_length_constraints: vec![crate::InputLengthConstraint {
                base_addr: 0x7000,
                len: 3,
                precision: FinalConstraintPrecision::Exact,
                source: FinalConstraintSource::MemoryWindowAssumption,
                reasons: Vec::new(),
            }],
            refusals: Vec::new(),
        };
        let candidates =
            tactic_candidates_for_constraint_graph(&graph, None, &SolveTacticConfig::default());
        assert!(!candidates.is_empty());
        assert_eq!(candidates[0].bytes[0], b'K');
        let folded = candidates[0].bytes.iter().fold(0u8, |acc, byte| acc ^ byte);
        assert!((0x40..=0x4f).contains(&folded));
    }

    #[test]
    fn mitm_scheduler_solves_xor_constraint_when_pairwise_algebraic_fails() {
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 4,
            accumulator: "RBX_2".to_string(),
            bits: 8,
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
        let graph = FinalConstraintGraph {
            constraints: vec![FinalConstraint::RecurrenceEquals(
                RecurrenceAggregateConstraint {
                    recurrence: ExactLoopRecurrenceEvidence::from(fold),
                    target: 0,
                    bits: 8,
                    source: FinalConstraintSource::TerminalCompareExact,
                    precision: FinalConstraintPrecision::Exact,
                    reasons: Vec::new(),
                },
            )],
            input_byte_constraints: vec![
                crate::InputByteConstraint {
                    addr: 0x7000,
                    allowed: vec![1, 2],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: Vec::new(),
                },
                crate::InputByteConstraint {
                    addr: 0x7001,
                    allowed: vec![3],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: Vec::new(),
                },
                crate::InputByteConstraint {
                    addr: 0x7002,
                    allowed: vec![4],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: Vec::new(),
                },
                crate::InputByteConstraint {
                    addr: 0x7003,
                    allowed: vec![5],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: Vec::new(),
                },
            ],
            input_length_constraints: vec![crate::InputLengthConstraint {
                base_addr: 0x7000,
                len: 4,
                precision: FinalConstraintPrecision::Exact,
                source: FinalConstraintSource::MemoryWindowAssumption,
                reasons: Vec::new(),
            }],
            refusals: Vec::new(),
        };

        let candidates =
            tactic_candidates_for_constraint_graph(&graph, None, &SolveTacticConfig::default());
        assert!(!candidates.is_empty());
        assert!(candidates[0].used_mitm);
        assert_eq!(candidates[0].bytes, vec![2, 3, 4, 5]);
        assert_eq!(
            candidates[0].bytes.iter().fold(0u8, |acc, byte| acc ^ byte),
            0
        );
    }

    #[test]
    fn mitm_scheduler_solves_add_constraint_when_greedy_algebraic_fails() {
        let fold = ExactLoopFoldEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 3,
            accumulator: "RBX_2".to_string(),
            bits: 16,
            operation: LoopFoldOperation::Add,
            term: LoopMemoryTerm {
                kind: LoopMemoryTermKind::InputRead,
                addr: "RDI_2".to_string(),
                bytes: 1,
                base: Some(0x7000),
                stride: Some(1),
                region: Some("argv1".to_string()),
                region_base: Some(0x7000),
                region_size: Some(3),
            },
        };
        let graph = FinalConstraintGraph {
            constraints: vec![FinalConstraint::RecurrenceEquals(
                RecurrenceAggregateConstraint {
                    recurrence: ExactLoopRecurrenceEvidence::from(fold),
                    target: 7,
                    bits: 16,
                    source: FinalConstraintSource::TerminalCompareExact,
                    precision: FinalConstraintPrecision::Exact,
                    reasons: Vec::new(),
                },
            )],
            input_byte_constraints: vec![
                crate::InputByteConstraint {
                    addr: 0x7000,
                    allowed: vec![1, 2],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: Vec::new(),
                },
                crate::InputByteConstraint {
                    addr: 0x7001,
                    allowed: vec![1, 4],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: Vec::new(),
                },
                crate::InputByteConstraint {
                    addr: 0x7002,
                    allowed: vec![1, 4],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: Vec::new(),
                },
            ],
            input_length_constraints: vec![crate::InputLengthConstraint {
                base_addr: 0x7000,
                len: 3,
                precision: FinalConstraintPrecision::Exact,
                source: FinalConstraintSource::MemoryWindowAssumption,
                reasons: Vec::new(),
            }],
            refusals: Vec::new(),
        };

        let candidates =
            tactic_candidates_for_constraint_graph(&graph, None, &SolveTacticConfig::default());
        assert!(!candidates.is_empty());
        assert!(candidates[0].used_mitm);
        assert_eq!(candidates[0].bytes, vec![2, 1, 4]);
        assert_eq!(
            candidates[0]
                .bytes
                .iter()
                .map(|byte| *byte as u16)
                .sum::<u16>(),
            7
        );
    }

    #[test]
    fn rotate_recurrence_constraint_produces_candidate_with_concrete_initial() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.set_register("RBX_1", SymValue::concrete(0xa5, 8));
        let recurrence = ExactLoopRecurrenceEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 3,
            accumulator: "RBX_2".to_string(),
            initial: "RBX_1".to_string(),
            bits: 8,
            kind: ExactLoopRecurrenceKind::RotateMix {
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
                    region_size: Some(3),
                },
            },
        };
        let expected = vec![0x12, 0x34, 0x56];
        let target =
            recurrence_target_for_bytes(&recurrence, Some(&state), &expected).expect("target");
        let graph = FinalConstraintGraph {
            constraints: vec![FinalConstraint::RecurrenceEquals(
                RecurrenceAggregateConstraint {
                    recurrence: recurrence.clone(),
                    target,
                    bits: 8,
                    source: FinalConstraintSource::TerminalCompareExact,
                    precision: FinalConstraintPrecision::Exact,
                    reasons: Vec::new(),
                },
            )],
            input_byte_constraints: vec![
                crate::InputByteConstraint {
                    addr: 0x7000,
                    allowed: vec![0x12, 0x13],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: Vec::new(),
                },
                crate::InputByteConstraint {
                    addr: 0x7001,
                    allowed: vec![0x34, 0x35],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: Vec::new(),
                },
                crate::InputByteConstraint {
                    addr: 0x7002,
                    allowed: vec![0x56, 0x57],
                    precision: FinalConstraintPrecision::Exact,
                    source: FinalConstraintSource::MemoryWindowAssumption,
                    reasons: Vec::new(),
                },
            ],
            input_length_constraints: vec![crate::InputLengthConstraint {
                base_addr: 0x7000,
                len: 3,
                precision: FinalConstraintPrecision::Exact,
                source: FinalConstraintSource::MemoryWindowAssumption,
                reasons: Vec::new(),
            }],
            refusals: Vec::new(),
        };

        let candidates = tactic_candidates_for_constraint_graph(
            &graph,
            Some(&state),
            &SolveTacticConfig::default(),
        );
        assert!(!candidates.is_empty());
        assert_eq!(candidates[0].recurrence, recurrence);
        assert_eq!(candidates[0].bytes, expected);
    }

    #[test]
    fn exact_rotate_recurrence_candidate_constrains_symbolic_input_bytes() {
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic_memory(0x7000, 3, "argv1");
        let recurrence = ExactLoopRecurrenceEvidence {
            header: 0x1000,
            exit_target: 0x2000,
            iterations: 3,
            accumulator: "RBX_2".to_string(),
            initial: "RBX_1".to_string(),
            bits: 8,
            kind: ExactLoopRecurrenceKind::RotateMix {
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
                    region_size: Some(3),
                },
            },
        };
        let expected = [0x12, 0x34, 0x56];
        let report = constrain_exact_recurrence_candidate(&mut state, &recurrence, &expected);
        assert_eq!(report.constrained_bytes, 3);
        assert!(report.skipped_reasons.is_empty());

        let solver = SymSolver::new(&ctx);
        let model = solver.solve(&state).expect("model");
        let bytes = model
            .eval_bytes(&state.symbolic_memory()[0].value, 3)
            .expect("bytes");
        assert_eq!(bytes, expected);
    }
}
