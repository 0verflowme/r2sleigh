use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::rc::Rc;

use r2ssa::graph::{InstPayload, ValueId};
use r2ssa::{CallSiteId, PredicateId, SsaArtifact};
use serde::{Deserialize, Serialize};
use z3::Context;
use z3::ast::{Ast, BV, Bool};
use z3::{SatResult as Z3SatResult, Solver};

use crate::sim::{CallConv, DerivedFunctionSummary};
use crate::state::SymState;
use crate::value::SymValue;
use crate::{
    MemoryRegionId, MemoryRegionKind, SemanticConfidence, SemanticEvidence,
    SemanticEvidenceCoverage, SemanticEvidenceProvenance, SemanticEvidenceReason,
    SemanticMemoryAddress,
};

const DEFAULT_REVERSE_PATH_LIMIT: usize = 16;
const DEFAULT_MAX_NORMALIZED_OFFSETS: usize = 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BackwardConditionPrecision {
    Exact,
    OverApprox,
    ResidualSearchRequired,
    Unsupported,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BackwardConditionSummary {
    pub simplified: String,
    pub terms: Vec<String>,
    pub memory_terms: Vec<BackwardMemoryCondition>,
    pub backward_memory_substitutions: usize,
    pub backward_memory_candidate_enumerations: usize,
    pub backward_memory_residual_fallbacks: usize,
    pub precision: BackwardConditionPrecision,
    pub supported_paths: usize,
    pub total_paths: usize,
}

impl BackwardConditionSummary {
    pub fn evidence(&self) -> SemanticEvidence {
        match self.precision {
            BackwardConditionPrecision::Exact => SemanticEvidence::exact(),
            BackwardConditionPrecision::OverApprox => {
                SemanticEvidence::likely(SemanticEvidenceReason::PartialPathCoverage)
                    .with_provenance(SemanticEvidenceProvenance::Normalized)
            }
            BackwardConditionPrecision::ResidualSearchRequired => {
                if self.supported_paths > 0
                    && !self.memory_terms.is_empty()
                    && self.backward_memory_residual_fallbacks == 0
                {
                    SemanticEvidence::likely(SemanticEvidenceReason::DerivedFromRanking)
                        .with_coverage(SemanticEvidenceCoverage::Bounded)
                        .with_provenance(SemanticEvidenceProvenance::Normalized)
                        .with_reason(SemanticEvidenceReason::PartialPathCoverage)
                } else if self.supported_paths > 0 {
                    SemanticEvidence::heuristic(SemanticEvidenceReason::ResidualSearchRequired)
                        .with_coverage(SemanticEvidenceCoverage::Bounded)
                } else {
                    SemanticEvidence::residual(SemanticEvidenceReason::ResidualSearchRequired)
                }
            }
            BackwardConditionPrecision::Unsupported => {
                SemanticEvidence::residual(SemanticEvidenceReason::ValueOpaque)
            }
        }
    }

    pub fn confidence(&self) -> SemanticConfidence {
        self.evidence().tier
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BackwardMemoryCondition {
    pub region: BackwardMemoryRegion,
    #[serde(flatten)]
    pub address: SemanticMemoryAddress,
    pub size: u32,
    #[serde(default, skip_serializing_if = "SemanticEvidence::is_default_exact")]
    pub evidence: SemanticEvidence,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub binding: Option<String>,
    pub expr: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub value_expr: Option<String>,
    #[serde(default)]
    pub exact_value: bool,
}

impl BackwardMemoryCondition {
    pub fn has_exact_address(&self) -> bool {
        self.address.has_exact_identity()
    }

    pub fn concrete_offset_range(&self) -> Option<(i64, i64)> {
        self.address.concrete_offset_range()
    }

    pub fn evidence(&self) -> SemanticEvidence {
        if self.evidence.is_default_exact() && !self.has_exact_address() {
            inferred_memory_term_evidence(
                &self.region,
                self.address.offset_lo(),
                self.address.offset_hi(),
                self.address.is_exact_offset(),
            )
        } else {
            self.evidence.clone()
        }
    }

    pub fn confidence(&self) -> SemanticConfidence {
        self.evidence().tier
    }
}

fn inferred_memory_term_evidence(
    region: &BackwardMemoryRegion,
    offset_lo: i64,
    offset_hi: i64,
    exact_offset: bool,
) -> SemanticEvidence {
    if exact_offset {
        SemanticEvidence::exact()
    } else {
        let Some(span) = (offset_hi >= offset_lo).then_some(offset_hi - offset_lo) else {
            return SemanticEvidence::heuristic(SemanticEvidenceReason::AliasAmbiguity)
                .with_coverage(SemanticEvidenceCoverage::Bounded);
        };

        let (likely_span, provenance, reason) = match region {
            BackwardMemoryRegion::Argument { .. } => (
                16,
                SemanticEvidenceProvenance::Stable,
                SemanticEvidenceReason::DerivedFromRanking,
            ),
            BackwardMemoryRegion::Region(region) => match region.kind {
                MemoryRegionKind::Stack | MemoryRegionKind::Global | MemoryRegionKind::Input => (
                    16,
                    SemanticEvidenceProvenance::Stable,
                    SemanticEvidenceReason::DerivedFromRanking,
                ),
                MemoryRegionKind::Replay => (
                    16,
                    SemanticEvidenceProvenance::Ranked,
                    SemanticEvidenceReason::ReplayOverlap,
                ),
                MemoryRegionKind::Heap => (
                    12,
                    SemanticEvidenceProvenance::Ranked,
                    SemanticEvidenceReason::HeapIdentityWeak,
                ),
                MemoryRegionKind::EscapedUnknown => (
                    8,
                    SemanticEvidenceProvenance::Unstable,
                    SemanticEvidenceReason::AliasAmbiguity,
                ),
            },
        };

        if span <= likely_span {
            SemanticEvidence::likely(reason)
                .with_coverage(SemanticEvidenceCoverage::Bounded)
                .with_provenance(provenance)
        } else {
            SemanticEvidence::heuristic(reason)
                .with_coverage(SemanticEvidenceCoverage::Bounded)
                .with_provenance(provenance)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BackwardRegionRef {
    pub id: MemoryRegionId,
    pub kind: MemoryRegionKind,
    pub name: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum BackwardMemoryRegion {
    Argument { index: usize },
    Region(BackwardRegionRef),
}

fn format_backward_memory_location(region: &BackwardMemoryRegion, offset: i64) -> String {
    match region {
        BackwardMemoryRegion::Argument { index } => {
            if offset == 0 {
                format!("*arg{index}")
            } else if offset > 0 {
                format!("*(arg{index} + 0x{:x})", offset as u64)
            } else {
                format!("*(arg{index} - 0x{:x})", offset.unsigned_abs())
            }
        }
        BackwardMemoryRegion::Region(region) => {
            let base = region.name.as_str();
            if offset == 0 {
                format!("*{base}")
            } else if offset > 0 {
                format!("*({base} + 0x{:x})", offset as u64)
            } else {
                format!("*({base} - 0x{:x})", offset.unsigned_abs())
            }
        }
    }
}

fn backward_memory_term_expr(
    region: &BackwardMemoryRegion,
    address: &SemanticMemoryAddress,
    fallback: &str,
) -> String {
    let offset_lo = address.offset_lo();
    let offset_hi = address.offset_hi();
    if !address.terms().is_empty() && offset_lo == offset_hi {
        let base = match region {
            BackwardMemoryRegion::Argument { index } => format!("arg{index}"),
            BackwardMemoryRegion::Region(region) => region.name.clone(),
        };
        let terms = address
            .terms()
            .iter()
            .map(|term| format!("{}*v{}", term.coefficient, term.value.0))
            .collect::<Vec<_>>();
        let mut components = Vec::with_capacity(terms.len() + 2);
        components.push(base);
        components.extend(terms);
        if offset_lo != 0 {
            components.push(offset_lo.to_string());
        }
        return format!("*({})", components.join(" + "));
    }
    if offset_lo == offset_hi {
        format_backward_memory_location(region, offset_lo)
    } else {
        fallback.to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct NormalizedMemoryLocation {
    region: BackwardMemoryRegion,
    offset: i64,
}

pub struct CompiledBackwardCondition {
    pub predicate: Bool,
    pub summary: BackwardConditionSummary,
}

#[derive(Clone)]
pub(crate) struct DerivedCallSummaryView<'ctx> {
    pub summary: Rc<DerivedFunctionSummary<'ctx>>,
    pub callconv: CallConv,
}

#[derive(Clone)]
struct ReversePath {
    block_addr: u64,
    phi_predecessors: BTreeMap<u64, u64>,
    assumptions: Vec<(PredicateId, bool)>,
    visited: BTreeSet<u64>,
}

#[derive(Debug)]
enum EvalUnsupported {
    Unsupported,
    Cycle,
}

struct ValueTranslator<'a, 'ctx> {
    func: &'a SsaArtifact,
    state: &'a SymState<'ctx>,
    memory_index: &'a BackwardMemoryIndex,
    phi_predecessors: &'a BTreeMap<u64, u64>,
    call_contexts: &'a HashMap<CallSiteId, CallTransformContext<'ctx>>,
    memo: HashMap<ValueId, SymValue<'ctx>>,
    visiting: HashSet<ValueId>,
    assumption_constraints: Vec<Bool>,
    memory_terms: Vec<BackwardMemoryCondition>,
    memory_substitutions: usize,
    memory_candidate_enumerations: usize,
    memory_residual_fallbacks: usize,
    used_unsummarized_memory: bool,
}

#[derive(Default)]
struct BackwardMemoryIndex {
    store_values: HashMap<(r2ssa::MemoryVersion, r2ssa::MemoryLocation), Option<r2ssa::SSAVar>>,
}

impl BackwardMemoryIndex {
    fn new(func: &SsaArtifact) -> Self {
        let mut index = Self::default();
        for (inst_id, defs) in &func.memory().defs_by_inst {
            let Some(inst) = func.graph().inst(*inst_id) else {
                continue;
            };
            let InstPayload::Op(r2ssa::SSAOp::Store { val, .. }) = &inst.payload else {
                continue;
            };
            for def in defs {
                let key = (def.next_version, def.location.clone());
                index
                    .store_values
                    .entry(key)
                    .and_modify(|candidate| {
                        if candidate.as_ref().is_some_and(|candidate| candidate != val) {
                            *candidate = None;
                        }
                    })
                    .or_insert_with(|| Some(val.clone()));
            }
        }
        index
    }

    fn reaching_store(&self, use_fact: &r2ssa::MemoryUseFact) -> Option<&r2ssa::SSAVar> {
        self.store_values
            .get(&(use_fact.version, use_fact.location.clone()))
            .and_then(Option::as_ref)
    }
}

#[derive(Clone)]
struct CallTransformContext<'ctx> {
    summary: Rc<DerivedFunctionSummary<'ctx>>,
    callconv: CallConv,
    args: Vec<SymValue<'ctx>>,
}

enum SummaryLocationMatch {
    Match(Vec<NormalizedMemoryLocation>),
    NoMatch,
    Residual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct LocationGroupRank {
    region_rank: u8,
    inexact_offset: bool,
    span: u64,
    offset_count: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct LocationGroupTieBreak {
    region_discriminant: u8,
    region_id: u32,
    arg_index: usize,
    min_offset: i64,
}

impl<'a, 'ctx> ValueTranslator<'a, 'ctx> {
    fn new(
        func: &'a SsaArtifact,
        state: &'a SymState<'ctx>,
        memory_index: &'a BackwardMemoryIndex,
        phi_predecessors: &'a BTreeMap<u64, u64>,
        call_contexts: &'a HashMap<CallSiteId, CallTransformContext<'ctx>>,
    ) -> Self {
        Self {
            func,
            state,
            memory_index,
            phi_predecessors,
            call_contexts,
            memo: HashMap::new(),
            visiting: HashSet::new(),
            assumption_constraints: Vec::new(),
            memory_terms: Vec::new(),
            memory_substitutions: 0,
            memory_candidate_enumerations: 0,
            memory_residual_fallbacks: 0,
            used_unsummarized_memory: false,
        }
    }

    fn note_assumption(&mut self, constraint: Bool) {
        self.assumption_constraints.push(constraint);
    }

    fn eval_predicate(
        &mut self,
        predicate: PredicateId,
        truth: bool,
    ) -> Result<Bool, EvalUnsupported> {
        let fact = self
            .func
            .predicates()
            .predicates
            .get(&predicate)
            .ok_or(EvalUnsupported::Unsupported)?;
        let value = self.eval_value_id(fact.condition)?;
        let bool_expr = value_to_bool(self.state.context(), &value);
        Ok(if truth { bool_expr } else { bool_expr.not() })
    }

    fn eval_value_id(&mut self, value_id: ValueId) -> Result<SymValue<'ctx>, EvalUnsupported> {
        if let Some(value) = self.memo.get(&value_id).cloned() {
            return Ok(value);
        }
        if !self.visiting.insert(value_id) {
            return Err(EvalUnsupported::Cycle);
        }

        let var = self
            .func
            .value_var(value_id)
            .ok_or(EvalUnsupported::Unsupported)?;
        let result = if var.is_const() {
            eval_const_var(var)
        } else if let Some(hex) = var.name.strip_prefix("ram:") {
            u64::from_str_radix(hex, 16)
                .map(|value| SymValue::concrete(value, var.size * 8))
                .map_err(|_| EvalUnsupported::Unsupported)
        } else if let Some(inst_id) = self.func.graph().def_inst(value_id) {
            let inst = self
                .func
                .graph()
                .inst(inst_id)
                .ok_or(EvalUnsupported::Unsupported)?;
            match &inst.payload {
                InstPayload::Phi { .. } => {
                    let block_addr = self
                        .func
                        .graph()
                        .block(inst.block)
                        .map(|block| block.addr)
                        .ok_or(EvalUnsupported::Unsupported)?;
                    let selected_pred = self
                        .phi_predecessors
                        .get(&block_addr)
                        .copied()
                        .ok_or(EvalUnsupported::Unsupported)?;
                    let block = self
                        .func
                        .get_block(block_addr)
                        .ok_or(EvalUnsupported::Unsupported)?;
                    let phi = block
                        .phis
                        .iter()
                        .find(|phi| phi.dst == *var)
                        .ok_or(EvalUnsupported::Unsupported)?;
                    let source = phi
                        .sources
                        .iter()
                        .find(|(pred, _)| *pred == selected_pred)
                        .map(|(_, source)| source)
                        .ok_or(EvalUnsupported::Unsupported)?;
                    self.eval_ssa_var(source)
                }
                InstPayload::Op(op) => {
                    let block_addr = self
                        .func
                        .graph()
                        .block(inst.block)
                        .map(|block| block.addr)
                        .ok_or(EvalUnsupported::Unsupported)?;
                    self.eval_op(inst_id, block_addr, op)
                }
            }
        } else {
            Ok(read_input_var(self.state, var))
        }?;

        self.visiting.remove(&value_id);
        self.memo.insert(value_id, result.clone());
        Ok(result)
    }

    fn eval_ssa_var(&mut self, var: &r2ssa::SSAVar) -> Result<SymValue<'ctx>, EvalUnsupported> {
        if let Some(value_id) = self.func.graph().value_id_for_var(var) {
            let value = self.eval_value_id(value_id)?;
            Ok(adjust_bits(self.state.context(), value, var.size * 8))
        } else {
            Ok(read_input_var(self.state, var))
        }
    }

    fn eval_op(
        &mut self,
        inst_id: r2ssa::graph::InstId,
        block_addr: u64,
        op: &r2ssa::SSAOp,
    ) -> Result<SymValue<'ctx>, EvalUnsupported> {
        let ctx = self.state.context();
        use r2ssa::SSAOp::*;

        match op {
            Copy { src, .. } | Cast { src, .. } => self.eval_ssa_var(src),
            Select {
                cond,
                if_true,
                if_false,
                ..
            } => {
                let cond = self.eval_ssa_var(cond)?;
                let when_true = self.eval_ssa_var(if_true)?;
                let when_false = self.eval_ssa_var(if_false)?;
                if let Some(cond) = cond.as_concrete() {
                    return Ok(if cond != 0 { when_true } else { when_false });
                }
                let guard = cond.to_bv(ctx).eq(BV::from_u64(0, cond.bits())).not();
                Ok(ite_value(ctx, &guard, &when_true, &when_false))
            }
            Load { dst, addr, .. } => {
                if let Some(local_value) = self.local_memory_value(inst_id, dst.size) {
                    return Ok(local_value);
                }
                let addr_value = self.eval_ssa_var(addr)?;
                let structural_locations =
                    self.normalized_memory_locations(addr).unwrap_or_default();
                let call_ctx = self.call_context_for_inst(inst_id, block_addr).cloned();
                let mut resolved_locations = None;
                if let Some(call_ctx) = call_ctx {
                    let resolved = self
                        .resolved_memory_locations(&addr_value, dst.size)
                        .unwrap_or_default()
                        .into_iter()
                        .filter(is_specific_memory_location)
                        .collect::<Vec<_>>();
                    if let Some(summary_value) = self.summary_memory_value(
                        &call_ctx,
                        &addr_value,
                        &resolved,
                        &structural_locations,
                        dst.size,
                    ) {
                        return Ok(summary_value);
                    }
                    resolved_locations = Some(resolved);
                }
                if addr_value.as_concrete().is_some() {
                    let resolved = resolved_locations.take().unwrap_or_else(|| {
                        self.resolved_memory_locations(&addr_value, dst.size)
                            .unwrap_or_default()
                            .into_iter()
                            .filter(is_specific_memory_location)
                            .collect()
                    });
                    let normalized = if !resolved.is_empty() {
                        resolved
                    } else {
                        structural_locations.clone()
                    };
                    let value = self.state.mem_read(&addr_value, dst.size);
                    if !self.record_memory_term(&normalized, dst.size, &value) {
                        self.used_unsummarized_memory = true;
                        self.memory_residual_fallbacks += 1;
                    }
                    return Ok(value);
                }
                if structural_locations.is_empty() {
                    let resolved = resolved_locations.get_or_insert_with(|| {
                        self.resolved_memory_locations(&addr_value, dst.size)
                            .unwrap_or_default()
                            .into_iter()
                            .filter(is_specific_memory_location)
                            .collect()
                    });
                    if !resolved.is_empty() {
                        let value = self.state.mem_read(&addr_value, dst.size);
                        if self.record_memory_term(resolved, dst.size, &value) {
                            return Ok(value);
                        }
                    }
                }
                if let Some(memory_input) =
                    self.memory_ssa_input_value(inst_id, dst.size, &structural_locations)
                {
                    return Ok(memory_input);
                }
                let resolved_locations = resolved_locations.unwrap_or_else(|| {
                    self.resolved_memory_locations(&addr_value, dst.size)
                        .unwrap_or_default()
                        .into_iter()
                        .filter(is_specific_memory_location)
                        .collect()
                });
                let normalized = if !resolved_locations.is_empty() {
                    resolved_locations.clone()
                } else {
                    structural_locations.clone()
                };
                let value = self.state.mem_read(&addr_value, dst.size);
                if self.record_memory_term(&normalized, dst.size, &value) {
                    return Ok(value);
                }
                self.used_unsummarized_memory = true;
                self.memory_residual_fallbacks += 1;
                Ok(value)
            }
            IntAdd { a, b, .. } => Ok(self.eval_ssa_var(a)?.add(ctx, &self.eval_ssa_var(b)?)),
            IntSub { a, b, .. } => Ok(self.eval_ssa_var(a)?.sub(ctx, &self.eval_ssa_var(b)?)),
            IntMult { a, b, .. } => Ok(self.eval_ssa_var(a)?.mul(ctx, &self.eval_ssa_var(b)?)),
            IntDiv { a, b, .. } => Ok(self.eval_ssa_var(a)?.udiv(ctx, &self.eval_ssa_var(b)?)),
            IntSDiv { a, b, .. } => Ok(self.eval_ssa_var(a)?.sdiv(ctx, &self.eval_ssa_var(b)?)),
            IntRem { a, b, .. } => Ok(self.eval_ssa_var(a)?.urem(ctx, &self.eval_ssa_var(b)?)),
            IntSRem { a, b, .. } => Ok(self.eval_ssa_var(a)?.srem(ctx, &self.eval_ssa_var(b)?)),
            IntNegate { src, .. } => Ok(self.eval_ssa_var(src)?.neg(ctx)),
            IntAnd { a, b, .. } => Ok(self.eval_ssa_var(a)?.and(ctx, &self.eval_ssa_var(b)?)),
            IntOr { a, b, .. } => Ok(self.eval_ssa_var(a)?.or(ctx, &self.eval_ssa_var(b)?)),
            IntXor { a, b, .. } => Ok(self.eval_ssa_var(a)?.xor(ctx, &self.eval_ssa_var(b)?)),
            IntNot { src, .. } => Ok(self.eval_ssa_var(src)?.not(ctx)),
            IntLeft { a, b, .. } => Ok(self.eval_ssa_var(a)?.shl(ctx, &self.eval_ssa_var(b)?)),
            IntRight { a, b, .. } => Ok(self.eval_ssa_var(a)?.lshr(ctx, &self.eval_ssa_var(b)?)),
            IntSRight { a, b, .. } => Ok(self.eval_ssa_var(a)?.ashr(ctx, &self.eval_ssa_var(b)?)),
            IntEqual { a, b, .. } => Ok(self.eval_ssa_var(a)?.eq(ctx, &self.eval_ssa_var(b)?)),
            IntNotEqual { a, b, .. } => {
                let eq = self.eval_ssa_var(a)?.eq(ctx, &self.eval_ssa_var(b)?);
                Ok(eq.not(ctx))
            }
            IntLess { a, b, .. } => Ok(self.eval_ssa_var(a)?.ult(ctx, &self.eval_ssa_var(b)?)),
            IntSLess { a, b, .. } => Ok(self.eval_ssa_var(a)?.slt(ctx, &self.eval_ssa_var(b)?)),
            IntLessEqual { a, b, .. } => Ok(self.eval_ssa_var(a)?.ule(ctx, &self.eval_ssa_var(b)?)),
            IntSLessEqual { a, b, .. } => {
                Ok(self.eval_ssa_var(a)?.sle(ctx, &self.eval_ssa_var(b)?))
            }
            IntZExt { dst, src } => Ok(self.eval_ssa_var(src)?.zero_extend(ctx, dst.size * 8)),
            IntSExt { dst, src } => {
                let value = self.eval_ssa_var(src)?;
                let current = value.to_bv(ctx);
                let extended = if dst.size * 8 > value.bits() {
                    current.sign_ext(dst.size * 8 - value.bits())
                } else {
                    current.extract(dst.size * 8 - 1, 0)
                };
                Ok(SymValue::symbolic_tainted(
                    extended,
                    dst.size * 8,
                    value.get_taint(),
                ))
            }
            BoolNot { src, .. } => Ok(self.eval_ssa_var(src)?.bool_not(ctx)),
            BoolAnd { a, b, .. } => Ok(self.eval_ssa_var(a)?.and(ctx, &self.eval_ssa_var(b)?)),
            BoolOr { a, b, .. } => Ok(self.eval_ssa_var(a)?.or(ctx, &self.eval_ssa_var(b)?)),
            BoolXor { a, b, .. } => Ok(self.eval_ssa_var(a)?.xor(ctx, &self.eval_ssa_var(b)?)),
            Piece { hi, lo, .. } => Ok(self.eval_ssa_var(hi)?.concat(ctx, &self.eval_ssa_var(lo)?)),
            Subpiece { dst, src, offset } => {
                let value = self.eval_ssa_var(src)?;
                let low = offset.saturating_mul(8);
                let high = low.saturating_add(dst.size * 8).saturating_sub(1);
                Ok(value.extract(ctx, high, low))
            }
            CallDefine { dst } => self.eval_call_define(inst_id, block_addr, dst),
            _ => Err(EvalUnsupported::Unsupported),
        }
    }

    fn eval_call_define(
        &mut self,
        inst_id: r2ssa::graph::InstId,
        block_addr: u64,
        dst: &r2ssa::SSAVar,
    ) -> Result<SymValue<'ctx>, EvalUnsupported> {
        let Some(call_ctx) = self.call_context_for_inst(inst_id, block_addr) else {
            return Err(EvalUnsupported::Unsupported);
        };
        if !register_aliases(call_ctx.callconv.ret_register_name())
            .iter()
            .any(|alias| dst.name.eq_ignore_ascii_case(alias))
        {
            return Err(EvalUnsupported::Unsupported);
        }
        let (value, coverage) = summary_return_value(self.state, call_ctx)?;
        if let Some(coverage) = coverage {
            self.note_assumption(coverage);
        }
        Ok(value)
    }

    fn call_context_for_inst(
        &self,
        inst_id: r2ssa::graph::InstId,
        block_addr: u64,
    ) -> Option<&CallTransformContext<'ctx>> {
        let (inst_block_addr, op_idx) = self.func.inst_op_site(inst_id)?;
        debug_assert_eq!(inst_block_addr, block_addr);
        self.func.get_block(block_addr)?;
        for scan_idx in (0..op_idx).rev() {
            let scan_inst = self
                .func
                .graph()
                .inst_id_for_op_site(block_addr, scan_idx)?;
            let Some(call_id) = self.func.call_sites().by_inst.get(&scan_inst).copied() else {
                continue;
            };
            if let Some(context) = self.call_contexts.get(&call_id) {
                return Some(context);
            }
        }
        let predecessors =
            if let Some(predecessor) = self.phi_predecessors.get(&block_addr).copied() {
                vec![predecessor]
            } else {
                let preds = self.func.predecessors(block_addr);
                if preds.len() == 1 { preds } else { Vec::new() }
            };
        for predecessor in predecessors {
            let predecessor_block = self.func.get_block(predecessor)?;
            for scan_idx in (0..predecessor_block.ops.len()).rev() {
                let scan_inst = self
                    .func
                    .graph()
                    .inst_id_for_op_site(predecessor, scan_idx)?;
                let Some(call_id) = self.func.call_sites().by_inst.get(&scan_inst).copied() else {
                    continue;
                };
                if let Some(context) = self.call_contexts.get(&call_id) {
                    return Some(context);
                }
            }
        }
        None
    }

    fn summary_memory_value(
        &mut self,
        call_ctx: &CallTransformContext<'ctx>,
        addr: &SymValue<'ctx>,
        resolved: &[NormalizedMemoryLocation],
        structural: &[NormalizedMemoryLocation],
        size: u32,
    ) -> Option<SymValue<'ctx>> {
        let mut actual_locations = resolved.to_vec();
        if actual_locations.is_empty() {
            actual_locations.extend(structural.iter().cloned());
        }
        if actual_locations.is_empty() {
            actual_locations.extend(summary_memory_locations(call_ctx, addr));
        }
        if actual_locations.is_empty() {
            return None;
        }
        let fallback_summary_locations = summary_memory_locations(call_ctx, addr);
        let substitutions = build_call_substitutions(self.state, call_ctx);
        let location_groups = group_normalized_locations(&actual_locations);
        let candidate_groups = if location_groups.len() <= 1 {
            location_groups
        } else if let Some(best_group) = select_best_location_group(location_groups) {
            vec![best_group]
        } else {
            self.memory_residual_fallbacks += 1;
            return None;
        };
        for location_group in candidate_groups {
            let summary_group = match self.summary_match_locations(call_ctx, &location_group) {
                SummaryLocationMatch::Match(group) => group,
                SummaryLocationMatch::NoMatch => {
                    if fallback_summary_locations.is_empty() {
                        continue;
                    }
                    fallback_summary_locations.clone()
                }
                SummaryLocationMatch::Residual => {
                    self.memory_residual_fallbacks += 1;
                    continue;
                }
            };
            let mut matches = call_ctx
                .summary
                .cases
                .iter()
                .filter_map(|case| {
                    let covering =
                        select_covering_writes(&case.memory_writes, &summary_group, size);
                    if covering.is_empty() || covering_writes_are_ambiguous(&covering) {
                        return None;
                    }
                    let (location, write) = select_best_covering_write(covering)?;
                    let guard = substitute_bool(&case.guard, &substitutions);
                    let value = substitute_value(
                        self.state.context(),
                        &slice_write_value(self.state.context(), write, location.offset, size),
                        &substitutions,
                    );
                    Some((guard, value))
                })
                .collect::<Vec<_>>();
            let alias_heavy = call_ctx.summary.cases.iter().any(|case| {
                covering_writes_are_ambiguous(&select_covering_writes(
                    &case.memory_writes,
                    &summary_group,
                    size,
                ))
            });
            if alias_heavy {
                self.memory_residual_fallbacks += 1;
                continue;
            }
            if matches.is_empty() {
                continue;
            }

            let mut merged = self.state.mem_read(addr, size);
            for (guard, value) in matches.drain(..).rev() {
                merged = ite_value(self.state.context(), &guard, &value, &merged);
            }
            self.record_memory_term(&location_group, size, &merged);
            self.memory_substitutions += 1;
            return Some(merged);
        }
        None
    }

    fn summary_match_locations(
        &self,
        call_ctx: &CallTransformContext<'ctx>,
        actual_group: &[NormalizedMemoryLocation],
    ) -> SummaryLocationMatch {
        if actual_group.is_empty() {
            return SummaryLocationMatch::NoMatch;
        }
        if actual_group
            .iter()
            .all(|location| matches!(location.region, BackwardMemoryRegion::Argument { .. }))
        {
            return SummaryLocationMatch::Match(actual_group.to_vec());
        }
        let mut actual_regions = actual_group
            .iter()
            .filter_map(|location| match &location.region {
                BackwardMemoryRegion::Region(region) => Some(region.clone()),
                BackwardMemoryRegion::Argument { .. } => None,
            })
            .collect::<BTreeSet<_>>();
        if actual_regions.len() != 1 {
            return SummaryLocationMatch::Residual;
        }

        let actual_region = actual_regions.pop_first().expect("single region");
        if actual_region.kind == MemoryRegionKind::EscapedUnknown {
            return SummaryLocationMatch::NoMatch;
        }

        let mut translated = BTreeMap::<usize, BTreeSet<i64>>::new();
        let pointer_args = summary_pointer_arg_indices(call_ctx);
        for (arg_index, base) in call_ctx.args.iter().enumerate() {
            if !pointer_args.is_empty() && !pointer_args.contains(&arg_index) {
                continue;
            }
            let Some(base_locations) = self.resolved_memory_locations(base, 1) else {
                continue;
            };
            for base_location in base_locations {
                let BackwardMemoryRegion::Region(base_region) = &base_location.region else {
                    continue;
                };
                if base_region.kind == MemoryRegionKind::EscapedUnknown {
                    continue;
                }
                if *base_region != actual_region {
                    continue;
                }
                let offsets = translated.entry(arg_index).or_default();
                for actual in actual_group {
                    offsets.insert(actual.offset.saturating_sub(base_location.offset));
                }
            }
        }

        match translated.len() {
            0 => SummaryLocationMatch::NoMatch,
            1 => SummaryLocationMatch::Match(translated_arg_locations(
                translated
                    .into_iter()
                    .next()
                    .expect("single translated arg"),
            )),
            _ => select_best_translated_arg(translated)
                .map(translated_arg_locations)
                .map(SummaryLocationMatch::Match)
                .unwrap_or(SummaryLocationMatch::Residual),
        }
    }

    fn local_memory_value(
        &mut self,
        inst_id: r2ssa::graph::InstId,
        size: u32,
    ) -> Option<SymValue<'ctx>> {
        let value = self.local_memory_store_var(inst_id, size)?;
        self.eval_ssa_var(&value).ok()
    }

    fn memory_ssa_input_value(
        &mut self,
        inst_id: r2ssa::graph::InstId,
        size: u32,
        structural_locations: &[NormalizedMemoryLocation],
    ) -> Option<SymValue<'ctx>> {
        let mut matching_uses = self
            .func
            .memory()
            .uses_by_inst
            .get(&inst_id)?
            .iter()
            .filter(|use_fact| use_fact.location.size == size);
        let use_fact = matching_uses.next()?;
        if matching_uses.next().is_some() {
            return None;
        }
        let value = SymValue::new_symbolic(
            self.state.context(),
            &format!(
                "memory_object_{}_version_{}_address_{}_size_{}",
                use_fact.location.object.0,
                use_fact.version.version,
                memory_address_symbol_component(&use_fact.location.address),
                use_fact.location.size
            ),
            size * 8,
        );
        let recorded = self.record_memory_term(structural_locations, size, &value)
            || self.record_prepared_memory_term(&use_fact.location, &value);
        if !recorded || use_fact.version.version != 0 {
            self.used_unsummarized_memory = true;
            self.memory_residual_fallbacks += 1;
        }
        Some(value)
    }

    fn local_memory_store_var(
        &self,
        inst_id: r2ssa::graph::InstId,
        size: u32,
    ) -> Option<r2ssa::SSAVar> {
        let mut matching_uses = self
            .func
            .memory()
            .uses_by_inst
            .get(&inst_id)?
            .iter()
            .filter(|use_fact| use_fact.location.size == size);
        let first = matching_uses.next()?;
        let candidate = self.memory_index.reaching_store(first)?.clone();
        for use_fact in matching_uses {
            if self.memory_index.reaching_store(use_fact) != Some(&candidate) {
                return None;
            }
        }
        Some(candidate)
    }

    fn record_memory_term(
        &mut self,
        locations: &[NormalizedMemoryLocation],
        size: u32,
        value: &SymValue<'ctx>,
    ) -> bool {
        if locations.is_empty() {
            return false;
        }
        let mut grouped = BTreeMap::<BackwardMemoryRegion, BTreeSet<i64>>::new();
        for location in locations {
            grouped
                .entry(location.region.clone())
                .or_default()
                .insert(location.offset);
        }
        if grouped.len() > 1 {
            self.memory_residual_fallbacks += 1;
        }
        for (region, offsets) in grouped {
            let offset_lo = offsets.iter().copied().min().unwrap_or(0);
            let offset_hi = offsets.iter().copied().max().unwrap_or(0);
            let exact_offset = offset_lo == offset_hi;
            let value_expr = value.to_string();
            let address = if exact_offset {
                SemanticMemoryAddress::exact(offset_lo)
            } else {
                SemanticMemoryAddress::bounded(offset_lo, offset_hi)
                    .expect("normalized backward memory bounds")
            };
            let expr = backward_memory_term_expr(&region, &address, &value_expr);
            let evidence =
                inferred_memory_term_evidence(&region, offset_lo, offset_hi, exact_offset);
            self.memory_terms.push(BackwardMemoryCondition {
                region,
                address,
                size,
                evidence,
                binding: None,
                expr,
                value_expr: Some(value_expr),
                exact_value: value.is_concrete(),
            });
        }
        true
    }

    fn record_prepared_memory_term(
        &mut self,
        location: &r2ssa::MemoryLocation,
        value: &SymValue<'ctx>,
    ) -> bool {
        let Some(r2ssa::ObjectKind::Parameter { index, .. }) = self
            .func
            .objects()
            .object(location.object)
            .map(|object| &object.kind)
        else {
            return false;
        };
        let Some(address) = SemanticMemoryAddress::from_ssa(&location.address) else {
            return false;
        };
        let region = BackwardMemoryRegion::Argument { index: *index };
        let value_expr = value.to_string();
        let expr = backward_memory_term_expr(&region, &address, &value_expr);
        self.memory_terms.push(BackwardMemoryCondition {
            region,
            address,
            size: location.size,
            evidence: SemanticEvidence::exact(),
            binding: None,
            expr,
            value_expr: Some(value_expr),
            exact_value: value.is_concrete(),
        });
        true
    }

    fn normalized_memory_locations(
        &mut self,
        addr: &r2ssa::SSAVar,
    ) -> Option<Vec<NormalizedMemoryLocation>> {
        let value_id = self.func.graph().value_id_for_var(addr)?;
        if let Some(expression) = self.func.addresses().parameter_expression(value_id)
            && expression.terms.is_empty()
        {
            return Some(vec![NormalizedMemoryLocation {
                region: BackwardMemoryRegion::Argument {
                    index: expression.parameter,
                },
                offset: expression.offset,
            }]);
        }
        self.normalized_memory_location_value_id(value_id)
    }

    fn resolved_memory_locations(
        &self,
        addr: &SymValue<'ctx>,
        size: u32,
    ) -> Option<Vec<NormalizedMemoryLocation>> {
        let mut constraints = self.state.constraints().to_vec();
        constraints.extend(self.assumption_constraints.iter().cloned());
        let resolved = self.state.memory.resolve_pointer(addr, size, &constraints);
        if resolved.truncated {
            return None;
        }
        let mut locations = Vec::new();
        for pointer in resolved.pointers {
            let Some(region) = self.region_for_pointer(pointer.region_id) else {
                continue;
            };
            let Ok(offset) = i64::try_from(pointer.offset) else {
                continue;
            };
            locations.push(NormalizedMemoryLocation { region, offset });
        }
        (!locations.is_empty()).then_some(locations)
    }

    fn region_for_pointer(&self, region_id: MemoryRegionId) -> Option<BackwardMemoryRegion> {
        let def = self.state.memory.region_def(region_id)?;
        Some(BackwardMemoryRegion::Region(BackwardRegionRef {
            id: def.id,
            kind: def.kind.clone(),
            name: def.name.clone(),
        }))
    }

    fn normalized_memory_location_value_id(
        &mut self,
        value_id: ValueId,
    ) -> Option<Vec<NormalizedMemoryLocation>> {
        let inst_id = self.func.graph().def_inst(value_id)?;
        let inst = self.func.graph().inst(inst_id)?;
        let InstPayload::Op(op) = &inst.payload else {
            return None;
        };
        use r2ssa::SSAOp::*;
        match op {
            Copy { src, .. } | Cast { src, .. } => self.normalized_memory_locations(src),
            IntAdd { a, b, .. } => {
                if let Some(base) = self.normalized_memory_locations(a)
                    && let Some(offsets) = self.resolve_delta_offsets(b, 1)
                {
                    return Some(apply_delta_offsets(&base, &offsets, true));
                }
                if let Some(base) = self.normalized_memory_locations(b)
                    && let Some(offsets) = self.resolve_delta_offsets(a, 1)
                {
                    return Some(apply_delta_offsets(&base, &offsets, true));
                }
                None
            }
            PtrAdd {
                base,
                index,
                element_size,
                ..
            } => {
                if let Some(base) = self.normalized_memory_locations(base)
                    && let Some(offsets) = self.resolve_delta_offsets(index, *element_size as i64)
                {
                    return Some(apply_delta_offsets(&base, &offsets, true));
                }
                None
            }
            IntSub { a, b, .. } => {
                if let Some(base) = self.normalized_memory_locations(a)
                    && let Some(offsets) = self.resolve_delta_offsets(b, 1)
                {
                    return Some(apply_delta_offsets(&base, &offsets, false));
                }
                None
            }
            PtrSub {
                base,
                index,
                element_size,
                ..
            } => {
                if let Some(base) = self.normalized_memory_locations(base)
                    && let Some(offsets) = self.resolve_delta_offsets(index, *element_size as i64)
                {
                    return Some(apply_delta_offsets(&base, &offsets, false));
                }
                None
            }
            IntZExt { src, .. } | IntSExt { src, .. } => self.normalized_memory_locations(src),
            Subpiece { src, offset, .. } if *offset == 0 => self.normalized_memory_locations(src),
            _ => None,
        }
    }

    fn resolve_delta_offsets(&mut self, delta: &r2ssa::SSAVar, scale: i64) -> Option<Vec<i64>> {
        let delta_value = self.eval_ssa_var(delta).ok()?;
        if let Some(concrete) = delta_value.as_concrete() {
            return Some(vec![(concrete as i64).saturating_mul(scale)]);
        }
        let candidates = self.enumerate_bounded_concrete_values(&delta_value)?;
        if candidates.is_empty() {
            return None;
        }
        self.memory_candidate_enumerations += 1;
        Some(
            candidates
                .into_iter()
                .map(|value| (value as i64).saturating_mul(scale))
                .collect(),
        )
    }

    fn enumerate_bounded_concrete_values(&mut self, value: &SymValue<'ctx>) -> Option<Vec<u64>> {
        if self.state.constraints().is_empty() && self.assumption_constraints.is_empty() {
            return None;
        }
        let ctx = self.state.context();
        let bv = value.to_bv(ctx);
        let solver = Solver::new();
        for constraint in self.state.constraints() {
            solver.assert(constraint);
        }
        for constraint in &self.assumption_constraints {
            solver.assert(constraint);
        }

        let mut values = BTreeSet::new();
        loop {
            match solver.check() {
                Z3SatResult::Sat => {
                    let model = solver.get_model()?;
                    let concrete = model.eval(&bv, true)?.as_u64()?;
                    values.insert(concrete);
                    if values.len() > DEFAULT_MAX_NORMALIZED_OFFSETS {
                        return None;
                    }
                    solver.assert(bv.eq(BV::from_u64(concrete, value.bits())).not());
                }
                Z3SatResult::Unsat => break,
                Z3SatResult::Unknown => return None,
            }
        }

        Some(values.into_iter().collect())
    }
}

pub fn compile_target_precondition<'ctx>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    target_addr: u64,
) -> Option<CompiledBackwardCondition> {
    compile_target_precondition_with_summaries(func, initial_state, target_addr, &HashMap::new())
}

pub(crate) fn compile_target_precondition_with_summaries<'ctx>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    target_addr: u64,
    call_summaries: &HashMap<u64, DerivedCallSummaryView<'ctx>>,
) -> Option<CompiledBackwardCondition> {
    let reverse_paths = enumerate_reverse_paths(func, target_addr, DEFAULT_REVERSE_PATH_LIMIT)?;
    compile_reverse_paths(func, initial_state, reverse_paths, None, call_summaries)
}

pub(crate) fn compile_branch_precondition_with_summaries<'ctx>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    block_addr: u64,
    truth: bool,
    call_summaries: &HashMap<u64, DerivedCallSummaryView<'ctx>>,
) -> Option<CompiledBackwardCondition> {
    let predicate = func
        .predicates()
        .predicates
        .iter()
        .find_map(|(id, fact)| (fact.block_addr == block_addr).then_some(*id))?;
    let reverse_paths = enumerate_reverse_paths(func, block_addr, DEFAULT_REVERSE_PATH_LIMIT)?;
    compile_reverse_paths(
        func,
        initial_state,
        reverse_paths,
        Some((predicate, truth)),
        call_summaries,
    )
}

pub(crate) fn compile_branch_preconditions_with_summaries<'ctx>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    block_addr: u64,
    call_summaries: &HashMap<u64, DerivedCallSummaryView<'ctx>>,
) -> Option<(CompiledBackwardCondition, CompiledBackwardCondition)> {
    let predicate = func
        .predicates()
        .predicates
        .iter()
        .find_map(|(id, fact)| (fact.block_addr == block_addr).then_some(*id))?;
    let reverse_paths = enumerate_reverse_paths(func, block_addr, DEFAULT_REVERSE_PATH_LIMIT)?;
    compile_reverse_paths_for_branch(
        func,
        initial_state,
        reverse_paths,
        predicate,
        call_summaries,
    )
}

pub fn compile_derived_summary_return_postcondition<'ctx, F>(
    state: &SymState<'ctx>,
    summary: &DerivedFunctionSummary<'ctx>,
    callconv: &CallConv,
    postcondition: F,
) -> Option<CompiledBackwardCondition>
where
    F: Fn(&SymValue<'ctx>) -> Bool,
{
    if summary.cases.is_empty() {
        return None;
    }

    let call =
        callconv.collect_call_info(state, summary.arg_count_hint.max(callconv.arg_capacity()));
    let substitutions = build_summary_substitutions(state, summary, &call);
    let mut terms = Vec::new();
    for case in &summary.cases {
        let Some(return_value) = &case.return_value else {
            continue;
        };
        let guard = substitute_bool(&case.guard, &substitutions);
        let value = substitute_value(state.context(), return_value, &substitutions);
        let post = postcondition(&value);
        terms.push(guard & post);
    }
    if terms.is_empty() {
        return None;
    }
    let predicate = or_all(state.context(), &terms);
    let simplified = predicate.simplify();
    Some(CompiledBackwardCondition {
        summary: BackwardConditionSummary {
            simplified: simplified.to_string(),
            terms: terms
                .iter()
                .map(|term| term.simplify().to_string())
                .collect(),
            memory_terms: Vec::new(),
            backward_memory_substitutions: 0,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: if matches!(
                summary.completion,
                crate::sim::DerivedSummaryCompletion::Exact
            ) {
                BackwardConditionPrecision::Exact
            } else {
                BackwardConditionPrecision::ResidualSearchRequired
            },
            supported_paths: terms.len(),
            total_paths: terms.len(),
        },
        predicate: simplified,
    })
}

pub fn compile_derived_summary_memory_postcondition<'ctx, F>(
    state: &SymState<'ctx>,
    summary: &DerivedFunctionSummary<'ctx>,
    callconv: &CallConv,
    arg_index: usize,
    offset: i64,
    size: u32,
    postcondition: F,
) -> Option<CompiledBackwardCondition>
where
    F: Fn(&SymValue<'ctx>) -> Bool,
{
    if summary.cases.is_empty() {
        return None;
    }

    let call =
        callconv.collect_call_info(state, summary.arg_count_hint.max(callconv.arg_capacity()));
    let substitutions = build_call_substitutions(
        state,
        &CallTransformContext {
            summary: Rc::new(summary.clone()),
            callconv: callconv.clone(),
            args: call.args.clone(),
        },
    );
    let base = call.args.get(arg_index)?;
    let addr = add_signed_offset(state.context(), base, offset, call.arg_bits);
    let mut terms = Vec::new();
    for case in &summary.cases {
        let Some((location, write)) = select_covering_write(
            &case.memory_writes,
            &[NormalizedMemoryLocation {
                region: BackwardMemoryRegion::Argument { index: arg_index },
                offset,
            }],
            size,
        ) else {
            continue;
        };
        let guard = substitute_bool(&case.guard, &substitutions);
        let value = substitute_value(
            state.context(),
            &slice_write_value(state.context(), write, location.offset, size),
            &substitutions,
        );
        terms.push(guard & postcondition(&value));
    }
    if terms.is_empty() {
        return None;
    }
    let predicate = or_all(state.context(), &terms);
    let simplified = predicate.simplify();
    let memory_term = state
        .memory
        .resolve_pointer(&addr, size, state.constraints())
        .pointers
        .into_iter()
        .find_map(|pointer| {
            state.memory.region_def(pointer.region_id).map(|def| {
                let region = BackwardMemoryRegion::Region(BackwardRegionRef {
                    id: def.id,
                    kind: def.kind.clone(),
                    name: def.name.clone(),
                });
                let offset = i64::try_from(pointer.offset).unwrap_or(0);
                BackwardMemoryCondition {
                    region: region.clone(),
                    address: SemanticMemoryAddress::exact(offset),
                    size,
                    evidence: if matches!(
                        summary.completion,
                        crate::sim::DerivedSummaryCompletion::Exact
                    ) {
                        SemanticEvidence::exact()
                    } else {
                        SemanticEvidence::likely(SemanticEvidenceReason::PartialPathCoverage)
                            .with_coverage(SemanticEvidenceCoverage::Bounded)
                            .with_provenance(SemanticEvidenceProvenance::Normalized)
                    },
                    binding: None,
                    expr: format_backward_memory_location(&region, offset),
                    value_expr: None,
                    exact_value: false,
                }
            })
        })
        .unwrap_or(BackwardMemoryCondition {
            region: BackwardMemoryRegion::Argument { index: arg_index },
            address: SemanticMemoryAddress::exact(offset),
            size,
            evidence: if matches!(
                summary.completion,
                crate::sim::DerivedSummaryCompletion::Exact
            ) {
                SemanticEvidence::exact()
            } else {
                SemanticEvidence::likely(SemanticEvidenceReason::PartialPathCoverage)
                    .with_coverage(SemanticEvidenceCoverage::Bounded)
                    .with_provenance(SemanticEvidenceProvenance::Normalized)
            },
            binding: None,
            expr: format_backward_memory_location(
                &BackwardMemoryRegion::Argument { index: arg_index },
                offset,
            ),
            value_expr: None,
            exact_value: false,
        });
    Some(CompiledBackwardCondition {
        summary: BackwardConditionSummary {
            simplified: simplified.to_string(),
            terms: terms
                .iter()
                .map(|term| term.simplify().to_string())
                .collect(),
            memory_terms: vec![memory_term],
            backward_memory_substitutions: 1,
            backward_memory_candidate_enumerations: 0,
            backward_memory_residual_fallbacks: 0,
            precision: if matches!(
                summary.completion,
                crate::sim::DerivedSummaryCompletion::Exact
            ) {
                BackwardConditionPrecision::Exact
            } else {
                BackwardConditionPrecision::ResidualSearchRequired
            },
            supported_paths: terms.len(),
            total_paths: terms.len(),
        },
        predicate: simplified,
    })
}

fn enumerate_reverse_paths(
    func: &SsaArtifact,
    target_addr: u64,
    limit: usize,
) -> Option<(Vec<ReversePath>, bool)> {
    func.get_block(target_addr)?;

    let mut pending = vec![ReversePath {
        block_addr: target_addr,
        phi_predecessors: BTreeMap::new(),
        assumptions: Vec::new(),
        visited: BTreeSet::from([target_addr]),
    }];
    let mut completed = Vec::new();
    let mut truncated = false;

    while let Some(path) = pending.pop() {
        if completed.len() >= limit {
            truncated = true;
            break;
        }
        if path.block_addr == func.entry {
            completed.push(path);
            continue;
        }

        let predecessors = func.predecessors(path.block_addr);
        if predecessors.is_empty() {
            continue;
        }

        for predecessor in predecessors {
            if path.visited.contains(&predecessor) {
                truncated = true;
                continue;
            }
            let mut next = path.clone();
            next.block_addr = predecessor;
            next.visited.insert(predecessor);
            next.phi_predecessors.insert(path.block_addr, predecessor);
            if let Some(assumptions) = func.predicates().block_assumptions.get(&path.block_addr) {
                for assumption in assumptions
                    .iter()
                    .filter(|assumption| assumption.predecessor == predecessor)
                {
                    next.assumptions
                        .push((assumption.predicate, assumption.truth));
                }
            }
            pending.push(next);
        }
    }

    Some((completed, truncated))
}

fn compile_reverse_paths<'ctx>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    (paths, truncated): (Vec<ReversePath>, bool),
    extra_predicate: Option<(PredicateId, bool)>,
    call_summaries: &HashMap<u64, DerivedCallSummaryView<'ctx>>,
) -> Option<CompiledBackwardCondition> {
    compile_reverse_paths_with_extra(
        func,
        initial_state,
        (paths, truncated),
        extra_predicate,
        call_summaries,
        |_, _| Ok(None),
    )
}

fn compile_reverse_paths_with_extra<'ctx, F>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    reverse_paths: (Vec<ReversePath>, bool),
    extra_predicate: Option<(PredicateId, bool)>,
    call_summaries: &HashMap<u64, DerivedCallSummaryView<'ctx>>,
    mut extra_constraint: F,
) -> Option<CompiledBackwardCondition>
where
    F: for<'a> FnMut(
        &mut ValueTranslator<'a, 'ctx>,
        &ReversePath,
    ) -> Result<Option<Bool>, EvalUnsupported>,
{
    let mut compiled = compile_reverse_path_alternatives(
        func,
        initial_state,
        reverse_paths,
        call_summaries,
        1,
        |translator, path| {
            if let Some((predicate, truth)) = extra_predicate {
                let condition = translator.eval_predicate(predicate, truth)?;
                translator.note_assumption(condition);
            }
            if let Some(condition) = extra_constraint(translator, path)? {
                translator.note_assumption(condition);
            }
            Ok(vec![None])
        },
    )?;
    compiled.pop()
}

fn compile_reverse_paths_for_branch<'ctx>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    reverse_paths: (Vec<ReversePath>, bool),
    predicate: PredicateId,
    call_summaries: &HashMap<u64, DerivedCallSummaryView<'ctx>>,
) -> Option<(CompiledBackwardCondition, CompiledBackwardCondition)> {
    let mut compiled = compile_reverse_path_alternatives(
        func,
        initial_state,
        reverse_paths,
        call_summaries,
        2,
        |translator, _| {
            let condition = translator.eval_predicate(predicate, true)?;
            Ok(vec![Some(condition.clone()), Some(condition.not())])
        },
    )?
    .into_iter();
    Some((compiled.next()?, compiled.next()?))
}

fn compile_reverse_path_alternatives<'ctx, F>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    (paths, truncated): (Vec<ReversePath>, bool),
    call_summaries: &HashMap<u64, DerivedCallSummaryView<'ctx>>,
    alternative_count: usize,
    mut alternatives: F,
) -> Option<Vec<CompiledBackwardCondition>>
where
    F: for<'a> FnMut(
        &mut ValueTranslator<'a, 'ctx>,
        &ReversePath,
    ) -> Result<Vec<Option<Bool>>, EvalUnsupported>,
{
    if paths.is_empty() || alternative_count == 0 {
        return None;
    }

    let mut supported_terms = vec![Vec::new(); alternative_count];
    let mut memory_terms = Vec::new();
    let mut unsupported_paths = 0usize;
    let mut used_unsummarized_memory = false;
    let mut backward_memory_substitutions = 0usize;
    let mut backward_memory_candidate_enumerations = 0usize;
    let mut backward_memory_residual_fallbacks = 0usize;
    let memory_index = BackwardMemoryIndex::new(func);

    for path in &paths {
        let call_contexts =
            build_call_transform_contexts(func, initial_state, path, call_summaries, &memory_index);
        let mut translator = ValueTranslator::new(
            func,
            initial_state,
            &memory_index,
            &path.phi_predecessors,
            &call_contexts,
        );
        let path_supported = path.assumptions.iter().all(|(predicate, truth)| {
            let Ok(condition) = translator.eval_predicate(*predicate, *truth) else {
                return false;
            };
            translator.note_assumption(condition);
            true
        });
        if !path_supported {
            unsupported_paths += 1;
            continue;
        }
        let Ok(path_alternatives) = alternatives(&mut translator, path) else {
            unsupported_paths += 1;
            continue;
        };
        if path_alternatives.len() != alternative_count {
            return None;
        }

        for (terms, condition) in supported_terms.iter_mut().zip(path_alternatives) {
            let term = if let Some(condition) = condition {
                let mut conditions = translator.assumption_constraints.clone();
                conditions.push(condition);
                and_all(initial_state.context(), &conditions)
            } else {
                and_all(initial_state.context(), &translator.assumption_constraints)
            };
            terms.push(term);
        }
        used_unsummarized_memory |= translator.used_unsummarized_memory;
        backward_memory_substitutions += translator.memory_substitutions;
        backward_memory_candidate_enumerations += translator.memory_candidate_enumerations;
        backward_memory_residual_fallbacks += translator.memory_residual_fallbacks;
        memory_terms.extend(translator.memory_terms);
    }

    let evidence = ReversePathCompilationEvidence {
        unsupported_paths,
        used_unsummarized_memory,
        memory_terms,
        backward_memory_substitutions,
        backward_memory_candidate_enumerations,
        backward_memory_residual_fallbacks,
    };
    supported_terms
        .into_iter()
        .map(|terms| {
            finish_reverse_path_compilation(
                initial_state.context(),
                terms,
                paths.len(),
                truncated,
                evidence.clone(),
            )
        })
        .collect()
}

#[derive(Clone)]
struct ReversePathCompilationEvidence {
    unsupported_paths: usize,
    used_unsummarized_memory: bool,
    memory_terms: Vec<BackwardMemoryCondition>,
    backward_memory_substitutions: usize,
    backward_memory_candidate_enumerations: usize,
    backward_memory_residual_fallbacks: usize,
}

fn finish_reverse_path_compilation(
    ctx: &Context,
    supported_terms: Vec<Bool>,
    total_paths: usize,
    truncated: bool,
    evidence: ReversePathCompilationEvidence,
) -> Option<CompiledBackwardCondition> {
    if supported_terms.is_empty() {
        return None;
    }

    let predicate = or_all(ctx, &supported_terms);
    let simplified = predicate.simplify();
    let precision = if evidence.unsupported_paths == 0
        && !truncated
        && !evidence.used_unsummarized_memory
        && evidence.backward_memory_residual_fallbacks == 0
    {
        BackwardConditionPrecision::Exact
    } else if evidence.unsupported_paths > 0
        || truncated
        || evidence.used_unsummarized_memory
        || evidence.backward_memory_residual_fallbacks > 0
    {
        BackwardConditionPrecision::ResidualSearchRequired
    } else {
        BackwardConditionPrecision::OverApprox
    };
    Some(CompiledBackwardCondition {
        summary: BackwardConditionSummary {
            simplified: simplified.to_string(),
            terms: supported_terms
                .iter()
                .map(|term| term.simplify().to_string())
                .collect(),
            memory_terms: evidence.memory_terms,
            backward_memory_substitutions: evidence.backward_memory_substitutions,
            backward_memory_candidate_enumerations: evidence.backward_memory_candidate_enumerations,
            backward_memory_residual_fallbacks: evidence.backward_memory_residual_fallbacks,
            precision,
            supported_paths: supported_terms.len(),
            total_paths,
        },
        predicate: simplified,
    })
}

pub(crate) fn compile_value_postcondition_with_summaries<'ctx, F>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    block_addr: u64,
    value_var: r2ssa::SSAVar,
    postcondition: F,
    call_summaries: &HashMap<u64, DerivedCallSummaryView<'ctx>>,
) -> Option<CompiledBackwardCondition>
where
    F: Fn(&SymValue<'ctx>) -> Bool + Clone,
{
    let reverse_paths = enumerate_reverse_paths(func, block_addr, DEFAULT_REVERSE_PATH_LIMIT)?;
    compile_reverse_paths_with_extra(
        func,
        initial_state,
        reverse_paths,
        None,
        call_summaries,
        move |translator, path| {
            let _ = path;
            let value = translator.eval_ssa_var(&value_var)?;
            Ok(Some(postcondition.clone()(&value)))
        },
    )
}

fn build_call_transform_contexts<'ctx>(
    func: &SsaArtifact,
    initial_state: &SymState<'ctx>,
    path: &ReversePath,
    call_summaries: &HashMap<u64, DerivedCallSummaryView<'ctx>>,
    memory_index: &BackwardMemoryIndex,
) -> HashMap<CallSiteId, CallTransformContext<'ctx>> {
    if call_summaries.is_empty() {
        return HashMap::new();
    }

    let sequence = path_block_sequence(path);
    let mut arg_state = BTreeMap::<usize, ValueId>::new();
    let mut contexts = HashMap::new();

    for (seq_index, block_addr) in sequence.iter().enumerate() {
        let Some(block) = func.get_block(*block_addr) else {
            continue;
        };
        if seq_index > 0 {
            let predecessor = sequence[seq_index - 1];
            for phi in &block.phis {
                if let Some(arg_index) = ssa_call_arg_slot_index(&phi.dst)
                    && let Some((_, source)) =
                        phi.sources.iter().find(|(pred, _)| *pred == predecessor)
                    && let Some(value_id) = func.graph().value_id_for_var(source)
                {
                    arg_state.insert(arg_index, value_id);
                }
            }
        }

        for (op_idx, op) in block.ops.iter().enumerate() {
            let Some(inst_id) = func.graph().inst_id_for_op_site(*block_addr, op_idx) else {
                continue;
            };
            if let Some(call_id) = func.call_sites().by_inst.get(&inst_id).copied()
                && let Some(callsite) = func.call_sites().by_id.get(&call_id)
                && let Some(target) = callsite.direct_target
                && let Some(view) = call_summaries.get(&target)
            {
                let context_snapshot = contexts.clone();
                let mut translator = ValueTranslator::new(
                    func,
                    initial_state,
                    memory_index,
                    &path.phi_predecessors,
                    &context_snapshot,
                );
                let args = (0..view.callconv.arg_capacity())
                    .map(|index| {
                        arg_state
                            .get(&index)
                            .copied()
                            .and_then(|value_id| translator.eval_value_id(value_id).ok())
                            .unwrap_or_else(|| {
                                view.callconv
                                    .arg_register_name(index)
                                    .map(|reg| {
                                        read_register_from_state(
                                            initial_state,
                                            reg,
                                            view.callconv.arg_bits(),
                                        )
                                    })
                                    .unwrap_or_else(|| SymValue::unknown(view.callconv.arg_bits()))
                            })
                    })
                    .collect::<Vec<_>>();
                contexts.insert(
                    call_id,
                    CallTransformContext {
                        summary: view.summary.clone(),
                        callconv: view.callconv.clone(),
                        args,
                    },
                );
            }

            if let Some(dst) = op.dst()
                && let Some(arg_index) = ssa_call_arg_slot_index(dst)
                && let Some(value_id) = func.graph().value_id_for_var(dst)
            {
                arg_state.insert(arg_index, value_id);
            }
        }
    }

    contexts
}

fn path_block_sequence(path: &ReversePath) -> Vec<u64> {
    let mut blocks = vec![path.block_addr];
    let mut current = path.block_addr;
    while let Some(predecessor) = path.phi_predecessors.get(&current).copied() {
        blocks.push(predecessor);
        current = predecessor;
    }
    blocks.reverse();
    blocks
}

fn and_all(_ctx: &Context, terms: &[Bool]) -> Bool {
    match terms {
        [] => Bool::from_bool(true),
        [term] => term.clone(),
        _ => {
            let refs = terms.iter().collect::<Vec<_>>();
            Bool::and(&refs)
        }
    }
}

fn or_all(_ctx: &Context, terms: &[Bool]) -> Bool {
    match terms {
        [] => Bool::from_bool(false),
        [term] => term.clone(),
        _ => {
            let refs = terms.iter().collect::<Vec<_>>();
            Bool::or(&refs)
        }
    }
}

fn eval_const_var<'ctx>(var: &r2ssa::SSAVar) -> Result<SymValue<'ctx>, EvalUnsupported> {
    if let Some(hex) = var.name.strip_prefix("const:") {
        u64::from_str_radix(hex, 16)
            .map(|value| SymValue::concrete(value, var.size * 8))
            .map_err(|_| EvalUnsupported::Unsupported)
    } else {
        Err(EvalUnsupported::Unsupported)
    }
}

fn read_input_var<'ctx>(state: &SymState<'ctx>, var: &r2ssa::SSAVar) -> SymValue<'ctx> {
    let key = var.display_name();
    let value = state.get_register_sized(&key, var.size * 8);
    if value.is_unknown() && var.version == 0 {
        let base = var.name.strip_prefix("reg:").unwrap_or(&var.name);
        state.get_register_sized(&base.to_ascii_uppercase(), var.size * 8)
    } else {
        value
    }
}

fn value_to_bool(ctx: &Context, value: &SymValue<'_>) -> Bool {
    value.to_bv(ctx).eq(BV::from_u64(0, value.bits())).not()
}

fn build_summary_substitutions<'ctx>(
    state: &SymState<'ctx>,
    summary: &DerivedFunctionSummary<'ctx>,
    call: &crate::sim::CallInfo<'ctx>,
) -> Vec<(BV, BV)> {
    let mut substitutions = Vec::new();
    for (index, symbol) in &summary.arg_symbols {
        let Some(actual) = call.args.get(*index) else {
            continue;
        };
        let adjusted = adjust_bits(state.context(), actual.clone(), symbol.bits());
        substitutions.push((
            symbol.to_bv(state.context()),
            adjusted.to_bv(state.context()),
        ));
    }
    for input in &summary.memory_inputs {
        let Some(base) = call.args.get(input.arg_index) else {
            continue;
        };
        let actual = adjust_bits(
            state.context(),
            state.mem_read(base, input.size),
            input.symbol.bits(),
        );
        substitutions.push((
            input.symbol.to_bv(state.context()),
            actual.to_bv(state.context()),
        ));
    }
    substitutions
}

fn build_call_substitutions<'ctx>(
    state: &SymState<'ctx>,
    call_ctx: &CallTransformContext<'ctx>,
) -> Vec<(BV, BV)> {
    let mut substitutions = Vec::new();
    for (index, symbol) in &call_ctx.summary.arg_symbols {
        let Some(actual) = call_ctx.args.get(*index) else {
            continue;
        };
        let adjusted = adjust_bits(state.context(), actual.clone(), symbol.bits());
        substitutions.push((
            symbol.to_bv(state.context()),
            adjusted.to_bv(state.context()),
        ));
    }
    for input in &call_ctx.summary.memory_inputs {
        let Some(base) = call_ctx.args.get(input.arg_index) else {
            continue;
        };
        let actual = adjust_bits(
            state.context(),
            state.mem_read(base, input.size),
            input.symbol.bits(),
        );
        substitutions.push((
            input.symbol.to_bv(state.context()),
            actual.to_bv(state.context()),
        ));
    }
    substitutions
}

fn summary_return_value<'ctx>(
    state: &SymState<'ctx>,
    call_ctx: &CallTransformContext<'ctx>,
) -> Result<(SymValue<'ctx>, Option<Bool>), EvalUnsupported> {
    if call_ctx.summary.cases.is_empty() {
        return Err(EvalUnsupported::Unsupported);
    }
    let substitutions = build_call_substitutions(state, call_ctx);
    let mut merged = SymValue::unknown(call_ctx.callconv.ret_bits());
    let mut matched = false;
    let mut guards = Vec::new();
    for case in call_ctx.summary.cases.iter().rev() {
        let Some(return_value) = &case.return_value else {
            continue;
        };
        let guard = substitute_bool(&case.guard, &substitutions);
        let value = substitute_value(state.context(), return_value, &substitutions);
        merged = ite_value(state.context(), &guard, &value, &merged);
        guards.push(guard);
        matched = true;
    }
    matched
        .then(|| {
            let coverage = matches!(
                call_ctx.summary.completion,
                crate::sim::DerivedSummaryCompletion::Exact
            )
            .then(|| or_all(state.context(), &guards));
            (merged, coverage)
        })
        .ok_or(EvalUnsupported::Unsupported)
}

fn summary_memory_locations<'ctx>(
    call_ctx: &CallTransformContext<'ctx>,
    addr: &SymValue<'ctx>,
) -> Vec<NormalizedMemoryLocation> {
    let Some(concrete_addr) = addr.as_concrete() else {
        return Vec::new();
    };
    let pointer_args = summary_pointer_arg_indices(call_ctx);
    let mut locations = Vec::new();
    for (index, base) in call_ctx.args.iter().enumerate() {
        if !pointer_args.is_empty() && !pointer_args.contains(&index) {
            continue;
        }
        let Some(base_addr) = base.as_concrete() else {
            continue;
        };
        if let Some(offset) = signed_offset_between(base_addr, concrete_addr) {
            locations.push(NormalizedMemoryLocation {
                region: BackwardMemoryRegion::Argument { index },
                offset,
            });
        }
    }
    locations
}

fn summary_pointer_arg_indices<'ctx>(call_ctx: &CallTransformContext<'ctx>) -> BTreeSet<usize> {
    let mut indices = BTreeSet::new();
    for input in &call_ctx.summary.memory_inputs {
        indices.insert(input.arg_index);
    }
    for case in &call_ctx.summary.cases {
        for write in &case.memory_writes {
            indices.insert(write.arg_index);
        }
    }
    indices
}

fn translated_arg_locations(
    (arg_index, offsets): (usize, BTreeSet<i64>),
) -> Vec<NormalizedMemoryLocation> {
    offsets
        .into_iter()
        .map(|offset| NormalizedMemoryLocation {
            region: BackwardMemoryRegion::Argument { index: arg_index },
            offset,
        })
        .collect()
}

fn memory_region_rank(region: &BackwardMemoryRegion) -> u8 {
    match region {
        BackwardMemoryRegion::Argument { .. } => 0,
        BackwardMemoryRegion::Region(region) => match region.kind {
            MemoryRegionKind::Stack => 1,
            MemoryRegionKind::Global => 2,
            MemoryRegionKind::Replay => 3,
            MemoryRegionKind::Input => 4,
            MemoryRegionKind::Heap => 5,
            MemoryRegionKind::EscapedUnknown => 6,
        },
    }
}

fn offsets_span(offsets: &BTreeSet<i64>) -> u64 {
    match (offsets.first().copied(), offsets.last().copied()) {
        (Some(lo), Some(hi)) => hi.saturating_sub(lo).unsigned_abs(),
        _ => 0,
    }
}

fn location_group_rank(group: &[NormalizedMemoryLocation]) -> Option<LocationGroupRank> {
    let region = group.first()?.region.clone();
    let offsets = group
        .iter()
        .map(|location| location.offset)
        .collect::<BTreeSet<_>>();
    let span = offsets_span(&offsets);
    Some(LocationGroupRank {
        region_rank: memory_region_rank(&region),
        inexact_offset: span != 0,
        span,
        offset_count: offsets.len(),
    })
}

fn location_group_tie_break(group: &[NormalizedMemoryLocation]) -> Option<LocationGroupTieBreak> {
    let region = group.first()?.region.clone();
    let min_offset = group
        .iter()
        .map(|location| location.offset)
        .min()
        .unwrap_or(0);
    Some(match region {
        BackwardMemoryRegion::Argument { index } => LocationGroupTieBreak {
            region_discriminant: 0,
            region_id: 0,
            arg_index: index,
            min_offset,
        },
        BackwardMemoryRegion::Region(region) => LocationGroupTieBreak {
            region_discriminant: 1,
            region_id: region.id.0,
            arg_index: 0,
            min_offset,
        },
    })
}

fn select_best_location_group(
    groups: Vec<Vec<NormalizedMemoryLocation>>,
) -> Option<Vec<NormalizedMemoryLocation>> {
    if groups.len() <= 1 {
        return groups.into_iter().next();
    }

    let mut ranked = groups
        .into_iter()
        .filter_map(|group| {
            Some((
                location_group_rank(&group)?,
                location_group_tie_break(&group)?,
                group,
            ))
        })
        .collect::<Vec<_>>();
    ranked.sort_by(|left, right| left.0.cmp(&right.0).then_with(|| left.1.cmp(&right.1)));
    if ranked.len() > 1 && ranked[0].0 == ranked[1].0 {
        None
    } else {
        ranked.into_iter().next().map(|(_, _, group)| group)
    }
}

fn translated_offsets_rank(offsets: &BTreeSet<i64>) -> (bool, u64, usize) {
    let span = offsets_span(offsets);
    (span != 0, span, offsets.len())
}

fn select_best_translated_arg(
    translated: BTreeMap<usize, BTreeSet<i64>>,
) -> Option<(usize, BTreeSet<i64>)> {
    if translated.len() <= 1 {
        return translated.into_iter().next();
    }

    let mut ranked = translated
        .into_iter()
        .map(|(arg_index, offsets)| (translated_offsets_rank(&offsets), arg_index, offsets))
        .collect::<Vec<_>>();
    ranked.sort_by(|left, right| left.0.cmp(&right.0).then_with(|| left.1.cmp(&right.1)));
    if ranked.len() > 1 && ranked[0].0 == ranked[1].0 {
        None
    } else {
        ranked
            .into_iter()
            .next()
            .map(|(_, arg_index, offsets)| (arg_index, offsets))
    }
}

fn group_normalized_locations(
    locations: &[NormalizedMemoryLocation],
) -> Vec<Vec<NormalizedMemoryLocation>> {
    let mut grouped = BTreeMap::<BackwardMemoryRegion, BTreeSet<i64>>::new();
    for location in locations {
        grouped
            .entry(location.region.clone())
            .or_default()
            .insert(location.offset);
    }
    grouped
        .into_iter()
        .map(|(region, offsets)| {
            offsets
                .into_iter()
                .map(|offset| NormalizedMemoryLocation {
                    region: region.clone(),
                    offset,
                })
                .collect()
        })
        .collect()
}

fn apply_delta_offsets(
    base_locations: &[NormalizedMemoryLocation],
    deltas: &[i64],
    add: bool,
) -> Vec<NormalizedMemoryLocation> {
    let mut merged = BTreeSet::new();
    for base in base_locations {
        for delta in deltas {
            let offset = if add {
                base.offset.saturating_add(*delta)
            } else {
                base.offset.saturating_sub(*delta)
            };
            merged.insert((base.region.clone(), offset));
        }
    }
    merged
        .into_iter()
        .map(|(region, offset)| NormalizedMemoryLocation { region, offset })
        .collect()
}

fn select_covering_write<'a, 'ctx>(
    writes: &'a [crate::sim::DerivedMemoryWrite<'ctx>],
    locations: &[NormalizedMemoryLocation],
    size: u32,
) -> Option<(
    NormalizedMemoryLocation,
    &'a crate::sim::DerivedMemoryWrite<'ctx>,
)> {
    select_covering_writes(writes, locations, size)
        .into_iter()
        .min_by_key(|(location, write)| (write.size, write.offset, location.offset))
}

fn select_covering_writes<'a, 'ctx>(
    writes: &'a [crate::sim::DerivedMemoryWrite<'ctx>],
    locations: &[NormalizedMemoryLocation],
    size: u32,
) -> Vec<(
    NormalizedMemoryLocation,
    &'a crate::sim::DerivedMemoryWrite<'ctx>,
)> {
    writes
        .iter()
        .flat_map(|write| {
            locations.iter().filter_map(move |location| {
                (matches!(
                    location.region,
                    BackwardMemoryRegion::Argument { index } if index == write.arg_index
                ) && {
                    let write_start = write.offset as i128;
                    let write_end = write_start.saturating_add(write.size as i128);
                    let read_start = location.offset as i128;
                    let read_end = read_start.saturating_add(size as i128);
                    write_start <= read_start && write_end >= read_end
                })
                .then_some((location.clone(), write))
            })
        })
        .collect()
}

fn select_best_covering_write<'a, 'ctx>(
    covering: Vec<(
        NormalizedMemoryLocation,
        &'a crate::sim::DerivedMemoryWrite<'ctx>,
    )>,
) -> Option<(
    NormalizedMemoryLocation,
    &'a crate::sim::DerivedMemoryWrite<'ctx>,
)> {
    covering
        .into_iter()
        .min_by_key(|(location, write)| (write.size, write.offset, location.offset))
}

fn covering_writes_are_ambiguous<'a, 'ctx>(
    covering: &[(
        NormalizedMemoryLocation,
        &'a crate::sim::DerivedMemoryWrite<'ctx>,
    )],
) -> bool {
    let distinct = covering
        .iter()
        .filter_map(|(location, write)| match location.region {
            BackwardMemoryRegion::Argument { index } => {
                Some((index, location.offset, write.arg_index))
            }
            BackwardMemoryRegion::Region(_) => None,
        })
        .collect::<BTreeSet<_>>();
    distinct.len() > 1
}

fn slice_write_value<'ctx>(
    ctx: &'ctx Context,
    write: &crate::sim::DerivedMemoryWrite<'ctx>,
    offset: i64,
    size: u32,
) -> SymValue<'ctx> {
    if write.offset == offset && write.size == size {
        return write.value.clone();
    }
    let relative = offset.saturating_sub(write.offset) as u64;
    let low_bit = (relative * 8) as u32;
    let high_bit = low_bit + (size * 8) - 1;
    adjust_bits(ctx, write.value.clone(), write.size * 8).extract(ctx, high_bit, low_bit)
}

fn signed_offset_between(base: u64, addr: u64) -> Option<i64> {
    if addr >= base {
        i64::try_from(addr - base).ok()
    } else {
        i64::try_from(base - addr).ok().map(|delta| -delta)
    }
}

fn is_specific_memory_location(location: &NormalizedMemoryLocation) -> bool {
    !matches!(
        &location.region,
        BackwardMemoryRegion::Region(BackwardRegionRef {
            kind: MemoryRegionKind::EscapedUnknown,
            ..
        })
    )
}

fn ssa_call_arg_slot_index(var: &r2ssa::SSAVar) -> Option<usize> {
    ssa_register_arg_index(var)
}

fn memory_address_symbol_component(address: &r2ssa::RelativeMemoryAddress) -> String {
    match address {
        r2ssa::RelativeMemoryAddress::Exact(offset) => format!("exact_{offset}"),
        r2ssa::RelativeMemoryAddress::Affine { terms, offset } => {
            let terms = terms
                .iter()
                .map(|term| format!("v{}_c{}", term.value.0, term.coefficient))
                .collect::<Vec<_>>()
                .join("_");
            format!("affine_{terms}_offset_{offset}")
        }
        r2ssa::RelativeMemoryAddress::Unknown => "unknown".to_string(),
    }
}

fn ssa_register_arg_index(var: &r2ssa::SSAVar) -> Option<usize> {
    let display = var.display_name();
    if let Some((prefix, _)) = split_version(&display)
        && let Some(index) = callconv_arg_index(prefix)
    {
        return Some(index);
    }
    callconv_arg_index(&display).or_else(|| callconv_arg_index(&var.name))
}

fn callconv_arg_index(name: &str) -> Option<usize> {
    let upper = name.to_ascii_uppercase();
    match upper.as_str() {
        "RDI" | "EDI" => Some(0),
        "RSI" | "ESI" => Some(1),
        "RDX" | "EDX" => Some(2),
        "RCX" | "ECX" => Some(3),
        "R8" | "R8D" => Some(4),
        "R9" | "R9D" => Some(5),
        _ => None,
    }
}

fn register_aliases(base: &str) -> Vec<&str> {
    match base {
        "RAX" => vec!["RAX", "EAX"],
        "RDI" => vec!["RDI", "EDI"],
        "RSI" => vec!["RSI", "ESI"],
        "RDX" => vec!["RDX", "EDX"],
        "RCX" => vec!["RCX", "ECX"],
        "R8" => vec!["R8", "R8D"],
        "R9" => vec!["R9", "R9D"],
        _ => vec![base],
    }
}

fn read_register_from_state<'ctx>(state: &SymState<'ctx>, base: &str, bits: u32) -> SymValue<'ctx> {
    for alias in register_aliases(base) {
        if let Some(key) = find_register_key(state, alias) {
            return state.get_register_sized(&key, bits);
        }
    }
    SymValue::unknown(bits)
}

fn add_signed_offset<'ctx>(
    ctx: &'ctx Context,
    base: &SymValue<'ctx>,
    offset: i64,
    bits: u32,
) -> SymValue<'ctx> {
    if offset >= 0 {
        base.add(ctx, &SymValue::concrete(offset as u64, bits))
    } else {
        base.sub(ctx, &SymValue::concrete(offset.unsigned_abs(), bits))
    }
}

fn find_register_key<'ctx>(state: &SymState<'ctx>, base: &str) -> Option<String> {
    let mut best: Option<(u32, String)> = None;
    for key in state.registers().keys() {
        if let Some((prefix, version)) = split_version(key) {
            if prefix.eq_ignore_ascii_case(base)
                && best
                    .as_ref()
                    .is_none_or(|(best_version, _)| version > *best_version)
            {
                best = Some((version, key.clone()));
            }
        } else if key.eq_ignore_ascii_case(base) {
            return Some(key.clone());
        }
    }
    best.map(|(_, key)| key)
}

fn split_version(name: &str) -> Option<(&str, u32)> {
    let (prefix, suffix) = name.rsplit_once('_')?;
    if suffix.is_empty() || !suffix.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let version = suffix.parse().ok()?;
    Some((prefix, version))
}

fn substitute_value<'ctx>(
    ctx: &'ctx Context,
    value: &SymValue<'ctx>,
    substitutions: &[(BV, BV)],
) -> SymValue<'ctx> {
    if substitutions.is_empty() {
        return value.clone();
    }
    let pairs = substitutions
        .iter()
        .map(|(from, to)| (from, to))
        .collect::<Vec<_>>();
    catch_unwind(AssertUnwindSafe(|| value.to_bv(ctx).substitute(&pairs)))
        .map(|substituted| SymValue::symbolic_tainted(substituted, value.bits(), value.get_taint()))
        .unwrap_or_else(|_| SymValue::unknown(value.bits()))
}

fn substitute_bool(ast: &Bool, substitutions: &[(BV, BV)]) -> Bool {
    if substitutions.is_empty() {
        return ast.clone();
    }
    let pairs = substitutions
        .iter()
        .map(|(from, to)| (from, to))
        .collect::<Vec<_>>();
    catch_unwind(AssertUnwindSafe(|| ast.substitute(&pairs)))
        .unwrap_or_else(|_| Bool::from_bool(true))
}

fn ite_value<'ctx>(
    ctx: &'ctx Context,
    guard: &Bool,
    when_true: &SymValue<'ctx>,
    when_false: &SymValue<'ctx>,
) -> SymValue<'ctx> {
    let bits = when_true.bits().max(when_false.bits());
    let taint = when_true.get_taint() | when_false.get_taint();
    let true_bv = adjust_bits(ctx, when_true.clone(), bits).to_bv(ctx);
    let false_bv = adjust_bits(ctx, when_false.clone(), bits).to_bv(ctx);
    SymValue::symbolic_tainted(guard.ite(&true_bv, &false_bv), bits, taint)
}

fn adjust_bits<'ctx>(ctx: &'ctx Context, value: SymValue<'ctx>, bits: u32) -> SymValue<'ctx> {
    if value.bits() == bits {
        return value;
    }
    if value.bits() < bits {
        value.zero_extend(ctx, bits)
    } else {
        value.extract(ctx, bits - 1, 0)
    }
}

#[cfg(test)]
mod tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec,
        SourceFunctionInterface, SourceFunctionReturn,
    };
    use z3::Context;

    use super::*;

    fn make_reg(offset: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Register,
            offset,
            size,
            meta: None,
        }
    }

    fn make_const(value: u64, size: u32) -> Varnode {
        Varnode {
            space: SpaceId::Const,
            offset: value,
            size,
            meta: None,
        }
    }

    #[test]
    fn compile_target_precondition_builds_guard_for_simple_branch() {
        let blocks = vec![
            R2ILBlock {
                addr: 0x1000,
                size: 4,
                ops: vec![
                    R2ILOp::IntEqual {
                        dst: make_reg(16, 1),
                        a: make_reg(56, 8),
                        b: make_const(0x1337, 8),
                    },
                    R2ILOp::CBranch {
                        target: make_const(0x1010, 8),
                        cond: make_reg(16, 1),
                    },
                ],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1004,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(0, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
            R2ILBlock {
                addr: 0x1010,
                size: 4,
                ops: vec![R2ILOp::Copy {
                    dst: make_reg(0, 8),
                    src: make_const(1, 8),
                }],
                switch_info: None,
                op_metadata: Default::default(),
            },
        ];
        let func = SsaArtifact::for_symbolic(&blocks, None).expect("ssa");
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        state.make_symbolic("reg:56_0", 64);

        let compiled = compile_target_precondition(&func, &state, 0x1010).expect("compiled");
        assert_eq!(
            compiled.summary.precision,
            BackwardConditionPrecision::Exact
        );
        assert!(compiled.summary.simplified.contains("1337") || !compiled.summary.terms.is_empty());
    }

    #[test]
    fn paired_branch_compilation_preserves_symbolic_memory_input() {
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RDI", 56, 8));
        let rdi = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 56,
            size: 8,
        };
        let interface = SourceFunctionInterface::new_exact(
            b"paired-symbolic-memory-input-v1".to_vec(),
            "x86-64",
            [SourceAbiParameterSpec::new(0, rdi)],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("exact untyped RDI parameter interface");
        let mut branch = R2ILBlock::new(0x1000, 4);
        branch.push(R2ILOp::Load {
            dst: Varnode::unique(0x10, 4),
            space: SpaceId::Ram,
            addr: make_reg(56, 8),
        });
        branch.push(R2ILOp::IntEqual {
            dst: Varnode::unique(0x20, 1),
            a: Varnode::unique(0x10, 4),
            b: make_const(0x41, 4),
        });
        branch.push(R2ILOp::CBranch {
            target: make_const(0x1010, 8),
            cond: Varnode::unique(0x20, 1),
        });
        let mut false_exit = R2ILBlock::new(0x1004, 4);
        false_exit.push(R2ILOp::Return {
            target: make_const(0, 8),
        });
        let mut true_exit = R2ILBlock::new(0x1010, 4);
        true_exit.push(R2ILOp::Return {
            target: make_const(1, 8),
        });
        let func = SsaArtifact::for_symbolic_with_interface(
            &[branch, false_exit, true_exit],
            Some(&arch),
            interface,
        )
        .expect("ssa");
        let ctx = Context::thread_local();
        let mut state = SymState::new(&ctx, 0x1000);
        crate::runtime::seed_default_state_for_arch(&mut state, &func, Some(&arch));

        let (when_true, when_false) =
            compile_branch_preconditions_with_summaries(&func, &state, 0x1000, &HashMap::new())
                .expect("paired branch conditions");
        let single_true = compile_branch_precondition_with_summaries(
            &func,
            &state,
            0x1000,
            true,
            &HashMap::new(),
        )
        .expect("true branch condition");
        let single_false = compile_branch_precondition_with_summaries(
            &func,
            &state,
            0x1000,
            false,
            &HashMap::new(),
        )
        .expect("false branch condition");

        assert_eq!(when_true.summary, single_true.summary);
        assert_eq!(when_false.summary, single_false.summary);
        assert_eq!(
            when_true.summary.precision,
            BackwardConditionPrecision::Exact
        );
        assert_eq!(when_true.summary.memory_terms.len(), 1);
        assert!(when_true.summary.simplified.contains("memory_object_"));
        assert_ne!(when_true.summary.simplified, "true");
        assert_ne!(when_true.summary.simplified, "false");
    }

    #[test]
    fn select_best_location_group_prefers_stable_exact_region() {
        let global_group = vec![NormalizedMemoryLocation {
            region: BackwardMemoryRegion::Region(BackwardRegionRef {
                id: MemoryRegionId(1),
                kind: MemoryRegionKind::Global,
                name: "global".to_string(),
            }),
            offset: 4,
        }];
        let heap_group = vec![
            NormalizedMemoryLocation {
                region: BackwardMemoryRegion::Region(BackwardRegionRef {
                    id: MemoryRegionId(2),
                    kind: MemoryRegionKind::Heap,
                    name: "heap".to_string(),
                }),
                offset: 4,
            },
            NormalizedMemoryLocation {
                region: BackwardMemoryRegion::Region(BackwardRegionRef {
                    id: MemoryRegionId(2),
                    kind: MemoryRegionKind::Heap,
                    name: "heap".to_string(),
                }),
                offset: 8,
            },
        ];

        let best =
            select_best_location_group(vec![heap_group, global_group.clone()]).expect("best group");
        assert_eq!(best, global_group);
    }

    #[test]
    fn select_best_translated_arg_ties_remain_residual() {
        let translated = BTreeMap::from([
            (0usize, BTreeSet::from([0i64])),
            (1usize, BTreeSet::from([0i64])),
        ]);
        assert!(select_best_translated_arg(translated).is_none());
    }

    #[test]
    fn ssa_call_arg_slot_index_tracks_written_abi_registers() {
        assert_eq!(
            ssa_call_arg_slot_index(&r2ssa::SSAVar::new("RDI", 1, 8)),
            Some(0)
        );
        assert_eq!(
            ssa_call_arg_slot_index(&r2ssa::SSAVar::new("EDX", 3, 4)),
            Some(2)
        );
        assert_eq!(
            ssa_call_arg_slot_index(&r2ssa::SSAVar::new("RAX", 1, 8)),
            None
        );
    }

    #[test]
    fn inferred_memory_term_evidence_promotes_bounded_global_and_replay_regions_to_likely() {
        let global_region = BackwardMemoryRegion::Region(BackwardRegionRef {
            id: MemoryRegionId(1),
            kind: MemoryRegionKind::Global,
            name: "global".to_string(),
        });
        let replay_region = BackwardMemoryRegion::Region(BackwardRegionRef {
            id: MemoryRegionId(2),
            kind: MemoryRegionKind::Replay,
            name: "replay".to_string(),
        });

        let global = inferred_memory_term_evidence(&global_region, 0, 12, false);
        let replay = inferred_memory_term_evidence(&replay_region, 4, 16, false);

        assert_eq!(global.tier, SemanticConfidence::Likely);
        assert!(
            global
                .reasons
                .contains(&SemanticEvidenceReason::DerivedFromRanking)
        );
        assert_eq!(replay.tier, SemanticConfidence::Likely);
        assert!(
            replay
                .reasons
                .contains(&SemanticEvidenceReason::ReplayOverlap)
        );
    }

    #[test]
    fn inferred_memory_term_evidence_promotes_small_heap_windows_to_likely() {
        let heap_region = BackwardMemoryRegion::Region(BackwardRegionRef {
            id: MemoryRegionId(3),
            kind: MemoryRegionKind::Heap,
            name: "heap".to_string(),
        });

        let heap = inferred_memory_term_evidence(&heap_region, 8, 16, false);
        let ambiguous = inferred_memory_term_evidence(&heap_region, 8, 32, false);

        assert_eq!(heap.tier, SemanticConfidence::Likely);
        assert!(
            heap.reasons
                .contains(&SemanticEvidenceReason::HeapIdentityWeak)
        );
        assert_eq!(ambiguous.tier, SemanticConfidence::Heuristic);
    }
}
