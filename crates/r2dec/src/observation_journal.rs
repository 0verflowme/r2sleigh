//! Authority-bound observations of the legacy renderer's final AST decisions.
//!
//! This module owns the only production allocator for render observation IDs.
//! It is intentionally not wired into lowering yet: Stage 5 callers will mark
//! exact occurrences, run every AST rewrite, then seal the dense source V/U/W
//! snapshot from the final wrapped nodes.

#![allow(
    dead_code,
    reason = "Stage 5 journal foundation is sealed before production cutover"
)]

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use r2ssa::{
    InstId, MachineUseDisposition, MachineWriteDisposition, SSAFunction, SsaArtifactAuthority,
    UseSite, ValueId,
};
use r2types::SourceOwnedFunctionFacts;

use crate::ast::{
    BinaryOp, CExpr, CFunction, CStmt, RenderObservationInspectError, RenderObservationNode,
    RenderObservationStripError, inspect_and_strip_render_observations,
};
use crate::binding_plan::{BindingPlan, BindingPlanSourceMismatch, ValueDisposition};
use crate::codegen::{EmissionReadyFunction, prepare_function_for_emission};
use crate::normalize::{
    NormalizationOriginError, NormalizationOrigins, NormalizedOpProjection, NormalizedOpSite,
};
use crate::shadow_report::{
    LegacyAnalysisSnapshot, LegacyBindingId, LegacyUseCell, LegacyUseObservation, LegacyValueCell,
    LegacyValueObservation, LegacyWriteCell, LegacyWriteObservation,
};
use crate::symbol::{SymbolId, SymbolTable};

/// Opaque dense identity of one exact marked AST occurrence.
///
/// It is deliberately neither serializable nor deserializable. Production
/// construction is private to [`LegacyObservationJournal`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RenderObservationId(u32);

impl RenderObservationId {
    pub(crate) const fn index(self) -> u32 {
        self.0
    }

    #[cfg(test)]
    pub(crate) const fn from_index(index: u32) -> Self {
        Self(index)
    }
}

/// Capability required to expose a marked emission tree for journal sealing.
/// Its constructor is private to this module, so no other lowering or codegen
/// caller can bypass the marked-draft boundary.
pub(crate) struct ObservationSealAuthority(());

impl ObservationSealAuthority {
    fn new() -> Self {
        Self(())
    }
}

#[cfg(test)]
pub(crate) const fn test_render_observation_id(index: u32) -> RenderObservationId {
    RenderObservationId::from_index(index)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ObservationTarget {
    Value(ValueId),
    Use {
        site: UseSite,
        observation: LegacyUseObservation,
    },
    Write {
        inst: InstId,
        observation: LegacyWriteObservation,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum LegacyObservationJournalError {
    SourceAuthority,
    BindingPlan(BindingPlanSourceMismatch),
    Normalization(NormalizationOriginError),
    TooManyObservations,
    InvalidValue(ValueId),
    InvalidUse(UseSite),
    InvalidWrite(InstId),
    OutputlessWrite(InstId),
    InvalidNormalizedSite(NormalizedOpSite),
    MissingNormalizedBlock(u64),
    MissingNormalizedSiteContext,
    InvalidNormalizedInput {
        site: NormalizedOpSite,
        input_idx: usize,
    },
    MissingNormalizedOutput(NormalizedOpSite),
    RefusedRenderedUse(UseSite),
    RefusedRenderedWrite(InstId),
    RenderedValueRequired(ValueId),
    ExactUseRequiresRenderedOccurrence(UseSite),
    ExactWriteRequiresRenderedOccurrence(InstId),
    SymbolTableMismatch,
    UnownedBindingSymbol(SymbolId),
    ConflictingValue(ValueId),
    ConflictingUse(UseSite),
    ConflictingWrite(InstId),
    Markers(RenderObservationStripError),
}

/// Final coverage of one dense source domain after marker inspection.
///
/// `accounted` counts only decisions that survived in the final emission tree
/// or were recorded explicitly as typed elision/refusal. `absent` is therefore
/// observable missing legacy coverage, not an inferred decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LegacyObservationDomainCoverage {
    pub(crate) total: usize,
    pub(crate) accounted: usize,
    pub(crate) absent: usize,
    pub(crate) refused: usize,
}

impl LegacyObservationDomainCoverage {
    fn from_counts(total: usize, accounted: usize, refused: usize) -> Self {
        Self {
            total,
            accounted,
            absent: total - accounted,
            refused,
        }
    }

    pub(crate) fn equations_hold(self) -> bool {
        self.accounted.checked_add(self.absent) == Some(self.total)
            && self.refused <= self.accounted
    }

    pub(crate) fn is_complete(self) -> bool {
        self.equations_hold() && self.absent == 0
    }

    pub(crate) fn passes_quality(self) -> bool {
        self.is_complete() && self.refused == 0
    }
}

/// Dense V/U/W coverage sealed from the final marker-bearing emission tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LegacyObservationCoverage {
    pub(crate) values: LegacyObservationDomainCoverage,
    pub(crate) uses: LegacyObservationDomainCoverage,
    pub(crate) writes: LegacyObservationDomainCoverage,
}

impl LegacyObservationCoverage {
    pub(crate) fn equations_hold(self) -> bool {
        self.values.equations_hold() && self.uses.equations_hold() && self.writes.equations_hold()
    }

    pub(crate) fn is_complete(self) -> bool {
        self.values.is_complete() && self.uses.is_complete() && self.writes.is_complete()
    }

    pub(crate) fn passes_quality(self) -> bool {
        self.values.passes_quality()
            && self.uses.passes_quality()
            && self.writes.passes_quality()
    }
}

/// One dense legacy snapshot and the independently visible coverage that
/// produced it. Missing cells remain `LegacyAbsent` in the snapshot while the
/// coverage keeps them distinguishable from explicit final decisions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SealedLegacyObservations {
    snapshot: LegacyAnalysisSnapshot,
    coverage: LegacyObservationCoverage,
}

impl SealedLegacyObservations {
    pub(crate) const fn snapshot(&self) -> &LegacyAnalysisSnapshot {
        &self.snapshot
    }

    pub(crate) const fn coverage(&self) -> LegacyObservationCoverage {
        self.coverage
    }
}

/// Sealed, source-authority-bound recorder for one legacy rendering run.
pub(crate) struct LegacyObservationJournal {
    authority: SsaArtifactAuthority,
    plan: Rc<BindingPlan>,
    normalized_projections: Vec<Box<[NormalizedOpProjection]>>,
    symbols: Rc<RefCell<SymbolTable>>,
    value_is_literal: Box<[bool]>,
    values: Box<[Option<LegacyValueObservation>]>,
    uses: Box<[Box<[Option<LegacyUseObservation>]>]>,
    write_has_output: Box<[bool]>,
    writes: Box<[Option<LegacyWriteObservation>]>,
    targets: Vec<ObservationTarget>,
}

/// Internal ownership boundary for an AST that may still contain markers.
///
/// There is deliberately no function accessor. A marked tree can become
/// visible to another decompiler module only by sealing it, which first runs
/// emission preparation and then strips every marker transactionally.
pub(crate) struct MarkedNativeDraft {
    function: CFunction,
    journal: LegacyObservationJournal,
}

impl MarkedNativeDraft {
    pub(crate) fn new(function: CFunction, journal: LegacyObservationJournal) -> Self {
        Self { function, journal }
    }

    pub(crate) fn seal(
        self,
        source: &SourceOwnedFunctionFacts,
    ) -> Result<SealedNativeFunction, LegacyObservationJournalError> {
        let mut ready = prepare_function_for_emission(&self.function);
        let plan = Rc::clone(&self.journal.plan);
        let observations = self.journal.seal(source, &mut ready)?;
        Ok(SealedNativeFunction {
            ready,
            observations,
            plan,
        })
    }
}

/// Marker-free exact emission tree paired with the observations sealed from it.
pub(crate) struct SealedNativeFunction {
    ready: EmissionReadyFunction,
    observations: SealedLegacyObservations,
    plan: Rc<BindingPlan>,
}

impl SealedNativeFunction {
    pub(crate) const fn emission(&self) -> &EmissionReadyFunction {
        &self.ready
    }

    pub(crate) const fn observations(&self) -> &LegacyAnalysisSnapshot {
        self.observations.snapshot()
    }

    pub(crate) const fn observation_coverage(&self) -> LegacyObservationCoverage {
        self.observations.coverage()
    }

    pub(crate) fn plan(&self) -> &BindingPlan {
        &self.plan
    }

    pub(crate) fn into_function(self) -> CFunction {
        self.ready.into_function()
    }
}

impl LegacyObservationJournal {
    pub(crate) fn new(
        source: &SourceOwnedFunctionFacts,
        normalized: &SSAFunction,
        origins: &NormalizationOrigins,
        plan: Rc<BindingPlan>,
        symbols: Rc<RefCell<SymbolTable>>,
    ) -> Result<Self, LegacyObservationJournalError> {
        plan.validate_source(source.source())
            .map_err(LegacyObservationJournalError::BindingPlan)?;
        origins
            .validate(normalized, source.source(), source.report().render())
            .map_err(LegacyObservationJournalError::Normalization)?;

        let graph = source.source().graph();
        let mut normalized_projections: Vec<Box<[NormalizedOpProjection]>> =
            vec![Vec::new().into_boxed_slice(); graph.blocks.len()];
        for block_id in graph.block_order.iter().copied() {
            let block = graph
                .block(block_id)
                .and_then(|block| normalized.get_block(block.addr))
                .ok_or(LegacyObservationJournalError::Normalization(
                    NormalizationOriginError::BlockTopology,
                ))?;
            let rows = (0..block.ops.len())
                .map(|op_idx| {
                    let site = NormalizedOpSite {
                        block: block_id,
                        op_idx,
                    };
                    origins
                        .projection(site, source.source())
                        .map_err(LegacyObservationJournalError::Normalization)?
                        .ok_or(LegacyObservationJournalError::InvalidNormalizedSite(site))
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_boxed_slice();
            normalized_projections[block_id.0 as usize] = rows;
        }
        let value_is_literal = graph
            .values
            .iter()
            .map(|value| value.var.constant_bits().is_some())
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let values = vec![None; graph.values.len()].into_boxed_slice();
        let uses = graph
            .insts
            .iter()
            .map(|inst| vec![None; inst.inputs.len()].into_boxed_slice())
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let write_has_output = graph
            .insts
            .iter()
            .map(|inst| inst.output.is_some())
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let writes = vec![None; graph.insts.len()].into_boxed_slice();

        let mut journal = Self {
            authority: source.source().authority().clone(),
            plan,
            normalized_projections,
            symbols,
            value_is_literal,
            values,
            uses,
            write_has_output,
            writes,
            targets: Vec::new(),
        };
        journal.record_upstream_nonrendered_dispositions()?;
        Ok(journal)
    }

    /// Seed only decisions whose upstream disposition proves that no rendered
    /// occurrence may exist. Bound, inline, and exact machine cells remain
    /// absent until a marker actually survives final emission.
    fn record_upstream_nonrendered_dispositions(
        &mut self,
    ) -> Result<(), LegacyObservationJournalError> {
        let nonrendered_values = (0..self.values.len())
            .filter_map(|index| {
                let value = ValueId(index as u32);
                matches!(
                    self.plan.disposition(value),
                    Some(ValueDisposition::Elided { .. } | ValueDisposition::Refused { .. })
                )
                .then_some(value)
            })
            .collect::<Vec<_>>();
        let refused_uses = self
            .plan
            .machine_projection()
            .use_dispositions()
            .iter()
            .enumerate()
            .flat_map(|(inst, row)| {
                row.iter().enumerate().filter_map(move |(input_idx, disposition)| {
                    matches!(disposition, MachineUseDisposition::Refused(_)).then_some(UseSite {
                        inst: InstId(inst as u32),
                        input_idx,
                    })
                })
            })
            .collect::<Vec<_>>();
        let refused_writes = self
            .plan
            .machine_projection()
            .write_dispositions()
            .iter()
            .enumerate()
            .filter_map(|(inst, disposition)| {
                matches!(disposition, Some(MachineWriteDisposition::Refused(_)))
                    .then_some(InstId(inst as u32))
            })
            .collect::<Vec<_>>();

        for value in nonrendered_values {
            self.record_nonrendered_value(value)?;
        }
        for site in refused_uses {
            self.record_refused_use(site)?;
        }
        for inst in refused_writes {
            self.record_refused_write(inst)?;
        }
        Ok(())
    }

    fn allocate_pair(
        &mut self,
        first: ObservationTarget,
        second: ObservationTarget,
    ) -> Result<(RenderObservationId, RenderObservationId), LegacyObservationJournalError> {
        let first_index = u32::try_from(self.targets.len())
            .map_err(|_| LegacyObservationJournalError::TooManyObservations)?;
        let second_index = first_index
            .checked_add(1)
            .ok_or(LegacyObservationJournalError::TooManyObservations)?;
        self.targets.push(first);
        self.targets.push(second);
        Ok((
            RenderObservationId(first_index),
            RenderObservationId(second_index),
        ))
    }

    fn allocate_many(
        &mut self,
        targets: Vec<ObservationTarget>,
    ) -> Result<Vec<RenderObservationId>, LegacyObservationJournalError> {
        let first = u32::try_from(self.targets.len())
            .map_err(|_| LegacyObservationJournalError::TooManyObservations)?;
        let count = u32::try_from(targets.len())
            .map_err(|_| LegacyObservationJournalError::TooManyObservations)?;
        if count > 0 {
            first
                .checked_add(count - 1)
                .ok_or(LegacyObservationJournalError::TooManyObservations)?;
        }
        let ids = (0..count)
            .map(|offset| RenderObservationId(first + offset))
            .collect();
        self.targets.extend(targets);
        Ok(ids)
    }

    fn allocate_normalized_output_targets(
        &mut self,
        site: NormalizedOpSite,
    ) -> Result<(RenderObservationId, RenderObservationId), LegacyObservationJournalError> {
        let output = self.normalized_output(site)?;
        self.value_slot(output.value)?;
        let write = self.rendered_write_observation(output.inst)?;
        self.allocate_pair(
            ObservationTarget::Value(output.value),
            ObservationTarget::Write {
                inst: output.inst,
                observation: write,
            },
        )
    }

    /// Mark one value occurrence and every original use represented by the
    /// exact normalized operand that produced it.
    ///
    /// Callers cannot supply a `ValueId`, `UseSite`, or machine disposition:
    /// all three come from the authority-checked normalization projection and
    /// binding plan retained by this journal.
    pub(crate) fn observe_normalized_input_expr(
        &mut self,
        site: NormalizedOpSite,
        input_idx: usize,
        expr: CExpr,
    ) -> Result<CExpr, LegacyObservationJournalError> {
        let input = self
            .normalized_projection(site)?
            .inputs
            .get(input_idx)
            .cloned()
            .ok_or(LegacyObservationJournalError::InvalidNormalizedInput { site, input_idx })?;
        let value = input.value;
        self.value_slot(value)?;
        let mut targets = Vec::with_capacity(1 + input.uses.len());
        targets.push(ObservationTarget::Value(value));
        for use_site in input.uses {
            let observation = self.rendered_use_observation(use_site)?;
            targets.push(ObservationTarget::Use {
                site: use_site,
                observation,
            });
        }
        let mut ids = self.allocate_many(targets)?.into_iter();
        let value_id = ids
            .next()
            .expect("a normalized input always allocates its value observation");
        let mut marked = CExpr::observed(value_id, expr);
        for id in ids {
            marked = CExpr::observed(id, marked);
        }
        Ok(marked)
    }

    /// Mark one rendered definition and its source write using the exact
    /// normalized output projection.
    pub(crate) fn observe_normalized_output_stmt(
        &mut self,
        site: NormalizedOpSite,
        stmt: CStmt,
    ) -> Result<CStmt, LegacyObservationJournalError> {
        let (value_id, write_id) = self.allocate_normalized_output_targets(site)?;
        Ok(CStmt::observed(write_id, CStmt::observed(value_id, stmt)))
    }

    /// Mark one rendered definition that survives inside an expression.
    ///
    /// This is the expression twin of [`Self::observe_normalized_output_stmt`].
    /// Both value and write identity come exclusively from the authority-bound
    /// normalized output projection retained by this journal.
    pub(crate) fn observe_normalized_output_expr(
        &mut self,
        site: NormalizedOpSite,
        expr: CExpr,
    ) -> Result<CExpr, LegacyObservationJournalError> {
        let (value_id, write_id) = self.allocate_normalized_output_targets(site)?;
        Ok(CExpr::observed(write_id, CExpr::observed(value_id, expr)))
    }

    /// Record a value only when the sealed plan proves that no rendered AST
    /// occurrence is allowed for it.
    pub(crate) fn record_nonrendered_value(
        &mut self,
        value: ValueId,
    ) -> Result<(), LegacyObservationJournalError> {
        let observation = match self.plan.disposition(value) {
            Some(ValueDisposition::Elided { .. }) => LegacyValueObservation::Elided,
            Some(ValueDisposition::Refused { reason }) => LegacyValueObservation::Refused(*reason),
            Some(ValueDisposition::Bound { .. } | ValueDisposition::Inline { .. }) | None => {
                return Err(LegacyObservationJournalError::RenderedValueRequired(value));
            }
        };
        let slot = self.value_slot_mut(value)?;
        record_same(slot, observation)
            .map_err(|()| LegacyObservationJournalError::ConflictingValue(value))
    }

    /// Record an upstream refusal for a use that therefore has no AST node.
    pub(crate) fn record_refused_use(
        &mut self,
        site: UseSite,
    ) -> Result<(), LegacyObservationJournalError> {
        let observation = match self.plan.use_disposition(site) {
            Some(MachineUseDisposition::Refused(reason)) => LegacyUseObservation::Refused(*reason),
            Some(MachineUseDisposition::Exact(_)) | None => {
                return Err(
                    LegacyObservationJournalError::ExactUseRequiresRenderedOccurrence(site),
                );
            }
        };
        let slot = self.use_slot_mut(site)?;
        record_same(slot, observation)
            .map_err(|()| LegacyObservationJournalError::ConflictingUse(site))
    }

    /// Record an upstream refusal for a write that therefore has no AST node.
    pub(crate) fn record_refused_write(
        &mut self,
        inst: InstId,
    ) -> Result<(), LegacyObservationJournalError> {
        let observation = match self.plan.write_disposition(inst) {
            Some(MachineWriteDisposition::Refused(reason)) => {
                LegacyWriteObservation::Refused(*reason)
            }
            Some(MachineWriteDisposition::Exact(_)) | None => {
                return Err(
                    LegacyObservationJournalError::ExactWriteRequiresRenderedOccurrence(inst),
                );
            }
        };
        let slot = self.write_slot_mut(inst)?;
        record_same(slot, observation)
            .map_err(|()| LegacyObservationJournalError::ConflictingWrite(inst))
    }

    fn normalized_projection(
        &self,
        site: NormalizedOpSite,
    ) -> Result<&NormalizedOpProjection, LegacyObservationJournalError> {
        self.normalized_projections
            .get(site.block.0 as usize)
            .and_then(|rows| rows.get(site.op_idx))
            .ok_or(LegacyObservationJournalError::InvalidNormalizedSite(site))
    }

    fn normalized_output(
        &self,
        site: NormalizedOpSite,
    ) -> Result<crate::normalize::NormalizedOutputProjection, LegacyObservationJournalError> {
        self.normalized_projection(site)?
            .output
            .ok_or(LegacyObservationJournalError::MissingNormalizedOutput(site))
    }

    fn rendered_use_observation(
        &self,
        site: UseSite,
    ) -> Result<LegacyUseObservation, LegacyObservationJournalError> {
        match self.plan.use_disposition(site) {
            Some(MachineUseDisposition::Exact(slice)) => Ok(LegacyUseObservation::Exact(*slice)),
            Some(MachineUseDisposition::Refused(_)) => {
                Err(LegacyObservationJournalError::RefusedRenderedUse(site))
            }
            None => Err(LegacyObservationJournalError::InvalidUse(site)),
        }
    }

    fn rendered_write_observation(
        &self,
        inst: InstId,
    ) -> Result<LegacyWriteObservation, LegacyObservationJournalError> {
        match self.plan.write_disposition(inst) {
            Some(MachineWriteDisposition::Exact(write)) => {
                Ok(LegacyWriteObservation::Exact(*write))
            }
            Some(MachineWriteDisposition::Refused(_)) => {
                Err(LegacyObservationJournalError::RefusedRenderedWrite(inst))
            }
            None => Err(LegacyObservationJournalError::InvalidWrite(inst)),
        }
    }

    pub(crate) fn seal(
        mut self,
        source: &SourceOwnedFunctionFacts,
        ready: &mut EmissionReadyFunction,
    ) -> Result<SealedLegacyObservations, LegacyObservationJournalError> {
        if self.authority != *source.source().authority() {
            return Err(LegacyObservationJournalError::SourceAuthority);
        }
        let mut seal_authority = ObservationSealAuthority::new();
        let function = ready.function_mut_for_observation_seal(&mut seal_authority);
        if !Rc::ptr_eq(&self.symbols, &function.symbols) {
            return Err(LegacyObservationJournalError::SymbolTableMismatch);
        }

        let mut values = self.values.clone();
        let mut uses = self.uses.clone();
        let mut writes = self.writes.clone();
        let targets = &self.targets;
        let value_is_literal = &self.value_is_literal;
        let symbol_bindings = declared_legacy_bindings(function);
        inspect_and_strip_render_observations(
            function,
            targets.len(),
            |id, node| -> Result<(), LegacyObservationJournalError> {
                let target = targets.get(id.index() as usize).copied().ok_or_else(|| {
                    LegacyObservationJournalError::Markers(
                        RenderObservationStripError::OutOfRange {
                            id,
                            expected_count: targets.len(),
                        },
                    )
                })?;
                match target {
                    ObservationTarget::Value(value) => {
                        let observation =
                            classify_value_node(value, node, value_is_literal, &symbol_bindings)?;
                        record_same(&mut values[value.0 as usize], observation)
                            .map_err(|()| LegacyObservationJournalError::ConflictingValue(value))
                    }
                    ObservationTarget::Use { site, observation } => {
                        record_same(&mut uses[site.inst.0 as usize][site.input_idx], observation)
                            .map_err(|()| LegacyObservationJournalError::ConflictingUse(site))
                    }
                    ObservationTarget::Write { inst, observation } => {
                        record_same(&mut writes[inst.0 as usize], observation)
                            .map_err(|()| LegacyObservationJournalError::ConflictingWrite(inst))
                    }
                }
            },
        )
        .map_err(|error| match error {
            RenderObservationInspectError::Markers(error) => {
                LegacyObservationJournalError::Markers(error)
            }
            RenderObservationInspectError::Observer(error) => error,
        })?;

        self.values = values;
        self.uses = uses;
        self.writes = writes;
        Ok(self.into_sealed_observations(source))
    }

    fn final_coverage(&self) -> LegacyObservationCoverage {
        let value_total = self.values.len();
        let value_accounted = self.values.iter().filter(|cell| cell.is_some()).count();
        let value_refused = self
            .values
            .iter()
            .filter(|cell| matches!(cell, Some(LegacyValueObservation::Refused(_))))
            .count();

        let use_total = self.uses.iter().map(|row| row.len()).sum();
        let use_accounted = self
            .uses
            .iter()
            .flat_map(|row| row.iter())
            .filter(|cell| cell.is_some())
            .count();
        let use_refused = self
            .uses
            .iter()
            .flat_map(|row| row.iter())
            .filter(|cell| matches!(cell, Some(LegacyUseObservation::Refused(_))))
            .count();

        let write_total = self
            .write_has_output
            .iter()
            .filter(|has_output| **has_output)
            .count();
        let write_accounted = self
            .writes
            .iter()
            .zip(self.write_has_output.iter())
            .filter(|(cell, has_output)| **has_output && cell.is_some())
            .count();
        let write_refused = self
            .writes
            .iter()
            .zip(self.write_has_output.iter())
            .filter(|(cell, has_output)| {
                **has_output && matches!(cell, Some(LegacyWriteObservation::Refused(_)))
            })
            .count();

        LegacyObservationCoverage {
            values: LegacyObservationDomainCoverage::from_counts(
                value_total,
                value_accounted,
                value_refused,
            ),
            uses: LegacyObservationDomainCoverage::from_counts(
                use_total,
                use_accounted,
                use_refused,
            ),
            writes: LegacyObservationDomainCoverage::from_counts(
                write_total,
                write_accounted,
                write_refused,
            ),
        }
    }

    fn into_sealed_observations(
        self,
        source: &SourceOwnedFunctionFacts,
    ) -> SealedLegacyObservations {
        let coverage = self.final_coverage();
        let snapshot = self.into_snapshot(source);
        SealedLegacyObservations { snapshot, coverage }
    }

    fn into_snapshot(self, source: &SourceOwnedFunctionFacts) -> LegacyAnalysisSnapshot {
        let values = self
            .values
            .into_vec()
            .into_iter()
            .enumerate()
            .map(|(index, observation)| LegacyValueCell {
                value: ValueId(index as u32),
                observation: observation.unwrap_or(LegacyValueObservation::LegacyAbsent),
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let uses = self
            .uses
            .into_vec()
            .into_iter()
            .enumerate()
            .map(|(inst, row)| {
                row.into_vec()
                    .into_iter()
                    .enumerate()
                    .map(|(input_idx, observation)| LegacyUseCell {
                        site: UseSite {
                            inst: InstId(inst as u32),
                            input_idx,
                        },
                        observation: observation.unwrap_or(LegacyUseObservation::LegacyAbsent),
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice()
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let writes = self
            .writes
            .into_vec()
            .into_iter()
            .zip(self.write_has_output)
            .enumerate()
            .map(|(index, (observation, has_output))| {
                has_output.then_some(LegacyWriteCell {
                    inst: InstId(index as u32),
                    observation: observation.unwrap_or(LegacyWriteObservation::LegacyAbsent),
                })
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        LegacyAnalysisSnapshot::new(source, values, uses, writes)
    }

    fn value_slot(
        &self,
        value: ValueId,
    ) -> Result<&Option<LegacyValueObservation>, LegacyObservationJournalError> {
        self.values
            .get(value.0 as usize)
            .ok_or(LegacyObservationJournalError::InvalidValue(value))
    }

    fn value_slot_mut(
        &mut self,
        value: ValueId,
    ) -> Result<&mut Option<LegacyValueObservation>, LegacyObservationJournalError> {
        self.values
            .get_mut(value.0 as usize)
            .ok_or(LegacyObservationJournalError::InvalidValue(value))
    }

    fn use_slot(
        &self,
        site: UseSite,
    ) -> Result<&Option<LegacyUseObservation>, LegacyObservationJournalError> {
        self.uses
            .get(site.inst.0 as usize)
            .and_then(|row| row.get(site.input_idx))
            .ok_or(LegacyObservationJournalError::InvalidUse(site))
    }

    fn use_slot_mut(
        &mut self,
        site: UseSite,
    ) -> Result<&mut Option<LegacyUseObservation>, LegacyObservationJournalError> {
        self.uses
            .get_mut(site.inst.0 as usize)
            .and_then(|row| row.get_mut(site.input_idx))
            .ok_or(LegacyObservationJournalError::InvalidUse(site))
    }

    fn write_slot(
        &self,
        inst: InstId,
    ) -> Result<&Option<LegacyWriteObservation>, LegacyObservationJournalError> {
        let has_output = self
            .write_has_output
            .get(inst.0 as usize)
            .copied()
            .ok_or(LegacyObservationJournalError::InvalidWrite(inst))?;
        if !has_output {
            return Err(LegacyObservationJournalError::OutputlessWrite(inst));
        }
        self.writes
            .get(inst.0 as usize)
            .ok_or(LegacyObservationJournalError::InvalidWrite(inst))
    }

    fn write_slot_mut(
        &mut self,
        inst: InstId,
    ) -> Result<&mut Option<LegacyWriteObservation>, LegacyObservationJournalError> {
        self.write_slot(inst)?;
        Ok(&mut self.writes[inst.0 as usize])
    }
}

fn record_same<T: Copy + Eq>(slot: &mut Option<T>, observation: T) -> Result<(), ()> {
    match slot {
        Some(existing) if *existing != observation => Err(()),
        Some(_) => Ok(()),
        None => {
            *slot = Some(observation);
            Ok(())
        }
    }
}

fn classify_value_node(
    value: ValueId,
    node: RenderObservationNode<'_>,
    value_is_literal: &[bool],
    symbol_bindings: &BTreeMap<SymbolId, LegacyBindingId>,
) -> Result<LegacyValueObservation, LegacyObservationJournalError> {
    let expr = match node {
        RenderObservationNode::Expr(expr) => expr.unobserved(),
        RenderObservationNode::Stmt(stmt) => match stmt.unobserved() {
            CStmt::Decl { name, .. } => return classify_symbol(*name, symbol_bindings),
            CStmt::Expr(expr) | CStmt::Return(Some(expr)) => expr.unobserved(),
            _ => return Ok(LegacyValueObservation::InlineNonLiteral),
        },
    };
    if let CExpr::Var(symbol) = expr {
        return classify_symbol(*symbol, symbol_bindings);
    }
    if let CExpr::Binary {
        op: BinaryOp::Assign,
        left,
        ..
    } = expr
        && let CExpr::Var(symbol) = left.unobserved()
    {
        return classify_symbol(*symbol, symbol_bindings);
    }
    let source_literal = value_is_literal
        .get(value.0 as usize)
        .copied()
        .ok_or(LegacyObservationJournalError::InvalidValue(value))?;
    if source_literal
        && matches!(
            expr,
            CExpr::IntLit(_)
                | CExpr::UIntLit(_)
                | CExpr::FloatLit(_)
                | CExpr::StringLit(_)
                | CExpr::CharLit(_)
        )
    {
        Ok(LegacyValueObservation::InlineConstant)
    } else {
        Ok(LegacyValueObservation::InlineNonLiteral)
    }
}

fn classify_symbol(
    symbol: SymbolId,
    symbol_bindings: &BTreeMap<SymbolId, LegacyBindingId>,
) -> Result<LegacyValueObservation, LegacyObservationJournalError> {
    let binding = symbol_bindings
        .get(&symbol)
        .copied()
        .ok_or(LegacyObservationJournalError::UnownedBindingSymbol(symbol))?;
    Ok(LegacyValueObservation::Bound { binding })
}

fn declared_legacy_bindings(function: &CFunction) -> BTreeMap<SymbolId, LegacyBindingId> {
    let mut bindings = BTreeMap::new();
    let mut mark = |symbol: SymbolId| {
        if !bindings.contains_key(&symbol) {
            let index = u32::try_from(bindings.len())
                .expect("a SymbolId-indexed table cannot exceed the legacy binding domain");
            bindings.insert(symbol, LegacyBindingId(index));
        }
    };
    for param in &function.params {
        mark(param.name);
    }
    for local in &function.locals {
        mark(local.name);
    }
    for stmt in &function.body {
        visit_stmt_declarations(stmt, &mut mark);
    }
    bindings
}

fn visit_stmt_declarations(stmt: &CStmt, visit: &mut impl FnMut(SymbolId)) {
    match stmt.unobserved() {
        CStmt::Decl { name, .. } => visit(*name),
        CStmt::Block(stmts) => {
            for stmt in stmts {
                visit_stmt_declarations(stmt, visit);
            }
        }
        CStmt::If {
            then_body,
            else_body,
            ..
        } => {
            visit_stmt_declarations(then_body, visit);
            if let Some(else_body) = else_body {
                visit_stmt_declarations(else_body, visit);
            }
        }
        CStmt::While { body, .. } | CStmt::DoWhile { body, .. } => {
            visit_stmt_declarations(body, visit);
        }
        CStmt::For { init, body, .. } => {
            if let Some(init) = init {
                visit_stmt_declarations(init, visit);
            }
            visit_stmt_declarations(body, visit);
        }
        CStmt::Switch { cases, default, .. } => {
            for case in cases {
                for stmt in &case.body {
                    visit_stmt_declarations(stmt, visit);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    visit_stmt_declarations(stmt, visit);
                }
            }
        }
        CStmt::Observed { .. } => unreachable!("unobserved statement returned a wrapper"),
        CStmt::Expr(_)
        | CStmt::Return(_)
        | CStmt::Empty
        | CStmt::Break
        | CStmt::Continue
        | CStmt::Goto(_)
        | CStmt::Label(_)
        | CStmt::Comment(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use r2il::{
        AddressSpace, ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef,
        RegisterProjection, RegisterProjectionDisposition, RegisterStorage, Varnode,
    };
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceFunctionInterface, SourceFunctionReturn,
        SsaArtifact,
    };

    use super::*;
    use crate::ast::{CLocal, CType};
    use crate::binding_plan::{BindingId, ValueDisposition};
    use crate::symbol::{SymbolOrigin, SymbolRole};

    fn source_owned() -> SourceOwnedFunctionFacts {
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::constant(1, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x20, 8),
            a: Varnode::unique(0x10, 8),
            b: Varnode::constant(2, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::unique(0x20, 8),
        });
        let mut arch = ArchSpec::new("x86-64");
        arch.add_space(AddressSpace::ram(8));
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("RSP", 0x28, 8));
        arch.add_register(RegisterDef::new("RIP", 0x30, 8));
        arch.register_projections = [(0, 8), (0x28, 8), (0x30, 8)]
            .into_iter()
            .map(|(offset, size)| RegisterProjection {
                written: RegisterStorage { offset, size },
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: RegisterStorage { offset, size },
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: u64::from(size) * 8,
                    },
                },
            })
            .collect();
        let storage = |offset| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = SourceFunctionInterface::new_exact(
            b"observation-journal-test".to_vec(),
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
                reason: "observation journal test".to_string(),
                fallback_comment: None,
            })
            .expect("source-owned finalization")
    }

    fn journal_fixture() -> (
        SourceOwnedFunctionFacts,
        BindingPlan,
        CFunction,
        LegacyObservationJournal,
    ) {
        let source = source_owned();
        let plan = BindingPlan::build_shadow(&source).expect("sealed binding plan");
        let function = CFunction::new("journal", CType::Void);
        let normalized = source.source().function().clone();
        let origins = NormalizationOrigins::for_unchanged(&normalized, source.source());
        let journal = LegacyObservationJournal::new(
            &source,
            &normalized,
            &origins,
            Rc::new(plan.clone()),
            Rc::clone(&function.symbols),
        )
        .expect("authority-bound journal");
        (source, plan, function, journal)
    }

    fn first_bound(plan: &BindingPlan, source: &SourceOwnedFunctionFacts) -> (ValueId, BindingId) {
        source
            .source()
            .graph()
            .values
            .iter()
            .find_map(|value| match plan.disposition(value.id) {
                Some(ValueDisposition::Bound { binding }) => Some((value.id, *binding)),
                _ => None,
            })
            .expect("fixture has a bound value")
    }

    fn first_bound_rendered_input(
        plan: &BindingPlan,
        source: &SourceOwnedFunctionFacts,
    ) -> (ValueId, BindingId, NormalizedOpSite, usize) {
        let graph = source.source().graph();
        graph
            .insts
            .iter()
            .find_map(|inst| {
                let (block_addr, op_idx) = source.source().inst_op_site(inst.id)?;
                let block = graph.block_id_for_addr(block_addr)?;
                inst.inputs
                    .iter()
                    .copied()
                    .enumerate()
                    .find_map(|(input_idx, value)| {
                        let ValueDisposition::Bound { binding } = plan.disposition(value)? else {
                            return None;
                        };
                        matches!(
                            plan.use_disposition(UseSite {
                                inst: inst.id,
                                input_idx,
                            }),
                            Some(MachineUseDisposition::Exact(_))
                        )
                        .then_some((
                            value,
                            *binding,
                            NormalizedOpSite { block, op_idx },
                            input_idx,
                        ))
                    })
            })
            .expect("fixture has an exactly projected bound input")
    }

    fn first_bound_rendered_output(
        plan: &BindingPlan,
        source: &SourceOwnedFunctionFacts,
    ) -> (ValueId, BindingId, InstId, NormalizedOpSite) {
        let graph = source.source().graph();
        graph
            .insts
            .iter()
            .find_map(|inst| {
                let value = inst.output?;
                let ValueDisposition::Bound { binding } = plan.disposition(value)? else {
                    return None;
                };
                if !matches!(
                    plan.write_disposition(inst.id),
                    Some(MachineWriteDisposition::Exact(_))
                ) {
                    return None;
                }
                let (block_addr, op_idx) = source.source().inst_op_site(inst.id)?;
                let block = graph.block_id_for_addr(block_addr)?;
                Some((value, *binding, inst.id, NormalizedOpSite { block, op_idx }))
            })
            .expect("fixture has an exactly projected bound output")
    }

    fn replace_observed_expr_semantic(expr: &mut CExpr, replacement: CExpr) {
        let mut semantic = expr;
        while let CExpr::Observed { expr, .. } = semantic {
            semantic = expr;
        }
        *semantic = replacement;
    }

    fn declare_legacy_symbol(
        function: &CFunction,
        plan: &BindingPlan,
        binding: BindingId,
        name: &str,
    ) -> SymbolId {
        function.symbols.borrow_mut().declare(
            name,
            plan.binding(binding)
                .expect("dense binding")
                .declaration_type()
                .clone(),
            SymbolRole::Carrier,
            SymbolOrigin::default(),
        )
    }

    fn declare_legacy_local(
        function: &mut CFunction,
        plan: &BindingPlan,
        binding: BindingId,
        name: &str,
    ) -> SymbolId {
        let symbol = declare_legacy_symbol(function, plan, binding, name);
        function.locals.push(CLocal {
            ty: plan
                .binding(binding)
                .expect("dense binding")
                .declaration_type()
                .clone(),
            name: symbol,
            stack_offset: None,
        });
        symbol
    }

    #[test]
    fn normalized_issuance_is_idempotent_and_raw_bound_recording_is_rejected() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "old_value");
        let first = journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("first projected occurrence");
        let second = journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("second projected occurrence");
        function.body = vec![CStmt::Expr(first), CStmt::Expr(second)];
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("same projected cell is idempotent");
        assert_eq!(
            sealed.snapshot().value_observation(value),
            Some(LegacyValueObservation::Bound {
                binding: LegacyBindingId(0),
            })
        );

        let (_source, plan, _function, mut journal) = journal_fixture();
        let (value, _) = first_bound(&plan, &_source);
        assert_eq!(
            journal.record_nonrendered_value(value),
            Err(LegacyObservationJournalError::RenderedValueRequired(value))
        );
    }

    #[test]
    fn normalized_output_expression_is_idempotent_and_reports_dense_coverage() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, inst, site) = first_bound_rendered_output(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "inline_output");
        let first = journal
            .observe_normalized_output_expr(site, CExpr::Var(symbol))
            .expect("first output expression");
        let second = journal
            .observe_normalized_output_expr(site, CExpr::Var(symbol))
            .expect("second output expression");
        function.body = vec![CStmt::Expr(first), CStmt::Expr(second)];

        let expected_write = match plan.write_disposition(inst) {
            Some(MachineWriteDisposition::Exact(write)) => LegacyWriteObservation::Exact(*write),
            other => panic!("expected exact write, got {other:?}"),
        };
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("identical output decisions are idempotent");

        assert_eq!(
            sealed.snapshot().value_observation(value),
            Some(LegacyValueObservation::Bound {
                binding: LegacyBindingId(0),
            })
        );
        assert_eq!(
            sealed.snapshot().write_observation(inst),
            Some(expected_write)
        );

        let coverage = sealed.coverage();
        let graph = source.source().graph();
        assert_eq!(coverage.values.total, graph.values.len());
        assert_eq!(
            coverage.uses.total,
            graph
                .insts
                .iter()
                .map(|inst| inst.inputs.len())
                .sum::<usize>()
        );
        assert_eq!(
            coverage.writes.total,
            graph
                .insts
                .iter()
                .filter(|inst| inst.output.is_some())
                .count()
        );
        assert_eq!(coverage.values.accounted, 1);
        assert_eq!(coverage.uses.accounted, 0);
        assert_eq!(coverage.writes.accounted, 1);
        assert_eq!(coverage.values.refused, 0);
        assert_eq!(coverage.uses.refused, 0);
        assert_eq!(coverage.writes.refused, 0);
        assert!(coverage.equations_hold());
    }

    #[test]
    fn conflicting_output_expression_decisions_are_transactional() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, _inst, site) = first_bound_rendered_output(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "conflicting_output");
        let bound = journal
            .observe_normalized_output_expr(site, CExpr::Var(symbol))
            .expect("bound output expression");
        let inline = journal
            .observe_normalized_output_expr(site, CExpr::IntLit(7))
            .expect("inline output expression");
        function.body = vec![CStmt::Expr(bound), CStmt::Expr(inline)];

        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let unchanged = ready.function_for_marker_test().clone();
        assert_eq!(
            journal.seal(&source, &mut ready),
            Err(LegacyObservationJournalError::ConflictingValue(value))
        );
        assert_eq!(ready.function_for_marker_test(), &unchanged);
    }

    #[test]
    fn final_rewritten_node_drives_value_classification() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_symbol(&function, &plan, binding, "rewritten_value");
        let marked = journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("value marker");
        function.body = vec![CStmt::Return(Some(marked))];
        let CStmt::Return(Some(expr)) = &mut function.body[0] else {
            panic!("marked return expression")
        };
        replace_observed_expr_semantic(expr, CExpr::IntLit(7));

        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("sealed final observations");
        assert_eq!(
            sealed.snapshot().value_observation(value),
            Some(LegacyValueObservation::InlineNonLiteral)
        );
        assert!(!matches!(
            &ready.function().body[0],
            CStmt::Return(Some(CExpr::Observed { .. }))
        ));
    }

    #[test]
    fn invalid_or_duplicate_markers_leave_ast_unchanged() {
        let (source, plan, mut duplicate_function, mut duplicate_journal) = journal_fixture();
        let (_value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_symbol(&duplicate_function, &plan, binding, "duplicate_value");
        let marked = duplicate_journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("value marker");
        duplicate_function.body = vec![CStmt::Expr(marked.clone()), CStmt::Expr(marked)];
        let mut duplicate_ready =
            crate::codegen::prepare_function_for_emission(&duplicate_function);
        let unchanged = duplicate_ready.function_for_marker_test().clone();
        assert!(matches!(
            duplicate_journal.seal(&source, &mut duplicate_ready),
            Err(LegacyObservationJournalError::Markers(
                RenderObservationStripError::Duplicate { .. }
            ))
        ));
        assert_eq!(duplicate_ready.function_for_marker_test(), &unchanged);

        let (source, plan, mut range_function, mut range_journal) = journal_fixture();
        let (_value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_symbol(&range_function, &plan, binding, "range_value");
        let mut marked = range_journal
            .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
            .expect("value marker");
        let CExpr::Observed { id, .. } = &mut marked else {
            panic!("marked expression")
        };
        *id = test_render_observation_id(2);
        range_function.body = vec![CStmt::Expr(marked)];
        let mut range_ready = crate::codegen::prepare_function_for_emission(&range_function);
        let unchanged = range_ready.function_for_marker_test().clone();
        assert!(matches!(
            range_journal.seal(&source, &mut range_ready),
            Err(LegacyObservationJournalError::Markers(
                RenderObservationStripError::OutOfRange { .. }
            ))
        ));
        assert_eq!(range_ready.function_for_marker_test(), &unchanged);
    }

    #[test]
    fn journal_construction_does_not_allocate_candidate_symbols() {
        let (source, plan, function, _journal) = journal_fixture();
        let (_, binding) = first_bound(&plan, &source);
        let requested = plan
            .binding(binding)
            .and_then(|binding| binding.presentation_name_hint())
            .unwrap_or("candidate_name");
        let symbol = declare_legacy_symbol(&function, &plan, binding, requested);
        assert_eq!(function.symbols.borrow().name(symbol), requested);
    }

    #[test]
    fn bound_marker_requires_and_observes_a_surviving_declaration() {
        let (source, plan, mut function, mut journal) = journal_fixture();
        let (value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_local(&mut function, &plan, binding, "surviving_value");
        function.body = vec![CStmt::Expr(
            journal
                .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
                .expect("value marker"),
        )];
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let sealed = journal
            .seal(&source, &mut ready)
            .expect("declared binding is authoritative");
        assert_eq!(
            sealed.snapshot().value_observation(value),
            Some(LegacyValueObservation::Bound {
                binding: LegacyBindingId(0),
            })
        );

        let (source, plan, mut function, mut journal) = journal_fixture();
        let (_value, binding, site, input_idx) = first_bound_rendered_input(&plan, &source);
        let symbol = declare_legacy_symbol(&function, &plan, binding, "undeclared_value");
        function.body = vec![CStmt::Expr(
            journal
                .observe_normalized_input_expr(site, input_idx, CExpr::Var(symbol))
                .expect("value marker"),
        )];
        let mut ready = crate::codegen::prepare_function_for_emission(&function);
        let unchanged = ready.function_for_marker_test().clone();
        assert_eq!(
            journal.seal(&source, &mut ready),
            Err(LegacyObservationJournalError::UnownedBindingSymbol(symbol))
        );
        assert_eq!(ready.function_for_marker_test(), &unchanged);
    }
}
