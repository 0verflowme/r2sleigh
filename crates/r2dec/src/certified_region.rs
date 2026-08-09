//! Proof-bound control-region foundations.
//!
//! The first supported shape is one canonical block. Every source instruction
//! and obligation is carried by stable ID. Value expressions bind to the
//! partial semantic-C layer. Admitted expressions, plain memory, and terminal
//! controls receive exact mappings; unsupported effects and control become
//! explicit residual mappings rather than disappearing.

use std::collections::{BTreeMap, BTreeSet};

use r2cert::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedArtifactOrigin, CertifiedCallArgumentOrigin,
    CertifiedConditionalControl, CertifiedControlTruthiness, CertifiedDirectCall,
    CertifiedDirectControl, CertifiedMachineFunction, CertifiedMachineProjection,
    CertifiedMemoryStatement, CertifiedReturnControl, CertifiedSourceTopology,
    CertifiedSwitchControl, EffectDisposition, ObligationLedger,
};
use r2ssa::{
    CanonicalInstructionId, SemanticInstructionState, SemanticObligationId,
    SemanticObligationInventory, SemanticObligationKind,
};
use serde::Serialize;

use crate::semantic_c::{
    SEMANTIC_C_SCHEMA_VERSION, SemanticCCallArgumentValue, SemanticCDirectCall, SemanticCError,
    SemanticCExpressionLayer, SemanticCIdentityScope, SemanticCReturn, SemanticCScope,
    semantic_call_from_control, semantic_return_from_control,
};

pub const CERTIFIED_REGION_SCHEMA_VERSION: u32 = 6;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SingleBlockAccountingScope {
    SourceAccountingWithCertifiedSemanticEntitiesAndOpenBlockExit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum RegionResidualReason {
    MemoryEffectRequiresCertifiedStatement,
    CallBoundaryRequiresCertifiedCall,
    ReturnRequiresCertifiedControl,
    ControlRequiresCertifiedRegion,
    TrapOrOrderingRequiresCertifiedEffect,
    LoopStateRequiresCertifiedStructuring,
    UnsupportedSourceSemantics,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum RegionObligationDisposition {
    AbsorbedIntoExpression { producer: CanonicalInstructionId },
    AbsorbedIntoStatement { producer: CanonicalInstructionId },
    AbsorbedIntoCall { producer: CanonicalInstructionId },
    AbsorbedIntoControl { producer: CanonicalInstructionId },
    AbsorbedIntoReturn { producer: CanonicalInstructionId },
    Residualized { reason: RegionResidualReason },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RegionObligationMapping {
    obligation: SemanticObligationId,
    disposition: RegionObligationDisposition,
}

impl RegionObligationMapping {
    pub const fn obligation(&self) -> SemanticObligationId {
        self.obligation
    }

    pub const fn disposition(&self) -> &RegionObligationDisposition {
        &self.disposition
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedRegionInstruction {
    source: CanonicalInstructionId,
    state: SemanticInstructionState,
    expression_producer: Option<CanonicalInstructionId>,
    statement_producer: Option<CanonicalInstructionId>,
    call_producer: Option<CanonicalInstructionId>,
    control_producer: Option<CanonicalInstructionId>,
    return_producer: Option<CanonicalInstructionId>,
}

impl CertifiedRegionInstruction {
    pub const fn source(&self) -> CanonicalInstructionId {
        self.source
    }

    pub const fn state(&self) -> SemanticInstructionState {
        self.state
    }

    pub const fn expression_producer(&self) -> Option<CanonicalInstructionId> {
        self.expression_producer
    }

    pub const fn statement_producer(&self) -> Option<CanonicalInstructionId> {
        self.statement_producer
    }

    pub const fn call_producer(&self) -> Option<CanonicalInstructionId> {
        self.call_producer
    }

    pub const fn control_producer(&self) -> Option<CanonicalInstructionId> {
        self.control_producer
    }

    pub const fn return_producer(&self) -> Option<CanonicalInstructionId> {
        self.return_producer
    }
}

/// Exact source accounting for one canonical basic block.
///
/// This envelope accounts for admitted terminal-control evidence but is not
/// itself a structured control region. Residual and absorbed mappings describe
/// local source obligations only and grant no execution or rendering
/// permission. Dispositions use stable producer IDs only; the artifact-local
/// expression root is resolved inside the owned layer and is never serialized
/// as proof evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedSingleBlockAccounting {
    schema_version: u32,
    scope: SingleBlockAccountingScope,
    identity_scope: SemanticCIdentityScope,
    origin: CertifiedArtifactOrigin,
    block_addr: u64,
    source: SemanticObligationInventory,
    topology: CertifiedSourceTopology,
    ledger: ObligationLedger,
    expression_layer: SemanticCExpressionLayer,
    memory_statements: Box<[CertifiedMemoryStatement]>,
    direct_calls: Box<[CertifiedDirectCall]>,
    semantic_calls: Box<[SemanticCDirectCall]>,
    direct_controls: Box<[CertifiedDirectControl]>,
    conditional_controls: Box<[CertifiedConditionalControl]>,
    switch_controls: Box<[CertifiedSwitchControl]>,
    return_controls: Box<[CertifiedReturnControl]>,
    semantic_returns: Box<[SemanticCReturn]>,
    instructions: Box<[CertifiedRegionInstruction]>,
    mappings: Box<[RegionObligationMapping]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegionBuildError {
    SemanticC(SemanticCError),
    EmptySource,
    MultipleBlocks(BTreeSet<u64>),
    MissingBlock(u64),
    MissingSourceInstruction(CanonicalInstructionId),
    MissingExpression(CanonicalInstructionId),
    ExpressionObligationMismatch(SemanticObligationId),
    StatementObligationMismatch(SemanticObligationId),
    CallObligationMismatch(SemanticObligationId),
    ControlObligationMismatch(SemanticObligationId),
    ReturnObligationMismatch(SemanticObligationId),
    AmbiguousControl(CanonicalInstructionId),
}

impl std::fmt::Display for RegionBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "certified region construction failed: {self:?}")
    }
}

impl std::error::Error for RegionBuildError {}

impl From<SemanticCError> for RegionBuildError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

fn only_source_block(topology: &CertifiedSourceTopology) -> Result<u64, RegionBuildError> {
    let [block] = topology.blocks() else {
        return if topology.blocks().is_empty() {
            Err(RegionBuildError::EmptySource)
        } else {
            Err(RegionBuildError::MultipleBlocks(
                topology.blocks().iter().map(|block| block.addr()).collect(),
            ))
        };
    };
    Ok(block.addr())
}

fn require_source_block(
    topology: &CertifiedSourceTopology,
    block_addr: u64,
) -> Result<&r2cert::CertifiedSourceBlock, RegionBuildError> {
    topology
        .block(block_addr)
        .ok_or(RegionBuildError::MissingBlock(block_addr))
}

struct CertifiedBlockParts {
    expression_layer: SemanticCExpressionLayer,
    memory_statements: Vec<CertifiedMemoryStatement>,
    direct_calls: Vec<CertifiedDirectCall>,
    direct_controls: Vec<CertifiedDirectControl>,
    conditional_controls: Vec<CertifiedConditionalControl>,
    switch_controls: Vec<CertifiedSwitchControl>,
    return_controls: Vec<CertifiedReturnControl>,
}

impl CertifiedSingleBlockAccounting {
    pub fn from_certified(certified: &CertifiedMachineFunction) -> Result<Self, RegionBuildError> {
        let block_addr = only_source_block(certified.topology())?;
        let expression_layer = SemanticCExpressionLayer::from_certified(certified)?;
        Self::from_parts(
            certified.origin(),
            certified.source(),
            certified.topology(),
            certified.ledger(),
            block_addr,
            CertifiedBlockParts {
                expression_layer,
                memory_statements: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.memory_statement_for_producer(*producer).cloned()
                    })
                    .collect(),
                direct_calls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| certified.direct_call_for_producer(*producer).cloned())
                    .collect(),
                direct_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.direct_control_for_producer(*producer).cloned()
                    })
                    .collect(),
                conditional_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified
                            .conditional_control_for_producer(*producer)
                            .cloned()
                    })
                    .collect(),
                switch_controls: certified
                    .switch_control_for_block(block_addr)
                    .cloned()
                    .into_iter()
                    .collect(),
                return_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.return_control_for_producer(*producer).cloned()
                    })
                    .collect(),
            },
        )
    }

    pub fn from_projection(
        certified: &CertifiedMachineProjection,
    ) -> Result<Self, RegionBuildError> {
        let block_addr = only_source_block(certified.topology())?;
        let expression_layer = SemanticCExpressionLayer::from_projection(certified)?;
        Self::from_parts(
            certified.origin(),
            certified.source(),
            certified.topology(),
            certified.ledger(),
            block_addr,
            CertifiedBlockParts {
                expression_layer,
                memory_statements: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.memory_statement_for_producer(*producer).cloned()
                    })
                    .collect(),
                direct_calls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| certified.direct_call_for_producer(*producer).cloned())
                    .collect(),
                direct_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.direct_control_for_producer(*producer).cloned()
                    })
                    .collect(),
                conditional_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified
                            .conditional_control_for_producer(*producer)
                            .cloned()
                    })
                    .collect(),
                switch_controls: certified
                    .switch_control_for_block(block_addr)
                    .cloned()
                    .into_iter()
                    .collect(),
                return_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.return_control_for_producer(*producer).cloned()
                    })
                    .collect(),
            },
        )
    }

    /// Account one selected block in a multi-block certified artifact.
    ///
    /// The expected instruction and obligation subset is always derived from
    /// the retained full-function topology and inventory.
    pub fn from_certified_block(
        certified: &CertifiedMachineFunction,
        block_addr: u64,
    ) -> Result<Self, RegionBuildError> {
        require_source_block(certified.topology(), block_addr)?;
        let expression_layer = SemanticCExpressionLayer::from_certified(certified)?;
        Self::from_parts(
            certified.origin(),
            certified.source(),
            certified.topology(),
            certified.ledger(),
            block_addr,
            CertifiedBlockParts {
                expression_layer,
                memory_statements: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.memory_statement_for_producer(*producer).cloned()
                    })
                    .collect(),
                direct_calls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| certified.direct_call_for_producer(*producer).cloned())
                    .collect(),
                direct_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.direct_control_for_producer(*producer).cloned()
                    })
                    .collect(),
                conditional_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified
                            .conditional_control_for_producer(*producer)
                            .cloned()
                    })
                    .collect(),
                switch_controls: certified
                    .switch_control_for_block(block_addr)
                    .cloned()
                    .into_iter()
                    .collect(),
                return_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.return_control_for_producer(*producer).cloned()
                    })
                    .collect(),
            },
        )
    }

    pub fn from_projection_block(
        certified: &CertifiedMachineProjection,
        block_addr: u64,
    ) -> Result<Self, RegionBuildError> {
        require_source_block(certified.topology(), block_addr)?;
        let expression_layer = SemanticCExpressionLayer::from_projection(certified)?;
        Self::from_parts(
            certified.origin(),
            certified.source(),
            certified.topology(),
            certified.ledger(),
            block_addr,
            CertifiedBlockParts {
                expression_layer,
                memory_statements: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.memory_statement_for_producer(*producer).cloned()
                    })
                    .collect(),
                direct_calls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| certified.direct_call_for_producer(*producer).cloned())
                    .collect(),
                direct_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.direct_control_for_producer(*producer).cloned()
                    })
                    .collect(),
                conditional_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified
                            .conditional_control_for_producer(*producer)
                            .cloned()
                    })
                    .collect(),
                switch_controls: certified
                    .switch_control_for_block(block_addr)
                    .cloned()
                    .into_iter()
                    .collect(),
                return_controls: certified
                    .topology()
                    .block(block_addr)
                    .into_iter()
                    .flat_map(|block| block.instructions())
                    .filter_map(|producer| {
                        certified.return_control_for_producer(*producer).cloned()
                    })
                    .collect(),
            },
        )
    }

    fn from_parts(
        origin: &CertifiedArtifactOrigin,
        source: &SemanticObligationInventory,
        topology: &CertifiedSourceTopology,
        ledger: &ObligationLedger,
        block_addr: u64,
        parts: CertifiedBlockParts,
    ) -> Result<Self, RegionBuildError> {
        let CertifiedBlockParts {
            expression_layer,
            memory_statements,
            direct_calls,
            direct_controls,
            conditional_controls,
            switch_controls,
            return_controls,
        } = parts;
        let source_block = require_source_block(topology, block_addr)?;
        let semantic_returns = return_controls
            .iter()
            .map(|control| semantic_return_from_control(control, &expression_layer))
            .collect::<Result<Vec<_>, _>>()?;
        let semantic_calls = direct_calls
            .iter()
            .map(|call| semantic_call_from_control(call, &expression_layer))
            .collect::<Result<Vec<_>, _>>()?;
        let expression_entities = expression_layer
            .entities()
            .iter()
            .map(|entity| (entity.producer(), entity))
            .collect::<BTreeMap<_, _>>();
        let statement_entities = memory_statements
            .iter()
            .map(|statement| (statement.producer(), statement))
            .collect::<BTreeMap<_, _>>();
        let direct_call_entities = direct_calls
            .iter()
            .map(|call| (call.producer(), call))
            .collect::<BTreeMap<_, _>>();
        let direct_control_entities = direct_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let conditional_control_entities = conditional_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let switch_control_entities = switch_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let return_control_entities = return_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        if let Some(producer) = direct_control_entities
            .keys()
            .find(|producer| {
                conditional_control_entities.contains_key(producer)
                    || switch_control_entities.contains_key(producer)
            })
            .or_else(|| {
                conditional_control_entities
                    .keys()
                    .find(|producer| switch_control_entities.contains_key(producer))
            })
        {
            return Err(RegionBuildError::AmbiguousControl(*producer));
        }
        let mut instructions = Vec::with_capacity(source.instructions().len());
        let mut mappings = Vec::with_capacity(source.obligations().len());

        for id in source_block.instructions() {
            let disposition = source
                .instructions()
                .get(id)
                .ok_or(RegionBuildError::MissingSourceInstruction(*id))?;
            let expression_producer = expression_entities.get(id).map(|entity| entity.producer());
            let statement_producer = statement_entities
                .get(id)
                .map(|statement| statement.producer());
            let call_producer = direct_call_entities.get(id).map(|call| call.producer());
            let control_producer = direct_control_entities
                .get(id)
                .map(|control| control.producer())
                .or_else(|| {
                    conditional_control_entities
                        .get(id)
                        .map(|control| control.producer())
                })
                .or_else(|| {
                    switch_control_entities
                        .get(id)
                        .map(|control| control.producer())
                });
            let return_producer = return_control_entities
                .get(id)
                .map(|control| control.producer());
            instructions.push(CertifiedRegionInstruction {
                source: *id,
                state: disposition.state,
                expression_producer,
                statement_producer,
                call_producer,
                control_producer,
                return_producer,
            });
            for obligation in &disposition.obligations {
                let mapping = if obligation.kind == SemanticObligationKind::LiveValueProducer {
                    if let Some(entity) = expression_entities.get(id) {
                        if !entity.source_obligations().contains(obligation) {
                            return Err(RegionBuildError::ExpressionObligationMismatch(
                                *obligation,
                            ));
                        }
                        RegionObligationDisposition::AbsorbedIntoExpression { producer: *id }
                    } else if expression_layer.open_obligations().contains(obligation) {
                        RegionObligationDisposition::Residualized {
                            reason: residual_reason(obligation.kind),
                        }
                    } else {
                        return Err(RegionBuildError::MissingExpression(*id));
                    }
                } else if matches!(
                    obligation.kind,
                    SemanticObligationKind::ObservableMemoryRead
                        | SemanticObligationKind::ObservableMemoryWrite
                ) && statement_entities
                    .get(id)
                    .is_some_and(|statement| statement.source_obligations().contains(obligation))
                {
                    let [effect] = ledger.effects(*obligation) else {
                        return Err(RegionBuildError::StatementObligationMismatch(*obligation));
                    };
                    if effect.disposition()
                        != &(EffectDisposition::AbsorbedIntoStatement { producer: *id })
                    {
                        return Err(RegionBuildError::StatementObligationMismatch(*obligation));
                    }
                    RegionObligationDisposition::AbsorbedIntoStatement { producer: *id }
                } else if matches!(
                    obligation.kind,
                    SemanticObligationKind::Call | SemanticObligationKind::CallArgument
                ) && direct_call_entities
                    .get(id)
                    .is_some_and(|call| call.source_obligations().contains(obligation))
                {
                    let [effect] = ledger.effects(*obligation) else {
                        return Err(RegionBuildError::CallObligationMismatch(*obligation));
                    };
                    if effect.disposition()
                        != &(EffectDisposition::AbsorbedIntoCall { producer: *id })
                        || effect.direct_call_evidence() != direct_call_entities.get(id).copied()
                    {
                        return Err(RegionBuildError::CallObligationMismatch(*obligation));
                    }
                    RegionObligationDisposition::AbsorbedIntoCall { producer: *id }
                } else if matches!(
                    obligation.kind,
                    SemanticObligationKind::ControlPredicate
                        | SemanticObligationKind::ControlTransfer
                ) && (direct_control_entities
                    .get(id)
                    .is_some_and(|control| control.source_obligation() == *obligation)
                    || conditional_control_entities
                        .get(id)
                        .is_some_and(|control| control.source_obligations().contains(obligation))
                    || switch_control_entities
                        .get(id)
                        .is_some_and(|control| control.source_obligation() == *obligation))
                {
                    let [effect] = ledger.effects(*obligation) else {
                        return Err(RegionBuildError::ControlObligationMismatch(*obligation));
                    };
                    if effect.disposition()
                        != &(EffectDisposition::AbsorbedIntoControl { producer: *id })
                        || switch_control_entities.contains_key(id)
                            && effect.switch_control_evidence()
                                != switch_control_entities.get(id).copied()
                    {
                        return Err(RegionBuildError::ControlObligationMismatch(*obligation));
                    }
                    RegionObligationDisposition::AbsorbedIntoControl { producer: *id }
                } else if matches!(
                    obligation.kind,
                    SemanticObligationKind::Return | SemanticObligationKind::ReturnValue
                ) && return_control_entities
                    .get(id)
                    .is_some_and(|control| control.source_obligations().contains(obligation))
                {
                    let [effect] = ledger.effects(*obligation) else {
                        return Err(RegionBuildError::ReturnObligationMismatch(*obligation));
                    };
                    if effect.disposition()
                        != &(EffectDisposition::AbsorbedIntoReturn { producer: *id })
                    {
                        return Err(RegionBuildError::ReturnObligationMismatch(*obligation));
                    }
                    RegionObligationDisposition::AbsorbedIntoReturn { producer: *id }
                } else {
                    RegionObligationDisposition::Residualized {
                        reason: residual_reason(obligation.kind),
                    }
                };
                mappings.push(RegionObligationMapping {
                    obligation: *obligation,
                    disposition: mapping,
                });
            }
        }

        Ok(Self {
			schema_version: CERTIFIED_REGION_SCHEMA_VERSION,
			scope: SingleBlockAccountingScope::SourceAccountingWithCertifiedSemanticEntitiesAndOpenBlockExit,
			identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
			origin: origin.clone(),
            block_addr,
            source: source.clone(),
            topology: topology.clone(),
            ledger: ledger.clone(),
            expression_layer,
            memory_statements: memory_statements.into_boxed_slice(),
            direct_calls: direct_calls.into_boxed_slice(),
            semantic_calls: semantic_calls.into_boxed_slice(),
            direct_controls: direct_controls.into_boxed_slice(),
            conditional_controls: conditional_controls.into_boxed_slice(),
            switch_controls: switch_controls.into_boxed_slice(),
            return_controls: return_controls.into_boxed_slice(),
            semantic_returns: semantic_returns.into_boxed_slice(),
            instructions: instructions.into_boxed_slice(),
            mappings: mappings.into_boxed_slice(),
        })
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> SingleBlockAccountingScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn block_addr(&self) -> u64 {
        self.block_addr
    }

    pub const fn topology(&self) -> &CertifiedSourceTopology {
        &self.topology
    }

    pub const fn ledger(&self) -> &ObligationLedger {
        &self.ledger
    }

    pub const fn expression_layer(&self) -> &SemanticCExpressionLayer {
        &self.expression_layer
    }

    pub const fn memory_statements(&self) -> &[CertifiedMemoryStatement] {
        &self.memory_statements
    }

    pub fn memory_statement_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedMemoryStatement> {
        self.memory_statements
            .iter()
            .find(|statement| statement.producer() == producer)
    }

    pub const fn direct_calls(&self) -> &[CertifiedDirectCall] {
        &self.direct_calls
    }

    pub const fn semantic_calls(&self) -> &[SemanticCDirectCall] {
        &self.semantic_calls
    }

    pub fn direct_call_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedDirectCall> {
        self.direct_calls
            .iter()
            .find(|call| call.producer() == producer)
    }

    pub const fn direct_controls(&self) -> &[CertifiedDirectControl] {
        &self.direct_controls
    }

    pub fn direct_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedDirectControl> {
        self.direct_controls
            .iter()
            .find(|control| control.producer() == producer)
    }

    pub const fn conditional_controls(&self) -> &[CertifiedConditionalControl] {
        &self.conditional_controls
    }

    pub fn conditional_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedConditionalControl> {
        self.conditional_controls
            .iter()
            .find(|control| control.producer() == producer)
    }

    pub const fn switch_controls(&self) -> &[CertifiedSwitchControl] {
        &self.switch_controls
    }

    pub fn switch_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedSwitchControl> {
        self.switch_controls
            .iter()
            .find(|control| control.producer() == producer)
    }

    pub const fn return_controls(&self) -> &[CertifiedReturnControl] {
        &self.return_controls
    }

    pub const fn semantic_returns(&self) -> &[SemanticCReturn] {
        &self.semantic_returns
    }

    pub fn return_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedReturnControl> {
        self.return_controls
            .iter()
            .find(|control| control.producer() == producer)
    }

    pub fn source_block(&self) -> Option<&r2cert::CertifiedSourceBlock> {
        self.topology.block(self.block_addr)
    }

    pub const fn instructions(&self) -> &[CertifiedRegionInstruction] {
        &self.instructions
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub fn audit(&self) -> RegionAuditReport {
        let source_block = self.topology.block(self.block_addr);
        let expected_instructions = source_block
            .into_iter()
            .flat_map(|block| block.instructions().iter().copied())
            .collect::<BTreeSet<_>>();
        let expected_obligations = expected_instructions
            .iter()
            .filter_map(|id| self.source.instructions().get(id))
            .flat_map(|instruction| instruction.obligations.iter().copied())
            .collect::<BTreeSet<_>>();
        let instruction_counts = counts(
            self.instructions
                .iter()
                .map(|instruction| instruction.source),
        );
        let obligation_counts = counts(self.mappings.iter().map(|mapping| mapping.obligation));
        let (missing_instructions, duplicate_instructions, unexpected_instructions) =
            reconcile(expected_instructions.iter().copied(), &instruction_counts);
        let (missing_obligations, duplicate_obligations, unexpected_obligations) =
            reconcile(expected_obligations.iter().copied(), &obligation_counts);
        let mut invalid = Vec::new();
        let expression_entities = self
            .expression_layer
            .entities()
            .iter()
            .map(|entity| (entity.producer(), entity))
            .collect::<BTreeMap<_, _>>();
        let expected_expression_producers = self
            .source
            .instructions()
            .iter()
            .filter_map(|(id, instruction)| {
                instruction
                    .obligations
                    .iter()
                    .any(|obligation| {
                        obligation.kind == SemanticObligationKind::LiveValueProducer
                            && !self
                                .expression_layer
                                .open_obligations()
                                .contains(obligation)
                    })
                    .then_some(*id)
            })
            .collect::<BTreeSet<_>>();
        let actual_expression_producers =
            expression_entities.keys().copied().collect::<BTreeSet<_>>();
        let expected_expression_obligations = self
            .source
            .obligations()
            .keys()
            .copied()
            .filter(|id| {
                id.kind == SemanticObligationKind::LiveValueProducer
                    && !self.expression_layer.open_obligations().contains(id)
            })
            .collect::<BTreeSet<_>>();
        let expected_block_expression_obligations = expected_obligations
            .iter()
            .copied()
            .filter(|id| {
                id.kind == SemanticObligationKind::LiveValueProducer
                    && !self.expression_layer.open_obligations().contains(id)
            })
            .collect::<BTreeSet<_>>();
        let entity_expression_obligations = self
            .expression_layer
            .entities()
            .iter()
            .flat_map(|entity| entity.source_obligations().iter().copied())
            .collect::<BTreeSet<_>>();
        let mapped_expression_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoExpression { .. }
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let statement_entities = self
            .memory_statements
            .iter()
            .map(|statement| (statement.producer(), statement))
            .collect::<BTreeMap<_, _>>();
        let statement_obligations = self
            .memory_statements
            .iter()
            .flat_map(|statement| statement.source_obligations().iter().copied())
            .collect::<BTreeSet<_>>();
        let mapped_statement_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoStatement { .. }
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let direct_call_entities = self
            .direct_calls
            .iter()
            .map(|call| (call.producer(), call))
            .collect::<BTreeMap<_, _>>();
        let semantic_call_entities = self
            .semantic_calls
            .iter()
            .map(|call| (call.producer(), call))
            .collect::<BTreeMap<_, _>>();
        let call_obligations = self
            .direct_calls
            .iter()
            .flat_map(CertifiedDirectCall::source_obligations)
            .collect::<BTreeSet<_>>();
        let mapped_call_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoCall { .. }
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let direct_control_entities = self
            .direct_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let conditional_control_entities = self
            .conditional_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let switch_control_entities = self
            .switch_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let return_control_entities = self
            .return_controls
            .iter()
            .map(|control| (control.producer(), control))
            .collect::<BTreeMap<_, _>>();
        let semantic_return_entities = self
            .semantic_returns
            .iter()
            .map(|returned| (returned.producer(), returned))
            .collect::<BTreeMap<_, _>>();
        let direct_control_obligations = self
            .direct_controls
            .iter()
            .map(CertifiedDirectControl::source_obligation)
            .collect::<BTreeSet<_>>();
        let conditional_control_obligations = self
            .conditional_controls
            .iter()
            .flat_map(CertifiedConditionalControl::source_obligations)
            .collect::<BTreeSet<_>>();
        let switch_control_obligations = self
            .switch_controls
            .iter()
            .map(CertifiedSwitchControl::source_obligation)
            .collect::<BTreeSet<_>>();
        let control_obligations = direct_control_obligations
            .union(&conditional_control_obligations)
            .copied()
            .chain(switch_control_obligations.iter().copied())
            .collect::<BTreeSet<_>>();
        let mapped_control_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoControl { .. }
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let return_obligations = self
            .return_controls
            .iter()
            .flat_map(CertifiedReturnControl::source_obligations)
            .collect::<BTreeSet<_>>();
        let mapped_return_obligations = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoReturn { .. }
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();

        if self.schema_version != CERTIFIED_REGION_SCHEMA_VERSION {
            invalid.push("region schema version mismatch".to_string());
        }
        if !self.source.is_complete() {
            invalid.push("retained source obligation inventory is incomplete".to_string());
        }
        if self.scope
			!= SingleBlockAccountingScope::SourceAccountingWithCertifiedSemanticEntitiesAndOpenBlockExit
		{
			invalid.push("single-block accounting scope mismatch".to_string());
		}
        if self.identity_scope != SemanticCIdentityScope::ArtifactLocalHandles {
            invalid.push("region identity scope mismatch".to_string());
        }
        if !self
            .origin
            .matches_retained_source(&self.source, &self.topology)
        {
            invalid.push("region artifact origin does not match retained source".to_string());
        }
        if self.topology.schema_version() != CERTIFICATION_SCHEMA_VERSION
            || source_block.is_none_or(|block| {
                block.instructions()
                    != self
                        .instructions
                        .iter()
                        .map(|instruction| instruction.source)
                        .collect::<Vec<_>>()
                        .as_slice()
            })
        {
            invalid.push("region instructions do not match retained source topology".to_string());
        }
        if self.expression_layer.entities().len() != expression_entities.len()
            || actual_expression_producers != expected_expression_producers
        {
            invalid.push(
                "semantic expression producer set does not match retained source".to_string(),
            );
        }
        if entity_expression_obligations != expected_expression_obligations
            || mapped_expression_obligations != expected_block_expression_obligations
        {
            invalid.push(
                "semantic expression obligations do not exactly match retained source".to_string(),
            );
        }
        if statement_entities.len() != self.memory_statements.len()
            || statement_obligations != mapped_statement_obligations
            || !statement_obligations.is_subset(&expected_obligations)
        {
            invalid.push(
                "certified memory statements do not exactly match selected mappings".to_string(),
            );
        }
        if direct_call_entities.len() != self.direct_calls.len()
            || semantic_call_entities.len() != self.semantic_calls.len()
            || direct_call_entities
                .keys()
                .copied()
                .collect::<BTreeSet<_>>()
                != semantic_call_entities
                    .keys()
                    .copied()
                    .collect::<BTreeSet<_>>()
            || call_obligations != mapped_call_obligations
            || !call_obligations.is_subset(&expected_obligations)
        {
            invalid
                .push("certified direct calls do not exactly match selected mappings".to_string());
        }
        for (producer, call) in &direct_call_entities {
            let source_interface = self
                .origin
                .machine_context()
                .source()
                .call_site_interface(call.call_site());
            let semantic_matches = semantic_call_entities
                .get(producer)
                .is_some_and(|semantic| {
                    semantic.call_site() == call.call_site()
                        && semantic.raw_identity() == call.raw_identity()
                        && semantic.interface_revision() == call.interface_revision()
                        && semantic.target_binding() == call.target_value().binding()
                        && semantic.target() == call.target()
                        && semantic.fallthrough() == call.fallthrough()
                        && semantic.calling_convention() == call.calling_convention()
                        && semantic.source_obligations() == &call.source_obligations()
                        && semantic.arguments().len() == call.arguments().len()
                        && semantic.arguments().iter().zip(call.arguments()).all(
                            |(semantic_argument, certified_argument)| {
                                semantic_argument.slot() == certified_argument.slot()
                                    && semantic_argument.binding()
                                        == certified_argument.value().binding()
                                    && semantic_argument.ty() == certified_argument.value().ty()
                                    && match (
                                        semantic_argument.value(),
                                        certified_argument.origin(),
                                    ) {
                                        (
                                            SemanticCCallArgumentValue::Expression(expression),
                                            CertifiedCallArgumentOrigin::Produced {
                                                producer: argument_producer,
                                            },
                                        ) => expression_entities
                                            .get(argument_producer)
                                            .is_some_and(|entity| {
                                                entity.root() == *expression
                                                    && entity.output()
                                                        == semantic_argument.binding()
                                            }),
                                        (
                                            SemanticCCallArgumentValue::Constant(actual),
                                            CertifiedCallArgumentOrigin::Constant { value },
                                        ) => actual == value,
                                        (
                                            SemanticCCallArgumentValue::AbiParameter {
                                                index: actual,
                                                input,
                                            },
                                            CertifiedCallArgumentOrigin::AbiParameter {
                                                index: expected,
                                            },
                                        ) => {
                                            actual == expected
                                                && self
                                                    .expression_layer
                                                    .function_interface()
                                                    .is_some_and(|interface| {
                                                        interface
                                                            .parameters()
                                                            .get(*actual as usize)
                                                            .is_some_and(|parameter| {
                                                                parameter.index() == *actual
                                                                    && parameter.value()
                                                                        == Some(*input)
                                                            })
                                                    })
                                        }
                                        _ => false,
                                    }
                            },
                        )
                });
            let source_interface_matches = source_interface.is_some_and(|interface| {
                interface.identity() == call.raw_identity()
                    && interface.revision_identity() == call.interface_revision()
                    && interface.calling_convention() == call.calling_convention()
                    && interface.arguments().len() == call.arguments().len()
                    && interface.arguments().iter().zip(call.arguments()).all(
                        |(expected, argument)| {
                            argument.slot()
                                == (r2ssa::CallBoundarySlot::Register {
                                    index: expected.index(),
                                    storage: expected.storage(),
                                })
                        },
                    )
                    && matches!(interface.result(), r2ssa::SourceCallResult::Void)
                    && interface.is_complete()
                    && !interface.is_variadic()
                    && !interface.is_noreturn()
            });
            if !semantic_matches || !source_interface_matches {
                invalid.push(format!(
                    "semantic direct call does not match certified call for {producer}"
                ));
            }
        }
        if direct_control_entities.len() != self.direct_controls.len()
            || conditional_control_entities.len() != self.conditional_controls.len()
            || switch_control_entities.len() != self.switch_controls.len()
            || direct_control_entities.keys().any(|producer| {
                conditional_control_entities.contains_key(producer)
                    || switch_control_entities.contains_key(producer)
            })
            || conditional_control_entities
                .keys()
                .any(|producer| switch_control_entities.contains_key(producer))
            || control_obligations.len()
                != self
                    .direct_controls
                    .len()
                    .saturating_add(self.conditional_controls.len().saturating_mul(2))
                    .saturating_add(self.switch_controls.len())
            || control_obligations != mapped_control_obligations
            || !control_obligations.is_subset(&expected_obligations)
        {
            invalid.push(
                "certified terminal controls do not exactly match selected mappings".to_string(),
            );
        }
        for control in &self.switch_controls {
            let effects = self.ledger.effects(control.source_obligation());
            if !matches!(
                effects,
                [effect]
                    if effect.disposition()
                        == &(EffectDisposition::AbsorbedIntoControl {
                            producer: control.producer(),
                        })
                        && effect.switch_control_evidence() == Some(control)
            ) {
                invalid.push(format!(
                    "switch control does not match certified ledger evidence for {}",
                    control.producer()
                ));
            }
        }
        if return_control_entities.len() != self.return_controls.len()
            || return_obligations != mapped_return_obligations
            || !return_obligations.is_subset(&expected_obligations)
            || semantic_return_entities.len() != self.semantic_returns.len()
            || semantic_return_entities
                .keys()
                .copied()
                .collect::<BTreeSet<_>>()
                != return_control_entities
                    .keys()
                    .copied()
                    .collect::<BTreeSet<_>>()
        {
            invalid.push("certified returns do not exactly match selected mappings".to_string());
        }
        for (producer, control) in &return_control_entities {
            let semantic_matches = semantic_return_entities
                .get(producer)
                .is_some_and(|returned| {
                    returned.control_target() == control.control_target().binding()
                        && returned.source_obligations() == &control.source_obligations()
                        && returned.values().len() == control.values().len()
                        && returned.values().iter().zip(control.values()).all(
                            |(semantic, certified)| {
                                semantic.slot() == certified.slot()
                                    && semantic.binding() == certified.value().binding()
                                    && expression_entities
                                        .get(&certified.value().producer().unwrap_or(*producer))
                                        .is_some_and(|entity| {
                                            entity.root() == semantic.expression()
                                                && entity.output() == semantic.binding()
                                        })
                            },
                        )
                });
            if !semantic_matches {
                invalid.push(format!(
                    "semantic return does not match certified return for {producer}"
                ));
            }
        }
        if self.expression_layer.schema_version() != SEMANTIC_C_SCHEMA_VERSION
            || self.expression_layer.scope() != SemanticCScope::LiveValueExpressionsOnly
            || self.expression_layer.identity_scope() != self.identity_scope
        {
            invalid.push("nested semantic expression layer contract mismatch".to_string());
        }
        for entity in self.expression_layer.entities() {
            let expected = self
                .source
                .instructions()
                .get(&entity.producer())
                .map(|instruction| {
                    instruction
                        .obligations
                        .iter()
                        .copied()
                        .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
                        .collect::<BTreeSet<_>>()
                });
            if expected.as_ref() != Some(entity.source_obligations())
                || entity
                    .source_obligations()
                    .iter()
                    .any(|id| id.instruction != entity.producer())
            {
                invalid.push(format!(
                    "semantic expression obligations are misbound for {}",
                    entity.producer()
                ));
            }
        }
        if self
            .instructions
            .iter()
            .map(|instruction| &instruction.source)
            .any(|id| id.block_addr != self.block_addr)
        {
            invalid.push("region block address does not match its source instructions".to_string());
        }
        for instruction in &self.instructions {
            if self
                .source
                .instructions()
                .get(&instruction.source)
                .map(|expected| expected.state)
                != Some(instruction.state)
            {
                invalid.push(format!(
                    "source instruction state mismatch for {}",
                    instruction.source
                ));
            }
            if let Some(producer) = instruction.expression_producer
                && !self.mappings.iter().any(|mapping| {
                    mapping.obligation.instruction == instruction.source
                        && matches!(
                            mapping.disposition,
                            RegionObligationDisposition::AbsorbedIntoExpression {
                                producer: mapped_producer,
                            } if producer == instruction.source && mapped_producer == producer
                        )
                })
            {
                invalid.push(format!(
                    "expression producer for {} has no live-value mapping",
                    instruction.source
                ));
            }
            if let Some(producer) = instruction.statement_producer
                && !self.mappings.iter().any(|mapping| {
                    mapping.obligation.instruction == instruction.source
                        && matches!(
                            mapping.disposition,
                            RegionObligationDisposition::AbsorbedIntoStatement {
                                producer: mapped_producer,
                            } if producer == instruction.source && mapped_producer == producer
                        )
                })
            {
                invalid.push(format!(
                    "statement producer for {} has no memory mapping",
                    instruction.source
                ));
            }
            if let Some(producer) = instruction.call_producer
                && !self.mappings.iter().any(|mapping| {
                    mapping.obligation.instruction == instruction.source
                        && matches!(
                            mapping.disposition,
                            RegionObligationDisposition::AbsorbedIntoCall {
                                producer: mapped_producer,
                            } if producer == instruction.source && mapped_producer == producer
                        )
                })
            {
                invalid.push(format!(
                    "call producer for {} has no call-boundary mapping",
                    instruction.source
                ));
            }
            if let Some(producer) = instruction.control_producer
                && !self.mappings.iter().any(|mapping| {
                    mapping.obligation.instruction == instruction.source
                        && matches!(
                            mapping.disposition,
                            RegionObligationDisposition::AbsorbedIntoControl {
                                producer: mapped_producer,
                            } if producer == instruction.source && mapped_producer == producer
                        )
                })
            {
                invalid.push(format!(
                    "control producer for {} has no transfer mapping",
                    instruction.source
                ));
            }
            if let Some(producer) = instruction.return_producer
                && !self.mappings.iter().any(|mapping| {
                    mapping.obligation.instruction == instruction.source
                        && matches!(
                            mapping.disposition,
                            RegionObligationDisposition::AbsorbedIntoReturn {
                                producer: mapped_producer,
                            } if producer == instruction.source && mapped_producer == producer
                        )
                })
            {
                invalid.push(format!(
                    "return producer for {} has no return mapping",
                    instruction.source
                ));
            }
            match (
                instruction.expression_producer,
                expression_entities.get(&instruction.source),
            ) {
                (Some(producer), Some(entity)) if entity.producer() == producer => {}
                (None, None) => {}
                _ => invalid.push(format!(
                    "expression producer for {} is not bound to its semantic entity",
                    instruction.source
                )),
            }
            match (
                instruction.statement_producer,
                statement_entities.get(&instruction.source),
            ) {
                (Some(producer), Some(statement)) if statement.producer() == producer => {}
                (None, None) => {}
                _ => invalid.push(format!(
                    "statement producer for {} is not bound to its certified memory statement",
                    instruction.source
                )),
            }
            match (
                instruction.call_producer,
                direct_call_entities
                    .get(&instruction.source)
                    .map(|call| call.producer()),
            ) {
                (Some(producer), Some(entity_producer)) if entity_producer == producer => {}
                (None, None) => {}
                _ => invalid.push(format!(
                    "call producer for {} is not bound to its certified direct call",
                    instruction.source
                )),
            }
            match (
                instruction.control_producer,
                direct_control_entities
                    .get(&instruction.source)
                    .map(|control| control.producer())
                    .or_else(|| {
                        conditional_control_entities
                            .get(&instruction.source)
                            .map(|control| control.producer())
                    })
                    .or_else(|| {
                        switch_control_entities
                            .get(&instruction.source)
                            .map(|control| control.producer())
                    }),
            ) {
                (Some(producer), Some(entity_producer)) if entity_producer == producer => {}
                (None, None) => {}
                _ => invalid.push(format!(
                    "control producer for {} is not bound to its certified terminal transfer",
                    instruction.source
                )),
            }
            match (
                instruction.return_producer,
                return_control_entities
                    .get(&instruction.source)
                    .map(|control| control.producer()),
            ) {
                (Some(producer), Some(entity_producer)) if entity_producer == producer => {}
                (None, None) => {}
                _ => invalid.push(format!(
                    "return producer for {} is not bound to its certified return",
                    instruction.source
                )),
            }
        }
        for mapping in &self.mappings {
            match mapping.disposition {
                RegionObligationDisposition::AbsorbedIntoExpression { producer } => {
                    let entity_matches = expression_entities.get(&producer).is_some_and(|entity| {
                        entity.source_obligations().contains(&mapping.obligation)
                    });
                    if mapping.obligation.kind != SemanticObligationKind::LiveValueProducer
                        || producer != mapping.obligation.instruction
                        || !entity_matches
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.expression_producer == Some(producer)
                        })
                    {
                        invalid.push(format!(
                            "invalid expression mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::AbsorbedIntoStatement { producer } => {
                    let statement_matches =
                        statement_entities.get(&producer).is_some_and(|statement| {
                            statement.source_obligations().contains(&mapping.obligation)
                        });
                    let ledger_matches = matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if effect.disposition()
                                == &EffectDisposition::AbsorbedIntoStatement { producer }
                                && effect.statement_evidence() == statement_entities
                                    .get(&producer)
                                    .copied()
                    );
                    if !matches!(
                        mapping.obligation.kind,
                        SemanticObligationKind::ObservableMemoryRead
                            | SemanticObligationKind::ObservableMemoryWrite
                    ) || producer != mapping.obligation.instruction
                        || !statement_matches
                        || !ledger_matches
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.statement_producer == Some(producer)
                        })
                    {
                        invalid.push(format!(
                            "invalid memory-statement mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::AbsorbedIntoCall { producer } => {
                    let call_matches = direct_call_entities.get(&producer).is_some_and(|call| {
                        call.source_obligations().contains(&mapping.obligation)
                            && self.source_block().is_some_and(|block| {
                                matches!(
                                    block.terminator(),
                                    r2cert::CertifiedSourceTerminator::Call {
                                        target,
                                        fallthrough: Some(fallthrough),
                                    } if *target == call.target()
                                        && *fallthrough == call.fallthrough()
                                ) && block.successors() == [call.fallthrough()]
                                    && self.topology.block(call.fallthrough()).is_some()
                                    && block.addr() != call.fallthrough()
                                    && block.instructions().last() == Some(&producer)
                            })
                    });
                    let ledger_matches = matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if effect.disposition()
                                == &EffectDisposition::AbsorbedIntoCall { producer }
                                && effect.direct_call_evidence()
                                    == direct_call_entities.get(&producer).copied()
                    );
                    if !matches!(
                        mapping.obligation.kind,
                        SemanticObligationKind::Call | SemanticObligationKind::CallArgument
                    ) || producer != mapping.obligation.instruction
                        || !call_matches
                        || !ledger_matches
                        || !semantic_call_entities.contains_key(&producer)
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.call_producer == Some(producer)
                        })
                    {
                        invalid.push(format!(
                            "invalid direct-call mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::AbsorbedIntoControl { producer } => {
                    let direct_matches =
                        direct_control_entities
                            .get(&producer)
                            .is_some_and(|control| {
                                control.source_obligation() == mapping.obligation
                                    && self.source_block().is_some_and(|block| {
                                        matches!(
                                                block.terminator(),
                                                r2cert::CertifiedSourceTerminator::Branch { target }
                                                    if *target == control.target()
                                        ) && block.successors() == [control.target()]
                                            && self.topology.block(control.target()).is_some()
                                            && block.addr() != control.target()
                                            && block.instructions().last() == Some(&producer)
                                    })
                            });
                    let conditional_matches = conditional_control_entities
                        .get(&producer)
                        .is_some_and(|control| {
                            let successors = self.source_block().map(|block| {
                                block.successors().iter().copied().collect::<BTreeSet<_>>()
                            });
                            let expected_successors =
                                BTreeSet::from([control.true_target(), control.false_target()]);
                            let values_are_grounded = [control.target_value(), control.condition()]
                                .into_iter()
                                .all(|value| {
                                    value.producer().is_none_or(|value_producer| {
                                        expression_entities.get(&value_producer).is_some_and(
                                            |entity| entity.output() == value.binding(),
                                        )
                                    })
                                });
                            let source_obligations_match = self
                                .source
                                .obligations()
                                .get(&control.predicate_obligation())
                                .is_some_and(|obligation| {
                                    obligation.inputs == [control.condition().binding().value()]
                                })
                                && self
                                    .source
                                    .obligations()
                                    .get(&control.transfer_obligation())
                                    .is_some_and(|obligation| {
                                        obligation.inputs
                                            == [
                                                control.target_value().binding().value(),
                                                control.condition().binding().value(),
                                            ]
                                    });
                            control.source_obligations().contains(&mapping.obligation)
                                && control.source_obligations().len() == 2
                                && control.condition().binding().width_bits() == 8
                                && control.truthiness() == CertifiedControlTruthiness::NonZeroIsTrue
                                && values_are_grounded
                                && source_obligations_match
                                && control.true_target() != control.false_target()
                                && self.source_block().is_some_and(|block| {
                                    matches!(
                                        block.terminator(),
                                        r2cert::CertifiedSourceTerminator::ConditionalBranch {
                                            true_target,
                                            false_target,
                                        } if *true_target == control.true_target()
                                            && *false_target == control.false_target()
                                    ) && successors.as_ref() == Some(&expected_successors)
                                        && block.successors().len() == 2
                                        && block.addr() != control.true_target()
                                        && block.addr() != control.false_target()
                                        && self.topology.block(control.true_target()).is_some()
                                        && self.topology.block(control.false_target()).is_some()
                                        && block.instructions().last() == Some(&producer)
                                })
                        });
                    let switch_matches =
                        switch_control_entities
                            .get(&producer)
                            .is_some_and(|control| {
                                let topology = control.topology();
                                control.source_obligation() == mapping.obligation
                                    && control.origin() == &self.origin
                                    && self.source_block().is_some_and(|block| {
                                        matches!(
                                            block.terminator(),
                                            r2cert::CertifiedSourceTerminator::Switch {
                                                switch_addr,
                                                terminal_instruction_addr,
                                                min_value,
                                                max_value,
                                                cases,
                                                default,
                                            } if *switch_addr == topology.switch_addr()
                                                && switch_addr == terminal_instruction_addr
                                                && *min_value == topology.min_value()
                                                && *max_value == topology.max_value()
                                                && cases.as_ref() == topology.cases()
                                                && *default == Some(topology.default_target())
                                        ) && block.instructions().last() == Some(&producer)
                                    })
                            });
                    let ledger_matches = matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if effect.disposition()
                                == &EffectDisposition::AbsorbedIntoControl { producer }
                                && ((direct_matches
                                    && effect.direct_control_evidence()
                                        == direct_control_entities.get(&producer).copied())
                                    || (conditional_matches
                                        && effect.conditional_control_evidence()
                                            == conditional_control_entities
                                                .get(&producer)
                                                .copied())
                                    || (switch_matches
                                        && effect.switch_control_evidence()
                                            == switch_control_entities.get(&producer).copied()))
                    );
                    if !matches!(
                        mapping.obligation.kind,
                        SemanticObligationKind::ControlPredicate
                            | SemanticObligationKind::ControlTransfer
                    ) || producer != mapping.obligation.instruction
                        || usize::from(direct_matches)
                            + usize::from(conditional_matches)
                            + usize::from(switch_matches)
                            != 1
                        || !ledger_matches
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.control_producer == Some(producer)
                        })
                    {
                        invalid.push(format!(
                            "invalid terminal-control mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::AbsorbedIntoReturn { producer } => {
                    let return_matches =
                        return_control_entities
                            .get(&producer)
                            .is_some_and(|control| {
                                let values_are_grounded = control.values().iter().all(|returned| {
                                    returned.value().producer().is_some_and(|value_producer| {
                                        expression_entities.get(&value_producer).is_some_and(
                                            |entity| entity.output() == returned.value().binding(),
                                        )
                                    })
                                });
                                control.source_obligations().contains(&mapping.obligation)
                                    && values_are_grounded
                                    && self.source_block().is_some_and(|block| {
                                        matches!(
                                            block.terminator(),
                                            r2cert::CertifiedSourceTerminator::Return
                                        ) && block.successors().is_empty()
                                            && block.instructions().last() == Some(&producer)
                                    })
                            });
                    let ledger_matches = matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if effect.disposition()
                                == &EffectDisposition::AbsorbedIntoReturn { producer }
                                && effect.return_control_evidence()
                                    == return_control_entities.get(&producer).copied()
                    );
                    if !matches!(
                        mapping.obligation.kind,
                        SemanticObligationKind::Return | SemanticObligationKind::ReturnValue
                    ) || producer != mapping.obligation.instruction
                        || !return_matches
                        || !ledger_matches
                        || !self.instructions.iter().any(|instruction| {
                            instruction.source == producer
                                && instruction.return_producer == Some(producer)
                        })
                    {
                        invalid.push(format!(
                            "invalid terminal-return mapping for {}",
                            mapping.obligation
                        ));
                    }
                }
                RegionObligationDisposition::Residualized { reason } => {
                    if reason != residual_reason(mapping.obligation.kind) {
                        invalid.push(format!("wrong residual reason for {}", mapping.obligation));
                    }
                    if matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if matches!(
                                effect.disposition(),
                                EffectDisposition::AbsorbedIntoStatement { .. }
                            )
                    ) {
                        invalid.push(format!(
                            "statement-absorbed obligation was downgraded to residual for {}",
                            mapping.obligation
                        ));
                    }
                    if matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if matches!(
                                effect.disposition(),
                                EffectDisposition::AbsorbedIntoCall { .. }
                            )
                    ) {
                        invalid.push(format!(
                            "call-absorbed obligation was downgraded to residual for {}",
                            mapping.obligation
                        ));
                    }
                    if matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if matches!(
                                effect.disposition(),
                                EffectDisposition::AbsorbedIntoControl { .. }
                            )
                    ) {
                        invalid.push(format!(
                            "control-absorbed obligation was downgraded to residual for {}",
                            mapping.obligation
                        ));
                    }
                    if matches!(
                        self.ledger.effects(mapping.obligation),
                        [effect]
                            if matches!(
                                effect.disposition(),
                                EffectDisposition::AbsorbedIntoReturn { .. }
                            )
                    ) {
                        invalid.push(format!(
                            "return-absorbed obligation was downgraded to residual for {}",
                            mapping.obligation
                        ));
                    }
                }
            }
        }
        let residual_set = self
            .mappings
            .iter()
            .filter_map(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::Residualized { .. }
                )
                .then_some(mapping.obligation)
            })
            .collect::<BTreeSet<_>>();
        let closed_set = mapped_expression_obligations
            .union(&mapped_statement_obligations)
            .copied()
            .chain(mapped_call_obligations.iter().copied())
            .chain(mapped_control_obligations.iter().copied())
            .chain(mapped_return_obligations.iter().copied())
            .collect::<BTreeSet<_>>();
        let expected_residual_set = expected_obligations
            .difference(&closed_set)
            .copied()
            .collect::<BTreeSet<_>>();
        if residual_set != expected_residual_set {
            invalid.push(
                "region residual mappings do not equal the unowned selected obligations"
                    .to_string(),
            );
        }

        RegionAuditReport {
            missing_instructions,
            duplicate_instructions,
            unexpected_instructions,
            missing_obligations,
            duplicate_obligations,
            unexpected_obligations,
            invalid,
            residualized_obligations: residual_set.into_iter().collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RegionAuditReport {
    missing_instructions: Vec<CanonicalInstructionId>,
    duplicate_instructions: Vec<CanonicalInstructionId>,
    unexpected_instructions: Vec<CanonicalInstructionId>,
    missing_obligations: Vec<SemanticObligationId>,
    duplicate_obligations: Vec<SemanticObligationId>,
    unexpected_obligations: Vec<SemanticObligationId>,
    invalid: Vec<String>,
    residualized_obligations: Vec<SemanticObligationId>,
}

impl RegionAuditReport {
    pub fn has_exact_source_accounting(&self) -> bool {
        self.missing_instructions.is_empty()
            && self.duplicate_instructions.is_empty()
            && self.unexpected_instructions.is_empty()
            && self.missing_obligations.is_empty()
            && self.duplicate_obligations.is_empty()
            && self.unexpected_obligations.is_empty()
            && self.invalid.is_empty()
    }

    pub fn missing_obligations(&self) -> &[SemanticObligationId] {
        &self.missing_obligations
    }

    pub fn missing_instructions(&self) -> &[CanonicalInstructionId] {
        &self.missing_instructions
    }

    pub fn duplicate_instructions(&self) -> &[CanonicalInstructionId] {
        &self.duplicate_instructions
    }

    pub fn unexpected_instructions(&self) -> &[CanonicalInstructionId] {
        &self.unexpected_instructions
    }

    pub fn duplicate_obligations(&self) -> &[SemanticObligationId] {
        &self.duplicate_obligations
    }

    pub fn unexpected_obligations(&self) -> &[SemanticObligationId] {
        &self.unexpected_obligations
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }

    pub fn residualized_obligations(&self) -> &[SemanticObligationId] {
        &self.residualized_obligations
    }

    /// Whether selected source obligations remain residual. This does not
    /// describe block-exit or successor-port openness.
    pub fn has_residuals(&self) -> bool {
        !self.residualized_obligations.is_empty()
    }
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut result = BTreeMap::new();
    for value in values {
        *result.entry(value).or_default() += 1;
    }
    result
}

fn reconcile<T: Copy + Ord>(
    expected: impl IntoIterator<Item = T>,
    actual: &BTreeMap<T, usize>,
) -> (Vec<T>, Vec<T>, Vec<T>) {
    let expected = expected.into_iter().collect::<BTreeSet<_>>();
    let missing = expected
        .iter()
        .copied()
        .filter(|value| !actual.contains_key(value))
        .collect();
    let duplicate = actual
        .iter()
        .filter_map(|(value, count)| (*count > 1).then_some(*value))
        .collect();
    let unexpected = actual
        .keys()
        .copied()
        .filter(|value| !expected.contains(value))
        .collect();
    (missing, duplicate, unexpected)
}

fn residual_reason(kind: SemanticObligationKind) -> RegionResidualReason {
    match kind {
        SemanticObligationKind::ObservableMemoryRead
        | SemanticObligationKind::ObservableMemoryWrite => {
            RegionResidualReason::MemoryEffectRequiresCertifiedStatement
        }
        SemanticObligationKind::Call
        | SemanticObligationKind::CallArgument
        | SemanticObligationKind::CallResult => {
            RegionResidualReason::CallBoundaryRequiresCertifiedCall
        }
        SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => {
            RegionResidualReason::ReturnRequiresCertifiedControl
        }
        SemanticObligationKind::ControlPredicate | SemanticObligationKind::ControlTransfer => {
            RegionResidualReason::ControlRequiresCertifiedRegion
        }
        SemanticObligationKind::Trap
        | SemanticObligationKind::Atomicity
        | SemanticObligationKind::MemoryOrdering => {
            RegionResidualReason::TrapOrOrderingRequiresCertifiedEffect
        }
        SemanticObligationKind::VolatileOrUnknownEffect => {
            RegionResidualReason::UnsupportedSourceSemantics
        }
        SemanticObligationKind::LoopCarriedState | SemanticObligationKind::LiveStateTransition => {
            RegionResidualReason::LoopStateRequiresCertifiedStructuring
        }
        SemanticObligationKind::LiveValueProducer => {
            RegionResidualReason::UnsupportedSourceSemantics
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2il::{ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCallArgumentSpec,
        SourceCallResult, SourceCallSiteIdentity, SourceCallSiteInterface, SourceFunctionInterface,
        SourceFunctionReturn, SsaArtifact,
    };

    fn straight_line_artifact() -> SsaArtifact {
        let initial = Varnode::unique(0x10, 8);
        let product = Varnode::unique(0x18, 8);
        let mut block = R2ILBlock::new(0x5000, 4);
        block.push(R2ILOp::Copy {
            dst: initial.clone(),
            src: Varnode::constant(0xcbf29ce484222325, 8),
        });
        block.push(R2ILOp::IntMult {
            dst: product.clone(),
            a: initial,
            b: Varnode::constant(0x100000001b3, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
            val: product,
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        SsaArtifact::raw(&[block], None).expect("straight-line artifact")
    }

    fn typed_memory_accounting() -> CertifiedSingleBlockAccounting {
        let address = Varnode::register(0, 8);
        let loaded = Varnode::unique(0x10, 4);
        let mut block = R2ILBlock::new(0x5050, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: address.clone(),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: address,
            val: loaded,
        });
        let mut arch = ArchSpec::new("region-memory-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(Endianness::Little);
        let artifact = SsaArtifact::raw(&[block], Some(&arch)).expect("typed memory artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("certified memory projection");
        CertifiedSingleBlockAccounting::from_projection(&certified)
            .expect("typed memory accounting")
    }

    fn conditional_accounting(condition: u64) -> CertifiedSingleBlockAccounting {
        let mut entry = R2ILBlock::new(0x5080, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x5090, 8),
            cond: Varnode::constant(condition, 1),
        });
        let fallthrough = R2ILBlock::new(0x5084, 4);
        let taken = R2ILBlock::new(0x5090, 4);
        let artifact =
            SsaArtifact::raw(&[entry, fallthrough, taken], None).expect("conditional artifact");
        let certified =
            CertifiedMachineProjection::from_artifact(&artifact).expect("conditional projection");
        CertifiedSingleBlockAccounting::from_projection_block(&certified, 0x5080)
            .expect("conditional accounting")
    }

    fn direct_call_accounting() -> CertifiedSingleBlockAccounting {
        let target = Varnode::ram(0x6000, 8);
        let mut entry = R2ILBlock::new(0x50a0, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(0x2a, 8),
        });
        entry.push(R2ILOp::Call {
            target: target.clone(),
        });
        let fallthrough = R2ILBlock::new(0x50a4, 4);
        let mut arch = ArchSpec::new("region-direct-call-test");
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        let argument_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 8,
            size: 8,
        };
        let identity =
            SourceCallSiteIdentity::new(0x50a0, 1, CanonicalStorageId::from_varnode(&target));
        let interface = SourceCallSiteInterface::new(
            b"region-direct-call-revision-1".to_vec(),
            identity,
            true,
            "test-call-abi",
            [SourceCallArgumentSpec::new(0, argument_storage)],
            false,
            false,
            SourceCallResult::Void,
        )
        .expect("direct call interface");
        let artifact = SsaArtifact::raw_with_interfaces(
            &[entry, fallthrough],
            Some(&arch),
            None,
            vec![interface],
        )
        .expect("direct call artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("certified direct call projection");
        CertifiedSingleBlockAccounting::from_projection_block(&certified, 0x50a0)
            .expect("direct call accounting")
    }

    fn explicit_return_accounting(
        return_kind: SourceFunctionReturn,
    ) -> CertifiedSingleBlockAccounting {
        let mut block = R2ILBlock::new(0x50c0, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::register(8, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::unique(0x10, 8),
        });
        block.push(R2ILOp::Return {
            target: Varnode::register(16, 8),
        });
        let mut arch = ArchSpec::new("region-explicit-return-test");
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        arch.add_register(RegisterDef::new("rip", 16, 8));
        let parameter_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 8,
            size: 8,
        };
        let interface = SourceFunctionInterface::new(
            b"region-explicit-return-revision-1".to_vec(),
            "test-register-abi",
            [SourceAbiParameterSpec::new(0, parameter_storage)],
            return_kind,
            [],
        )
        .expect("explicit interface");
        let artifact = SsaArtifact::raw_with_interface(&[block], Some(&arch), interface)
            .expect("explicit return artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("explicit return projection");
        CertifiedSingleBlockAccounting::from_projection(&certified)
            .expect("explicit return accounting")
    }

    fn colliding_direct_control() -> CertifiedDirectControl {
        let mut entry = R2ILBlock::new(0x5080, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x5090, 8),
        });
        let target = R2ILBlock::new(0x5090, 4);
        let artifact = SsaArtifact::raw(&[entry, target], None).expect("direct artifact");
        let certified =
            CertifiedMachineProjection::from_artifact(&artifact).expect("direct projection");
        let accounting = CertifiedSingleBlockAccounting::from_projection_block(&certified, 0x5080)
            .expect("direct accounting");
        accounting.direct_controls()[0].clone()
    }

    #[test]
    fn conditional_control_maps_exact_predicate_and_transfer_evidence() {
        let accounting = conditional_accounting(1);
        let report = accounting.audit();
        let [control] = accounting.conditional_controls() else {
            panic!("one conditional control expected");
        };

        assert!(report.has_exact_source_accounting(), "{report:?}");
        assert!(!report.has_residuals(), "{report:?}");
        assert!(accounting.direct_controls().is_empty());
        assert_eq!(control.source_obligations().len(), 2);
        assert_eq!(
            accounting
                .mappings()
                .iter()
                .filter(|mapping| matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoControl { producer }
                        if *producer == control.producer()
                ))
                .count(),
            2
        );
    }

    #[test]
    fn direct_call_maps_exact_typed_boundary_without_residuals() {
        let accounting = direct_call_accounting();
        let report = accounting.audit();
        let [call] = accounting.direct_calls() else {
            panic!("one certified direct call expected");
        };
        let [semantic] = accounting.semantic_calls() else {
            panic!("one semantic direct call expected");
        };
        let [argument] = call.arguments() else {
            panic!("one certified call argument expected");
        };
        let [semantic_argument] = semantic.arguments() else {
            panic!("one semantic call argument expected");
        };

        assert!(report.has_exact_source_accounting(), "{report:?}");
        assert!(!report.has_residuals(), "{report:?}");
        assert_eq!(semantic.producer(), call.producer());
        assert_eq!(semantic.call_site(), call.call_site());
        assert_eq!(semantic.target(), call.target());
        assert_eq!(semantic.fallthrough(), call.fallthrough());
        assert_eq!(semantic.calling_convention(), call.calling_convention());
        assert_eq!(semantic_argument.slot(), argument.slot());
        assert_eq!(semantic_argument.binding(), argument.value().binding());
        assert_eq!(semantic_argument.ty(), argument.value().ty());
        let argument_producer = argument.value().producer().expect("argument producer");
        let argument_entity = accounting
            .expression_layer()
            .entity_for_producer(argument_producer)
            .expect("argument expression");
        assert_eq!(argument_entity.output(), semantic_argument.binding());
        assert_eq!(semantic_argument.expression(), None);
        let SemanticCCallArgumentValue::Constant(value) = semantic_argument.value() else {
            panic!("constant-backed call argument expected");
        };
        assert_eq!(value.width_bits(), 64);
        assert_eq!(value.bits(), 0x2a);
        assert_eq!(semantic.source_obligations(), &call.source_obligations());
        assert_eq!(
            accounting
                .mappings()
                .iter()
                .filter(|mapping| matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoCall { producer }
                        if *producer == call.producer()
                ))
                .count(),
            call.source_obligations().len()
        );
        assert!(accounting.instructions().iter().any(|instruction| {
            instruction.source() == call.producer()
                && instruction.call_producer() == Some(call.producer())
        }));
    }

    #[test]
    fn direct_call_evidence_and_mapping_mutations_fail_audit() {
        let accounting = direct_call_accounting();
        let producer = accounting.direct_calls()[0].producer();

        let mut certified_deleted = accounting.clone();
        certified_deleted.direct_calls = Box::new([]);
        assert!(!certified_deleted.audit().has_exact_source_accounting());

        let mut certified_duplicated = accounting.clone();
        let call = certified_duplicated.direct_calls[0].clone();
        certified_duplicated.direct_calls = vec![call.clone(), call].into_boxed_slice();
        assert!(!certified_duplicated.audit().has_exact_source_accounting());

        let mut semantic_deleted = accounting.clone();
        semantic_deleted.semantic_calls = Box::new([]);
        assert!(!semantic_deleted.audit().has_exact_source_accounting());

        let mut semantic_duplicated = accounting.clone();
        let call = semantic_duplicated.semantic_calls[0].clone();
        semantic_duplicated.semantic_calls = vec![call.clone(), call].into_boxed_slice();
        assert!(!semantic_duplicated.audit().has_exact_source_accounting());

        let mut producer_cleared = accounting.clone();
        producer_cleared
            .instructions
            .iter_mut()
            .find(|instruction| instruction.source == producer)
            .expect("call instruction")
            .call_producer = None;
        assert!(!producer_cleared.audit().has_exact_source_accounting());

        let mut downgraded = accounting;
        let mapping = downgraded
            .mappings
            .iter_mut()
            .find(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoCall { .. }
                )
            })
            .expect("call mapping");
        mapping.disposition = RegionObligationDisposition::Residualized {
            reason: RegionResidualReason::CallBoundaryRequiresCertifiedCall,
        };
        assert!(!downgraded.audit().has_exact_source_accounting());
    }

    #[test]
    fn explicit_return_maps_to_typed_semantic_return_without_residuals() {
        let accounting = explicit_return_accounting(SourceFunctionReturn::Register {
            storage: CanonicalStorageId {
                space: CanonicalStorageSpace::Register,
                offset: 0,
                size: 8,
            },
        });
        let report = accounting.audit();
        assert!(report.has_exact_source_accounting(), "{report:?}");
        assert!(!report.has_residuals(), "{report:?}");
        let [returned] = accounting.semantic_returns() else {
            panic!("one semantic return expected");
        };
        assert_eq!(returned.values().len(), 1);
        assert_eq!(accounting.return_controls().len(), 1);
        assert_eq!(returned.source_obligations().len(), 2);
        let interface = accounting
            .expression_layer()
            .function_interface()
            .expect("semantic function interface");
        assert_eq!(interface.parameters().len(), 1);
        assert!(matches!(
            interface.return_kind(),
            crate::semantic_c::SemanticCFunctionReturn::Register { .. }
        ));
        assert!(
            accounting
                .expression_layer()
                .input_origins()
                .values()
                .all(|origin| matches!(
                    origin,
                    crate::semantic_c::SemanticCInputOrigin::AbiParameter { .. }
                ))
        );
        assert!(
            accounting
                .mappings()
                .iter()
                .filter(|mapping| matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoReturn { .. }
                ))
                .count()
                == 2
        );
    }

    #[test]
    fn return_evidence_deletion_downgrade_and_foreign_swap_fail_audit() {
        let return_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let accounting = explicit_return_accounting(SourceFunctionReturn::Register {
            storage: return_storage,
        });

        let mut missing_semantic = accounting.clone();
        missing_semantic.semantic_returns = Box::new([]);
        assert!(!missing_semantic.audit().has_exact_source_accounting());

        let mut missing_certificate = accounting.clone();
        missing_certificate.return_controls = Box::new([]);
        assert!(!missing_certificate.audit().has_exact_source_accounting());

        let mut downgraded = accounting.clone();
        let mapping = downgraded
            .mappings
            .iter_mut()
            .find(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoReturn { .. }
                )
            })
            .expect("return mapping");
        mapping.disposition = RegionObligationDisposition::Residualized {
            reason: RegionResidualReason::ReturnRequiresCertifiedControl,
        };
        assert!(!downgraded.audit().has_exact_source_accounting());

        let foreign_void = explicit_return_accounting(SourceFunctionReturn::Void);
        let mut swapped = accounting;
        swapped.semantic_returns = foreign_void.semantic_returns;
        assert!(!swapped.audit().has_exact_source_accounting());
    }

    #[test]
    fn conditional_control_mutations_collisions_and_downgrades_fail_audit() {
        let accounting = conditional_accounting(1);

        let mut deleted = accounting.clone();
        deleted.conditional_controls = Box::new([]);
        assert!(!deleted.audit().has_exact_source_accounting());

        let mut duplicated = accounting.clone();
        let control = duplicated.conditional_controls[0].clone();
        duplicated.conditional_controls = vec![control.clone(), control].into_boxed_slice();
        assert!(!duplicated.audit().has_exact_source_accounting());

        let mut downgraded = accounting.clone();
        let mapping = downgraded
            .mappings
            .iter_mut()
            .find(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoControl { .. }
                )
            })
            .expect("conditional control mapping");
        mapping.disposition = RegionObligationDisposition::Residualized {
            reason: RegionResidualReason::ControlRequiresCertifiedRegion,
        };
        assert!(!downgraded.audit().has_exact_source_accounting());

        let mut collision = accounting.clone();
        collision.direct_controls = vec![colliding_direct_control()].into_boxed_slice();
        assert!(!collision.audit().has_exact_source_accounting());

        let mut foreign = accounting;
        foreign.conditional_controls = conditional_accounting(0).conditional_controls;
        assert!(!foreign.audit().has_exact_source_accounting());
    }

    #[test]
    fn statement_mapping_deletion_or_downgrade_fails_region_audit() {
        let accounting = typed_memory_accounting();
        let report = accounting.audit();
        assert!(report.has_exact_source_accounting(), "{report:?}");
        assert!(!report.has_residuals());

        let mut downgraded = accounting.clone();
        let mapping = downgraded
            .mappings
            .iter_mut()
            .find(|mapping| {
                matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoStatement { .. }
                )
            })
            .expect("statement mapping");
        mapping.disposition = RegionObligationDisposition::Residualized {
            reason: RegionResidualReason::MemoryEffectRequiresCertifiedStatement,
        };
        assert!(!downgraded.audit().has_exact_source_accounting());

        let mut deleted = accounting;
        let mut statements = deleted.memory_statements.to_vec();
        statements.remove(0);
        deleted.memory_statements = statements.into_boxed_slice();
        assert!(!deleted.audit().has_exact_source_accounting());
    }

    #[test]
    fn straight_line_region_maps_every_source_and_residualizes_open_effects() {
        let artifact = straight_line_artifact();
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let region =
            CertifiedSingleBlockAccounting::from_certified(&certified).expect("source accounting");
        let report = region.audit();

        assert!(report.has_exact_source_accounting(), "{report:?}");
        assert_eq!(
            region.instructions().len(),
            artifact.obligations().instructions().len()
        );
        assert_eq!(
            region.mappings().len(),
            artifact.obligations().obligations().len()
        );
        assert!(region.mappings().iter().any(|mapping| {
            mapping.obligation.kind == SemanticObligationKind::LiveValueProducer
                && matches!(
                    mapping.disposition,
                    RegionObligationDisposition::AbsorbedIntoExpression { .. }
                )
        }));
        for kind in [
            SemanticObligationKind::ObservableMemoryWrite,
            SemanticObligationKind::Return,
        ] {
            assert!(region.mappings().iter().any(|mapping| {
                mapping.obligation.kind == kind
                    && matches!(
                        mapping.disposition,
                        RegionObligationDisposition::Residualized { .. }
                    )
            }));
        }
        assert!(report.has_residuals());
    }

    #[test]
    fn effect_only_block_has_empty_expression_layer_and_exact_residual_accounting() {
        let mut block = R2ILBlock::new(0x5100, 4);
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
            val: Varnode::constant(7, 8),
        });
        let artifact = SsaArtifact::raw(&[block], None).expect("effect-only artifact");
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let accounting =
            CertifiedSingleBlockAccounting::from_certified(&certified).expect("source accounting");
        let report = accounting.audit();

        assert!(accounting.expression_layer().entities().is_empty());
        assert!(report.has_exact_source_accounting(), "{report:?}");
        assert!(report.has_residuals());
    }

    #[test]
    fn unsupported_value_chain_has_exact_residual_accounting() {
        let loaded = Varnode::unique(0x10, 8);
        let sum = Varnode::unique(0x18, 8);
        let mut block = R2ILBlock::new(0x5150, 4);
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: sum.clone(),
            a: loaded,
            b: Varnode::constant(1, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(8, 8),
            val: sum,
        });
        let artifact = SsaArtifact::raw(&[block], None).expect("unsupported value artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("certified partial projection");
        let accounting = CertifiedSingleBlockAccounting::from_projection(&certified)
            .expect("partial source accounting");
        let report = accounting.audit();

        assert!(report.has_exact_source_accounting(), "{report:?}");
        assert!(report.has_residuals());
        assert!(accounting.expression_layer().entities().is_empty());
        assert_eq!(
            accounting.mappings().len(),
            artifact.obligations().obligations().len()
        );
        assert!(accounting.mappings().iter().any(|mapping| {
            mapping.obligation.kind == SemanticObligationKind::LiveValueProducer
                && matches!(
                    mapping.disposition,
                    RegionObligationDisposition::Residualized {
                        reason: RegionResidualReason::UnsupportedSourceSemantics,
                    }
                )
        }));
        assert!(!certified.finish().authorizes_certified_c());
    }

    #[test]
    fn empty_single_block_has_exact_empty_accounting() {
        let block = R2ILBlock::new(0x5180, 4);
        let artifact = SsaArtifact::raw(&[block], None).expect("empty block artifact");
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("empty certified machine");
        let accounting = CertifiedSingleBlockAccounting::from_certified(&certified)
            .expect("empty source accounting");
        let report = accounting.audit();

        assert!(report.has_exact_source_accounting(), "{report:?}");
        assert!(accounting.instructions().is_empty());
        assert!(accounting.mappings().is_empty());
        assert!(!report.has_residuals());
    }

    #[test]
    fn multiple_blocks_are_rejected_before_expression_lowering() {
        let mut entry = R2ILBlock::new(0x5200, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x5210, 8),
        });
        let empty = R2ILBlock::new(0x5210, 4);
        let artifact = SsaArtifact::raw(&[entry, empty], None).expect("two-block artifact");
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");

        assert!(matches!(
            CertifiedSingleBlockAccounting::from_certified(&certified),
            Err(RegionBuildError::MultipleBlocks(blocks))
                if blocks == BTreeSet::from([0x5200, 0x5210])
        ));
    }

    #[test]
    fn selected_multi_block_accounting_derives_exact_local_subset() {
        let entry_value = Varnode::unique(0x10, 8);
        let exit_value = Varnode::unique(0x18, 8);
        let mut entry = R2ILBlock::new(0x5250, 4);
        entry.push(R2ILOp::Copy {
            dst: entry_value.clone(),
            src: Varnode::constant(1, 8),
        });
        entry.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
            val: entry_value,
        });
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x5260, 8),
        });
        let mut exit = R2ILBlock::new(0x5260, 4);
        exit.push(R2ILOp::Copy {
            dst: exit_value.clone(),
            src: Varnode::constant(2, 8),
        });
        exit.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(8, 8),
            val: exit_value,
        });
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let artifact = SsaArtifact::raw(&[entry, exit], None).expect("two-block artifact");
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");

        for block_addr in [0x5250, 0x5260] {
            let accounting =
                CertifiedSingleBlockAccounting::from_certified_block(&certified, block_addr)
                    .expect("selected block accounting");
            let report = accounting.audit();
            let topology_block = certified
                .topology()
                .block(block_addr)
                .expect("selected topology block");
            let expected_obligations = topology_block
                .instructions()
                .iter()
                .map(|id| {
                    artifact
                        .obligations()
                        .instructions()
                        .get(id)
                        .expect("source instruction")
                        .obligations
                        .len()
                })
                .sum::<usize>();

            assert!(report.has_exact_source_accounting(), "{report:?}");
            assert_eq!(
                accounting.instructions().len(),
                topology_block.instructions().len()
            );
            assert_eq!(accounting.mappings().len(), expected_obligations);
            assert!(
                accounting
                    .instructions()
                    .iter()
                    .all(|instruction| instruction.source().block_addr == block_addr)
            );
        }
        assert!(matches!(
            CertifiedSingleBlockAccounting::from_certified_block(&certified, 0xdead),
            Err(RegionBuildError::MissingBlock(0xdead))
        ));
    }

    #[test]
    fn deleting_fnv_value_mapping_fails_region_audit() {
        let artifact = straight_line_artifact();
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let mut region =
            CertifiedSingleBlockAccounting::from_certified(&certified).expect("source accounting");
        let removed = region
            .mappings
            .iter()
            .position(|mapping| {
                mapping.obligation.kind == SemanticObligationKind::LiveValueProducer
            })
            .expect("live value mapping");
        let mut mappings = region.mappings.to_vec();
        let removed = mappings.remove(removed).obligation;
        region.mappings = mappings.into_boxed_slice();

        let report = region.audit();
        assert!(!report.has_exact_source_accounting());
        assert!(report.missing_obligations().contains(&removed));
    }

    #[test]
    fn duplicating_memory_write_mapping_fails_region_audit() {
        let artifact = straight_line_artifact();
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let mut region =
            CertifiedSingleBlockAccounting::from_certified(&certified).expect("source accounting");
        let duplicate = region
            .mappings
            .iter()
            .find(|mapping| {
                mapping.obligation.kind == SemanticObligationKind::ObservableMemoryWrite
            })
            .expect("memory write mapping")
            .clone();
        let duplicated_id = duplicate.obligation;
        let mut mappings = region.mappings.to_vec();
        mappings.push(duplicate);
        region.mappings = mappings.into_boxed_slice();

        let report = region.audit();
        assert!(!report.has_exact_source_accounting());
        assert!(report.duplicate_obligations().contains(&duplicated_id));
    }

    #[test]
    fn swapping_expression_producers_fails_region_audit() {
        let artifact = straight_line_artifact();
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let mut region =
            CertifiedSingleBlockAccounting::from_certified(&certified).expect("source accounting");
        let expression_indices = region
            .instructions
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| {
                instruction
                    .expression_producer
                    .map(|producer| (index, producer))
            })
            .collect::<Vec<_>>();
        let [
            (first_index, first_producer),
            (second_index, second_producer),
        ] = expression_indices[..]
        else {
            panic!("two expression producers expected");
        };
        region.instructions[first_index].expression_producer = Some(second_producer);
        region.instructions[second_index].expression_producer = Some(first_producer);
        for mapping in &mut region.mappings {
            if let RegionObligationDisposition::AbsorbedIntoExpression { producer } =
                &mut mapping.disposition
            {
                if *producer == first_producer {
                    *producer = second_producer;
                } else if *producer == second_producer {
                    *producer = first_producer;
                }
            }
        }

        let report = region.audit();
        assert!(!report.has_exact_source_accounting());
        assert!(
            report
                .invalid()
                .iter()
                .any(|reason| reason.contains("not bound to its semantic entity"))
        );
    }

    #[test]
    fn wrong_residual_reason_fails_region_audit() {
        let artifact = straight_line_artifact();
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let mut region =
            CertifiedSingleBlockAccounting::from_certified(&certified).expect("source accounting");
        let mapping = region
            .mappings
            .iter_mut()
            .find(|mapping| {
                mapping.obligation.kind == SemanticObligationKind::ObservableMemoryWrite
            })
            .expect("memory write mapping");
        mapping.disposition = RegionObligationDisposition::Residualized {
            reason: RegionResidualReason::ReturnRequiresCertifiedControl,
        };

        let report = region.audit();
        assert!(!report.has_exact_source_accounting());
        assert!(
            report
                .invalid()
                .iter()
                .any(|reason| reason.contains("wrong residual reason"))
        );
    }

    #[test]
    fn changing_region_block_address_fails_region_audit() {
        let artifact = straight_line_artifact();
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let mut region =
            CertifiedSingleBlockAccounting::from_certified(&certified).expect("source accounting");
        region.block_addr = 0xdead;

        let report = region.audit();
        assert!(!report.has_exact_source_accounting());
        assert!(
            report
                .invalid()
                .iter()
                .any(|reason| reason.contains("block address"))
        );
    }

    #[test]
    fn changing_instruction_state_or_source_order_fails_accounting() {
        let artifact = straight_line_artifact();
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let mut wrong_state =
            CertifiedSingleBlockAccounting::from_certified(&certified).expect("source accounting");
        wrong_state.instructions[0].state =
            if wrong_state.instructions[0].state == SemanticInstructionState::ProvenDead {
                SemanticInstructionState::LiveObligation
            } else {
                SemanticInstructionState::ProvenDead
            };
        assert!(!wrong_state.audit().has_exact_source_accounting());

        let mut wrong_order =
            CertifiedSingleBlockAccounting::from_certified(&certified).expect("source accounting");
        wrong_order.instructions.reverse();
        let report = wrong_order.audit();
        assert!(!report.has_exact_source_accounting());
        assert!(
            report
                .invalid()
                .iter()
                .any(|reason| reason.contains("source topology"))
        );
    }
}
