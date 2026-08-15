//! Whole-function machine proof for a two-arm private-frame value join.
//!
//! This certificate composes existing source-owned controls, stack regions,
//! MemorySSA value flows, ledger evidence, and topology. It creates no source
//! local, type, statement, AST node, or rendering permission.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    CanonicalInstructionId, InstPayload, SemanticInstructionState, SemanticObligationKind,
    SsaArtifact, StructuredAccessId, ValueId,
};
use serde::Serialize;

use super::{
    CERTIFICATION_SCHEMA_VERSION, CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION,
    CertifiedArtifactOrigin, CertifiedConditionalControl, CertifiedDirectControl,
    CertifiedFramePreservation, CertifiedLedgerClosure, CertifiedMemoryStatement,
    CertifiedMemoryStatementKind, CertifiedPrivateFrameStore, CertifiedPrivateFrameValueFlow,
    CertifiedReturnControl, CertifiedSourceTerminator, CertifiedSourceTopology,
    CertifiedStackDiscipline, CertifiedStackRelease, CertifiedTypedRegionKind, EffectDisposition,
    LedgerClosureError, ObligationLedger, TypedRegionMapping,
    exact_frame_pointer_storage_is_unused, exact_frame_restore_for_return,
    frame_statement_is_ledgered, replay_certified_frame_preservation,
    return_machine_state_matches_origin, try_certified_memory_statement,
};

/// One exact branch-only forwarding block in a conditional arm.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameTransparentBranch {
    block_addr: u64,
    control: CertifiedDirectControl,
}

/// Exact source-owned transfer from an arm's terminal store into the shared
/// join. A fallthrough carries topology only: it owns no control obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedPrivateFrameJoinTransfer {
    Direct(CertifiedDirectControl),
    Fallthrough { block_addr: u64, target: u64 },
}

impl CertifiedPrivateFrameJoinTransfer {
    pub const fn direct(&self) -> Option<&CertifiedDirectControl> {
        match self {
            Self::Direct(control) => Some(control),
            Self::Fallthrough { .. } => None,
        }
    }

    pub const fn block_addr(&self) -> u64 {
        match self {
            Self::Direct(control) => control.producer().block_addr,
            Self::Fallthrough { block_addr, .. } => *block_addr,
        }
    }

    pub const fn target(&self) -> u64 {
        match self {
            Self::Direct(control) => control.target(),
            Self::Fallthrough { target, .. } => *target,
        }
    }
}

impl CertifiedPrivateFrameTransparentBranch {
    pub const fn block_addr(&self) -> u64 {
        self.block_addr
    }

    pub const fn control(&self) -> &CertifiedDirectControl {
        &self.control
    }
}

/// One conditional arm ending in the exact store definition entering the
/// shared private-frame MemorySSA phi.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameConditionalArm {
    entry_target: u64,
    transparent: Box<[CertifiedPrivateFrameTransparentBranch]>,
    store_block: u64,
    store: CertifiedPrivateFrameStore,
    join_transfer: CertifiedPrivateFrameJoinTransfer,
}

impl CertifiedPrivateFrameConditionalArm {
    pub const fn entry_target(&self) -> u64 {
        self.entry_target
    }

    pub const fn transparent(&self) -> &[CertifiedPrivateFrameTransparentBranch] {
        &self.transparent
    }

    pub const fn store_block(&self) -> u64 {
        self.store_block
    }

    pub const fn store(&self) -> &CertifiedPrivateFrameStore {
        &self.store
    }

    pub const fn join_transfer(&self) -> &CertifiedPrivateFrameJoinTransfer {
        &self.join_transfer
    }
}

/// Exact ordinary SSA phi proven inert at the shared join.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedInertPrivateFrameJoinPhi {
    producer: CanonicalInstructionId,
    output: ValueId,
    predecessors: Box<[u64]>,
}

impl CertifiedInertPrivateFrameJoinPhi {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn output(&self) -> ValueId {
        self.output
    }

    pub const fn predecessors(&self) -> &[u64] {
        &self.predecessors
    }
}

/// Whole-function proof of a two-arm private-frame store join and its unique
/// terminal load/release/return. Auxiliary direct flows retain other exact
/// private regions used while computing the branch condition. When the exact
/// function actually uses a source-declared frame pointer through an exactly
/// certified save/restore sequence, the join also retains that replayed frame
/// certificate and the statements needed to close the function.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedPrivateFrameConditionalJoin {
    schema_version: u32,
    origin: CertifiedArtifactOrigin,
    header: u64,
    condition: CertifiedConditionalControl,
    true_arm: CertifiedPrivateFrameConditionalArm,
    false_arm: CertifiedPrivateFrameConditionalArm,
    join_block: u64,
    joined_flow: CertifiedPrivateFrameValueFlow,
    inert_join_phis: Box<[CertifiedInertPrivateFrameJoinPhi]>,
    auxiliary_direct_flows: Box<[(StructuredAccessId, CertifiedPrivateFrameValueFlow)]>,
    frame_preservation: Option<CertifiedFramePreservation>,
    release: CertifiedStackRelease,
    return_control: CertifiedReturnControl,
}

impl CertifiedPrivateFrameConditionalJoin {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn header(&self) -> u64 {
        self.header
    }

    pub const fn condition(&self) -> &CertifiedConditionalControl {
        &self.condition
    }

    pub const fn true_arm(&self) -> &CertifiedPrivateFrameConditionalArm {
        &self.true_arm
    }

    pub const fn false_arm(&self) -> &CertifiedPrivateFrameConditionalArm {
        &self.false_arm
    }

    pub const fn join_block(&self) -> u64 {
        self.join_block
    }

    pub const fn joined_flow(&self) -> &CertifiedPrivateFrameValueFlow {
        &self.joined_flow
    }

    pub const fn inert_join_phis(&self) -> &[CertifiedInertPrivateFrameJoinPhi] {
        &self.inert_join_phis
    }

    pub const fn auxiliary_direct_flows(
        &self,
    ) -> &[(StructuredAccessId, CertifiedPrivateFrameValueFlow)] {
        &self.auxiliary_direct_flows
    }

    pub const fn frame_preservation(&self) -> Option<&CertifiedFramePreservation> {
        self.frame_preservation.as_ref()
    }

    pub const fn release(&self) -> &CertifiedStackRelease {
        &self.release
    }

    pub const fn return_control(&self) -> &CertifiedReturnControl {
        &self.return_control
    }
}

fn direct_control_is_ledgered(control: &CertifiedDirectControl, ledger: &ObligationLedger) -> bool {
    matches!(ledger.effects(control.source_obligation()), [effect]
        if effect.direct_control_evidence() == Some(control)
            && matches!(effect.disposition(), EffectDisposition::AbsorbedIntoControl {
                producer
            } if *producer == control.producer()))
}

fn conditional_control_is_ledgered(
    control: &CertifiedConditionalControl,
    ledger: &ObligationLedger,
) -> bool {
    control.source_obligations().iter().all(|obligation| {
        matches!(ledger.effects(*obligation), [effect]
            if effect.conditional_control_evidence() == Some(control)
                && matches!(effect.disposition(), EffectDisposition::AbsorbedIntoControl {
                    producer
                } if *producer == control.producer()))
    })
}

fn return_control_is_ledgered(control: &CertifiedReturnControl, ledger: &ObligationLedger) -> bool {
    control.source_obligations().iter().all(|obligation| {
        matches!(ledger.effects(*obligation), [effect]
            if effect.return_control_evidence() == Some(control)
                && matches!(effect.disposition(), EffectDisposition::AbsorbedIntoReturn {
                    producer
                } if *producer == control.producer()))
    })
}

fn whole_source_ledger_is_exact(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
) -> bool {
    if !ledger.matches_origin(origin)
        || origin
            .source()
            .instructions()
            .values()
            .any(|instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown)
    {
        return false;
    }
    let report = ledger.audit(origin.source());
    report.has_exactly_one_disposition_per_source()
        && report.residualized().is_empty()
        && report.refused().is_empty()
        && report.invalid().is_empty()
}

struct PrivateFrameConditionalJoinLedgerBinding<'a> {
    producers: BTreeSet<CanonicalInstructionId>,
    statements: BTreeMap<CanonicalInstructionId, &'a CertifiedMemoryStatement>,
    direct_controls: BTreeMap<CanonicalInstructionId, &'a CertifiedDirectControl>,
    condition: &'a CertifiedConditionalControl,
    return_control: &'a CertifiedReturnControl,
}

fn private_frame_conditional_join_ledger_binding<'a>(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    join: &'a CertifiedPrivateFrameConditionalJoin,
) -> Option<PrivateFrameConditionalJoinLedgerBinding<'a>> {
    let interface = origin.machine_context().source().function_interface()?;
    let frame = join.frame_preservation();
    if join.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || join.origin() != origin
        || origin.topology().entry_addr() != join.header()
        || join.condition().producer().block_addr != join.header()
        || join.return_control().producer().block_addr != join.join_block()
        || join.release().return_control() != join.return_control()
        || join.joined_flow().schema_version() != CERTIFICATION_SCHEMA_VERSION
        || join.joined_flow().origin() != origin
        || join.auxiliary_direct_flows().iter().any(|(access, flow)| {
            flow.schema_version() != CERTIFICATION_SCHEMA_VERSION
                || flow.origin() != origin
                || *access != flow.load().statement().access()
        })
        || join.condition().validate(origin.source()).is_err()
        || join.return_control().validate(origin.source()).is_err()
    {
        return None;
    }
    if let Some(frame) = frame {
        let restore = exact_frame_restore_for_return(origin, frame, join.return_control())?;
        if replay_certified_frame_preservation(artifact, origin, ledger).as_ref() != Some(frame)
            || frame.restores().len() != 1
            || interface.exact_frame_pointer_storage() != Some(frame.frame_pointer_storage())
            || interface.stack_pointer_storage() != Some(frame.stack_pointer_storage())
            || restore.return_address_read() != join.release().return_address_read()
            || frame.entry_save().producer().block_addr != join.header()
            || restore.restore_read().producer().block_addr != join.join_block()
        {
            return None;
        }
    } else if interface
        .exact_frame_pointer_storage()
        .is_some_and(|storage| !exact_frame_pointer_storage_is_unused(artifact, storage))
    {
        return None;
    }
    for arm in [join.true_arm(), join.false_arm()] {
        let block = origin.topology().block(arm.store_block())?;
        if arm.store().statement().producer().block_addr != arm.store_block()
            || arm.join_transfer().block_addr() != arm.store_block()
            || arm.join_transfer().target() != join.join_block()
            || block.predecessors().len() != 1
            || block.successors() != [join.join_block()]
        {
            return None;
        }
        match arm.join_transfer() {
            CertifiedPrivateFrameJoinTransfer::Direct(control) => {
                if !matches!(block.terminator(), CertifiedSourceTerminator::Branch { target }
                    if *target == join.join_block())
                    || control.producer().block_addr != arm.store_block()
                {
                    return None;
                }
            }
            CertifiedPrivateFrameJoinTransfer::Fallthrough { block_addr, target } => {
                if *block_addr != arm.store_block()
                    || *target != join.join_block()
                    || !matches!(block.terminator(), CertifiedSourceTerminator::Fallthrough { next }
                        if *next == join.join_block())
                    || block.instructions().last() != Some(&arm.store().statement().producer())
                {
                    return None;
                }
            }
        }
    }
    let producers = origin
        .topology()
        .blocks()
        .iter()
        .flat_map(|block| block.instructions())
        .copied()
        .collect::<BTreeSet<_>>();
    let mut statements = BTreeMap::new();
    for statement in std::iter::once(join.joined_flow())
        .chain(join.auxiliary_direct_flows().iter().map(|(_, flow)| flow))
        .flat_map(|flow| flow.region().accesses())
        .map(|access| access.statement())
        .chain(join.release().return_address_read())
        .chain(frame.into_iter().flat_map(|frame| {
            std::iter::once(frame.entry_save()).chain(
                frame
                    .restores()
                    .iter()
                    .map(|restore| restore.restore_read()),
            )
        }))
    {
        if !producers.contains(&statement.producer())
            || statement.validate(origin.source()).is_err()
            || try_certified_memory_statement(artifact, statement.access().inst)
                .ok()
                .flatten()
                .as_ref()
                != Some(statement)
            || statements
                .insert(statement.producer(), statement)
                .is_some_and(|previous| previous != statement)
        {
            return None;
        }
    }
    let mut direct_controls = BTreeMap::new();
    for control in join
        .true_arm()
        .transparent()
        .iter()
        .map(|branch| branch.control())
        .chain(join.true_arm().join_transfer().direct())
        .chain(
            join.false_arm()
                .transparent()
                .iter()
                .map(|branch| branch.control()),
        )
        .chain(join.false_arm().join_transfer().direct())
    {
        if !producers.contains(&control.producer())
            || control.validate(origin.source()).is_err()
            || direct_controls
                .insert(control.producer(), control)
                .is_some()
        {
            return None;
        }
    }
    producers
        .contains(&join.condition().producer())
        .then_some(())?;
    producers
        .contains(&join.return_control().producer())
        .then_some(())?;
    Some(PrivateFrameConditionalJoinLedgerBinding {
        producers,
        statements,
        direct_controls,
        condition: join.condition(),
        return_control: join.return_control(),
    })
}

fn certify_private_frame_conditional_join_region_binding(
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: Vec<TypedRegionMapping>,
    binding: &PrivateFrameConditionalJoinLedgerBinding<'_>,
) -> Result<CertifiedLedgerClosure, LedgerClosureError> {
    if !origin.is_valid()
        || !ledger.matches_origin(origin)
        || !return_machine_state_matches_origin(origin, ledger)
    {
        return Err(LedgerClosureError::InvalidOrigin);
    }
    let report = ledger.audit(origin.source());
    if !report.has_exactly_one_disposition_per_source() || !report.invalid().is_empty() {
        return Err(LedgerClosureError::IncompleteLedger);
    }
    if let Some(obligation) = report.residualized().iter().chain(report.refused()).next() {
        return Err(LedgerClosureError::ResidualOrRefusedObligation(*obligation));
    }
    if let Some(instruction) = origin
        .source()
        .instructions()
        .values()
        .find(|instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown)
    {
        return Err(LedgerClosureError::UnsupportedSourceSemantics(
            instruction.id,
        ));
    }

    let mut by_obligation = BTreeMap::new();
    for mapping in &mappings {
        if !origin
            .source()
            .obligations()
            .contains_key(&mapping.obligation())
        {
            return Err(LedgerClosureError::UnexpectedMapping(mapping.obligation()));
        }
        if by_obligation
            .insert(mapping.obligation(), mapping)
            .is_some()
        {
            return Err(LedgerClosureError::DuplicateMapping(mapping.obligation()));
        }
    }

    for obligation in origin.source().obligations().values() {
        let [effect] = ledger.effects(obligation.id) else {
            return Err(LedgerClosureError::IncompleteLedger);
        };
        let producer = obligation.id.instruction;
        let valid = match obligation.id.kind {
            SemanticObligationKind::LiveValueProducer => {
                binding.producers.contains(&producer)
                    && effect
                        .expression_evidence()
                        .is_some_and(|expression| expression.entity().producer() == producer)
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoExpression { producer: owner }
                            if *owner == producer
                    )
            }
            SemanticObligationKind::ObservableMemoryRead
            | SemanticObligationKind::ObservableMemoryWrite => {
                binding
                    .statements
                    .get(&producer)
                    .is_some_and(|statement| effect.statement_evidence() == Some(*statement))
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoStatement { producer: owner }
                            if *owner == producer
                    )
            }
            SemanticObligationKind::ControlPredicate => {
                effect.conditional_control_evidence() == Some(binding.condition)
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoControl { producer: owner }
                            if *owner == binding.condition.producer()
                    )
            }
            SemanticObligationKind::ControlTransfer => {
                let conditional = effect.conditional_control_evidence() == Some(binding.condition);
                let direct = binding
                    .direct_controls
                    .get(&producer)
                    .is_some_and(|control| effect.direct_control_evidence() == Some(*control));
                (conditional || direct)
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoControl { producer: owner }
                            if *owner == producer
                    )
            }
            SemanticObligationKind::Return | SemanticObligationKind::ReturnValue => {
                effect.return_control_evidence() == Some(binding.return_control)
                    && matches!(
                        effect.disposition(),
                        EffectDisposition::AbsorbedIntoReturn { producer: owner }
                            if *owner == binding.return_control.producer()
                    )
            }
            _ => false,
        };
        if !valid {
            return Err(LedgerClosureError::InvalidRegionDisposition(obligation.id));
        }
        let mapping = by_obligation
            .get(&obligation.id)
            .ok_or(LedgerClosureError::MissingMapping(obligation.id))?;
        if mapping.source_disposition() != effect.disposition()
            || matches!(
                mapping.source_disposition(),
                EffectDisposition::Residualized { .. } | EffectDisposition::Refused { .. }
            )
        {
            return Err(LedgerClosureError::DispositionMismatch(obligation.id));
        }
    }

    Ok(CertifiedLedgerClosure {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        region_kind: CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction,
        region_schema_version: CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION,
        mappings: mappings.into_boxed_slice(),
    })
}

/// Close the exact source obligation ledger for one already-sealed private
/// frame conditional join. This grants no rendering permission.
pub fn certify_private_frame_conditional_join_region(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    mappings: impl IntoIterator<Item = TypedRegionMapping>,
    join: &CertifiedPrivateFrameConditionalJoin,
) -> Result<CertifiedLedgerClosure, LedgerClosureError> {
    if !origin.is_valid()
        || origin.authority.artifact.as_ref() != Some(artifact.authority())
        || origin.source() != artifact.obligations()
        || !ledger.matches_origin(origin)
        || !return_machine_state_matches_origin(origin, ledger)
    {
        return Err(LedgerClosureError::InvalidOrigin);
    }
    let binding = private_frame_conditional_join_ledger_binding(artifact, origin, ledger, join)
        .ok_or(LedgerClosureError::InvalidRegionTopology)?;
    certify_private_frame_conditional_join_region_binding(
        origin,
        ledger,
        mappings.into_iter().collect(),
        &binding,
    )
}

fn exact_release_return_address_read(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    release: &CertifiedStackRelease,
    join: u64,
) -> Option<Option<CanonicalInstructionId>> {
    let Some(read) = release.return_address_read() else {
        return Some(None);
    };
    exact_return_address_read_producer(artifact, origin, ledger, read, join).map(Some)
}

fn exact_return_address_read_producer(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    ledger: &ObligationLedger,
    read: &super::CertifiedMemoryStatement,
    join: u64,
) -> Option<CanonicalInstructionId> {
    let replayed = try_certified_memory_statement(artifact, read.access().inst)
        .ok()
        .flatten()?;
    (replayed == *read
        && read.validate(origin.source()).is_ok()
        && frame_statement_is_ledgered(read, ledger)
        && read.producer().block_addr == join
        && matches!(read.kind(), CertifiedMemoryStatementKind::Read { .. }))
    .then_some(read.producer())
}

fn direct_controls_by_block<'a>(
    controls: &'a BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
) -> Option<BTreeMap<u64, &'a CertifiedDirectControl>> {
    let mut by_block = BTreeMap::new();
    for control in controls.values() {
        if by_block
            .insert(control.producer().block_addr, control)
            .is_some()
        {
            return None;
        }
    }
    Some(by_block)
}

fn exact_branch_block(
    topology: &CertifiedSourceTopology,
    block_addr: u64,
    expected_predecessor: u64,
    expected_target: u64,
    control: &CertifiedDirectControl,
    branch_only: bool,
) -> bool {
    let Some(block) = topology.block(block_addr) else {
        return false;
    };
    block.predecessors() == [expected_predecessor]
        && block.successors() == [expected_target]
        && matches!(block.terminator(), CertifiedSourceTerminator::Branch { target }
            if *target == expected_target)
        && control.producer().block_addr == block_addr
        && control.target() == expected_target
        && (!branch_only || block.instructions() == [control.producer()])
}

fn certify_arm(
    source: &r2ssa::SemanticObligationInventory,
    topology: &CertifiedSourceTopology,
    start: u64,
    header: u64,
    terminal: u64,
    join: u64,
    store: &CertifiedPrivateFrameStore,
    controls: &BTreeMap<u64, &CertifiedDirectControl>,
    ledger: &ObligationLedger,
) -> Option<CertifiedPrivateFrameConditionalArm> {
    if store.statement().producer().block_addr != terminal
        || !matches!(
            store.statement().kind(),
            CertifiedMemoryStatementKind::Write { .. }
        )
    {
        return None;
    }
    let (transparent, transfer) = certify_arm_route(
        source,
        topology,
        start,
        header,
        terminal,
        join,
        store.statement().producer(),
        controls,
        ledger,
    )?;
    Some(CertifiedPrivateFrameConditionalArm {
        entry_target: start,
        transparent,
        store_block: terminal,
        store: store.clone(),
        join_transfer: transfer,
    })
}

fn certify_arm_route(
    source: &r2ssa::SemanticObligationInventory,
    topology: &CertifiedSourceTopology,
    start: u64,
    header: u64,
    terminal: u64,
    join: u64,
    store_producer: CanonicalInstructionId,
    controls: &BTreeMap<u64, &CertifiedDirectControl>,
    ledger: &ObligationLedger,
) -> Option<(
    Box<[CertifiedPrivateFrameTransparentBranch]>,
    CertifiedPrivateFrameJoinTransfer,
)> {
    let mut current = start;
    let mut predecessor = header;
    let mut seen = BTreeSet::new();
    let mut transparent = Vec::new();
    while current != terminal {
        if current == header || current == join || !seen.insert(current) {
            return None;
        }
        let control = *controls.get(&current)?;
        if control.validate(source).is_err()
            || !direct_control_is_ledgered(control, ledger)
            || !exact_branch_block(
                topology,
                current,
                predecessor,
                control.target(),
                control,
                true,
            )
        {
            return None;
        }
        transparent.push(CertifiedPrivateFrameTransparentBranch {
            block_addr: current,
            control: control.clone(),
        });
        predecessor = current;
        current = control.target();
    }
    if !seen.insert(terminal) {
        return None;
    }
    let block = topology.block(terminal)?;
    if block.predecessors() != [predecessor] || block.successors() != [join] {
        return None;
    }
    let transfer = match block.terminator() {
        CertifiedSourceTerminator::Branch { target } if *target == join => {
            let control = *controls.get(&terminal)?;
            if control.validate(source).is_err()
                || !direct_control_is_ledgered(control, ledger)
                || !exact_branch_block(topology, terminal, predecessor, join, control, false)
            {
                return None;
            }
            CertifiedPrivateFrameJoinTransfer::Direct(control.clone())
        }
        CertifiedSourceTerminator::Fallthrough { next }
            if *next == join
                && !controls.contains_key(&terminal)
                && block.instructions().last() == Some(&store_producer) =>
        {
            CertifiedPrivateFrameJoinTransfer::Fallthrough {
                block_addr: terminal,
                target: join,
            }
        }
        _ => return None,
    };
    Some((transparent.into_boxed_slice(), transfer))
}

fn joined_flow_stores(
    flow: &CertifiedPrivateFrameValueFlow,
) -> Option<(u64, [(u64, CertifiedPrivateFrameStore); 2])> {
    let root = flow.definition(flow.root_version())?.phi()?;
    if flow.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || flow.definitions().len() != 3
        || root.inputs().len() != 2
        || flow.load().statement().producer().block_addr != root.block_addr()
        || !matches!(
            flow.load().statement().kind(),
            CertifiedMemoryStatementKind::Read { .. }
        )
        || flow.region().accesses().len() != 3
    {
        return None;
    }
    let mut stores = Vec::new();
    for input in root.inputs() {
        let store = flow.definition(input.version())?.store()?;
        if store.next_version() != input.version()
            || store.statement().producer().block_addr != input.predecessor()
        {
            return None;
        }
        stores.push((input.predecessor(), store.clone()));
    }
    let [first, second] = stores.as_slice() else {
        return None;
    };
    let covered = flow
        .region()
        .accesses()
        .iter()
        .map(|access| access.statement().access())
        .collect::<BTreeSet<_>>();
    let expected = BTreeSet::from([
        first.1.statement().access(),
        second.1.statement().access(),
        flow.load().statement().access(),
    ]);
    (covered == expected).then(|| (root.block_addr(), [first.clone(), second.clone()]))
}

fn direct_flow_is_exact(flow: &CertifiedPrivateFrameValueFlow) -> bool {
    if flow.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || flow.definitions().len() != 1
        || flow.region().accesses().len() != 2
        || !matches!(
            flow.load().statement().kind(),
            CertifiedMemoryStatementKind::Read { .. }
        )
    {
        return false;
    }
    let Some(store) = flow
        .definition(flow.root_version())
        .and_then(|definition| definition.store())
    else {
        return false;
    };
    flow.root_version() == store.next_version()
        && flow
            .region()
            .accesses()
            .iter()
            .map(|access| access.statement().access())
            .collect::<BTreeSet<_>>()
            == BTreeSet::from([store.statement().access(), flow.load().statement().access()])
}

fn inert_join_phis(
    artifact: &SsaArtifact,
    topology: &CertifiedSourceTopology,
    join: u64,
) -> Option<Vec<CertifiedInertPrivateFrameJoinPhi>> {
    let graph = artifact.graph();
    let block = graph.block(*graph.block_by_addr.get(&join)?)?;
    let expected_predecessors = topology.block(join)?.predecessors();
    let mut inert = Vec::new();
    for instruction in &graph.insts {
        let InstPayload::Phi { predecessors } = &instruction.payload else {
            continue;
        };
        let owner = graph.block(instruction.block)?;
        if owner.addr != join || instruction.canonical_storage.is_none() {
            return None;
        }
        let actual_predecessors = predecessors
            .iter()
            .map(|predecessor| graph.block(*predecessor).map(|block| block.addr))
            .collect::<Option<Vec<_>>>()?;
        let output = instruction.output?;
        let disposition = artifact
            .obligations()
            .instruction_for_inst(instruction.id)?;
        if owner.id != block.id
            || actual_predecessors != expected_predecessors
            || disposition.state != SemanticInstructionState::ProvenDead
            || !disposition.obligations.is_empty()
            || !graph.use_sites(output).is_empty()
        {
            return None;
        }
        inert.push(CertifiedInertPrivateFrameJoinPhi {
            producer: disposition.id,
            output,
            predecessors: actual_predecessors.into_boxed_slice(),
        });
    }
    Some(inert)
}

fn proven_dead_subgraph_is_closed(
    artifact: &SsaArtifact,
    producer: CanonicalInstructionId,
    memo: &mut BTreeMap<CanonicalInstructionId, bool>,
    visiting: &mut BTreeSet<CanonicalInstructionId>,
) -> bool {
    if let Some(closed) = memo.get(&producer) {
        return *closed;
    }
    if !visiting.insert(producer) {
        return false;
    }
    let closed = (|| {
        let source = artifact.obligations();
        let instruction = source.instructions().get(&producer)?;
        if instruction.state != SemanticInstructionState::ProvenDead
            || !instruction.obligations.is_empty()
        {
            return None;
        }
        let inst_id = instruction.source.graph_inst()?;
        if source.instruction_for_inst(inst_id) != Some(instruction) {
            return None;
        }
        let graph = artifact.graph();
        let inst = graph.inst(inst_id)?;
        let Some(output) = inst.output else {
            return Some(true);
        };
        if graph.def_inst(output) != Some(inst_id) {
            return None;
        }
        for use_site in graph.use_sites(output) {
            let consumer = graph.inst(use_site.inst)?;
            if consumer.inputs.get(use_site.input_idx) != Some(&output) {
                return None;
            }
            let consumer_disposition = source.instruction_for_inst(consumer.id)?;
            if !proven_dead_subgraph_is_closed(artifact, consumer_disposition.id, memo, visiting) {
                return None;
            }
        }
        Some(true)
    })()
    .unwrap_or(false);
    visiting.remove(&producer);
    memo.insert(producer, closed);
    closed
}

fn expression_or_dead_instruction_is_closed(
    artifact: &SsaArtifact,
    producer: CanonicalInstructionId,
    ledger: &ObligationLedger,
) -> bool {
    let Some(instruction) = artifact.obligations().instructions().get(&producer) else {
        return false;
    };
    match instruction.state {
        SemanticInstructionState::ProvenDead => proven_dead_subgraph_is_closed(
            artifact,
            producer,
            &mut BTreeMap::new(),
            &mut BTreeSet::new(),
        ),
        SemanticInstructionState::LiveObligation => {
            !instruction.obligations.is_empty()
                && instruction.obligations.iter().all(|obligation| {
                    matches!(ledger.effects(*obligation), [effect]
                    if effect.expression_evidence().is_some_and(|expression| {
                        expression.entity().producer() == producer
                    }) && matches!(effect.disposition(), EffectDisposition::AbsorbedIntoExpression {
                        producer: owner
                    } if *owner == producer))
                })
        }
        SemanticInstructionState::StructuralControlOnly
        | SemanticInstructionState::UnsupportedUnknown => false,
    }
}

fn exact_private_access_coverage(
    stack: &CertifiedStackDiscipline,
    all_flows: &BTreeMap<StructuredAccessId, CertifiedPrivateFrameValueFlow>,
    primary_key: StructuredAccessId,
    primary: &CertifiedPrivateFrameValueFlow,
) -> Option<Vec<(StructuredAccessId, CertifiedPrivateFrameValueFlow)>> {
    let mut selected = BTreeSet::from([primary_key]);
    let mut auxiliary = Vec::new();
    for region in stack.private_regions() {
        if region == primary.region() {
            continue;
        }
        let matching = all_flows
            .iter()
            .filter(|(access, flow)| {
                **access == flow.load().statement().access()
                    && flow.region() == region
                    && direct_flow_is_exact(flow)
            })
            .collect::<Vec<_>>();
        let [(access, flow)] = matching.as_slice() else {
            return None;
        };
        selected.insert(**access);
        auxiliary.push((**access, (*flow).clone()));
    }
    if selected.len() != all_flows.len()
        || selected
            .iter()
            .any(|access| !all_flows.contains_key(access))
    {
        return None;
    }
    let stack_accesses = stack
        .private_regions()
        .iter()
        .flat_map(|region| region.accesses())
        .map(|access| access.statement().access())
        .collect::<BTreeSet<_>>();
    let selected_accesses = std::iter::once(primary)
        .chain(auxiliary.iter().map(|(_, flow)| flow))
        .flat_map(|flow| flow.region().accesses())
        .map(|access| access.statement().access())
        .collect::<BTreeSet<_>>();
    (stack_accesses == selected_accesses).then_some(auxiliary)
}

fn certify_conditional_join(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
    stack: &CertifiedStackDiscipline,
    frame: Option<&CertifiedFramePreservation>,
    flows: &BTreeMap<StructuredAccessId, CertifiedPrivateFrameValueFlow>,
    direct_controls: &BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
    conditional: &CertifiedConditionalControl,
    return_control: &CertifiedReturnControl,
    ledger: &ObligationLedger,
) -> Option<CertifiedPrivateFrameConditionalJoin> {
    if !origin.is_valid()
        || origin.authority.artifact.as_ref() != Some(artifact.authority())
        || origin.source() != artifact.obligations()
        || !whole_source_ledger_is_exact(origin, ledger)
        || stack.origin() != origin
        || stack.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || topology != origin.topology()
        || flows.values().any(|flow| flow.origin() != origin)
        || !conditional.validate(origin.source()).is_ok()
        || !conditional_control_is_ledgered(conditional, ledger)
        || !return_control.validate(origin.source()).is_ok()
        || !return_control_is_ledgered(return_control, ledger)
        || conditional.producer().block_addr != topology.entry_addr()
    {
        return None;
    }
    let interface = origin.machine_context().source().function_interface()?;
    if frame.is_none()
        && interface
            .exact_frame_pointer_storage()
            .is_some_and(|storage| !exact_frame_pointer_storage_is_unused(artifact, storage))
    {
        return None;
    }
    let frame_restore = if let Some(frame) = frame {
        let restore = exact_frame_restore_for_return(origin, frame, return_control)?;
        if replay_certified_frame_preservation(artifact, origin, ledger).as_ref() != Some(frame)
            || frame.restores().len() != 1
            || interface.exact_frame_pointer_storage() != Some(frame.frame_pointer_storage())
            || interface.stack_pointer_storage() != Some(frame.stack_pointer_storage())
            || stack.stack_pointer_storage() != frame.stack_pointer_storage()
        {
            return None;
        }
        Some(restore)
    } else {
        None
    };
    let header = conditional.producer().block_addr;
    let header_block = topology.block(header)?;
    if !header_block.predecessors().is_empty()
        || header_block.successors() != [conditional.true_target(), conditional.false_target()]
        || !matches!(header_block.terminator(), CertifiedSourceTerminator::ConditionalBranch {
            true_target,
            false_target,
        } if *true_target == conditional.true_target() && *false_target == conditional.false_target())
    {
        return None;
    }
    let joined = flows
        .iter()
        .filter_map(|(access, flow)| {
            (*access == flow.load().statement().access())
                .then(|| joined_flow_stores(flow))
                .flatten()
                .map(|shape| (*access, flow, shape))
        })
        .collect::<Vec<_>>();
    let [(primary_key, primary, (join, stores))] = joined.as_slice() else {
        return None;
    };
    let join_block = topology.block(*join)?;
    if join_block.predecessors() != [stores[0].0, stores[1].0]
        || !join_block.successors().is_empty()
        || !matches!(join_block.terminator(), CertifiedSourceTerminator::Return)
        || return_control.producer().block_addr != *join
    {
        return None;
    }
    let controls = direct_controls_by_block(direct_controls)?;
    let store_by_block = BTreeMap::from([
        (stores[0].0, stores[0].1.clone()),
        (stores[1].0, stores[1].1.clone()),
    ]);
    if store_by_block.len() != 2 {
        return None;
    }
    let true_terminal = arm_terminal(topology, conditional.true_target(), *join, &store_by_block)?;
    let false_terminal =
        arm_terminal(topology, conditional.false_target(), *join, &store_by_block)?;
    if true_terminal == false_terminal {
        return None;
    }
    let true_arm = certify_arm(
        origin.source(),
        topology,
        conditional.true_target(),
        header,
        true_terminal,
        *join,
        store_by_block.get(&true_terminal)?,
        &controls,
        ledger,
    )?;
    let false_arm = certify_arm(
        origin.source(),
        topology,
        conditional.false_target(),
        header,
        false_terminal,
        *join,
        store_by_block.get(&false_terminal)?,
        &controls,
        ledger,
    )?;
    let selected_direct = true_arm
        .transparent()
        .iter()
        .map(|branch| branch.control().producer())
        .chain(
            true_arm
                .join_transfer()
                .direct()
                .map(|control| control.producer()),
        )
        .chain(
            false_arm
                .transparent()
                .iter()
                .map(|branch| branch.control().producer()),
        )
        .chain(
            false_arm
                .join_transfer()
                .direct()
                .map(|control| control.producer()),
        )
        .collect::<BTreeSet<_>>();
    if selected_direct != direct_controls.keys().copied().collect() {
        return None;
    }
    let mut owned_blocks = BTreeSet::from([header, *join]);
    owned_blocks.extend(
        true_arm
            .transparent()
            .iter()
            .map(|branch| branch.block_addr()),
    );
    owned_blocks.insert(true_arm.store_block());
    owned_blocks.extend(
        false_arm
            .transparent()
            .iter()
            .map(|branch| branch.block_addr()),
    );
    owned_blocks.insert(false_arm.store_block());
    if owned_blocks.len() != topology.blocks().len()
        || owned_blocks != topology.blocks().iter().map(|block| block.addr()).collect()
    {
        return None;
    }
    let inert_join_phis = inert_join_phis(artifact, topology, *join)?;
    let auxiliary = exact_private_access_coverage(stack, flows, *primary_key, primary)?;
    if auxiliary.iter().any(|(_, flow)| {
        flow.region()
            .accesses()
            .iter()
            .any(|access| access.statement().producer().block_addr != header)
    }) {
        return None;
    }
    let [release] = stack.releases() else {
        return None;
    };
    if release.return_control() != return_control {
        return None;
    }
    let return_address_read =
        exact_release_return_address_read(artifact, origin, ledger, release, *join)?;
    if let Some(restore) = frame_restore {
        let frame = frame?;
        if restore.return_address_read() != release.return_address_read()
            || frame.entry_save().producer().block_addr != header
            || restore.restore_read().producer().block_addr != *join
        {
            return None;
        }
        for statement in [frame.entry_save(), restore.restore_read()] {
            if statement.validate(origin.source()).is_err()
                || try_certified_memory_statement(artifact, statement.access().inst)
                    .ok()
                    .flatten()
                    .as_ref()
                    != Some(statement)
                || !frame_statement_is_ledgered(statement, ledger)
            {
                return None;
            }
        }
    }
    let known = std::iter::once(conditional.producer())
        .chain(selected_direct)
        .chain(
            stack
                .private_regions()
                .iter()
                .flat_map(|region| region.accesses())
                .map(|access| access.statement().producer()),
        )
        .chain(std::iter::once(return_control.producer()))
        .chain(return_address_read)
        .chain(frame.into_iter().flat_map(|frame| {
            std::iter::once(frame.entry_save().producer()).chain(
                frame
                    .restores()
                    .iter()
                    .map(|restore| restore.restore_read().producer()),
            )
        }))
        .chain(inert_join_phis.iter().map(|phi| phi.producer()))
        .collect::<BTreeSet<_>>();
    if topology
        .blocks()
        .iter()
        .flat_map(|block| block.instructions())
        .any(|producer| {
            !known.contains(producer)
                && !expression_or_dead_instruction_is_closed(artifact, *producer, ledger)
        })
    {
        return None;
    }
    Some(CertifiedPrivateFrameConditionalJoin {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        origin: origin.clone(),
        header,
        condition: conditional.clone(),
        true_arm,
        false_arm,
        join_block: *join,
        joined_flow: (*primary).clone(),
        inert_join_phis: inert_join_phis.into_boxed_slice(),
        auxiliary_direct_flows: auxiliary.into_boxed_slice(),
        frame_preservation: frame.cloned(),
        release: release.clone(),
        return_control: return_control.clone(),
    })
}

fn arm_terminal(
    topology: &CertifiedSourceTopology,
    start: u64,
    join: u64,
    stores: &BTreeMap<u64, CertifiedPrivateFrameStore>,
) -> Option<u64> {
    let mut current = start;
    let mut seen = BTreeSet::new();
    while !stores.contains_key(&current) {
        if current == join || !seen.insert(current) {
            return None;
        }
        let CertifiedSourceTerminator::Branch { target } = topology.block(current)?.terminator()
        else {
            return None;
        };
        current = *target;
    }
    Some(current)
}

pub(super) fn certified_private_frame_conditional_joins(
    artifact: &SsaArtifact,
    origin: &CertifiedArtifactOrigin,
    topology: &CertifiedSourceTopology,
    stack: Option<&CertifiedStackDiscipline>,
    frame: Option<&CertifiedFramePreservation>,
    flows: &BTreeMap<StructuredAccessId, CertifiedPrivateFrameValueFlow>,
    direct_controls: &BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
    conditional_controls: &BTreeMap<CanonicalInstructionId, CertifiedConditionalControl>,
    return_controls: &BTreeMap<CanonicalInstructionId, CertifiedReturnControl>,
    ledger: &ObligationLedger,
) -> BTreeMap<u64, CertifiedPrivateFrameConditionalJoin> {
    let Some(stack) = stack else {
        return BTreeMap::new();
    };
    let conditional_values = conditional_controls.values().collect::<Vec<_>>();
    let return_values = return_controls.values().collect::<Vec<_>>();
    let ([conditional], [return_control]) =
        (conditional_values.as_slice(), return_values.as_slice())
    else {
        return BTreeMap::new();
    };
    let Some(join) = certify_conditional_join(
        artifact,
        origin,
        topology,
        stack,
        frame,
        flows,
        direct_controls,
        conditional,
        return_control,
        ledger,
    ) else {
        return BTreeMap::new();
    };
    BTreeMap::from([(join.header(), join)])
}

#[cfg(test)]
mod tests {
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageId, CanonicalStorageSpace, MachineProjection, SemanticObligationKind,
        SourceFunctionInterface, SourceFunctionReturn, SsaArtifact,
    };

    use super::*;
    use crate::{
        CertifiedAuthoritySeal, CertifiedFunction, CertifiedMachineContext,
        GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION, certified_conditional_controls,
        certified_direct_controls, certified_return_controls, certified_source_topology,
    };

    fn instruction_id(artifact: &SsaArtifact, index: usize) -> CanonicalInstructionId {
        let inst = artifact.graph().insts[index].id;
        artifact
            .obligations()
            .instruction_for_inst(inst)
            .expect("canonical instruction disposition")
            .id
    }

    #[test]
    fn proven_dead_closure_traverses_only_finite_all_dead_use_graphs() {
        let first = Varnode::unique(0x100, 8);
        let second = Varnode::unique(0x108, 8);
        let mut dead_chain = R2ILBlock::new(0x1000, 4);
        dead_chain.push(R2ILOp::Copy {
            dst: first.clone(),
            src: Varnode::constant(1, 8),
        });
        dead_chain.push(R2ILOp::Copy {
            dst: second.clone(),
            src: first.clone(),
        });
        let artifact = SsaArtifact::raw(&[dead_chain], None).expect("dead copy chain");
        assert!(proven_dead_subgraph_is_closed(
            &artifact,
            instruction_id(&artifact, 0),
            &mut BTreeMap::new(),
            &mut BTreeSet::new(),
        ));

        let mut live_endpoint = R2ILBlock::new(0x1010, 4);
        live_endpoint.push(R2ILOp::Copy {
            dst: first.clone(),
            src: Varnode::constant(1, 8),
        });
        live_endpoint.push(R2ILOp::Copy {
            dst: second,
            src: first,
        });
        live_endpoint.push(R2ILOp::Return {
            target: Varnode::unique(0x108, 8),
        });
        let artifact = SsaArtifact::raw(&[live_endpoint], None).expect("live copy endpoint");
        assert!(!proven_dead_subgraph_is_closed(
            &artifact,
            instruction_id(&artifact, 0),
            &mut BTreeMap::new(),
            &mut BTreeSet::new(),
        ));
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum RouteMutation {
        None,
        TransparentPayload,
        WrongTerminalTarget,
        TrueFallthrough,
        FallthroughWrongNext,
        FallthroughNonfinalStore,
        UseJoinPhi,
        UnsupportedSource,
        ReturnAddressRead,
    }

    struct RouteFixture {
        artifact: SsaArtifact,
        origin: CertifiedArtifactOrigin,
        topology: CertifiedSourceTopology,
        ledger: ObligationLedger,
        direct: BTreeMap<CanonicalInstructionId, CertifiedDirectControl>,
        conditional: CertifiedConditionalControl,
        return_control: Option<CertifiedReturnControl>,
        statements: BTreeMap<CanonicalInstructionId, super::super::CertifiedMemoryStatement>,
        return_address_read: Option<super::super::CertifiedMemoryStatement>,
    }

    fn route_fixture(with_chain: bool, mutation: RouteMutation) -> RouteFixture {
        let true_target = if with_chain { 0x5008 } else { 0x5010 };
        let mut header = R2ILBlock::new(0x5000, 4);
        let condition = Varnode::unique(0x80, 1);
        header.push(R2ILOp::Copy {
            dst: condition.clone(),
            src: Varnode::constant(1, 1),
        });
        header.push(R2ILOp::CBranch {
            target: Varnode::ram(true_target, 8),
            cond: condition,
        });

        let shared = Varnode::unique(0x100, 4);
        let mut false_terminal = R2ILBlock::new(0x5004, 4);
        false_terminal.push(R2ILOp::Copy {
            dst: shared.clone(),
            src: Varnode::constant(0, 4),
        });
        false_terminal.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x8000, 8),
            val: Varnode::constant(0, 4),
        });
        false_terminal.push(R2ILOp::Branch {
            target: Varnode::ram(0x5014, 8),
        });

        let mut blocks = vec![header, false_terminal];
        if with_chain {
            let mut transparent = R2ILBlock::new(0x5008, 4);
            if mutation == RouteMutation::TransparentPayload {
                transparent.push(R2ILOp::Copy {
                    dst: Varnode::unique(0x108, 4),
                    src: Varnode::constant(7, 4),
                });
            }
            transparent.push(R2ILOp::Branch {
                target: Varnode::ram(0x5010, 8),
            });
            blocks.push(transparent);
        }

        let mut true_terminal = R2ILBlock::new(
            0x5010,
            if mutation == RouteMutation::FallthroughWrongNext {
                8
            } else {
                4
            },
        );
        true_terminal.push(R2ILOp::Copy {
            dst: shared.clone(),
            src: Varnode::constant(1, 4),
        });
        true_terminal.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x8000, 8),
            val: Varnode::constant(1, 4),
        });
        if mutation == RouteMutation::FallthroughNonfinalStore {
            true_terminal.push(R2ILOp::Copy {
                dst: Varnode::unique(0x130, 4),
                src: Varnode::constant(9, 4),
            });
        } else if !matches!(
            mutation,
            RouteMutation::TrueFallthrough | RouteMutation::FallthroughWrongNext
        ) {
            true_terminal.push(R2ILOp::Branch {
                target: Varnode::ram(
                    if mutation == RouteMutation::WrongTerminalTarget {
                        0x5004
                    } else {
                        0x5014
                    },
                    8,
                ),
            });
        }
        blocks.push(true_terminal);
        if mutation == RouteMutation::FallthroughWrongNext {
            let mut wrong_next = R2ILBlock::new(0x5018, 4);
            wrong_next.push(R2ILOp::Branch {
                target: Varnode::ram(0x5014, 8),
            });
            blocks.push(wrong_next);
        }

        let mut join = R2ILBlock::new(0x5014, 4);
        if mutation == RouteMutation::UnsupportedSource {
            join.push(R2ILOp::CallOther {
                output: None,
                userop: 7,
                inputs: vec![],
            });
        }

        if mutation == RouteMutation::ReturnAddressRead {
            join.push(R2ILOp::Load {
                dst: Varnode::unique(0x118, 8),
                space: SpaceId::Ram,
                addr: Varnode::register(0, 8),
            });
        }
        join.push(R2ILOp::Load {
            dst: Varnode::unique(0x120, 4),
            space: SpaceId::Ram,
            addr: Varnode::constant(0x8000, 8),
        });
        if mutation == RouteMutation::UseJoinPhi {
            join.push(R2ILOp::Copy {
                dst: Varnode::unique(0x110, 4),
                src: shared,
            });
        }
        join.push(R2ILOp::Return {
            target: Varnode::register(8, 8),
        });
        blocks.push(join);

        let mut arch = ArchSpec::new("conditional-route-test");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("sp", 0, 8));
        arch.add_register(RegisterDef::new("ra", 8, 8));
        let storage = |offset| CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = SourceFunctionInterface::new_exact(
            b"conditional-route-revision-1".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Void,
            [],
        )
        .and_then(|interface| interface.with_return_address_storage(storage(8)))
        .and_then(|interface| interface.with_stack_pointer_storage(storage(0)))
        .expect("exact route interface");
        let artifact = SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface)
            .expect("route artifact");
        let machine_context =
            CertifiedMachineContext::from_artifact(&artifact).expect("machine context");
        let topology = certified_source_topology(&artifact).expect("source topology");
        let direct = certified_direct_controls(&artifact, &topology).expect("direct controls");
        let conditional_controls =
            certified_conditional_controls(&artifact, &topology).expect("conditional control");
        let conditional_values = conditional_controls.values().collect::<Vec<_>>();
        let [conditional] = conditional_values.as_slice() else {
            panic!("one conditional control");
        };
        let returns = certified_return_controls(&artifact, &topology).expect("return control");
        let statements = crate::certified_memory_statements(&artifact).expect("memory statements");
        let projection = MachineProjection::from_artifact(&artifact).expect("machine projection");
        let origin = CertifiedArtifactOrigin {
            schema_version: CERTIFICATION_SCHEMA_VERSION,
            lift_provenance_schema_version: GENUINE_LIFT_PROVENANCE_SCHEMA_VERSION,
            lift_manifest_hash: 1,
            authority: CertifiedAuthoritySeal::new(),
            graph_snapshot: vec![1].into_boxed_slice(),
            prepare_mode: artifact.mode().into(),
            decompile_preparation: None,
            assumptions: artifact.facts().assumptions.clone(),
            machine_context,
            source: artifact.obligations().clone(),
            topology: topology.clone(),
        };
        let mut certification =
            CertifiedFunction::bound(origin.source().clone(), &origin).expect("bound ledger");
        for entity in projection.entities() {
            let obligations = entity
                .source_obligations()
                .iter()
                .copied()
                .filter(|obligation| obligation.kind == SemanticObligationKind::LiveValueProducer)
                .collect::<BTreeSet<_>>();
            if obligations.is_empty() {
                continue;
            }
            let expression = crate::certified_expr_from_machine(
                &artifact,
                &projection,
                entity,
                obligations.clone(),
            )
            .expect("certified expression");
            for obligation in obligations {
                certification
                    .record_absorbed_expression(obligation, expression.clone())
                    .expect("ledgered expression");
            }
        }
        for control in direct.values() {
            certification
                .record_absorbed_control(control.clone())
                .expect("ledgered direct control");
        }
        certification
            .record_absorbed_conditional_control((*conditional).clone())
            .expect("ledgered conditional control");
        for control in returns.values() {
            certification
                .record_absorbed_return(control.clone())
                .expect("ledgered return");
        }
        for statement in statements.values() {
            let obligation = *statement
                .source_obligations()
                .iter()
                .next()
                .expect("statement obligation");
            certification
                .record_absorbed_statement(obligation, statement.clone())
                .expect("ledgered statement");
        }
        let return_address_read = (mutation == RouteMutation::ReturnAddressRead)
            .then(|| {
                statements.values().find(|statement| {
                    statement.width_bits() == 64
                        && matches!(statement.kind(), CertifiedMemoryStatementKind::Read { .. })
                })
            })
            .flatten()
            .cloned();
        RouteFixture {
            artifact,
            origin,
            topology,
            ledger: certification.ledger().clone(),
            direct,
            conditional: (*conditional).clone(),
            return_control: returns.values().next().cloned(),
            statements,
            return_address_read,
        }
    }

    fn write_producer(fixture: &RouteFixture, block_addr: u64) -> CanonicalInstructionId {
        fixture
            .statements
            .values()
            .find(|statement| {
                statement.producer().block_addr == block_addr
                    && matches!(statement.kind(), CertifiedMemoryStatementKind::Write { .. })
            })
            .expect("terminal write statement")
            .producer()
    }

    #[test]
    fn accepts_zero_and_one_branch_only_forwarders() {
        for with_chain in [false, true] {
            let fixture = route_fixture(with_chain, RouteMutation::None);
            let controls = direct_controls_by_block(&fixture.direct).expect("controls by block");
            let (transparent, transfer) = certify_arm_route(
                fixture.origin.source(),
                &fixture.topology,
                fixture.conditional.true_target(),
                fixture.conditional.producer().block_addr,
                0x5010,
                0x5014,
                write_producer(&fixture, 0x5010),
                &controls,
                &fixture.ledger,
            )
            .expect("exact arm route");
            assert_eq!(transparent.len(), usize::from(with_chain));
            assert_eq!(transfer.block_addr(), 0x5010);
            assert_eq!(transfer.target(), 0x5014);
            assert!(transfer.direct().is_some());
            let (false_transparent, false_transfer) = certify_arm_route(
                fixture.origin.source(),
                &fixture.topology,
                fixture.conditional.false_target(),
                fixture.conditional.producer().block_addr,
                0x5004,
                0x5014,
                write_producer(&fixture, 0x5004),
                &controls,
                &fixture.ledger,
            )
            .expect("unchanged direct false-arm route");
            assert!(false_transparent.is_empty());
            assert_eq!(false_transfer.block_addr(), 0x5004);
            assert_eq!(false_transfer.target(), 0x5014);
            assert!(false_transfer.direct().is_some());
            let inert = inert_join_phis(&fixture.artifact, &fixture.topology, 0x5014)
                .expect("inert join phis");
            assert_eq!(inert.len(), 1);
            assert_eq!(inert[0].predecessors(), [0x5004, 0x5010]);
        }
    }

    #[test]
    fn accepts_terminal_store_fallthrough_without_inventing_control() {
        let fixture = route_fixture(false, RouteMutation::TrueFallthrough);
        let controls = direct_controls_by_block(&fixture.direct).expect("controls by block");
        assert!(!controls.contains_key(&0x5010));
        let block = fixture.topology.block(0x5010).expect("terminal block");
        assert_eq!(block.predecessors(), [0x5000]);
        assert_eq!(block.successors(), [0x5014]);
        assert!(matches!(
            block.terminator(),
            CertifiedSourceTerminator::Fallthrough { next: 0x5014 }
        ));
        let producer = write_producer(&fixture, 0x5010);
        assert_eq!(block.instructions().last(), Some(&producer));
        let (transparent, transfer) = certify_arm_route(
            fixture.origin.source(),
            &fixture.topology,
            fixture.conditional.true_target(),
            fixture.conditional.producer().block_addr,
            0x5010,
            0x5014,
            producer,
            &controls,
            &fixture.ledger,
        )
        .expect("sealed fallthrough route");
        assert!(transparent.is_empty());
        assert_eq!(transfer.block_addr(), 0x5010);
        assert_eq!(transfer.target(), 0x5014);
        assert!(transfer.direct().is_none());
        assert!(matches!(
            transfer,
            CertifiedPrivateFrameJoinTransfer::Fallthrough {
                block_addr: 0x5010,
                target: 0x5014,
            }
        ));
        assert_eq!(
            serde_json::to_value(&transfer).expect("serialized fallthrough transfer"),
            serde_json::json!({
                "Fallthrough": {
                    "block_addr": 0x5010,
                    "target": 0x5014,
                }
            })
        );
    }

    #[test]
    fn refuses_mutated_fallthrough_topology_payload_control_and_polarity() {
        let wrong_next = route_fixture(false, RouteMutation::FallthroughWrongNext);
        let controls = direct_controls_by_block(&wrong_next.direct).unwrap();
        let wrong_next_block = wrong_next.topology.block(0x5010).unwrap();
        assert_eq!(wrong_next_block.successors(), [0x5018]);
        assert!(matches!(
            wrong_next_block.terminator(),
            CertifiedSourceTerminator::Fallthrough { next: 0x5018 }
        ));
        assert!(
            certify_arm_route(
                wrong_next.origin.source(),
                &wrong_next.topology,
                wrong_next.conditional.true_target(),
                wrong_next.conditional.producer().block_addr,
                0x5010,
                0x5014,
                write_producer(&wrong_next, 0x5010),
                &controls,
                &wrong_next.ledger,
            )
            .is_none()
        );

        let exact = route_fixture(false, RouteMutation::TrueFallthrough);
        let controls = direct_controls_by_block(&exact.direct).unwrap();
        assert!(
            certify_arm_route(
                exact.origin.source(),
                &exact.topology,
                exact.conditional.true_target(),
                0xdead,
                0x5010,
                0x5014,
                write_producer(&exact, 0x5010),
                &controls,
                &exact.ledger,
            )
            .is_none()
        );

        let nonfinal = route_fixture(false, RouteMutation::FallthroughNonfinalStore);
        let controls = direct_controls_by_block(&nonfinal.direct).unwrap();
        let producer = write_producer(&nonfinal, 0x5010);
        assert_ne!(
            nonfinal
                .topology
                .block(0x5010)
                .unwrap()
                .instructions()
                .last(),
            Some(&producer)
        );
        assert!(
            certify_arm_route(
                nonfinal.origin.source(),
                &nonfinal.topology,
                nonfinal.conditional.true_target(),
                nonfinal.conditional.producer().block_addr,
                0x5010,
                0x5014,
                producer,
                &controls,
                &nonfinal.ledger,
            )
            .is_none()
        );

        let direct = route_fixture(false, RouteMutation::None);
        let stray = direct
            .direct
            .values()
            .find(|control| control.producer().block_addr == 0x5010)
            .unwrap()
            .clone();
        let mut controls = direct_controls_by_block(&exact.direct).unwrap();
        controls.insert(0x5010, &stray);
        assert!(
            certify_arm_route(
                exact.origin.source(),
                &exact.topology,
                exact.conditional.true_target(),
                exact.conditional.producer().block_addr,
                0x5010,
                0x5014,
                write_producer(&exact, 0x5010),
                &controls,
                &exact.ledger,
            )
            .is_none()
        );

        let mut swapped = exact.conditional.clone();
        std::mem::swap(&mut swapped.true_target, &mut swapped.false_target);
        let controls = direct_controls_by_block(&exact.direct).unwrap();
        assert!(
            certify_arm_route(
                exact.origin.source(),
                &exact.topology,
                swapped.true_target(),
                swapped.producer().block_addr,
                0x5010,
                0x5014,
                write_producer(&exact, 0x5010),
                &controls,
                &exact.ledger,
            )
            .is_none()
        );
    }

    #[test]
    fn refuses_nontransparent_wrong_target_used_phi_and_foreign_ledger() {
        let payload = route_fixture(true, RouteMutation::TransparentPayload);
        let controls = direct_controls_by_block(&payload.direct).unwrap();
        assert!(
            certify_arm_route(
                payload.origin.source(),
                &payload.topology,
                payload.conditional.true_target(),
                payload.conditional.producer().block_addr,
                0x5010,
                0x5014,
                write_producer(&payload, 0x5010),
                &controls,
                &payload.ledger,
            )
            .is_none()
        );

        let wrong = route_fixture(false, RouteMutation::WrongTerminalTarget);
        let controls = direct_controls_by_block(&wrong.direct).unwrap();
        assert!(
            certify_arm_route(
                wrong.origin.source(),
                &wrong.topology,
                wrong.conditional.true_target(),
                wrong.conditional.producer().block_addr,
                0x5010,
                0x5014,
                write_producer(&wrong, 0x5010),
                &controls,
                &wrong.ledger,
            )
            .is_none()
        );

        let used = route_fixture(false, RouteMutation::UseJoinPhi);
        assert!(inert_join_phis(&used.artifact, &used.topology, 0x5014).is_none());

        let exact = route_fixture(false, RouteMutation::None);
        let foreign = route_fixture(false, RouteMutation::None);
        assert!(!foreign.ledger.matches_origin(&exact.origin));
        assert_ne!(foreign.origin, exact.origin);
    }

    #[test]
    fn whole_source_audit_refuses_missing_duplicate_residual_and_unsupported() {
        let exact = route_fixture(false, RouteMutation::None);
        assert!(whole_source_ledger_is_exact(&exact.origin, &exact.ledger));
        let obligation = *exact
            .conditional
            .source_obligations()
            .iter()
            .next()
            .unwrap();

        let mut missing = exact.ledger.clone();
        missing.effects.remove(&obligation);
        assert!(!whole_source_ledger_is_exact(&exact.origin, &missing));

        let mut duplicate = exact.ledger.clone();
        let effect = duplicate.effects[&obligation][0].clone();
        duplicate.effects.get_mut(&obligation).unwrap().push(effect);
        assert!(!whole_source_ledger_is_exact(&exact.origin, &duplicate));

        let mut residual = exact.ledger.clone();
        let effect = &mut residual.effects.get_mut(&obligation).unwrap()[0];
        effect.disposition = EffectDisposition::Residualized {
            reason: "retained native/source obligation".to_owned(),
        };
        effect.evidence = crate::DispositionEvidence::Diagnostic;
        assert!(!whole_source_ledger_is_exact(&exact.origin, &residual));

        let unsupported = route_fixture(false, RouteMutation::UnsupportedSource);
        assert!(
            unsupported
                .origin
                .source()
                .instructions()
                .values()
                .any(
                    |instruction| instruction.state == SemanticInstructionState::UnsupportedUnknown
                )
        );
        assert!(!whole_source_ledger_is_exact(
            &unsupported.origin,
            &unsupported.ledger
        ));
    }

    #[test]
    fn return_address_read_requires_exact_artifact_and_ledger_ownership() {
        let exact = route_fixture(false, RouteMutation::ReturnAddressRead);
        let read = exact
            .return_address_read
            .as_ref()
            .expect("retained return-address-like read");
        assert_eq!(
            exact_return_address_read_producer(
                &exact.artifact,
                &exact.origin,
                &exact.ledger,
                read,
                0x5014,
            ),
            Some(read.producer())
        );

        let obligation = *read.source_obligations().iter().next().unwrap();
        let mut unowned = exact.ledger.clone();
        unowned.effects.remove(&obligation);
        assert!(
            exact_return_address_read_producer(
                &exact.artifact,
                &exact.origin,
                &unowned,
                read,
                0x5014,
            )
            .is_none()
        );

        let mut fabricated = read.clone();
        fabricated.width_bits += 8;
        assert!(
            exact_return_address_read_producer(
                &exact.artifact,
                &exact.origin,
                &exact.ledger,
                &fabricated,
                0x5014,
            )
            .is_none()
        );
    }

    fn fixture_ledger_binding(
        fixture: &RouteFixture,
    ) -> PrivateFrameConditionalJoinLedgerBinding<'_> {
        PrivateFrameConditionalJoinLedgerBinding {
            producers: fixture
                .topology
                .blocks()
                .iter()
                .flat_map(|block| block.instructions())
                .copied()
                .collect(),
            statements: fixture
                .statements
                .iter()
                .map(|(producer, statement)| (*producer, statement))
                .collect(),
            direct_controls: fixture
                .direct
                .iter()
                .map(|(producer, control)| (*producer, control))
                .collect(),
            condition: &fixture.conditional,
            return_control: fixture.return_control.as_ref().expect("return control"),
        }
    }

    fn exact_ledger_mappings(fixture: &RouteFixture) -> Vec<TypedRegionMapping> {
        fixture
            .origin
            .source()
            .obligations()
            .keys()
            .map(|obligation| {
                let [effect] = fixture.ledger.effects(*obligation) else {
                    panic!("one exact effect")
                };
                TypedRegionMapping::new(*obligation, effect.disposition().clone())
            })
            .collect()
    }

    #[test]
    fn private_join_ledger_closure_requires_exact_classes_and_mapping_bijection() {
        let fixture = route_fixture(false, RouteMutation::None);
        let binding = fixture_ledger_binding(&fixture);
        let mappings = exact_ledger_mappings(&fixture);
        let closure = certify_private_frame_conditional_join_region_binding(
            &fixture.origin,
            &fixture.ledger,
            mappings.clone(),
            &binding,
        )
        .expect("exact private-frame join ledger closure");
        assert_eq!(
            closure.region_kind(),
            CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction
        );
        assert_eq!(
            closure.region_schema_version(),
            CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION
        );
        assert!(closure.matches_ledger(
            &fixture.origin,
            CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction,
            CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION,
            &mappings,
        ));

        let mut missing = mappings.clone();
        let removed = missing.pop().unwrap();
        assert_eq!(
            certify_private_frame_conditional_join_region_binding(
                &fixture.origin,
                &fixture.ledger,
                missing,
                &binding,
            ),
            Err(LedgerClosureError::MissingMapping(removed.obligation()))
        );

        let mut duplicate = mappings.clone();
        duplicate.push(duplicate[0].clone());
        assert!(matches!(
            certify_private_frame_conditional_join_region_binding(
                &fixture.origin,
                &fixture.ledger,
                duplicate,
                &binding,
            ),
            Err(LedgerClosureError::DuplicateMapping(_))
        ));

        let mut mismatched = mappings.clone();
        mismatched[0] =
            TypedRegionMapping::new(mismatched[0].obligation(), EffectDisposition::ProvenDead);
        assert!(matches!(
            certify_private_frame_conditional_join_region_binding(
                &fixture.origin,
                &fixture.ledger,
                mismatched,
                &binding,
            ),
            Err(LedgerClosureError::DispositionMismatch(_))
        ));

        let mut unexpected = mappings.clone();
        let mut unexpected_id = unexpected[0].obligation();
        unexpected_id.kind = SemanticObligationKind::VolatileOrUnknownEffect;
        unexpected.push(TypedRegionMapping::new(
            unexpected_id,
            EffectDisposition::ProvenDead,
        ));
        assert_eq!(
            certify_private_frame_conditional_join_region_binding(
                &fixture.origin,
                &fixture.ledger,
                unexpected,
                &binding,
            ),
            Err(LedgerClosureError::UnexpectedMapping(unexpected_id))
        );

        let memory_producer = fixture
            .origin
            .source()
            .obligations()
            .values()
            .find(|obligation| {
                matches!(
                    obligation.id.kind,
                    SemanticObligationKind::ObservableMemoryRead
                        | SemanticObligationKind::ObservableMemoryWrite
                )
            })
            .unwrap()
            .id
            .instruction;
        let mut missing_statement = fixture_ledger_binding(&fixture);
        missing_statement.statements.remove(&memory_producer);
        assert!(matches!(
            certify_private_frame_conditional_join_region_binding(
                &fixture.origin,
                &fixture.ledger,
                mappings.clone(),
                &missing_statement,
            ),
            Err(LedgerClosureError::InvalidRegionDisposition(_))
        ));

        let live_producer = fixture
            .origin
            .source()
            .obligations()
            .values()
            .find(|obligation| obligation.id.kind == SemanticObligationKind::LiveValueProducer)
            .unwrap()
            .id
            .instruction;
        let mut missing_expression_owner = fixture_ledger_binding(&fixture);
        missing_expression_owner.producers.remove(&live_producer);
        assert!(matches!(
            certify_private_frame_conditional_join_region_binding(
                &fixture.origin,
                &fixture.ledger,
                mappings.clone(),
                &missing_expression_owner,
            ),
            Err(LedgerClosureError::InvalidRegionDisposition(_))
        ));

        let mut missing_direct = fixture_ledger_binding(&fixture);
        let direct_producer = *missing_direct.direct_controls.keys().next().unwrap();
        missing_direct.direct_controls.remove(&direct_producer);
        assert!(matches!(
            certify_private_frame_conditional_join_region_binding(
                &fixture.origin,
                &fixture.ledger,
                mappings.clone(),
                &missing_direct,
            ),
            Err(LedgerClosureError::InvalidRegionDisposition(_))
        ));

        let mut mutated_condition = fixture.conditional.clone();
        std::mem::swap(
            &mut mutated_condition.true_target,
            &mut mutated_condition.false_target,
        );
        let mut wrong_condition = fixture_ledger_binding(&fixture);
        wrong_condition.condition = &mutated_condition;
        assert!(matches!(
            certify_private_frame_conditional_join_region_binding(
                &fixture.origin,
                &fixture.ledger,
                mappings.clone(),
                &wrong_condition,
            ),
            Err(LedgerClosureError::InvalidRegionDisposition(_))
        ));

        let mut mutated_return = fixture.return_control.clone().unwrap();
        mutated_return.producer = fixture.conditional.producer();
        let mut wrong_return = fixture_ledger_binding(&fixture);
        wrong_return.return_control = &mutated_return;
        assert!(matches!(
            certify_private_frame_conditional_join_region_binding(
                &fixture.origin,
                &fixture.ledger,
                mappings,
                &wrong_return,
            ),
            Err(LedgerClosureError::InvalidRegionDisposition(_))
        ));
    }
}
