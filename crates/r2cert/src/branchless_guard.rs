//! Closed certification for exact one-block x86-64 branchless guards.
//!
//! This module intentionally stops before rendering authority.  It seals one
//! exact source artifact, including its standard stack envelope and partial
//! return-register composition, and assigns every source obligation exactly
//! one proof class.  A later typed renderer must still introduce its own
//! region contract and render permit.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{
    BRANCHLESS_GUARD_FACT_SCHEMA_VERSION, BranchlessGuardFact, BranchlessGuardKind,
    CallBoundarySlot, CanonicalInstructionId, CanonicalStorageId, CanonicalStorageSpace, InstId,
    MachineBuildError, SOURCE_RETURN_REGISTER_COMPOSITION_SCHEMA_VERSION, SemanticInstructionState,
    SemanticObligationId, SemanticObligationInventory, SemanticObligationKind,
    SourceReturnRegisterCompositionFact, SsaArtifact, ValueId,
};
use serde::Serialize;

use super::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedArtifactOrigin, CertifiedMachineContext,
    certified_artifact_origin, certified_source_topology,
};

pub const CERTIFIED_BRANCHLESS_GUARD_CONTRACT_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedBranchlessGuardKind {
    SimpleSubtractEqual {
        expected: u32,
    },
    DualWrap32XorOrEqual {
        sum_expected: u32,
        difference_expected: u32,
    },
}

impl From<BranchlessGuardKind> for CertifiedBranchlessGuardKind {
    fn from(value: BranchlessGuardKind) -> Self {
        match value {
            BranchlessGuardKind::SimpleSubtractEqual { expected } => {
                Self::SimpleSubtractEqual { expected }
            }
            BranchlessGuardKind::DualWrap32XorOrEqual {
                sum_expected,
                difference_expected,
            } => Self::DualWrap32XorOrEqual {
                sum_expected,
                difference_expected,
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedBranchlessGuardDispositionClass {
    FrameEnvelope,
    PredicateSemantics,
    ReturnComposition,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedBranchlessGuardReturn {
    slot: CallBoundarySlot,
    zero_base: ValueId,
    boolean: ValueId,
    base_instruction: CanonicalInstructionId,
    overlay_instruction: CanonicalInstructionId,
    return_instruction: CanonicalInstructionId,
    return_target: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CertifiedBranchlessGuardParameter {
    index: u32,
    abi_storage: CanonicalStorageId,
    low32_storage: CanonicalStorageId,
    low32_value: ValueId,
}

impl CertifiedBranchlessGuardParameter {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn abi_storage(&self) -> CanonicalStorageId {
        self.abi_storage
    }

    pub const fn low32_storage(&self) -> CanonicalStorageId {
        self.low32_storage
    }

    pub const fn low32_value(&self) -> ValueId {
        self.low32_value
    }
}

impl CertifiedBranchlessGuardReturn {
    pub const fn slot(&self) -> CallBoundarySlot {
        self.slot
    }

    pub const fn zero_base(&self) -> ValueId {
        self.zero_base
    }

    pub const fn boolean(&self) -> ValueId {
        self.boolean
    }

    pub const fn base_instruction(&self) -> CanonicalInstructionId {
        self.base_instruction
    }

    pub const fn overlay_instruction(&self) -> CanonicalInstructionId {
        self.overlay_instruction
    }

    pub const fn return_instruction(&self) -> CanonicalInstructionId {
        self.return_instruction
    }

    pub const fn return_target(&self) -> ValueId {
        self.return_target
    }
}

/// Opaque whole-source proof.  Construction is artifact-only and the retained
/// origin includes the canonical graph snapshot, machine context, interface
/// revision, source inventory, and topology.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedBranchlessGuardFunction {
    schema_version: u32,
    contract_version: u32,
    origin: CertifiedArtifactOrigin,
    entry: u64,
    kind: CertifiedBranchlessGuardKind,
    parameters: Box<[CertifiedBranchlessGuardParameter]>,
    return_storage: CanonicalStorageId,
    returned: CertifiedBranchlessGuardReturn,
    instruction_inventory: Box<[CanonicalInstructionId]>,
    frame_instructions: BTreeSet<CanonicalInstructionId>,
    semantic_instructions: BTreeSet<CanonicalInstructionId>,
    obligation_dispositions: Box<
        [(
            SemanticObligationId,
            CertifiedBranchlessGuardDispositionClass,
        )],
    >,
}

impl CertifiedBranchlessGuardFunction {
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn contract_version(&self) -> u32 {
        self.contract_version
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn entry(&self) -> u64 {
        self.entry
    }

    pub const fn kind(&self) -> CertifiedBranchlessGuardKind {
        self.kind
    }

    pub const fn parameters(&self) -> &[CertifiedBranchlessGuardParameter] {
        &self.parameters
    }

    pub const fn return_storage(&self) -> CanonicalStorageId {
        self.return_storage
    }

    pub const fn returned(&self) -> &CertifiedBranchlessGuardReturn {
        &self.returned
    }

    pub const fn instruction_inventory(&self) -> &[CanonicalInstructionId] {
        &self.instruction_inventory
    }

    pub const fn obligation_dispositions(
        &self,
    ) -> &[(
        SemanticObligationId,
        CertifiedBranchlessGuardDispositionClass,
    )] {
        &self.obligation_dispositions
    }

    /// Recheck exact closure against the retained source inventory.
    pub fn validate(&self, source: &SemanticObligationInventory) -> bool {
        if self.schema_version != CERTIFICATION_SCHEMA_VERSION
            || self.contract_version != CERTIFIED_BRANCHLESS_GUARD_CONTRACT_VERSION
            || self.origin.source() != source
            || !self
                .origin
                .matches_retained_source(source, self.origin.topology())
            || self.instruction_inventory.len() != source.instructions().len()
            || self
                .instruction_inventory
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                != source.instructions().keys().copied().collect()
            || self
                .frame_instructions
                .intersection(&self.semantic_instructions)
                .next()
                .is_some()
            || self
                .frame_instructions
                .union(&self.semantic_instructions)
                .copied()
                .collect::<BTreeSet<_>>()
                != source.instructions().keys().copied().collect()
            || source.instructions().values().any(|instruction| {
                instruction.state == SemanticInstructionState::UnsupportedUnknown
                    && !self.frame_instructions.contains(&instruction.id)
            })
        {
            return false;
        }
        let dispositions = self
            .obligation_dispositions
            .iter()
            .copied()
            .collect::<BTreeMap<_, _>>();
        if dispositions.len() != self.obligation_dispositions.len()
            || dispositions.len() != source.obligations().len()
            || dispositions.keys().copied().collect::<BTreeSet<_>>()
                != source.obligations().keys().copied().collect()
        {
            return false;
        }
        source.obligations().keys().all(|obligation| {
            dispositions.get(obligation).copied()
                == disposition_class(
                    *obligation,
                    &self.frame_instructions,
                    &self.semantic_instructions,
                    self.returned.return_instruction,
                )
        })
    }
}

/// Construct the exact certificate when, and only when, the artifact contains
/// one admitted branchless-guard source fact.
pub fn certify_branchless_guard_function(
    artifact: &SsaArtifact,
) -> Result<Option<CertifiedBranchlessGuardFunction>, MachineBuildError> {
    let facts = &artifact.structured().branchless_guards;
    if facts.is_empty() {
        return Ok(None);
    }
    if facts.len() != 1 {
        return Err(MachineBuildError::TopologyMismatch);
    }
    certify_one(artifact, facts.values().next().expect("one fact")).map(Some)
}

fn certify_one(
    artifact: &SsaArtifact,
    fact: &BranchlessGuardFact,
) -> Result<CertifiedBranchlessGuardFunction, MachineBuildError> {
    if fact.schema_version != BRANCHLESS_GUARD_FACT_SCHEMA_VERSION
        || !fact.validate_against(artifact)
        || !fact.returned.composition.validate(
            artifact.function(),
            artifact.graph(),
            artifact.machine_context(),
            fact.returned.return_inst,
        )
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    validate_composition(fact, &fact.returned.composition)?;
    let machine_context = CertifiedMachineContext::from_artifact(artifact)?;
    let topology = certified_source_topology(artifact)?;
    let origin = certified_artifact_origin(artifact, &machine_context, &topology)?;
    let instruction_inventory = canonical_instructions(artifact, &fact.instruction_inventory)?;
    let frame_instructions = canonical_instruction_set(artifact, &fact.frame_instructions)?;
    let semantic_instructions = canonical_instruction_set(artifact, &fact.semantic_instructions)?;
    let return_instruction = canonical_instruction(artifact, fact.returned.return_inst)?;
    let base_instruction =
        canonical_instruction(artifact, fact.returned.composition.base.producer)?;
    let overlay_instruction = canonical_instruction(
        artifact,
        fact.returned.composition.overlays[0].definition.producer,
    )?;

    let mut obligation_dispositions =
        Vec::with_capacity(artifact.obligations().obligations().len());
    for obligation in artifact.obligations().obligations().keys().copied() {
        let class = disposition_class(
            obligation,
            &frame_instructions,
            &semantic_instructions,
            return_instruction,
        )
        .ok_or_else(|| obligation_error(artifact, obligation))?;
        obligation_dispositions.push((obligation, class));
    }
    obligation_dispositions.sort_by_key(|(obligation, _)| *obligation);
    let certificate = CertifiedBranchlessGuardFunction {
        schema_version: CERTIFICATION_SCHEMA_VERSION,
        contract_version: CERTIFIED_BRANCHLESS_GUARD_CONTRACT_VERSION,
        origin,
        entry: fact.entry,
        kind: fact.kind.into(),
        parameters: fact
            .abi
            .parameters
            .iter()
            .map(|parameter| CertifiedBranchlessGuardParameter {
                index: parameter.index,
                abi_storage: parameter.abi_storage,
                low32_storage: parameter.low32_storage,
                low32_value: parameter.low32_value,
            })
            .collect::<Vec<_>>()
            .into_boxed_slice(),
        return_storage: fact.abi.return_storage,
        returned: CertifiedBranchlessGuardReturn {
            slot: fact.returned.composition.slot,
            zero_base: fact.returned.zero_base,
            boolean: fact.returned.boolean,
            base_instruction,
            overlay_instruction,
            return_instruction,
            return_target: fact.returned.return_target,
        },
        instruction_inventory: instruction_inventory.into_boxed_slice(),
        frame_instructions,
        semantic_instructions,
        obligation_dispositions: obligation_dispositions.into_boxed_slice(),
    };
    if !certificate.validate(artifact.obligations()) {
        return Err(MachineBuildError::TopologyMismatch);
    }
    Ok(certificate)
}

fn validate_composition(
    fact: &BranchlessGuardFact,
    composition: &SourceReturnRegisterCompositionFact,
) -> Result<(), MachineBuildError> {
    let [overlay] = composition.overlays.as_slice() else {
        return Err(MachineBuildError::TopologyMismatch);
    };
    if composition.schema_version != SOURCE_RETURN_REGISTER_COMPOSITION_SCHEMA_VERSION
        || composition.slot
            != (CallBoundarySlot::Register {
                index: 0,
                storage: fact.abi.return_storage,
            })
        || fact.abi.return_storage.space != CanonicalStorageSpace::Register
        || fact.abi.return_storage.size != 8
        || composition.base.storage != fact.abi.return_storage
        || composition.base.producer != fact.returned.composition.base.producer
        || composition.base.value != fact.returned.zero_base
        || overlay.offset_bytes != 0
        || overlay.definition.producer != fact.returned.composition.overlays[0].definition.producer
        || overlay.definition.storage.space != CanonicalStorageSpace::Register
        || overlay.definition.storage.offset != fact.abi.return_storage.offset
        || overlay.definition.storage.size != 1
        || overlay.definition.value != fact.returned.boolean
    {
        return Err(MachineBuildError::TopologyMismatch);
    }
    Ok(())
}

fn disposition_class(
    obligation: SemanticObligationId,
    frame: &BTreeSet<CanonicalInstructionId>,
    semantics: &BTreeSet<CanonicalInstructionId>,
    return_instruction: CanonicalInstructionId,
) -> Option<CertifiedBranchlessGuardDispositionClass> {
    if obligation.instruction == return_instruction
        && matches!(
            obligation.kind,
            SemanticObligationKind::Return | SemanticObligationKind::ReturnValue
        )
    {
        return Some(CertifiedBranchlessGuardDispositionClass::ReturnComposition);
    }
    if frame.contains(&obligation.instruction) {
        return matches!(
            obligation.kind,
            SemanticObligationKind::LiveValueProducer
                | SemanticObligationKind::ObservableMemoryRead
                | SemanticObligationKind::ObservableMemoryWrite
                | SemanticObligationKind::ControlTransfer
                | SemanticObligationKind::Return
                | SemanticObligationKind::ReturnValue
                | SemanticObligationKind::Trap
                | SemanticObligationKind::VolatileOrUnknownEffect
        )
        .then_some(CertifiedBranchlessGuardDispositionClass::FrameEnvelope);
    }
    if semantics.contains(&obligation.instruction) {
        return matches!(
            obligation.kind,
            SemanticObligationKind::LiveValueProducer | SemanticObligationKind::Trap
        )
        .then_some(CertifiedBranchlessGuardDispositionClass::PredicateSemantics);
    }
    None
}

fn canonical_instructions(
    artifact: &SsaArtifact,
    insts: &[InstId],
) -> Result<Vec<CanonicalInstructionId>, MachineBuildError> {
    insts
        .iter()
        .map(|inst| canonical_instruction(artifact, *inst))
        .collect()
}

fn canonical_instruction_set(
    artifact: &SsaArtifact,
    insts: &[InstId],
) -> Result<BTreeSet<CanonicalInstructionId>, MachineBuildError> {
    canonical_instructions(artifact, insts).map(|instructions| instructions.into_iter().collect())
}

fn canonical_instruction(
    artifact: &SsaArtifact,
    inst: InstId,
) -> Result<CanonicalInstructionId, MachineBuildError> {
    artifact
        .obligations()
        .instruction_for_inst(inst)
        .map(|instruction| instruction.id)
        .ok_or(MachineBuildError::ObligationMismatch(inst))
}

fn obligation_error(artifact: &SsaArtifact, obligation: SemanticObligationId) -> MachineBuildError {
    MachineBuildError::ObligationMismatch(
        artifact
            .obligations()
            .obligations()
            .get(&obligation)
            .map(|source| source.source_inst)
            .unwrap_or(InstId(u32::MAX)),
    )
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use r2il::{
        AddressSpace, ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode,
    };
    use r2ssa::{
        CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierKind, SourceCarrierProjection,
        SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue, SourceType,
        SourceTypeGraph, SourceTypeKind,
    };

    use super::*;

    const DATA: SpaceId = SpaceId::Custom(17);
    const ENTRY: u64 = 0x4000;

    fn reg(offset: u64, size: u32) -> Varnode {
        Varnode::register(offset, size)
    }

    fn con(value: u64, size: u32) -> Varnode {
        Varnode::constant(value, size)
    }

    fn tmp(next: &mut u64, size: u32) -> Varnode {
        let value = Varnode::unique(*next, size);
        *next += 0x80;
        value
    }

    fn storage(offset: u64) -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset,
            size: 8,
        }
    }

    fn arch() -> ArchSpec {
        let mut arch = ArchSpec::new("x86-64-branchless-cert-test");
        arch.addr_size = 8;
        arch.alignment = 1;
        for (name, offset, size) in [
            ("AL", 0, 1),
            ("EAX", 0, 4),
            ("RAX", 0, 8),
            ("ECX", 8, 4),
            ("RCX", 8, 8),
            ("RSP", 32, 8),
            ("RBP", 40, 8),
            ("ESI", 48, 4),
            ("RSI", 48, 8),
            ("EDI", 56, 4),
            ("RDI", 56, 8),
            ("CF", 512, 1),
            ("PF", 514, 1),
            ("ZF", 518, 1),
            ("SF", 519, 1),
            ("OF", 523, 1),
            ("RIP", 648, 8),
        ] {
            arch.add_register(RegisterDef::new(name, offset, size));
        }
        arch.add_space(AddressSpace::new(DATA, "x86-data", 8));
        arch.set_memory_endianness(Endianness::Little);
        arch
    }

    fn interface(parameter_count: usize) -> SourceFunctionInterface {
        let types = SourceTypeGraph::new(
            [SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32)],
            [],
        )
        .expect("type graph");
        let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
        SourceFunctionInterface::new_exact_with_logical_types(
            b"branchless-cert-revision-1".to_vec(),
            "sysv_amd64",
            [storage(56), storage(48)]
                .into_iter()
                .take(parameter_count)
                .enumerate()
                .map(|(index, storage)| SourceAbiParameterSpec::new(index as u32, storage)),
            SourceFunctionReturn::Register {
                storage: storage(0),
            },
            [],
            (0..parameter_count).map(|_| SourceLogicalValue::new(0, low32)),
            Some(SourceLogicalValue::new(0, low32)),
            Some(types),
        )
        .expect("interface")
    }

    fn prefix(block: &mut R2ILBlock, next: &mut u64) {
        let saved = tmp(next, 8);
        block.push(R2ILOp::Copy {
            dst: saved.clone(),
            src: reg(40, 8),
        });
        block.push(R2ILOp::IntSub {
            dst: reg(32, 8),
            a: reg(32, 8),
            b: con(8, 8),
        });
        block.push(R2ILOp::Store {
            space: DATA,
            addr: reg(32, 8),
            val: saved,
        });
        block.push(R2ILOp::Copy {
            dst: reg(40, 8),
            src: reg(32, 8),
        });
    }

    fn zero_flags(block: &mut R2ILBlock) {
        block.push(R2ILOp::Copy {
            dst: reg(512, 1),
            src: con(0, 1),
        });
        block.push(R2ILOp::Copy {
            dst: reg(523, 1),
            src: con(0, 1),
        });
    }

    fn flags(block: &mut R2ILBlock, next: &mut u64, value: Varnode) {
        block.push(R2ILOp::IntSLess {
            dst: reg(519, 1),
            a: value.clone(),
            b: con(0, 4),
        });
        block.push(R2ILOp::IntEqual {
            dst: reg(518, 1),
            a: value.clone(),
            b: con(0, 4),
        });
        let low = tmp(next, 4);
        block.push(R2ILOp::IntAnd {
            dst: low.clone(),
            a: value,
            b: con(0xff, 4),
        });
        let population = tmp(next, 1);
        block.push(R2ILOp::PopCount {
            dst: population.clone(),
            src: low,
        });
        let parity = tmp(next, 1);
        block.push(R2ILOp::IntAnd {
            dst: parity.clone(),
            a: population,
            b: con(1, 1),
        });
        block.push(R2ILOp::IntEqual {
            dst: reg(514, 1),
            a: parity,
            b: con(0, 1),
        });
    }

    fn suffix(block: &mut R2ILBlock, next: &mut u64) {
        let restored = tmp(next, 8);
        block.push(R2ILOp::Copy {
            dst: restored.clone(),
            src: con(0, 8),
        });
        block.push(R2ILOp::Load {
            dst: restored.clone(),
            space: DATA,
            addr: reg(32, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: reg(32, 8),
            a: reg(32, 8),
            b: con(8, 8),
        });
        block.push(R2ILOp::Copy {
            dst: reg(40, 8),
            src: restored,
        });
        block.push(R2ILOp::Load {
            dst: reg(648, 8),
            space: DATA,
            addr: reg(32, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: reg(32, 8),
            a: reg(32, 8),
            b: con(8, 8),
        });
        block.push(R2ILOp::Return {
            target: reg(648, 8),
        });
    }

    fn simple() -> R2ILBlock {
        let mut block = R2ILBlock::new(ENTRY, 17);
        let mut next = 0x10000;
        prefix(&mut block, &mut next);
        zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: reg(0, 4),
            a: reg(0, 4),
            b: reg(0, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: reg(0, 8),
            src: reg(0, 4),
        });
        flags(&mut block, &mut next, reg(0, 4));
        let copied = tmp(&mut next, 4);
        block.push(R2ILOp::Copy {
            dst: copied.clone(),
            src: reg(56, 4),
        });
        block.push(R2ILOp::IntLess {
            dst: reg(512, 1),
            a: copied.clone(),
            b: con(0xdead, 4),
        });
        block.push(R2ILOp::IntSBorrow {
            dst: reg(523, 1),
            a: copied.clone(),
            b: con(0xdead, 4),
        });
        let difference = tmp(&mut next, 4);
        block.push(R2ILOp::IntSub {
            dst: difference.clone(),
            a: copied,
            b: con(0xdead, 4),
        });
        flags(&mut block, &mut next, difference);
        block.push(R2ILOp::Copy {
            dst: reg(0, 1),
            src: reg(518, 1),
        });
        suffix(&mut block, &mut next);
        block
    }

    fn dual() -> R2ILBlock {
        let mut block = R2ILBlock::new(ENTRY, 24);
        let mut next = 0x20000;
        prefix(&mut block, &mut next);
        let scaled = tmp(&mut next, 8);
        block.push(R2ILOp::IntMult {
            dst: scaled.clone(),
            a: reg(56, 8),
            b: con(1, 8),
        });
        let sum = tmp(&mut next, 8);
        block.push(R2ILOp::IntAdd {
            dst: sum.clone(),
            a: reg(48, 8),
            b: scaled,
        });
        block.push(R2ILOp::Subpiece {
            dst: reg(8, 4),
            src: sum,
            offset: 0,
        });
        block.push(R2ILOp::IntZExt {
            dst: reg(8, 8),
            src: reg(8, 4),
        });
        block.push(R2ILOp::IntLess {
            dst: reg(512, 1),
            a: reg(56, 4),
            b: reg(48, 4),
        });
        block.push(R2ILOp::IntSBorrow {
            dst: reg(523, 1),
            a: reg(56, 4),
            b: reg(48, 4),
        });
        block.push(R2ILOp::IntSub {
            dst: reg(56, 4),
            a: reg(56, 4),
            b: reg(48, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: reg(56, 8),
            src: reg(56, 4),
        });
        flags(&mut block, &mut next, reg(56, 4));
        zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: reg(8, 4),
            a: reg(8, 4),
            b: con(100, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: reg(8, 8),
            src: reg(8, 4),
        });
        flags(&mut block, &mut next, reg(8, 4));
        zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: reg(56, 4),
            a: reg(56, 4),
            b: con(20, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: reg(56, 8),
            src: reg(56, 4),
        });
        flags(&mut block, &mut next, reg(56, 4));
        zero_flags(&mut block);
        block.push(R2ILOp::IntXor {
            dst: reg(0, 4),
            a: reg(0, 4),
            b: reg(0, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: reg(0, 8),
            src: reg(0, 4),
        });
        flags(&mut block, &mut next, reg(0, 4));
        zero_flags(&mut block);
        block.push(R2ILOp::IntOr {
            dst: reg(56, 4),
            a: reg(56, 4),
            b: reg(8, 4),
        });
        block.push(R2ILOp::IntZExt {
            dst: reg(56, 8),
            src: reg(56, 4),
        });
        flags(&mut block, &mut next, reg(56, 4));
        block.push(R2ILOp::Copy {
            dst: reg(0, 1),
            src: reg(518, 1),
        });
        suffix(&mut block, &mut next);
        block
    }

    fn artifact(block: R2ILBlock, parameters: usize) -> SsaArtifact {
        SsaArtifact::raw_with_interface(&[block], Some(&arch()), interface(parameters))
            .expect("artifact")
    }

    fn assert_closed(artifact: &SsaArtifact, expected_instructions: usize) {
        let certificate = certify_branchless_guard_function(artifact)
            .expect("certification result")
            .expect("branchless certificate");
        assert!(certificate.validate(artifact.obligations()));
        assert_eq!(
            certificate.instruction_inventory().len(),
            expected_instructions
        );
        assert_eq!(
            certificate.obligation_dispositions().len(),
            artifact.obligations().obligations().len()
        );
        assert_eq!(
            certificate
                .obligation_dispositions()
                .iter()
                .map(|(obligation, _)| *obligation)
                .collect::<BTreeSet<_>>()
                .len(),
            artifact.obligations().obligations().len()
        );
    }

    #[test]
    fn exact_simple_and_dual_sources_close_once() {
        assert_closed(&artifact(simple(), 1), 32);
        assert_closed(&artifact(dual(), 2), 66);
    }

    #[test]
    fn private_certificate_corruption_fails_validation() {
        let artifact = artifact(simple(), 1);
        let certificate = certify_branchless_guard_function(&artifact)
            .expect("certification")
            .expect("certificate");

        let mut duplicate = certificate.clone();
        let mut dispositions = duplicate.obligation_dispositions.to_vec();
        dispositions.push(dispositions[0]);
        duplicate.obligation_dispositions = dispositions.into_boxed_slice();
        assert!(!duplicate.validate(artifact.obligations()));

        let mut wrong_class = certificate.clone();
        wrong_class.obligation_dispositions[0].1 = match wrong_class.obligation_dispositions[0].1 {
            CertifiedBranchlessGuardDispositionClass::FrameEnvelope => {
                CertifiedBranchlessGuardDispositionClass::PredicateSemantics
            }
            _ => CertifiedBranchlessGuardDispositionClass::FrameEnvelope,
        };
        assert!(!wrong_class.validate(artifact.obligations()));

        let mut extra_instruction = certificate.clone();
        let mut inventory = extra_instruction.instruction_inventory.to_vec();
        inventory.push(inventory[0]);
        extra_instruction.instruction_inventory = inventory.into_boxed_slice();
        assert!(!extra_instruction.validate(artifact.obligations()));
    }

    #[test]
    fn unsupported_or_extra_semantic_source_has_no_certificate() {
        let mut unsupported = simple();
        unsupported.ops.insert(24, R2ILOp::Unimplemented);
        let unsupported = artifact(unsupported, 1);
        assert!(unsupported.structured().branchless_guards.is_empty());
        assert!(
            certify_branchless_guard_function(&unsupported)
                .expect("unsupported result")
                .is_none()
        );
    }

    #[test]
    fn composition_revalidator_rejects_all_identity_mutations() {
        let artifact = artifact(simple(), 1);
        let fact = artifact
            .structured()
            .branchless_guards
            .values()
            .next()
            .expect("fact");
        let exact = &fact.returned.composition;
        assert!(validate_composition(fact, exact).is_ok());

        let mut wrong_space = exact.clone();
        wrong_space.overlays[0].definition.storage.space = CanonicalStorageSpace::Unique;
        assert!(validate_composition(fact, &wrong_space).is_err());

        let mut wrong_base_size = exact.clone();
        wrong_base_size.base.storage.size = 4;
        assert!(validate_composition(fact, &wrong_base_size).is_err());

        let mut wrong_base_producer = exact.clone();
        wrong_base_producer.base.producer = wrong_base_producer.overlays[0].definition.producer;
        assert!(validate_composition(fact, &wrong_base_producer).is_err());

        let mut wrong_overlay_producer = exact.clone();
        wrong_overlay_producer.overlays[0].definition.producer =
            wrong_overlay_producer.base.producer;
        assert!(validate_composition(fact, &wrong_overlay_producer).is_err());
    }
}
