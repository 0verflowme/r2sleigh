//! Artifact-bound, name-independent access to executable SSA graph entities.
//!
//! The serialized SSA graph uses compact artifact-local IDs. This module binds
//! those IDs to one exact [`SsaArtifact`] authority before they cross into an
//! execution engine. Presentation names remain available on the underlying
//! graph for renderers, but are deliberately absent from this API.

use std::collections::BTreeSet;
use std::fmt;
use std::hash::{Hash, Hasher};

use r2il::{MemoryOrdering, SpaceId};

use crate::function::{SSAFunction, SsaArtifact, SsaArtifactAuthority};
use crate::graph::{BlockId, GraphBlock, GraphInst, InstId, InstPayload, SsaGraph, ValueId};
use crate::{CanonicalStorageId, CanonicalStorageSpace, SSAOp};

macro_rules! artifact_id {
    ($name:ident, $local:ty) => {
        #[derive(Clone, PartialEq, Eq)]
        pub struct $name {
            authority: SsaArtifactAuthority,
            local: $local,
        }

        impl $name {
            pub(crate) const fn local_id(&self) -> $local {
                self.local
            }

            pub const fn authority(&self) -> &SsaArtifactAuthority {
                &self.authority
            }

            pub fn belongs_to(&self, artifact: &SsaArtifact) -> bool {
                &self.authority == artifact.authority()
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_tuple(stringify!($name)).field(&self.local).finish()
            }
        }

        impl Hash for $name {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.authority.hash(state);
                self.local.hash(state);
            }
        }
    };
}

artifact_id!(ArtifactValueId, ValueId);
artifact_id!(ArtifactInstId, InstId);
artifact_id!(ArtifactBlockId, BlockId);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntryStorageError {
    Missing(CanonicalStorageId),
    Ambiguous(CanonicalStorageId),
}

impl fmt::Display for EntryStorageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Missing(storage) => write!(f, "no entry SSA value for {storage:?}"),
            Self::Ambiguous(storage) => {
                write!(f, "multiple entry SSA values for {storage:?}")
            }
        }
    }
}

impl std::error::Error for EntryStorageError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionViewError {
    WidthOverflow { value: ValueId, size_bytes: u32 },
    IncoherentBlock(BlockId),
    IncoherentValue(ValueId),
    UnexpectedPhiOp(InstId),
}

impl fmt::Display for ExecutionViewError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WidthOverflow { value, size_bytes } => {
                write!(
                    f,
                    "SSA value {value:?} width overflows for {size_bytes} bytes"
                )
            }
            Self::IncoherentBlock(block) => write!(f, "incoherent SSA block {block:?}"),
            Self::IncoherentValue(value) => write!(f, "incoherent SSA value {value:?}"),
            Self::UnexpectedPhiOp(inst) => {
                write!(
                    f,
                    "SSA instruction {inst:?} contains an unbound Phi operation"
                )
            }
        }
    }
}

impl std::error::Error for ExecutionViewError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExecutionOpcode {
    Phi,
    Copy,
    Load,
    Store,
    Fence,
    LoadLinked,
    StoreConditional,
    AtomicCAS,
    LoadGuarded,
    StoreGuarded,
    IntAdd,
    IntSub,
    IntMult,
    IntDiv,
    IntSDiv,
    IntRem,
    IntSRem,
    IntNegate,
    IntCarry,
    IntSCarry,
    IntSBorrow,
    IntAnd,
    IntOr,
    IntXor,
    IntNot,
    IntLeft,
    IntRight,
    IntSRight,
    IntEqual,
    IntNotEqual,
    IntLess,
    IntSLess,
    IntLessEqual,
    IntSLessEqual,
    IntZExt,
    IntSExt,
    BoolNot,
    BoolAnd,
    BoolOr,
    BoolXor,
    Piece,
    Subpiece,
    PopCount,
    Lzcount,
    Branch,
    CBranch,
    BranchInd,
    Call,
    CallInd,
    CallDefine,
    Return,
    FloatAdd,
    FloatSub,
    FloatMult,
    FloatDiv,
    FloatNeg,
    FloatAbs,
    FloatSqrt,
    FloatCeil,
    FloatFloor,
    FloatRound,
    FloatNaN,
    FloatEqual,
    FloatNotEqual,
    FloatLess,
    FloatLessEqual,
    Int2Float,
    Float2Int,
    FloatFloat,
    Trunc,
    CallOther,
    Nop,
    Unimplemented,
    CpuId,
    Breakpoint,
    PtrAdd,
    PtrSub,
    SegmentOp,
    New,
    Cast,
    Extract,
    Insert,
    Select,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecutionPhiIncoming {
    predecessor: ArtifactBlockId,
    value: ArtifactValueId,
}

impl ExecutionPhiIncoming {
    pub const fn predecessor(&self) -> &ArtifactBlockId {
        &self.predecessor
    }

    pub const fn value(&self) -> &ArtifactValueId {
        &self.value
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecutionEffect {
    None,
    Phi {
        incoming: Vec<ExecutionPhiIncoming>,
    },
    Memory {
        space: SpaceId,
        ordering: Option<MemoryOrdering>,
    },
    Fence {
        ordering: MemoryOrdering,
    },
    Subpiece {
        offset_bytes: u32,
    },
    CallOther {
        userop: u32,
    },
    Pointer {
        element_size: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecutionOperands {
    inputs: Vec<ArtifactValueId>,
    output: Option<ArtifactValueId>,
}

impl ExecutionOperands {
    pub fn inputs(&self) -> &[ArtifactValueId] {
        &self.inputs
    }

    pub const fn output(&self) -> Option<&ArtifactValueId> {
        self.output.as_ref()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecutionOperation {
    opcode: ExecutionOpcode,
    operands: ExecutionOperands,
    effect: ExecutionEffect,
}

impl ExecutionOperation {
    pub const fn opcode(&self) -> ExecutionOpcode {
        self.opcode
    }

    pub const fn operands(&self) -> &ExecutionOperands {
        &self.operands
    }

    pub const fn effect(&self) -> &ExecutionEffect {
        &self.effect
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SsaExecutionView<'a> {
    artifact: &'a SsaArtifact,
}

fn checked_width_bits(value: ValueId, size_bytes: u32) -> Result<u32, ExecutionViewError> {
    size_bytes
        .checked_mul(8)
        .ok_or(ExecutionViewError::WidthOverflow { value, size_bytes })
}

fn phi_predecessors_cover_block(block: &crate::GraphBlock, predecessors: &[BlockId]) -> bool {
    if predecessors.len() != block.predecessors.len() {
        return false;
    }
    let expected = block.predecessors.iter().copied().collect::<BTreeSet<_>>();
    let actual = predecessors.iter().copied().collect::<BTreeSet<_>>();
    expected.len() == block.predecessors.len()
        && actual.len() == predecessors.len()
        && actual == expected
}

fn graph_block_is_coherent(function: &SSAFunction, graph: &SsaGraph, block: &GraphBlock) -> bool {
    let index = block.id.0 as usize;
    if graph.blocks.len() != function.num_blocks()
        || graph.block_order.len() != graph.blocks.len()
        || graph.block_by_addr.len() != graph.blocks.len()
        || graph.blocks.get(index) != Some(block)
        || graph.block_order.get(index) != Some(&block.id)
        || function.block_addrs().get(index) != Some(&block.addr)
        || graph.block_by_addr.get(&block.addr) != Some(&block.id)
    {
        return false;
    }

    let Some(function_block) = function.get_block(block.addr) else {
        return false;
    };
    if function_block.addr != block.addr
        || function_block.size != block.size
        || function_block.phis.len() + function_block.ops.len() != block.insts.len()
    {
        return false;
    }

    let expected_predecessors = function
        .predecessors(block.addr)
        .into_iter()
        .map(|addr| graph.block_by_addr.get(&addr).copied())
        .collect::<Option<Vec<_>>>();
    let expected_successors = function
        .successors(block.addr)
        .into_iter()
        .map(|addr| graph.block_by_addr.get(&addr).copied())
        .collect::<Option<Vec<_>>>();
    if expected_predecessors.as_deref() != Some(block.predecessors.as_slice())
        || expected_successors.as_deref() != Some(block.successors.as_slice())
    {
        return false;
    }

    block.predecessors.iter().all(|predecessor| {
        graph
            .block(*predecessor)
            .is_some_and(|other| other.id == *predecessor && other.successors.contains(&block.id))
    }) && block.successors.iter().all(|successor| {
        graph
            .block(*successor)
            .is_some_and(|other| other.id == *successor && other.predecessors.contains(&block.id))
    })
}

/// Return the exact graph definition, distinguishing a valid entry value from
/// a malformed or non-inverse `def_of` relation.
fn validated_definition(graph: &SsaGraph, value: ValueId) -> Option<Option<InstId>> {
    if graph.def_of.len() != graph.values.len() {
        return None;
    }
    let recorded = *graph.def_of.get(value.0 as usize)?;
    let mut definitions = graph.insts.iter().filter(|inst| inst.output == Some(value));
    let first = definitions.next().map(|inst| inst.id);
    if definitions.next().is_some() || recorded != first {
        return None;
    }
    match recorded {
        Some(inst)
            if graph.inst(inst).is_some_and(|candidate| {
                candidate.id == inst && candidate.output == Some(value)
            }) =>
        {
            Some(Some(inst))
        }
        Some(_) => None,
        None if first.is_none() => Some(None),
        None => None,
    }
}

fn opcode_for_op(op: &SSAOp) -> ExecutionOpcode {
    match op {
        SSAOp::Phi { .. } => ExecutionOpcode::Phi,
        SSAOp::Copy { .. } => ExecutionOpcode::Copy,
        SSAOp::Load { .. } => ExecutionOpcode::Load,
        SSAOp::Store { .. } => ExecutionOpcode::Store,
        SSAOp::Fence { .. } => ExecutionOpcode::Fence,
        SSAOp::LoadLinked { .. } => ExecutionOpcode::LoadLinked,
        SSAOp::StoreConditional { .. } => ExecutionOpcode::StoreConditional,
        SSAOp::AtomicCAS { .. } => ExecutionOpcode::AtomicCAS,
        SSAOp::LoadGuarded { .. } => ExecutionOpcode::LoadGuarded,
        SSAOp::StoreGuarded { .. } => ExecutionOpcode::StoreGuarded,
        SSAOp::IntAdd { .. } => ExecutionOpcode::IntAdd,
        SSAOp::IntSub { .. } => ExecutionOpcode::IntSub,
        SSAOp::IntMult { .. } => ExecutionOpcode::IntMult,
        SSAOp::IntDiv { .. } => ExecutionOpcode::IntDiv,
        SSAOp::IntSDiv { .. } => ExecutionOpcode::IntSDiv,
        SSAOp::IntRem { .. } => ExecutionOpcode::IntRem,
        SSAOp::IntSRem { .. } => ExecutionOpcode::IntSRem,
        SSAOp::IntNegate { .. } => ExecutionOpcode::IntNegate,
        SSAOp::IntCarry { .. } => ExecutionOpcode::IntCarry,
        SSAOp::IntSCarry { .. } => ExecutionOpcode::IntSCarry,
        SSAOp::IntSBorrow { .. } => ExecutionOpcode::IntSBorrow,
        SSAOp::IntAnd { .. } => ExecutionOpcode::IntAnd,
        SSAOp::IntOr { .. } => ExecutionOpcode::IntOr,
        SSAOp::IntXor { .. } => ExecutionOpcode::IntXor,
        SSAOp::IntNot { .. } => ExecutionOpcode::IntNot,
        SSAOp::IntLeft { .. } => ExecutionOpcode::IntLeft,
        SSAOp::IntRight { .. } => ExecutionOpcode::IntRight,
        SSAOp::IntSRight { .. } => ExecutionOpcode::IntSRight,
        SSAOp::IntEqual { .. } => ExecutionOpcode::IntEqual,
        SSAOp::IntNotEqual { .. } => ExecutionOpcode::IntNotEqual,
        SSAOp::IntLess { .. } => ExecutionOpcode::IntLess,
        SSAOp::IntSLess { .. } => ExecutionOpcode::IntSLess,
        SSAOp::IntLessEqual { .. } => ExecutionOpcode::IntLessEqual,
        SSAOp::IntSLessEqual { .. } => ExecutionOpcode::IntSLessEqual,
        SSAOp::IntZExt { .. } => ExecutionOpcode::IntZExt,
        SSAOp::IntSExt { .. } => ExecutionOpcode::IntSExt,
        SSAOp::BoolNot { .. } => ExecutionOpcode::BoolNot,
        SSAOp::BoolAnd { .. } => ExecutionOpcode::BoolAnd,
        SSAOp::BoolOr { .. } => ExecutionOpcode::BoolOr,
        SSAOp::BoolXor { .. } => ExecutionOpcode::BoolXor,
        SSAOp::Piece { .. } => ExecutionOpcode::Piece,
        SSAOp::Subpiece { .. } => ExecutionOpcode::Subpiece,
        SSAOp::PopCount { .. } => ExecutionOpcode::PopCount,
        SSAOp::Lzcount { .. } => ExecutionOpcode::Lzcount,
        SSAOp::Branch { .. } => ExecutionOpcode::Branch,
        SSAOp::CBranch { .. } => ExecutionOpcode::CBranch,
        SSAOp::BranchInd { .. } => ExecutionOpcode::BranchInd,
        SSAOp::Call { .. } => ExecutionOpcode::Call,
        SSAOp::CallInd { .. } => ExecutionOpcode::CallInd,
        SSAOp::CallDefine { .. } => ExecutionOpcode::CallDefine,
        SSAOp::Return { .. } => ExecutionOpcode::Return,
        SSAOp::FloatAdd { .. } => ExecutionOpcode::FloatAdd,
        SSAOp::FloatSub { .. } => ExecutionOpcode::FloatSub,
        SSAOp::FloatMult { .. } => ExecutionOpcode::FloatMult,
        SSAOp::FloatDiv { .. } => ExecutionOpcode::FloatDiv,
        SSAOp::FloatNeg { .. } => ExecutionOpcode::FloatNeg,
        SSAOp::FloatAbs { .. } => ExecutionOpcode::FloatAbs,
        SSAOp::FloatSqrt { .. } => ExecutionOpcode::FloatSqrt,
        SSAOp::FloatCeil { .. } => ExecutionOpcode::FloatCeil,
        SSAOp::FloatFloor { .. } => ExecutionOpcode::FloatFloor,
        SSAOp::FloatRound { .. } => ExecutionOpcode::FloatRound,
        SSAOp::FloatNaN { .. } => ExecutionOpcode::FloatNaN,
        SSAOp::FloatEqual { .. } => ExecutionOpcode::FloatEqual,
        SSAOp::FloatNotEqual { .. } => ExecutionOpcode::FloatNotEqual,
        SSAOp::FloatLess { .. } => ExecutionOpcode::FloatLess,
        SSAOp::FloatLessEqual { .. } => ExecutionOpcode::FloatLessEqual,
        SSAOp::Int2Float { .. } => ExecutionOpcode::Int2Float,
        SSAOp::Float2Int { .. } => ExecutionOpcode::Float2Int,
        SSAOp::FloatFloat { .. } => ExecutionOpcode::FloatFloat,
        SSAOp::Trunc { .. } => ExecutionOpcode::Trunc,
        SSAOp::CallOther { .. } => ExecutionOpcode::CallOther,
        SSAOp::Nop => ExecutionOpcode::Nop,
        SSAOp::Unimplemented => ExecutionOpcode::Unimplemented,
        SSAOp::CpuId { .. } => ExecutionOpcode::CpuId,
        SSAOp::Breakpoint => ExecutionOpcode::Breakpoint,
        SSAOp::PtrAdd { .. } => ExecutionOpcode::PtrAdd,
        SSAOp::PtrSub { .. } => ExecutionOpcode::PtrSub,
        SSAOp::SegmentOp { .. } => ExecutionOpcode::SegmentOp,
        SSAOp::New { .. } => ExecutionOpcode::New,
        SSAOp::Cast { .. } => ExecutionOpcode::Cast,
        SSAOp::Extract { .. } => ExecutionOpcode::Extract,
        SSAOp::Insert { .. } => ExecutionOpcode::Insert,
        SSAOp::Select { .. } => ExecutionOpcode::Select,
    }
}

fn effect_for_op(inst: InstId, op: &SSAOp) -> Result<ExecutionEffect, ExecutionViewError> {
    match op {
        SSAOp::Phi { .. } => Err(ExecutionViewError::UnexpectedPhiOp(inst)),
        SSAOp::Load { space, .. } | SSAOp::Store { space, .. } => Ok(ExecutionEffect::Memory {
            space: *space,
            ordering: None,
        }),
        SSAOp::LoadLinked {
            space, ordering, ..
        }
        | SSAOp::StoreConditional {
            space, ordering, ..
        }
        | SSAOp::AtomicCAS {
            space, ordering, ..
        }
        | SSAOp::LoadGuarded {
            space, ordering, ..
        }
        | SSAOp::StoreGuarded {
            space, ordering, ..
        } => Ok(ExecutionEffect::Memory {
            space: *space,
            ordering: Some(*ordering),
        }),
        SSAOp::Fence { ordering } => Ok(ExecutionEffect::Fence {
            ordering: *ordering,
        }),
        SSAOp::Subpiece { offset, .. } => Ok(ExecutionEffect::Subpiece {
            offset_bytes: *offset,
        }),
        SSAOp::CallOther { userop, .. } => Ok(ExecutionEffect::CallOther { userop: *userop }),
        SSAOp::PtrAdd { element_size, .. } | SSAOp::PtrSub { element_size, .. } => {
            Ok(ExecutionEffect::Pointer {
                element_size: *element_size,
            })
        }
        SSAOp::Copy { .. }
        | SSAOp::IntAdd { .. }
        | SSAOp::IntSub { .. }
        | SSAOp::IntMult { .. }
        | SSAOp::IntDiv { .. }
        | SSAOp::IntSDiv { .. }
        | SSAOp::IntRem { .. }
        | SSAOp::IntSRem { .. }
        | SSAOp::IntNegate { .. }
        | SSAOp::IntCarry { .. }
        | SSAOp::IntSCarry { .. }
        | SSAOp::IntSBorrow { .. }
        | SSAOp::IntAnd { .. }
        | SSAOp::IntOr { .. }
        | SSAOp::IntXor { .. }
        | SSAOp::IntNot { .. }
        | SSAOp::IntLeft { .. }
        | SSAOp::IntRight { .. }
        | SSAOp::IntSRight { .. }
        | SSAOp::IntEqual { .. }
        | SSAOp::IntNotEqual { .. }
        | SSAOp::IntLess { .. }
        | SSAOp::IntSLess { .. }
        | SSAOp::IntLessEqual { .. }
        | SSAOp::IntSLessEqual { .. }
        | SSAOp::IntZExt { .. }
        | SSAOp::IntSExt { .. }
        | SSAOp::BoolNot { .. }
        | SSAOp::BoolAnd { .. }
        | SSAOp::BoolOr { .. }
        | SSAOp::BoolXor { .. }
        | SSAOp::Piece { .. }
        | SSAOp::PopCount { .. }
        | SSAOp::Lzcount { .. }
        | SSAOp::Branch { .. }
        | SSAOp::CBranch { .. }
        | SSAOp::BranchInd { .. }
        | SSAOp::Call { .. }
        | SSAOp::CallInd { .. }
        | SSAOp::CallDefine { .. }
        | SSAOp::Return { .. }
        | SSAOp::FloatAdd { .. }
        | SSAOp::FloatSub { .. }
        | SSAOp::FloatMult { .. }
        | SSAOp::FloatDiv { .. }
        | SSAOp::FloatNeg { .. }
        | SSAOp::FloatAbs { .. }
        | SSAOp::FloatSqrt { .. }
        | SSAOp::FloatCeil { .. }
        | SSAOp::FloatFloor { .. }
        | SSAOp::FloatRound { .. }
        | SSAOp::FloatNaN { .. }
        | SSAOp::FloatEqual { .. }
        | SSAOp::FloatNotEqual { .. }
        | SSAOp::FloatLess { .. }
        | SSAOp::FloatLessEqual { .. }
        | SSAOp::Int2Float { .. }
        | SSAOp::Float2Int { .. }
        | SSAOp::FloatFloat { .. }
        | SSAOp::Trunc { .. }
        | SSAOp::Nop
        | SSAOp::Unimplemented
        | SSAOp::CpuId { .. }
        | SSAOp::Breakpoint
        | SSAOp::SegmentOp { .. }
        | SSAOp::New { .. }
        | SSAOp::Cast { .. }
        | SSAOp::Extract { .. }
        | SSAOp::Insert { .. }
        | SSAOp::Select { .. } => Ok(ExecutionEffect::None),
    }
}

impl SsaArtifact {
    /// Bind executable graph access to this exact run-local artifact authority.
    pub const fn execution_view(&self) -> SsaExecutionView<'_> {
        SsaExecutionView { artifact: self }
    }
}

impl<'a> SsaExecutionView<'a> {
    fn block(self, id: BlockId) -> Option<ExecutionBlockRef<'a>> {
        let block = self.artifact.graph().block(id)?;
        if block.id != id
            || !graph_block_is_coherent(self.artifact.function(), self.artifact.graph(), block)
        {
            return None;
        }
        Some(ExecutionBlockRef { view: self, id })
    }

    /// Resolve the authoritative CFG entry as an artifact-bound block.
    pub fn entry_block(self) -> Option<ExecutionBlockRef<'a>> {
        let id = self.artifact.graph().entry;
        let block = self.block(id)?;
        let function_entry = self.artifact.function().entry_block()?;
        (function_entry.addr == block.addr()
            && self.artifact.graph().block_order.first() == Some(&id))
        .then_some(block)
    }

    /// Traverse all executable blocks in authoritative reverse-postorder.
    pub fn blocks(self) -> Result<Vec<ExecutionBlockRef<'a>>, ExecutionViewError> {
        let mut blocks = Vec::with_capacity(self.artifact.graph().block_order.len());
        for id in &self.artifact.graph().block_order {
            blocks.push(
                self.block(*id)
                    .ok_or(ExecutionViewError::IncoherentBlock(*id))?,
            );
        }
        Ok(blocks)
    }

    pub fn block_by_addr(self, addr: u64) -> Option<ExecutionBlockRef<'a>> {
        let id = self.artifact.graph().block_id_for_addr(addr)?;
        self.block(id).filter(|block| block.addr() == addr)
    }

    fn value(self, id: ValueId) -> Option<ExecutionValueRef<'a>> {
        let value = self.artifact.graph().value(id)?;
        if value.id != id
            || self.artifact.graph().value_id_for_var(&value.var) != Some(id)
            || validated_definition(self.artifact.graph(), id).is_none()
        {
            return None;
        }
        let expected_storage = self
            .artifact
            .function()
            .canonical_storage_for_var(&value.var)
            .or_else(|| {
                value.var.constant_bits().map(|bits| CanonicalStorageId {
                    space: CanonicalStorageSpace::Constant,
                    offset: bits,
                    size: value.var.size,
                })
            });
        (expected_storage == value.canonical_storage)
            .then_some(ExecutionValueRef { view: self, id })
    }

    fn inst(self, id: InstId) -> Option<ExecutionInstRef<'a>> {
        let inst = self.artifact.graph().inst(id)?;
        if inst.id != id || !self.inst_is_coherent(inst) {
            return None;
        }
        Some(ExecutionInstRef { view: self, id })
    }

    pub fn resolve_block(self, id: &ArtifactBlockId) -> Option<ExecutionBlockRef<'a>> {
        id.belongs_to(self.artifact)
            .then(|| self.block(id.local_id()))
            .flatten()
    }

    pub fn resolve_value(self, id: &ArtifactValueId) -> Option<ExecutionValueRef<'a>> {
        id.belongs_to(self.artifact)
            .then(|| self.value(id.local_id()))
            .flatten()
    }

    pub fn resolve_inst(self, id: &ArtifactInstId) -> Option<ExecutionInstRef<'a>> {
        id.belongs_to(self.artifact)
            .then(|| self.inst(id.local_id()))
            .flatten()
    }

    /// Resolve one exact, definition-free SSA carrier for canonical storage.
    ///
    /// Overlapping storage is not considered. Missing or duplicate exact
    /// carriers are explicit errors rather than alias/name fallbacks.
    pub fn unique_entry_value(
        self,
        storage: CanonicalStorageId,
    ) -> Result<ExecutionValueRef<'a>, EntryStorageError> {
        let mut candidates = self
            .artifact
            .graph()
            .values
            .iter()
            .filter(|value| value.canonical_storage == Some(storage))
            .filter(|value| validated_definition(self.artifact.graph(), value.id) == Some(None))
            .filter_map(|value| self.value(value.id));
        let first = candidates
            .next()
            .ok_or(EntryStorageError::Missing(storage))?;
        if candidates.next().is_some() {
            return Err(EntryStorageError::Ambiguous(storage));
        }
        Ok(first)
    }

    fn inst_is_coherent(self, inst: &GraphInst) -> bool {
        let Some(block) = self.block(inst.block) else {
            return false;
        };
        if block.graph().insts.get(inst.ordinal).copied() != Some(inst.id) {
            return false;
        }
        if !inst.inputs.iter().all(|input| self.value(*input).is_some()) {
            return false;
        }
        let output = inst.output.and_then(|output| self.value(output));
        if inst.output.is_some() != output.is_some()
            || inst.canonical_storage != output.and_then(|value| value.canonical_storage())
        {
            return false;
        }

        let function_block = self.artifact.function().get_block(block.addr()).unwrap();
        match &inst.payload {
            InstPayload::Phi { predecessors } => {
                let Some(phi) = function_block.phis.get(inst.ordinal) else {
                    return false;
                };
                if predecessors.len() != inst.inputs.len()
                    || predecessors.len() != phi.sources.len()
                    || !phi_predecessors_cover_block(block.graph(), predecessors)
                    || inst.output != self.artifact.graph().value_id_for_var(&phi.dst)
                {
                    return false;
                }
                let Some(output) = output else {
                    return false;
                };
                if inst.inputs.iter().any(|input| {
                    self.value(*input)
                        .is_none_or(|input| input.graph().var.size != output.graph().var.size)
                }) {
                    return false;
                }
                phi.sources
                    .iter()
                    .enumerate()
                    .all(|(index, (addr, source))| {
                        self.artifact.graph().block_id_for_addr(*addr)
                            == predecessors.get(index).copied()
                            && self.artifact.graph().value_id_for_var(source)
                                == inst.inputs.get(index).copied()
                    })
            }
            InstPayload::Op(op) => {
                let Some(op_index) = inst.ordinal.checked_sub(function_block.phis.len()) else {
                    return false;
                };
                let Some(function_op) = function_block.ops.get(op_index) else {
                    return false;
                };
                let sources = op.sources();
                op == function_op
                    && sources.len() == inst.inputs.len()
                    && sources.iter().enumerate().all(|(index, source)| {
                        self.artifact.graph().value_id_for_var(source)
                            == inst.inputs.get(index).copied()
                    })
                    && op
                        .dst()
                        .and_then(|dst| self.artifact.graph().value_id_for_var(dst))
                        == inst.output
                    && self
                        .artifact
                        .graph()
                        .inst_id_for_op_site(block.addr(), op_index)
                        == Some(inst.id)
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExecutionValueRef<'a> {
    view: SsaExecutionView<'a>,
    id: ValueId,
}

impl<'a> ExecutionValueRef<'a> {
    pub fn handle(self) -> ArtifactValueId {
        ArtifactValueId {
            authority: self.view.artifact.authority().clone(),
            local: self.id,
        }
    }

    pub fn width_bits(self) -> Result<u32, ExecutionViewError> {
        checked_width_bits(self.id, self.graph().var.size)
    }

    pub fn constant_bits(self) -> Option<u64> {
        self.graph().var.constant_bits()
    }

    pub fn canonical_storage(self) -> Option<CanonicalStorageId> {
        self.graph().canonical_storage
    }

    pub fn def_inst(self) -> Option<ExecutionInstRef<'a>> {
        self.view
            .artifact
            .graph()
            .def_inst(self.id)
            .and_then(|inst| self.view.inst(inst))
    }

    fn graph(self) -> &'a crate::GraphValue {
        self.view.artifact.graph().value(self.id).unwrap()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExecutionInstRef<'a> {
    view: SsaExecutionView<'a>,
    id: InstId,
}

impl<'a> ExecutionInstRef<'a> {
    pub fn handle(self) -> ArtifactInstId {
        ArtifactInstId {
            authority: self.view.artifact.authority().clone(),
            local: self.id,
        }
    }

    pub fn block(self) -> ExecutionBlockRef<'a> {
        self.view.block(self.graph().block).unwrap()
    }

    pub fn ordinal(self) -> usize {
        self.graph().ordinal
    }

    pub fn input_count(self) -> usize {
        self.graph().inputs.len()
    }

    pub fn input(self, index: usize) -> Option<ExecutionValueRef<'a>> {
        self.graph()
            .inputs
            .get(index)
            .copied()
            .and_then(|value| self.view.value(value))
    }

    pub fn output(self) -> Option<ExecutionValueRef<'a>> {
        self.graph().output.and_then(|value| self.view.value(value))
    }

    pub fn canonical_storage(self) -> Option<CanonicalStorageId> {
        self.graph().canonical_storage
    }

    pub fn is_phi(self) -> bool {
        matches!(self.graph().payload, InstPayload::Phi { .. })
    }

    pub fn phi_predecessor(self, index: usize) -> Option<ExecutionBlockRef<'a>> {
        let InstPayload::Phi { predecessors } = &self.graph().payload else {
            return None;
        };
        predecessors
            .get(index)
            .copied()
            .and_then(|block| self.view.block(block))
    }

    /// Return the complete name-independent executable operation.
    ///
    /// Operands preserve [`SSAOp::sources`] order, outputs and Phi edges are
    /// authority-bound, and all non-operand semantic payload is retained.
    pub fn operation(self) -> Result<ExecutionOperation, ExecutionViewError> {
        let inst = self.graph();
        let mut inputs = Vec::with_capacity(inst.inputs.len());
        for input in &inst.inputs {
            let value = self
                .view
                .value(*input)
                .ok_or(ExecutionViewError::IncoherentValue(*input))?;
            value.width_bits()?;
            inputs.push(value.handle());
        }
        let output = inst
            .output
            .map(|output| {
                let value = self
                    .view
                    .value(output)
                    .ok_or(ExecutionViewError::IncoherentValue(output))?;
                value.width_bits()?;
                Ok(value.handle())
            })
            .transpose()?;
        let operands = ExecutionOperands { inputs, output };

        match &inst.payload {
            InstPayload::Phi { predecessors } => {
                let incoming = predecessors
                    .iter()
                    .zip(&inst.inputs)
                    .map(|(predecessor, value)| {
                        let predecessor = self
                            .view
                            .block(*predecessor)
                            .ok_or(ExecutionViewError::IncoherentBlock(*predecessor))?
                            .handle();
                        let value = self
                            .view
                            .value(*value)
                            .ok_or(ExecutionViewError::IncoherentValue(*value))?
                            .handle();
                        Ok(ExecutionPhiIncoming { predecessor, value })
                    })
                    .collect::<Result<Vec<_>, ExecutionViewError>>()?;
                Ok(ExecutionOperation {
                    opcode: ExecutionOpcode::Phi,
                    operands,
                    effect: ExecutionEffect::Phi { incoming },
                })
            }
            InstPayload::Op(op) => Ok(ExecutionOperation {
                opcode: opcode_for_op(op),
                operands,
                effect: effect_for_op(self.id, op)?,
            }),
        }
    }

    fn graph(self) -> &'a GraphInst {
        self.view.artifact.graph().inst(self.id).unwrap()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExecutionBlockRef<'a> {
    view: SsaExecutionView<'a>,
    id: BlockId,
}

impl<'a> ExecutionBlockRef<'a> {
    pub fn handle(self) -> ArtifactBlockId {
        ArtifactBlockId {
            authority: self.view.artifact.authority().clone(),
            local: self.id,
        }
    }

    pub fn addr(self) -> u64 {
        self.graph().addr
    }

    pub fn size(self) -> u32 {
        self.graph().size
    }

    pub fn predecessor_count(self) -> usize {
        self.graph().predecessors.len()
    }

    pub fn predecessor(self, index: usize) -> Option<ExecutionBlockRef<'a>> {
        self.graph()
            .predecessors
            .get(index)
            .copied()
            .and_then(|block| self.view.block(block))
    }

    pub fn successor_count(self) -> usize {
        self.graph().successors.len()
    }

    pub fn successor(self, index: usize) -> Option<ExecutionBlockRef<'a>> {
        self.graph()
            .successors
            .get(index)
            .copied()
            .and_then(|block| self.view.block(block))
    }

    pub fn instruction_count(self) -> usize {
        self.graph().insts.len()
    }

    pub fn instruction(self, index: usize) -> Option<ExecutionInstRef<'a>> {
        self.graph()
            .insts
            .get(index)
            .copied()
            .and_then(|inst| self.view.inst(inst))
    }

    fn graph(self) -> &'a crate::GraphBlock {
        self.view.artifact.graph().block(self.id).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::collections::hash_map::DefaultHasher;

    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};

    use super::*;
    use crate::AssumptionSet;

    fn artifact(register_name: &str) -> SsaArtifact {
        let mut arch = ArchSpec::new("execution-view-test");
        arch.add_register(RegisterDef::new(register_name, 0x20, 8));
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::unique(0x40, 8),
            src: Varnode::register(0x20, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: Varnode::unique(0x48, 8),
            a: Varnode::unique(0x40, 8),
            b: Varnode::constant(7, 8),
        });
        SsaArtifact::for_symbolic(&[block], Some(&arch)).expect("symbolic artifact")
    }

    fn phi_artifact() -> SsaArtifact {
        let mut arch = ArchSpec::new("execution-phi-test");
        arch.add_register(RegisterDef::new("r0", 0x20, 8));
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::CBranch {
            target: Varnode::ram(0x1008, 8),
            cond: Varnode::register(0x28, 1),
        });
        let mut fallthrough = R2ILBlock::new(0x1004, 4);
        fallthrough.push(R2ILOp::Copy {
            dst: Varnode::register(0x20, 8),
            src: Varnode::constant(1, 8),
        });
        fallthrough.push(R2ILOp::Branch {
            target: Varnode::ram(0x100c, 8),
        });
        let mut taken = R2ILBlock::new(0x1008, 4);
        taken.push(R2ILOp::Copy {
            dst: Varnode::register(0x20, 8),
            src: Varnode::constant(2, 8),
        });
        taken.push(R2ILOp::Branch {
            target: Varnode::ram(0x100c, 8),
        });
        let mut merge = R2ILBlock::new(0x100c, 4);
        merge.push(R2ILOp::Copy {
            dst: Varnode::unique(0x40, 8),
            src: Varnode::register(0x20, 8),
        });
        SsaArtifact::raw(&[entry, fallthrough, taken, merge], Some(&arch)).expect("phi artifact")
    }

    fn every_ssa_op() -> Vec<SSAOp> {
        let v = || crate::SSAVar::new("const:display-spoof", 0, 8);
        vec![
            SSAOp::Phi {
                dst: v(),
                sources: vec![v()],
            },
            SSAOp::Copy { dst: v(), src: v() },
            SSAOp::Load {
                dst: v(),
                space: r2il::SpaceId::Ram,
                addr: v(),
            },
            SSAOp::Store {
                space: r2il::SpaceId::Ram,
                addr: v(),
                val: v(),
            },
            SSAOp::Fence {
                ordering: MemoryOrdering::SeqCst,
            },
            SSAOp::LoadLinked {
                dst: v(),
                space: r2il::SpaceId::Ram,
                addr: v(),
                ordering: MemoryOrdering::Acquire,
            },
            SSAOp::StoreConditional {
                result: Some(v()),
                space: r2il::SpaceId::Ram,
                addr: v(),
                val: v(),
                ordering: MemoryOrdering::Release,
            },
            SSAOp::AtomicCAS {
                dst: v(),
                space: r2il::SpaceId::Ram,
                addr: v(),
                expected: v(),
                replacement: v(),
                ordering: MemoryOrdering::AcqRel,
            },
            SSAOp::LoadGuarded {
                dst: v(),
                space: r2il::SpaceId::Ram,
                addr: v(),
                guard: v(),
                ordering: MemoryOrdering::Acquire,
            },
            SSAOp::StoreGuarded {
                space: r2il::SpaceId::Ram,
                addr: v(),
                val: v(),
                guard: v(),
                ordering: MemoryOrdering::Release,
            },
            SSAOp::IntAdd {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntSub {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntMult {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntDiv {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntSDiv {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntRem {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntSRem {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntNegate { dst: v(), src: v() },
            SSAOp::IntCarry {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntSCarry {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntSBorrow {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntAnd {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntOr {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntXor {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntNot { dst: v(), src: v() },
            SSAOp::IntLeft {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntRight {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntSRight {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntEqual {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntNotEqual {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntLess {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntSLess {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntLessEqual {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntSLessEqual {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::IntZExt { dst: v(), src: v() },
            SSAOp::IntSExt { dst: v(), src: v() },
            SSAOp::BoolNot { dst: v(), src: v() },
            SSAOp::BoolAnd {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::BoolOr {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::BoolXor {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::Piece {
                dst: v(),
                hi: v(),
                lo: v(),
            },
            SSAOp::Subpiece {
                dst: v(),
                src: v(),
                offset: 3,
            },
            SSAOp::PopCount { dst: v(), src: v() },
            SSAOp::Lzcount { dst: v(), src: v() },
            SSAOp::Branch { target: v() },
            SSAOp::CBranch {
                target: v(),
                cond: v(),
            },
            SSAOp::BranchInd { target: v() },
            SSAOp::Call { target: v() },
            SSAOp::CallInd { target: v() },
            SSAOp::CallDefine { dst: v() },
            SSAOp::Return { target: v() },
            SSAOp::FloatAdd {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::FloatSub {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::FloatMult {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::FloatDiv {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::FloatNeg { dst: v(), src: v() },
            SSAOp::FloatAbs { dst: v(), src: v() },
            SSAOp::FloatSqrt { dst: v(), src: v() },
            SSAOp::FloatCeil { dst: v(), src: v() },
            SSAOp::FloatFloor { dst: v(), src: v() },
            SSAOp::FloatRound { dst: v(), src: v() },
            SSAOp::FloatNaN { dst: v(), src: v() },
            SSAOp::FloatEqual {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::FloatNotEqual {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::FloatLess {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::FloatLessEqual {
                dst: v(),
                a: v(),
                b: v(),
            },
            SSAOp::Int2Float { dst: v(), src: v() },
            SSAOp::Float2Int { dst: v(), src: v() },
            SSAOp::FloatFloat { dst: v(), src: v() },
            SSAOp::Trunc { dst: v(), src: v() },
            SSAOp::CallOther {
                output: Some(v()),
                userop: 19,
                inputs: vec![v(), v()],
            },
            SSAOp::Nop,
            SSAOp::Unimplemented,
            SSAOp::CpuId { dst: v() },
            SSAOp::Breakpoint,
            SSAOp::PtrAdd {
                dst: v(),
                base: v(),
                index: v(),
                element_size: 16,
            },
            SSAOp::PtrSub {
                dst: v(),
                base: v(),
                index: v(),
                element_size: 32,
            },
            SSAOp::SegmentOp {
                dst: v(),
                segment: v(),
                offset: v(),
            },
            SSAOp::New { dst: v(), src: v() },
            SSAOp::Cast { dst: v(), src: v() },
            SSAOp::Extract {
                dst: v(),
                src: v(),
                position: v(),
            },
            SSAOp::Insert {
                dst: v(),
                src: v(),
                value: v(),
                position: v(),
            },
            SSAOp::Select {
                dst: v(),
                cond: v(),
                if_true: v(),
                if_false: v(),
            },
        ]
    }

    fn register_storage() -> CanonicalStorageId {
        CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0x20,
            size: 8,
        }
    }

    fn hash_of(value: &impl Hash) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn authority_bound_ids_follow_only_exact_artifact_shares() {
        let original = std::sync::Arc::new(artifact("r0"));
        let shared = std::sync::Arc::clone(&original);
        let rebuilt = artifact("r0");
        let assumed = original.with_assumptions(&AssumptionSet::default());
        let original_id = original
            .execution_view()
            .unique_entry_value(register_storage())
            .unwrap()
            .handle();
        let shared_id = shared
            .execution_view()
            .unique_entry_value(register_storage())
            .unwrap()
            .handle();
        let rebuilt_id = rebuilt
            .execution_view()
            .unique_entry_value(register_storage())
            .unwrap()
            .handle();
        let assumed_id = assumed
            .execution_view()
            .unique_entry_value(register_storage())
            .unwrap()
            .handle();

        assert_eq!(original_id, shared_id);
        assert_eq!(hash_of(&original_id), hash_of(&shared_id));
        assert_ne!(original_id, rebuilt_id);
        assert_ne!(original_id, assumed_id);
        assert_ne!(hash_of(&original_id), hash_of(&rebuilt_id));
        assert_ne!(hash_of(&original_id), hash_of(&assumed_id));
        assert!(
            original
                .execution_view()
                .resolve_value(&shared_id)
                .is_some()
        );
        assert!(
            original
                .execution_view()
                .resolve_value(&rebuilt_id)
                .is_none()
        );

        let mut ids = HashSet::new();
        ids.insert(original_id);
        ids.insert(shared_id);
        ids.insert(rebuilt_id);
        ids.insert(assumed_id);
        assert_eq!(ids.len(), 3);
    }

    #[test]
    fn entry_and_block_order_are_authority_bound_and_exact() {
        let artifact = phi_artifact();
        let view = artifact.execution_view();
        let entry = view.entry_block().expect("entry block");
        assert_eq!(
            entry.addr(),
            artifact.function().entry_block().unwrap().addr
        );
        assert!(entry.handle().belongs_to(&artifact));

        let blocks = view.blocks().expect("ordered blocks");
        let addresses = blocks.iter().map(|block| block.addr()).collect::<Vec<_>>();
        assert_eq!(addresses, artifact.function().block_addrs());
        assert_eq!(
            blocks.first().map(|block| block.handle()),
            Some(entry.handle())
        );
        assert!(
            blocks
                .iter()
                .all(|block| block.handle().belongs_to(&artifact))
        );
    }

    #[test]
    fn block_validation_rejects_cfg_address_edge_and_order_mutations() {
        let artifact = phi_artifact();
        let function = artifact.function();
        let original = artifact.graph();
        let entry = original.entry;
        assert!(graph_block_is_coherent(
            function,
            original,
            original.block(entry).unwrap()
        ));

        let mut bad_address = original.clone();
        bad_address.blocks[entry.0 as usize].addr ^= 0x100;
        assert!(!graph_block_is_coherent(
            function,
            &bad_address,
            bad_address.block(entry).unwrap()
        ));

        let mut bad_map = original.clone();
        bad_map.block_by_addr.remove(&0x1000);
        assert!(!graph_block_is_coherent(
            function,
            &bad_map,
            bad_map.block(entry).unwrap()
        ));

        let mut bad_order = original.clone();
        bad_order.block_order.swap(0, 1);
        assert!(!graph_block_is_coherent(
            function,
            &bad_order,
            bad_order.block(entry).unwrap()
        ));

        let mut bad_edges = original.clone();
        bad_edges.blocks[entry.0 as usize].successors.clear();
        assert!(!graph_block_is_coherent(
            function,
            &bad_edges,
            bad_edges.block(entry).unwrap()
        ));

        let successor = original.block(entry).unwrap().successors[0];
        let mut bad_inverse_edge = original.clone();
        bad_inverse_edge.blocks[successor.0 as usize]
            .predecessors
            .retain(|predecessor| *predecessor != entry);
        assert!(!graph_block_is_coherent(
            function,
            &bad_inverse_edge,
            bad_inverse_edge.block(entry).unwrap()
        ));
    }

    #[test]
    fn definition_validation_requires_an_exact_inverse_relation() {
        let artifact = artifact("r0");
        let graph = artifact.graph();
        let copy = graph.block(graph.entry).unwrap().insts[0];
        let output = graph.inst(copy).unwrap().output.unwrap();
        let entry = graph.inst(copy).unwrap().inputs[0];
        assert_eq!(validated_definition(graph, output), Some(Some(copy)));
        assert_eq!(validated_definition(graph, entry), Some(None));

        let mut missing_record = graph.clone();
        missing_record.def_of[output.0 as usize] = None;
        assert_eq!(validated_definition(&missing_record, output), None);

        let mut wrong_record = graph.clone();
        wrong_record.def_of[output.0 as usize] = Some(InstId(u32::MAX));
        assert_eq!(validated_definition(&wrong_record, output), None);

        let mut wrong_output = graph.clone();
        wrong_output.insts[copy.0 as usize].output = None;
        assert_eq!(validated_definition(&wrong_output, output), None);

        let mut fabricated_entry_def = graph.clone();
        fabricated_entry_def.insts[copy.0 as usize].output = Some(entry);
        assert_eq!(validated_definition(&fabricated_entry_def, entry), None);

        let mut truncated = graph.clone();
        truncated.def_of.pop();
        assert_eq!(validated_definition(&truncated, entry), None);
    }

    #[test]
    fn exact_block_instruction_and_value_lookups_remain_bound() {
        let first = artifact("r0");
        let second = artifact("r0");
        let view = first.execution_view();
        let block = view.block_by_addr(0x1000).expect("entry block");
        assert_eq!(block.addr(), 0x1000);
        assert_eq!(block.size(), 4);
        assert_eq!(block.instruction_count(), 2);

        let copy = block.instruction(0).expect("copy");
        assert!(!copy.is_phi());
        assert_eq!(copy.input_count(), 1);
        let input = copy.input(0).expect("register input");
        let output = copy.output().expect("copy output");
        assert_eq!(input.canonical_storage(), Some(register_storage()));
        assert_eq!(input.width_bits(), Ok(64));
        assert!(input.def_inst().is_none());
        assert_eq!(output.def_inst().unwrap().handle(), copy.handle());
        assert_eq!(view.resolve_block(&block.handle()).unwrap().addr(), 0x1000);
        assert_eq!(view.resolve_inst(&copy.handle()).unwrap().ordinal(), 0);
        assert!(
            second
                .execution_view()
                .resolve_block(&block.handle())
                .is_none()
        );
        assert!(
            second
                .execution_view()
                .resolve_inst(&copy.handle())
                .is_none()
        );
    }

    #[test]
    fn unique_entry_storage_requires_exact_single_carrier() {
        let artifact = artifact("r0");
        let view = artifact.execution_view();
        let entry = view.unique_entry_value(register_storage()).unwrap();
        assert_eq!(entry.canonical_storage(), Some(register_storage()));
        assert_eq!(entry.constant_bits(), None);

        let overlapping = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0x20,
            size: 4,
        };
        assert!(matches!(
            view.unique_entry_value(overlapping),
            Err(EntryStorageError::Missing(storage)) if storage == overlapping
        ));
    }

    #[test]
    fn display_name_spoofs_do_not_change_execution_identity_or_storage() {
        let ordinary = artifact("r0");
        let spoofed = artifact("const:deadbeef");
        let ordinary_view = ordinary.execution_view();
        let spoofed_view = spoofed.execution_view();
        let ordinary_entry = ordinary_view
            .unique_entry_value(register_storage())
            .unwrap();
        let spoofed_entry = spoofed_view.unique_entry_value(register_storage()).unwrap();

        assert_eq!(
            ordinary_entry.handle().local_id(),
            spoofed_entry.handle().local_id()
        );
        assert_eq!(ordinary_entry.width_bits(), spoofed_entry.width_bits());
        assert_eq!(
            ordinary_entry.canonical_storage(),
            spoofed_entry.canonical_storage()
        );
        assert_eq!(spoofed_entry.constant_bits(), None);
        assert_ne!(ordinary_entry.handle(), spoofed_entry.handle());

        let ordinary_block = ordinary_view.block_by_addr(0x1000).unwrap();
        let spoofed_block = spoofed_view.block_by_addr(0x1000).unwrap();
        assert_eq!(
            ordinary_block.handle().local_id(),
            spoofed_block.handle().local_id()
        );
        for index in 0..ordinary_block.instruction_count() {
            let ordinary_inst = ordinary_block.instruction(index).unwrap();
            let spoofed_inst = spoofed_block.instruction(index).unwrap();
            assert_eq!(
                ordinary_inst.handle().local_id(),
                spoofed_inst.handle().local_id()
            );
            assert_eq!(ordinary_inst.input_count(), spoofed_inst.input_count());
            assert_eq!(
                ordinary_inst
                    .output()
                    .map(|value| value.handle().local_id()),
                spoofed_inst.output().map(|value| value.handle().local_id())
            );
        }
    }

    #[test]
    fn operation_api_binds_ordered_operands_and_rejects_mutated_graph_semantics() {
        let artifact = artifact("r0");
        let view = artifact.execution_view();
        let block = view.block_by_addr(0x1000).unwrap();
        let copy = block.instruction(0).unwrap();
        let operation = copy.operation().unwrap();
        assert_eq!(operation.opcode(), ExecutionOpcode::Copy);
        assert_eq!(operation.effect(), &ExecutionEffect::None);
        assert_eq!(
            operation.operands().inputs(),
            &[copy.input(0).unwrap().handle()]
        );
        assert_eq!(
            operation.operands().output(),
            Some(&copy.output().unwrap().handle())
        );

        let add = block.instruction(1).unwrap();
        let add_operation = add.operation().unwrap();
        assert_eq!(add_operation.opcode(), ExecutionOpcode::IntAdd);
        assert_eq!(
            add_operation.operands().inputs(),
            &[
                add.input(0).unwrap().handle(),
                add.input(1).unwrap().handle()
            ]
        );

        let original = artifact
            .graph()
            .inst(copy.handle().local_id())
            .unwrap()
            .clone();
        assert!(view.inst_is_coherent(&original));
        let mut bad_arity = original.clone();
        bad_arity.inputs.clear();
        assert!(!view.inst_is_coherent(&bad_arity));
        let mut bad_storage = original.clone();
        bad_storage.canonical_storage = Some(CanonicalStorageId {
            space: CanonicalStorageSpace::Constant,
            offset: 0xdead,
            size: 8,
        });
        assert!(!view.inst_is_coherent(&bad_storage));
        let mut bad_payload = original;
        bad_payload.payload = InstPayload::Op(SSAOp::Nop);
        assert!(!view.inst_is_coherent(&bad_payload));
    }

    #[test]
    fn opcode_and_effect_mapping_is_exhaustive_and_retains_all_immediates() {
        let ops = every_ssa_op();
        let mut opcodes = HashSet::new();
        for (index, op) in ops.iter().enumerate() {
            assert!(
                opcodes.insert(opcode_for_op(op)),
                "duplicate opcode for {op:?}"
            );
            let effect = effect_for_op(InstId(index as u32), op);
            if matches!(op, SSAOp::Phi { .. }) {
                assert_eq!(effect, Err(ExecutionViewError::UnexpectedPhiOp(InstId(0))));
            } else {
                assert!(effect.is_ok(), "missing effect mapping for {op:?}");
            }
        }
        assert_eq!(opcodes.len(), ops.len());

        let subpiece = SSAOp::Subpiece {
            dst: crate::SSAVar::new("d", 1, 4),
            src: crate::SSAVar::new("s", 0, 8),
            offset: 3,
        };
        assert_eq!(
            effect_for_op(InstId(0), &subpiece),
            Ok(ExecutionEffect::Subpiece { offset_bytes: 3 })
        );
        let callother = SSAOp::CallOther {
            output: None,
            userop: 0x1234,
            inputs: Vec::new(),
        };
        assert_eq!(
            effect_for_op(InstId(0), &callother),
            Ok(ExecutionEffect::CallOther { userop: 0x1234 })
        );
        let load = SSAOp::Load {
            dst: crate::SSAVar::new("d", 1, 8),
            space: SpaceId::Custom(0x1234),
            addr: crate::SSAVar::new("a", 0, 8),
        };
        assert_eq!(
            effect_for_op(InstId(0), &load),
            Ok(ExecutionEffect::Memory {
                space: SpaceId::Custom(0x1234),
                ordering: None,
            })
        );
    }

    #[test]
    fn phi_requires_duplicate_free_exact_predecessor_cover_and_typed_incoming() {
        let artifact = phi_artifact();
        let view = artifact.execution_view();
        let block = view.block_by_addr(0x100c).expect("merge block");
        assert_eq!(block.predecessor_count(), 2);
        let phi = block.instruction(0).expect("merge phi");
        assert!(phi.is_phi());
        let operation = phi.operation().expect("typed phi operation");
        assert_eq!(operation.opcode(), ExecutionOpcode::Phi);
        let ExecutionEffect::Phi { incoming } = operation.effect() else {
            panic!("expected typed Phi effect");
        };
        assert_eq!(incoming.len(), block.predecessor_count());
        for (index, incoming) in incoming.iter().enumerate() {
            assert!(incoming.predecessor().belongs_to(&artifact));
            assert!(incoming.value().belongs_to(&artifact));
            assert_eq!(
                incoming.predecessor(),
                &phi.phi_predecessor(index).unwrap().handle()
            );
            assert_eq!(incoming.value(), &phi.input(index).unwrap().handle());
        }

        let graph_block = artifact.graph().block(block.handle().local_id()).unwrap();
        let original = artifact
            .graph()
            .inst(phi.handle().local_id())
            .unwrap()
            .clone();
        let InstPayload::Phi { predecessors } = &original.payload else {
            panic!("expected graph Phi");
        };
        assert!(phi_predecessors_cover_block(graph_block, predecessors));
        let mut reordered = predecessors.clone();
        reordered.reverse();
        assert!(phi_predecessors_cover_block(graph_block, &reordered));
        let duplicate = vec![predecessors[0], predecessors[0]];
        assert!(!phi_predecessors_cover_block(graph_block, &duplicate));
        assert!(!phi_predecessors_cover_block(
            graph_block,
            &predecessors[..1]
        ));
        let mut extra = predecessors.clone();
        extra.push(BlockId(u32::MAX));
        assert!(!phi_predecessors_cover_block(graph_block, &extra));

        let mut mutated = original;
        mutated.payload = InstPayload::Phi {
            predecessors: duplicate,
        };
        assert!(!view.inst_is_coherent(&mutated));
    }

    #[test]
    fn width_conversion_is_exact_and_reports_overflow() {
        assert_eq!(checked_width_bits(ValueId(7), 8), Ok(64));
        assert_eq!(
            checked_width_bits(ValueId(7), u32::MAX),
            Err(ExecutionViewError::WidthOverflow {
                value: ValueId(7),
                size_bytes: u32::MAX,
            })
        );
    }
}
