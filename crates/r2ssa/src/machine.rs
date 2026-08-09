//! Ownership-safe machine expression representation.
//!
//! This module is the semantic boundary between prepared SSA and renderers. It
//! deliberately excludes presentation names and output-tree positions. Source
//! values are identified by artifact-local [`ValueId`] plus an explicit width;
//! persistent provenance is carried by canonical instruction and obligation IDs.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::function::{SsaArtifact, StackAddressBase};
use crate::graph::{BlockId, GraphInst, GraphValue, InstId, InstPayload, ValueId};
use crate::machine_context::MachineMemoryEndianness;
use crate::obligation::{CanonicalInstructionId, SemanticObligationId};
use crate::op::SSAOp;
use crate::semantic::{ObjectId, ObjectKind, StructuredAccessId};

/// Opaque, artifact-local handle into a [`MachineExprArena`].
///
/// This is an ownership handle, not a persistent semantic identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct MachineExprId(u32);

impl MachineExprId {
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Name-independent reference to one prepared SSA value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct MachineValueBinding {
    value: ValueId,
    width_bits: u32,
}

impl MachineValueBinding {
    pub const fn value(self) -> ValueId {
        self.value
    }

    pub const fn width_bits(self) -> u32 {
        self.width_bits
    }
}

/// Exact use of one artifact-local machine value.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineValueUse {
    binding: MachineValueBinding,
    ty: MachineType,
    constant: Option<MachineBitVector>,
    producer: Option<CanonicalInstructionId>,
    memory_access: Option<StructuredAccessId>,
}

impl MachineValueUse {
    pub fn from_artifact(
        artifact: &SsaArtifact,
        value: ValueId,
    ) -> Result<Self, MachineBuildError> {
        let graph_value = artifact
            .graph()
            .value(value)
            .ok_or(MachineBuildError::MissingGraphValue(value))?;
        let binding = binding_for_value(graph_value)?;
        Self::from_artifact_with_type(
            artifact,
            value,
            integer_type(binding.width_bits, MachineSignedness::Unsigned),
            None,
        )
    }

    /// Derive the exact typed address use for one structured memory access.
    pub fn memory_address_for_access(
        artifact: &SsaArtifact,
        access: StructuredAccessId,
    ) -> Result<Self, MachineBuildError> {
        let fact = artifact
            .facts()
            .structured
            .memory_accesses
            .get(&access)
            .filter(|fact| {
                fact.id == access
                    && fact.provenance_complete
                    && artifact.graph().op_site_for_inst(access.inst)
                        == Some((fact.block_addr, fact.op_index))
                    && artifact.objects().object(fact.object).is_some()
                    && artifact.objects().object_for_value(fact.address) == Some(fact.object)
            })
            .ok_or(MachineBuildError::EntityMismatch(access.inst))?;
        let source_space = artifact
            .machine_context()
            .memory_space_at(fact.block_addr, fact.op_index)
            .ok_or(MachineBuildError::MachineContextMismatch)?;
        let model = artifact.machine_context().memory_model();
        let space_model = model
            .space(source_space)
            .filter(|space| {
                model.is_available()
                    && model.is_coherent()
                    && space.address_bits() > 0
                    && space.word_size_bytes() > 0
            })
            .ok_or(MachineBuildError::MachineContextMismatch)?;
        let space = MachineAddressSpace::from(source_space);
        Self::from_artifact_with_type(
            artifact,
            fact.address,
            MachineType::Address {
                width_bits: space_model.address_bits(),
                space,
                provenance: machine_address_provenance(artifact, fact.object),
            },
            Some(access),
        )
    }

    fn from_artifact_with_type(
        artifact: &SsaArtifact,
        value: ValueId,
        ty: MachineType,
        memory_access: Option<StructuredAccessId>,
    ) -> Result<Self, MachineBuildError> {
        let graph_value = artifact
            .graph()
            .value(value)
            .ok_or(MachineBuildError::MissingGraphValue(value))?;
        let binding = binding_for_value(graph_value)?;
        if binding.width_bits != ty.width_bits() {
            return Err(MachineBuildError::InvalidExpressionType {
                expr: MachineExprId(u32::MAX),
            });
        }
        let constant = graph_value
            .var
            .constant_bits()
            .map(|bits| bit_vector(value, binding.width_bits, bits))
            .transpose()?;
        let producer = artifact
            .graph()
            .def_inst(value)
            .map(|inst| {
                artifact
                    .obligations()
                    .instruction_for_inst(inst)
                    .map(|instruction| instruction.id)
                    .ok_or(MachineBuildError::MissingInstructionDisposition(inst))
            })
            .transpose()?;
        Ok(Self {
            binding,
            ty,
            constant,
            producer,
            memory_access,
        })
    }

    pub const fn binding(&self) -> MachineValueBinding {
        self.binding
    }

    pub const fn ty(&self) -> &MachineType {
        &self.ty
    }

    pub const fn constant(&self) -> Option<MachineBitVector> {
        self.constant
    }

    pub const fn producer(&self) -> Option<CanonicalInstructionId> {
        self.producer
    }

    pub const fn memory_access(&self) -> Option<StructuredAccessId> {
        self.memory_access
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineSignedness {
    Unsigned,
    Signed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineAddressSpace {
    Ram,
    Register,
    Unique,
    Constant,
    Custom(u32),
}

impl From<r2il::SpaceId> for MachineAddressSpace {
    fn from(space: r2il::SpaceId) -> Self {
        match space {
            r2il::SpaceId::Ram => Self::Ram,
            r2il::SpaceId::Register => Self::Register,
            r2il::SpaceId::Unique => Self::Unique,
            r2il::SpaceId::Const => Self::Constant,
            r2il::SpaceId::Custom(id) => Self::Custom(id),
        }
    }
}

/// Prepared origin annotation for an address value.
///
/// This is not standalone lvalue or memory-access proof. Object association is
/// artifact-local and certification must additionally validate the exact
/// structured access, typed address space, and machine-memory policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineAddressProvenance {
    Unknown,
    Parameter { index: u32 },
    Stack { base: MachineStackBase, offset: i64 },
    Global { address: u64 },
    Derived { base: MachineValueBinding },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineStackBase {
    FramePointer,
    StackPointer,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineType {
    Bool {
        storage_bits: u32,
    },
    Integer {
        width_bits: u32,
        signedness: MachineSignedness,
    },
    Address {
        width_bits: u32,
        space: MachineAddressSpace,
        provenance: MachineAddressProvenance,
    },
}

impl MachineType {
    pub const fn width_bits(&self) -> u32 {
        match self {
            Self::Bool { storage_bits } => *storage_bits,
            Self::Integer { width_bits, .. } | Self::Address { width_bits, .. } => *width_bits,
        }
    }

    pub const fn signedness(&self) -> Option<MachineSignedness> {
        match self {
            Self::Integer { signedness, .. } => Some(*signedness),
            Self::Bool { .. } | Self::Address { .. } => None,
        }
    }
}

/// Exact bitvector constant carried by prepared SSA.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct MachineBitVector {
    width_bits: u32,
    bits: u64,
}

impl MachineBitVector {
    pub const fn width_bits(self) -> u32 {
        self.width_bits
    }

    pub const fn bits(self) -> u64 {
        self.bits
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineArithmeticOp {
    Add,
    Subtract,
    Multiply,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineArithmeticMode {
    Wrapping,
    Checked,
}

/// Exact carry/overflow predicate produced by a fixed-width machine operation.
///
/// These are boolean results over the input bit patterns. They are distinct
/// from comparisons: signed carry and signed borrow describe overflow of the
/// corresponding wrapping arithmetic operation, not ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineArithmeticFlagOp {
    UnsignedCarry,
    SignedCarry,
    SignedBorrow,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineBitwiseOp {
    And,
    Or,
    Xor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineBooleanOp {
    And,
    Or,
    Xor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineShiftKind {
    Left,
    LogicalRight,
    ArithmeticRight,
}

/// Machine behavior when a shift count is at least the value width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineOvershiftBehavior {
    Zero,
    SignFill,
    MaskCount,
    Checked,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineComparisonOp {
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineCastKind {
    ZeroExtend,
    SignExtend,
    Truncate,
    BitReinterpret,
    IntegerToAddress,
    AddressToInteger,
}

/// One immutable machine expression node.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum MachineExprKind {
    Source {
        binding: MachineValueBinding,
    },
    Constant {
        binding: MachineValueBinding,
        value: MachineBitVector,
    },
    MemoryRead {
        access: StructuredAccessId,
        object: ObjectId,
        space: MachineAddressSpace,
        endianness: MachineMemoryEndianness,
        word_size_bytes: u32,
        address: MachineExprId,
        width_bits: u32,
    },
    Copy {
        input: MachineExprId,
    },
    Arithmetic {
        op: MachineArithmeticOp,
        mode: MachineArithmeticMode,
        left: MachineExprId,
        right: MachineExprId,
    },
    ArithmeticFlag {
        op: MachineArithmeticFlagOp,
        left: MachineExprId,
        right: MachineExprId,
    },
    Bitwise {
        op: MachineBitwiseOp,
        left: MachineExprId,
        right: MachineExprId,
    },
    BitwiseNot {
        input: MachineExprId,
    },
    BooleanNot {
        input: MachineExprId,
    },
    Boolean {
        op: MachineBooleanOp,
        left: MachineExprId,
        right: MachineExprId,
    },
    Shift {
        kind: MachineShiftKind,
        overshift: MachineOvershiftBehavior,
        value: MachineExprId,
        count: MachineExprId,
    },
    Compare {
        op: MachineComparisonOp,
        interpretation: MachineSignedness,
        left: MachineExprId,
        right: MachineExprId,
    },
    Cast {
        kind: MachineCastKind,
        input: MachineExprId,
    },
    Extract {
        input: MachineExprId,
        lsb_bits: u32,
    },
    Select {
        condition: MachineExprId,
        if_true: MachineExprId,
        if_false: MachineExprId,
    },
    Phi {
        inputs: Box<[MachineExprId]>,
    },
}

impl MachineExprKind {
    fn children(&self) -> Vec<MachineExprId> {
        match self {
            Self::Source { .. } | Self::Constant { .. } => Vec::new(),
            Self::MemoryRead { address, .. } => vec![*address],
            Self::Copy { input }
            | Self::BitwiseNot { input }
            | Self::BooleanNot { input }
            | Self::Cast { input, .. }
            | Self::Extract { input, .. } => vec![*input],
            Self::Arithmetic { left, right, .. }
            | Self::ArithmeticFlag { left, right, .. }
            | Self::Bitwise { left, right, .. }
            | Self::Boolean { left, right, .. }
            | Self::Compare { left, right, .. } => vec![*left, *right],
            Self::Shift { value, count, .. } => vec![*value, *count],
            Self::Select {
                condition,
                if_true,
                if_false,
            } => vec![*condition, *if_true, *if_false],
            Self::Phi { inputs } => inputs.to_vec(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineExpr {
    ty: MachineType,
    origin: Option<CanonicalInstructionId>,
    kind: MachineExprKind,
}

impl MachineExpr {
    pub const fn ty(&self) -> &MachineType {
        &self.ty
    }

    pub const fn origin(&self) -> Option<CanonicalInstructionId> {
        self.origin
    }

    pub const fn kind(&self) -> &MachineExprKind {
        &self.kind
    }
}

/// Immutable owner of all expression nodes for one machine function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineExprArena {
    nodes: Box<[MachineExpr]>,
}

impl MachineExprArena {
    pub fn get(&self, id: MachineExprId) -> Option<&MachineExpr> {
        self.nodes.get(id.index())
    }

    pub fn iter(&self) -> impl Iterator<Item = (MachineExprId, &MachineExpr)> {
        self.nodes
            .iter()
            .enumerate()
            .map(|(index, expr)| (MachineExprId(index as u32), expr))
    }

    pub const fn len(&self) -> usize {
        self.nodes.len()
    }

    pub const fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

/// Proof-bearing semantic root for one source instruction output.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineEntity {
    output: MachineValueBinding,
    root: MachineExprId,
    producer: CanonicalInstructionId,
    source_obligations: BTreeSet<SemanticObligationId>,
}

impl MachineEntity {
    pub const fn output(&self) -> MachineValueBinding {
        self.output
    }

    pub const fn root(&self) -> MachineExprId {
        self.root
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn source_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.source_obligations
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum MachineBuildError {
    IncompleteObligationInventory,
    MissingGraphValue(ValueId),
    MissingGraphBlock(BlockId),
    DuplicateBlockAddress(u64),
    TopologyMismatch,
    MachineContextMismatch,
    MissingInstruction(InstId),
    MissingInstructionDisposition(InstId),
    MissingOutput(InstId),
    InvalidValueWidth {
        value: ValueId,
        size_bytes: u32,
    },
    ConstantTooWide {
        value: ValueId,
        width_bits: u32,
    },
    WrongOperandCount {
        inst: InstId,
        expected: usize,
        actual: usize,
    },
    WidthMismatch {
        inst: InstId,
        expected_bits: u32,
        actual_bits: u32,
    },
    InvalidCastWidth {
        inst: InstId,
        kind: MachineCastKind,
        from_bits: u32,
        to_bits: u32,
    },
    InvalidSubpiece {
        inst: InstId,
        source_bits: u32,
        result_bits: u32,
        lsb_bits: u32,
    },
    InvalidChild {
        expr: MachineExprId,
        child: MachineExprId,
    },
    InvalidExpressionType {
        expr: MachineExprId,
    },
    DuplicateEntity(ValueId),
    EntityMismatch(InstId),
    ObligationMismatch(InstId),
    UnsupportedOperation {
        inst: InstId,
        op: Box<SSAOp>,
    },
}

impl std::fmt::Display for MachineBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "machine expression construction failed: {self:?}")
    }
}

impl std::error::Error for MachineBuildError {}

/// One value producer that could not enter the machine-expression vocabulary.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MachineProjectionFailure {
    output: ValueId,
    producer: CanonicalInstructionId,
    error: MachineBuildError,
}

impl MachineProjectionFailure {
    pub const fn output(&self) -> ValueId {
        self.output
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn error(&self) -> &MachineBuildError {
        &self.error
    }
}

/// Partial machine projection with explicit, source-bound failures.
///
/// Unsupported value semantics remain in `failures`; they are never converted
/// to input leaves or guessed expressions. `r2cert` can therefore residualize
/// both the failed producer and all dependent value producers exactly once.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MachineProjection {
    machine: MachineFunction,
    failures: Box<[MachineProjectionFailure]>,
}

impl MachineProjection {
    pub fn from_artifact(artifact: &SsaArtifact) -> Result<Self, MachineBuildError> {
        if !artifact.obligations().is_complete() {
            return Err(MachineBuildError::IncompleteObligationInventory);
        }
        let graph = artifact.graph();
        let mut builder = MachineBuilder::default();
        let mut entities = Vec::new();
        let mut failures = Vec::new();

        for inst in &graph.insts {
            let Some(output_id) = inst.output else {
                continue;
            };
            let disposition = artifact
                .obligations()
                .instruction_for_inst(inst.id)
                .ok_or(MachineBuildError::MissingInstructionDisposition(inst.id))?;
            let graph_value = graph
                .value(output_id)
                .ok_or(MachineBuildError::MissingGraphValue(output_id))?;
            let output = binding_for_value(graph_value)?;
            match builder.lower_inst(artifact, inst, disposition.id, output) {
                Ok(root) => entities.push(MachineEntity {
                    output,
                    root,
                    producer: disposition.id,
                    source_obligations: disposition.obligations.clone(),
                }),
                Err(error @ MachineBuildError::UnsupportedOperation { .. }) => {
                    failures.push(MachineProjectionFailure {
                        output: output_id,
                        producer: disposition.id,
                        error,
                    });
                }
                Err(error) => return Err(error),
            }
        }

        let projection = Self {
            machine: MachineFunction {
                arena: MachineExprArena {
                    nodes: builder.nodes.into_boxed_slice(),
                },
                entities: entities.into_boxed_slice(),
            },
            failures: failures.into_boxed_slice(),
        };
        projection.validate_against(artifact)?;
        Ok(projection)
    }

    pub const fn arena(&self) -> &MachineExprArena {
        self.machine.arena()
    }

    pub const fn entities(&self) -> &[MachineEntity] {
        self.machine.entities()
    }

    pub const fn failures(&self) -> &[MachineProjectionFailure] {
        &self.failures
    }

    pub fn expr(&self, id: MachineExprId) -> Option<&MachineExpr> {
        self.machine.expr(id)
    }

    pub fn entity_for_output(&self, value: ValueId) -> Option<&MachineEntity> {
        self.machine.entity_for_output(value)
    }

    pub fn entity_for_producer(&self, producer: CanonicalInstructionId) -> Option<&MachineEntity> {
        self.machine.entity_for_producer(producer)
    }

    pub fn failure_for_output(&self, value: ValueId) -> Option<&MachineProjectionFailure> {
        self.failures.iter().find(|failure| failure.output == value)
    }

    pub fn validate_against(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        let entities = self.machine.validate_entities_against(artifact)?;
        let graph = artifact.graph();
        let mut failed_outputs = BTreeMap::new();
        for failure in &self.failures {
            if failed_outputs.insert(failure.output, failure).is_some()
                || entities.contains_key(&failure.output)
            {
                return Err(MachineBuildError::DuplicateEntity(failure.output));
            }
            let inst_id = graph
                .def_inst(failure.output)
                .ok_or(MachineBuildError::EntityMismatch(InstId(u32::MAX)))?;
            let disposition = artifact
                .obligations()
                .instruction_for_inst(inst_id)
                .ok_or(MachineBuildError::MissingInstructionDisposition(inst_id))?;
            if disposition.id != failure.producer {
                return Err(MachineBuildError::EntityMismatch(inst_id));
            }
        }
        for inst in &graph.insts {
            let Some(output) = inst.output else {
                continue;
            };
            if entities.contains_key(&output) == failed_outputs.contains_key(&output) {
                return Err(MachineBuildError::EntityMismatch(inst.id));
            }
        }
        Ok(())
    }

    fn into_machine(self) -> MachineFunction {
        self.machine
    }
}

/// Immutable machine-semantic projection of the value-producing SSA graph.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MachineFunction {
    arena: MachineExprArena,
    entities: Box<[MachineEntity]>,
}

impl MachineFunction {
    /// Construct machine expressions only from prepared, name-independent facts.
    ///
    /// Effect-only and control-only instructions have no expression output and are
    /// intentionally outside this layer. Any unsupported value-producing operation
    /// fails explicitly instead of falling back to textual lowering.
    pub fn from_artifact(artifact: &SsaArtifact) -> Result<Self, MachineBuildError> {
        let projection = MachineProjection::from_artifact(artifact)?;
        if let Some(failure) = projection.failures.first() {
            return Err(failure.error.clone());
        }
        let function = projection.into_machine();
        function.validate_against(artifact)?;
        Ok(function)
    }

    pub const fn arena(&self) -> &MachineExprArena {
        &self.arena
    }

    pub const fn entities(&self) -> &[MachineEntity] {
        &self.entities
    }

    pub fn expr(&self, id: MachineExprId) -> Option<&MachineExpr> {
        self.arena.get(id)
    }

    pub fn entity_for_output(&self, value: ValueId) -> Option<&MachineEntity> {
        self.entities
            .iter()
            .find(|entity| entity.output.value == value)
    }

    pub fn entity_for_producer(&self, producer: CanonicalInstructionId) -> Option<&MachineEntity> {
        self.entities
            .iter()
            .find(|entity| entity.producer == producer)
    }

    /// Recheck all arena and source-identity invariants against the owning artifact.
    pub fn validate_against(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        let by_output = self.validate_entities_against(artifact)?;
        for inst in &artifact.graph().insts {
            let Some(output) = inst.output else {
                continue;
            };
            if !by_output.contains_key(&output) {
                return Err(MachineBuildError::EntityMismatch(inst.id));
            }
        }
        Ok(())
    }

    fn validate_entities_against<'a>(
        &'a self,
        artifact: &SsaArtifact,
    ) -> Result<BTreeMap<ValueId, &'a MachineEntity>, MachineBuildError> {
        if !artifact.obligations().is_complete() {
            return Err(MachineBuildError::IncompleteObligationInventory);
        }
        self.validate_arena(artifact)?;

        let graph = artifact.graph();
        let mut by_output = BTreeMap::new();
        for entity in &self.entities {
            if by_output.insert(entity.output.value, entity).is_some() {
                return Err(MachineBuildError::DuplicateEntity(entity.output.value));
            }
            let value = graph
                .value(entity.output.value)
                .ok_or(MachineBuildError::MissingGraphValue(entity.output.value))?;
            if binding_for_value(value)? != entity.output {
                return Err(MachineBuildError::EntityMismatch(
                    graph
                        .def_inst(entity.output.value)
                        .ok_or(MachineBuildError::EntityMismatch(InstId(u32::MAX)))?,
                ));
            }
            let inst_id = graph
                .def_inst(entity.output.value)
                .ok_or(MachineBuildError::EntityMismatch(InstId(u32::MAX)))?;
            let disposition = artifact
                .obligations()
                .instruction_for_inst(inst_id)
                .ok_or(MachineBuildError::MissingInstructionDisposition(inst_id))?;
            if disposition.id != entity.producer
                || self
                    .arena
                    .get(entity.root)
                    .is_none_or(|root| root.origin != Some(entity.producer))
            {
                return Err(MachineBuildError::EntityMismatch(inst_id));
            }
            if disposition.obligations != entity.source_obligations
                || entity
                    .source_obligations
                    .iter()
                    .any(|id| id.instruction != entity.producer)
            {
                return Err(MachineBuildError::ObligationMismatch(inst_id));
            }
            let inst = graph
                .inst(inst_id)
                .ok_or(MachineBuildError::MissingInstruction(inst_id))?;
            self.validate_entity_shape(artifact, inst, entity)?;
        }
        Ok(by_output)
    }

    fn validate_arena(&self, artifact: &SsaArtifact) -> Result<(), MachineBuildError> {
        let address_nodes = self
            .arena
            .iter()
            .filter_map(|(_, expression)| match expression.kind() {
                MachineExprKind::MemoryRead { address, .. } => Some(*address),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        for (id, expr) in self.arena.iter() {
            for child in expr.kind.children() {
                if child.index() >= id.index() || self.arena.get(child).is_none() {
                    return Err(MachineBuildError::InvalidChild { expr: id, child });
                }
            }
            self.validate_expr_type(id, expr)?;
            match &expr.kind {
                MachineExprKind::Source { binding } => {
                    let value = artifact
                        .graph()
                        .value(binding.value)
                        .ok_or(MachineBuildError::MissingGraphValue(binding.value))?;
                    if binding_for_value(value)? != *binding
                        || value.var.constant_bits().is_some()
                        || (matches!(expr.ty, MachineType::Bool { .. })
                            && !value_has_boolean_producer(artifact.graph(), binding.value))
                        || (matches!(expr.ty, MachineType::Address { .. })
                            && !address_nodes.contains(&id))
                    {
                        return Err(MachineBuildError::InvalidExpressionType { expr: id });
                    }
                }
                MachineExprKind::Constant { binding, value } => {
                    let graph_value = artifact
                        .graph()
                        .value(binding.value)
                        .ok_or(MachineBuildError::MissingGraphValue(binding.value))?;
                    let source_bits = graph_value
                        .var
                        .constant_bits()
                        .ok_or(MachineBuildError::InvalidExpressionType { expr: id })?;
                    if binding_for_value(graph_value)? != *binding
                        || *value != bit_vector(binding.value, binding.width_bits, source_bits)?
                        || matches!(expr.ty, MachineType::Bool { .. })
                        || (matches!(expr.ty, MachineType::Address { .. })
                            && !address_nodes.contains(&id))
                    {
                        return Err(MachineBuildError::InvalidExpressionType { expr: id });
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn validate_expr_type(
        &self,
        id: MachineExprId,
        expr: &MachineExpr,
    ) -> Result<(), MachineBuildError> {
        if expr.ty.width_bits() == 0 {
            return Err(MachineBuildError::InvalidExpressionType { expr: id });
        }
        let child = |child| {
            self.arena
                .get(child)
                .ok_or(MachineBuildError::InvalidChild { expr: id, child })
        };
        let same_width = |child: &MachineExpr| child.ty.width_bits() == expr.ty.width_bits();
        let valid = match &expr.kind {
            MachineExprKind::Source { binding } | MachineExprKind::Constant { binding, .. } => {
                expr.ty == integer_type(binding.width_bits, MachineSignedness::Unsigned)
                    || expr.ty
                        == MachineType::Bool {
                            storage_bits: binding.width_bits,
                        }
                    || matches!(
                        expr.ty,
                        MachineType::Address { width_bits, .. }
                            if width_bits == binding.width_bits
                    )
            }
            MachineExprKind::MemoryRead {
                space,
                endianness,
                word_size_bytes,
                address,
                width_bits,
                ..
            } => {
                expr.ty == integer_type(*width_bits, MachineSignedness::Unsigned)
                    && *word_size_bytes > 0
                    && *endianness != MachineMemoryEndianness::Unknown
                    && matches!(
                        child(*address)?.ty,
                        MachineType::Address {
                            space: address_space,
                            ..
                        } if address_space == *space
                    )
            }
            MachineExprKind::Copy { input } | MachineExprKind::BitwiseNot { input } => {
                same_width(child(*input)?)
            }
            MachineExprKind::BooleanNot { input } => {
                matches!(expr.ty, MachineType::Bool { .. }) && child(*input)?.ty == expr.ty
            }
            MachineExprKind::Boolean { left, right, .. } => {
                matches!(expr.ty, MachineType::Bool { .. })
                    && child(*left)?.ty == expr.ty
                    && child(*right)?.ty == expr.ty
            }
            MachineExprKind::Arithmetic { left, right, .. }
            | MachineExprKind::Bitwise { left, right, .. } => {
                same_width(child(*left)?) && same_width(child(*right)?)
            }
            MachineExprKind::ArithmeticFlag { left, right, .. } => {
                matches!(expr.ty, MachineType::Bool { .. })
                    && child(*left)?.ty.width_bits() == child(*right)?.ty.width_bits()
            }
            MachineExprKind::Shift {
                kind,
                overshift,
                value,
                count,
            } => {
                let overshift_matches = matches!(
                    (kind, overshift),
                    (
                        MachineShiftKind::Left | MachineShiftKind::LogicalRight,
                        MachineOvershiftBehavior::Zero
                    ) | (
                        MachineShiftKind::ArithmeticRight,
                        MachineOvershiftBehavior::SignFill
                    )
                );
                same_width(child(*value)?)
                    && child(*count)?.ty.width_bits() > 0
                    && overshift_matches
            }
            MachineExprKind::Compare { left, right, .. } => {
                matches!(expr.ty, MachineType::Bool { .. })
                    && child(*left)?.ty.width_bits() == child(*right)?.ty.width_bits()
            }
            MachineExprKind::Cast { kind, input } => {
                let from = child(*input)?.ty.width_bits();
                let to = expr.ty.width_bits();
                match kind {
                    MachineCastKind::ZeroExtend | MachineCastKind::SignExtend => to > from,
                    MachineCastKind::Truncate => to < from,
                    MachineCastKind::BitReinterpret => to == from,
                    MachineCastKind::IntegerToAddress | MachineCastKind::AddressToInteger => {
                        to == from
                    }
                }
            }
            MachineExprKind::Extract { input, lsb_bits } => {
                let input_bits = child(*input)?.ty.width_bits();
                lsb_bits
                    .checked_add(expr.ty.width_bits())
                    .is_some_and(|end| end <= input_bits)
            }
            MachineExprKind::Select {
                condition,
                if_true,
                if_false,
            } => {
                matches!(child(*condition)?.ty, MachineType::Bool { .. })
                    && child(*if_true)?.ty == expr.ty
                    && child(*if_false)?.ty == expr.ty
            }
            MachineExprKind::Phi { inputs } => {
                !inputs.is_empty()
                    && inputs
                        .iter()
                        .all(|input| child(*input).is_ok_and(same_width))
            }
        };
        if valid {
            Ok(())
        } else {
            Err(MachineBuildError::InvalidExpressionType { expr: id })
        }
    }

    fn validate_entity_shape(
        &self,
        artifact: &SsaArtifact,
        inst: &GraphInst,
        entity: &MachineEntity,
    ) -> Result<(), MachineBuildError> {
        let root = self
            .arena
            .get(entity.root)
            .ok_or(MachineBuildError::EntityMismatch(inst.id))?;
        if root.ty.width_bits() != entity.output.width_bits {
            return Err(MachineBuildError::EntityMismatch(inst.id));
        }
        let inputs = root.kind.children();
        if inputs.len() != inst.inputs.len() {
            return Err(MachineBuildError::EntityMismatch(inst.id));
        }
        for (child, expected) in inputs.iter().zip(&inst.inputs) {
            let binding = leaf_binding(
                self.arena
                    .get(*child)
                    .ok_or(MachineBuildError::EntityMismatch(inst.id))?,
            )
            .ok_or(MachineBuildError::EntityMismatch(inst.id))?;
            if binding.value != *expected {
                return Err(MachineBuildError::EntityMismatch(inst.id));
            }
        }
        let shape_matches = match (&inst.payload, &root.kind) {
            (InstPayload::Phi { .. }, MachineExprKind::Phi { .. }) => {
                root.ty == integer_type(entity.output.width_bits, MachineSignedness::Unsigned)
            }
            (InstPayload::Op(op), kind) => {
                machine_kind_matches_op(op, kind)
                    && machine_type_matches_op(op, &root.ty, entity.output.width_bits)
            }
            _ => false,
        };
        if !shape_matches {
            return Err(MachineBuildError::EntityMismatch(inst.id));
        }
        if let MachineExprKind::MemoryRead { .. } = &root.kind {
            self.validate_memory_read(artifact, inst, entity, root)?;
        }
        let disposition = artifact
            .obligations()
            .instruction_for_inst(inst.id)
            .ok_or(MachineBuildError::MissingInstructionDisposition(inst.id))?;
        if disposition.id != entity.producer || disposition.obligations != entity.source_obligations
        {
            return Err(MachineBuildError::ObligationMismatch(inst.id));
        }
        Ok(())
    }

    fn validate_memory_read(
        &self,
        artifact: &SsaArtifact,
        inst: &GraphInst,
        entity: &MachineEntity,
        root: &MachineExpr,
    ) -> Result<(), MachineBuildError> {
        let MachineExprKind::MemoryRead {
            access,
            object,
            space,
            endianness,
            word_size_bytes,
            address,
            width_bits,
        } = &root.kind
        else {
            return Err(MachineBuildError::EntityMismatch(inst.id));
        };
        let fact = artifact
            .facts()
            .structured
            .memory_accesses
            .get(access)
            .filter(|fact| {
                fact.id.inst == inst.id
                    && fact.provenance_complete
                    && !fact.is_write
                    && fact.id.ordinal == 0
                    && fact.value == Some(entity.output.value)
                    && inst.inputs.as_slice() == [fact.address]
            })
            .ok_or(MachineBuildError::EntityMismatch(inst.id))?;
        let source_space = artifact
            .machine_context()
            .memory_space_at(fact.block_addr, fact.op_index)
            .ok_or(MachineBuildError::MachineContextMismatch)?;
        let source_model = artifact.machine_context().memory_model();
        let source_space_model = source_model
            .space(source_space)
            .filter(|_| source_model.is_available() && source_model.is_coherent())
            .ok_or(MachineBuildError::MachineContextMismatch)?;
        let fact_width_bits = fact.width.checked_mul(8).unwrap_or(0);
        let expected_address = self
            .arena
            .get(*address)
            .ok_or(MachineBuildError::EntityMismatch(inst.id))?;
        let expected_address_type = MachineType::Address {
            width_bits: source_space_model.address_bits(),
            space: MachineAddressSpace::from(source_space),
            provenance: machine_address_provenance(artifact, fact.object),
        };
        if *object != fact.object
            || *space != MachineAddressSpace::from(source_space)
            || *endianness != source_space_model.endianness()
            || *word_size_bytes != source_space_model.word_size_bytes()
            || *width_bits != fact_width_bits
            || fact_width_bits != entity.output.width_bits
            || expected_address.ty != expected_address_type
        {
            return Err(MachineBuildError::EntityMismatch(inst.id));
        }
        Ok(())
    }
}

#[derive(Default)]
struct MachineBuilder {
    nodes: Vec<MachineExpr>,
    value_nodes: BTreeMap<(ValueId, MachineType), MachineExprId>,
    address_nodes: BTreeMap<(ValueId, ObjectId, MachineAddressSpace), MachineExprId>,
}

impl MachineBuilder {
    fn push(
        &mut self,
        ty: MachineType,
        origin: Option<CanonicalInstructionId>,
        kind: MachineExprKind,
    ) -> MachineExprId {
        let id = MachineExprId(self.nodes.len() as u32);
        self.nodes.push(MachineExpr { ty, origin, kind });
        id
    }

    fn intern_value(&mut self, value: &GraphValue) -> Result<MachineExprId, MachineBuildError> {
        let binding = binding_for_value(value)?;
        let ty = integer_type(binding.width_bits, MachineSignedness::Unsigned);
        self.intern_value_with_type(value, ty)
    }

    fn intern_boolean_value(
        &mut self,
        graph: &crate::graph::SsaGraph,
        value: &GraphValue,
        inst: InstId,
    ) -> Result<MachineExprId, MachineBuildError> {
        let binding = binding_for_value(value)?;
        if !value_has_boolean_producer(graph, value.id) {
            return Err(MachineBuildError::UnsupportedOperation {
                inst,
                op: Box::new(
                    graph
                        .inst(inst)
                        .and_then(|inst| match &inst.payload {
                            InstPayload::Op(op) => Some(op.clone()),
                            InstPayload::Phi { .. } => None,
                        })
                        .unwrap_or(SSAOp::Unimplemented),
                ),
            });
        }
        self.intern_value_with_type(
            value,
            MachineType::Bool {
                storage_bits: binding.width_bits,
            },
        )
    }

    fn intern_value_with_type(
        &mut self,
        value: &GraphValue,
        ty: MachineType,
    ) -> Result<MachineExprId, MachineBuildError> {
        let binding = binding_for_value(value)?;
        let key = (value.id, ty.clone());
        if let Some(id) = self.value_nodes.get(&key).copied() {
            return Ok(id);
        }
        let kind = if let Some(bits) = value.var.constant_bits() {
            MachineExprKind::Constant {
                binding,
                value: bit_vector(value.id, binding.width_bits, bits)?,
            }
        } else {
            MachineExprKind::Source { binding }
        };
        let id = self.push(ty, None, kind);
        self.value_nodes.insert(key, id);
        Ok(id)
    }

    fn intern_address(
        &mut self,
        artifact: &SsaArtifact,
        value: &GraphValue,
        object: ObjectId,
        space: MachineAddressSpace,
        address_bits: u32,
    ) -> Result<MachineExprId, MachineBuildError> {
        let key = (value.id, object, space);
        if let Some(id) = self.address_nodes.get(&key).copied() {
            return Ok(id);
        }
        let binding = binding_for_value(value)?;
        if binding.width_bits != address_bits {
            return Err(MachineBuildError::WidthMismatch {
                inst: artifact
                    .graph()
                    .def_inst(value.id)
                    .unwrap_or(InstId(u32::MAX)),
                expected_bits: address_bits,
                actual_bits: binding.width_bits,
            });
        }
        let provenance = machine_address_provenance(artifact, object);
        let ty = MachineType::Address {
            width_bits: address_bits,
            space,
            provenance,
        };
        let kind = if let Some(bits) = value.var.constant_bits() {
            MachineExprKind::Constant {
                binding,
                value: bit_vector(value.id, binding.width_bits, bits)?,
            }
        } else {
            MachineExprKind::Source { binding }
        };
        let id = self.push(ty, None, kind);
        self.address_nodes.insert(key, id);
        Ok(id)
    }

    fn operand_nodes(
        &mut self,
        graph: &crate::graph::SsaGraph,
        inst: &GraphInst,
        expected: usize,
    ) -> Result<Vec<MachineExprId>, MachineBuildError> {
        if inst.inputs.len() != expected {
            return Err(MachineBuildError::WrongOperandCount {
                inst: inst.id,
                expected,
                actual: inst.inputs.len(),
            });
        }
        inst.inputs
            .iter()
            .map(|value| {
                let graph_value = graph
                    .value(*value)
                    .ok_or(MachineBuildError::MissingGraphValue(*value))?;
                self.intern_value(graph_value)
            })
            .collect()
    }

    fn lower_inst(
        &mut self,
        artifact: &SsaArtifact,
        inst: &GraphInst,
        producer: CanonicalInstructionId,
        output: MachineValueBinding,
    ) -> Result<MachineExprId, MachineBuildError> {
        let graph = artifact.graph();
        let output_unsigned = integer_type(output.width_bits, MachineSignedness::Unsigned);
        let (ty, kind) = match &inst.payload {
            InstPayload::Phi { .. } => {
                if inst.inputs.is_empty() {
                    return Err(MachineBuildError::WrongOperandCount {
                        inst: inst.id,
                        expected: 1,
                        actual: 0,
                    });
                }
                let mut inputs = Vec::with_capacity(inst.inputs.len());
                for value in &inst.inputs {
                    inputs.push(
                        self.intern_value(
                            graph
                                .value(*value)
                                .ok_or(MachineBuildError::MissingGraphValue(*value))?,
                        )?,
                    );
                }
                (
                    output_unsigned,
                    MachineExprKind::Phi {
                        inputs: inputs.into_boxed_slice(),
                    },
                )
            }
            InstPayload::Op(op) => self.lower_op(artifact, inst, op, output)?,
        };
        Ok(self.push(ty, Some(producer), kind))
    }

    fn lower_op(
        &mut self,
        artifact: &SsaArtifact,
        inst: &GraphInst,
        op: &SSAOp,
        output: MachineValueBinding,
    ) -> Result<(MachineType, MachineExprKind), MachineBuildError> {
        let graph = artifact.graph();
        let unsigned = integer_type(output.width_bits, MachineSignedness::Unsigned);
        let signed = integer_type(output.width_bits, MachineSignedness::Signed);
        match op {
            SSAOp::Load { .. } => {
                let accesses = artifact
                    .facts()
                    .structured
                    .memory_accesses
                    .values()
                    .filter(|access| access.id.inst == inst.id)
                    .collect::<Vec<_>>();
                let [access] = accesses.as_slice() else {
                    return Err(MachineBuildError::UnsupportedOperation {
                        inst: inst.id,
                        op: Box::new(op.clone()),
                    });
                };
                let width_bits = access.width.checked_mul(8).unwrap_or(0);
                let source_space = artifact
                    .machine_context()
                    .memory_space_at(access.block_addr, access.op_index);
                let model = artifact.machine_context().memory_model();
                let space_model = source_space.and_then(|space| model.space(space));
                if !access.provenance_complete
                    || access.is_write
                    || access.id.ordinal != 0
                    || access.value != Some(output.value)
                    || inst.inputs.as_slice() != [access.address]
                    || width_bits == 0
                    || width_bits != output.width_bits
                    || !model.is_available()
                    || !model.is_coherent()
                    || space_model.is_none()
                {
                    return Err(MachineBuildError::UnsupportedOperation {
                        inst: inst.id,
                        op: Box::new(op.clone()),
                    });
                }
                let space_model = space_model.expect("checked memory space");
                let address = graph
                    .value(access.address)
                    .ok_or(MachineBuildError::MissingGraphValue(access.address))?;
                let space = MachineAddressSpace::from(space_model.space());
                let address = self.intern_address(
                    artifact,
                    address,
                    access.object,
                    space,
                    space_model.address_bits(),
                )?;
                Ok((
                    unsigned,
                    MachineExprKind::MemoryRead {
                        access: access.id,
                        object: access.object,
                        space,
                        endianness: space_model.endianness(),
                        word_size_bytes: space_model.word_size_bytes(),
                        address,
                        width_bits,
                    },
                ))
            }
            SSAOp::Copy { .. } => {
                let inputs = self.operand_nodes(graph, inst, 1)?;
                Ok((unsigned, MachineExprKind::Copy { input: inputs[0] }))
            }
            SSAOp::IntAdd { .. } | SSAOp::IntSub { .. } | SSAOp::IntMult { .. } => {
                let inputs = self.operand_nodes(graph, inst, 2)?;
                let op = match op {
                    SSAOp::IntAdd { .. } => MachineArithmeticOp::Add,
                    SSAOp::IntSub { .. } => MachineArithmeticOp::Subtract,
                    SSAOp::IntMult { .. } => MachineArithmeticOp::Multiply,
                    _ => unreachable!(),
                };
                Ok((
                    unsigned,
                    MachineExprKind::Arithmetic {
                        op,
                        mode: MachineArithmeticMode::Wrapping,
                        left: inputs[0],
                        right: inputs[1],
                    },
                ))
            }
            SSAOp::IntCarry { .. } | SSAOp::IntSCarry { .. } | SSAOp::IntSBorrow { .. } => {
                let inputs = self.operand_nodes(graph, inst, 2)?;
                let op = match op {
                    SSAOp::IntCarry { .. } => MachineArithmeticFlagOp::UnsignedCarry,
                    SSAOp::IntSCarry { .. } => MachineArithmeticFlagOp::SignedCarry,
                    SSAOp::IntSBorrow { .. } => MachineArithmeticFlagOp::SignedBorrow,
                    _ => unreachable!(),
                };
                Ok((
                    MachineType::Bool {
                        storage_bits: output.width_bits,
                    },
                    MachineExprKind::ArithmeticFlag {
                        op,
                        left: inputs[0],
                        right: inputs[1],
                    },
                ))
            }
            SSAOp::IntAnd { .. } | SSAOp::IntOr { .. } | SSAOp::IntXor { .. } => {
                let inputs = self.operand_nodes(graph, inst, 2)?;
                let op = match op {
                    SSAOp::IntAnd { .. } => MachineBitwiseOp::And,
                    SSAOp::IntOr { .. } => MachineBitwiseOp::Or,
                    SSAOp::IntXor { .. } => MachineBitwiseOp::Xor,
                    _ => unreachable!(),
                };
                Ok((
                    unsigned,
                    MachineExprKind::Bitwise {
                        op,
                        left: inputs[0],
                        right: inputs[1],
                    },
                ))
            }
            SSAOp::IntNot { .. } => {
                let inputs = self.operand_nodes(graph, inst, 1)?;
                Ok((unsigned, MachineExprKind::BitwiseNot { input: inputs[0] }))
            }
            SSAOp::BoolNot { .. } => {
                if inst.inputs.len() != 1 {
                    return Err(MachineBuildError::WrongOperandCount {
                        inst: inst.id,
                        expected: 1,
                        actual: inst.inputs.len(),
                    });
                }
                let input_value = graph
                    .value(inst.inputs[0])
                    .ok_or(MachineBuildError::MissingGraphValue(inst.inputs[0]))?;
                let input = self.intern_boolean_value(graph, input_value, inst.id)?;
                Ok((
                    MachineType::Bool {
                        storage_bits: output.width_bits,
                    },
                    MachineExprKind::BooleanNot { input },
                ))
            }
            SSAOp::BoolAnd { .. } | SSAOp::BoolOr { .. } | SSAOp::BoolXor { .. } => {
                if inst.inputs.len() != 2 {
                    return Err(MachineBuildError::WrongOperandCount {
                        inst: inst.id,
                        expected: 2,
                        actual: inst.inputs.len(),
                    });
                }
                let left_value = graph
                    .value(inst.inputs[0])
                    .ok_or(MachineBuildError::MissingGraphValue(inst.inputs[0]))?;
                let right_value = graph
                    .value(inst.inputs[1])
                    .ok_or(MachineBuildError::MissingGraphValue(inst.inputs[1]))?;
                let left = self.intern_boolean_value(graph, left_value, inst.id)?;
                let right = self.intern_boolean_value(graph, right_value, inst.id)?;
                let op = match op {
                    SSAOp::BoolAnd { .. } => MachineBooleanOp::And,
                    SSAOp::BoolOr { .. } => MachineBooleanOp::Or,
                    SSAOp::BoolXor { .. } => MachineBooleanOp::Xor,
                    _ => unreachable!(),
                };
                Ok((
                    MachineType::Bool {
                        storage_bits: output.width_bits,
                    },
                    MachineExprKind::Boolean { op, left, right },
                ))
            }
            SSAOp::IntLeft { .. } | SSAOp::IntRight { .. } | SSAOp::IntSRight { .. } => {
                let inputs = self.operand_nodes(graph, inst, 2)?;
                let (kind, overshift, ty) = match op {
                    SSAOp::IntLeft { .. } => (
                        MachineShiftKind::Left,
                        MachineOvershiftBehavior::Zero,
                        unsigned,
                    ),
                    SSAOp::IntRight { .. } => (
                        MachineShiftKind::LogicalRight,
                        MachineOvershiftBehavior::Zero,
                        unsigned,
                    ),
                    SSAOp::IntSRight { .. } => (
                        MachineShiftKind::ArithmeticRight,
                        MachineOvershiftBehavior::SignFill,
                        signed,
                    ),
                    _ => unreachable!(),
                };
                Ok((
                    ty,
                    MachineExprKind::Shift {
                        kind,
                        overshift,
                        value: inputs[0],
                        count: inputs[1],
                    },
                ))
            }
            SSAOp::IntEqual { .. }
            | SSAOp::IntNotEqual { .. }
            | SSAOp::IntLess { .. }
            | SSAOp::IntSLess { .. }
            | SSAOp::IntLessEqual { .. }
            | SSAOp::IntSLessEqual { .. } => {
                let inputs = self.operand_nodes(graph, inst, 2)?;
                let (op, interpretation) = match op {
                    SSAOp::IntEqual { .. } => {
                        (MachineComparisonOp::Equal, MachineSignedness::Unsigned)
                    }
                    SSAOp::IntNotEqual { .. } => {
                        (MachineComparisonOp::NotEqual, MachineSignedness::Unsigned)
                    }
                    SSAOp::IntLess { .. } => {
                        (MachineComparisonOp::LessThan, MachineSignedness::Unsigned)
                    }
                    SSAOp::IntSLess { .. } => {
                        (MachineComparisonOp::LessThan, MachineSignedness::Signed)
                    }
                    SSAOp::IntLessEqual { .. } => (
                        MachineComparisonOp::LessThanOrEqual,
                        MachineSignedness::Unsigned,
                    ),
                    SSAOp::IntSLessEqual { .. } => (
                        MachineComparisonOp::LessThanOrEqual,
                        MachineSignedness::Signed,
                    ),
                    _ => unreachable!(),
                };
                Ok((
                    MachineType::Bool {
                        storage_bits: output.width_bits,
                    },
                    MachineExprKind::Compare {
                        op,
                        interpretation,
                        left: inputs[0],
                        right: inputs[1],
                    },
                ))
            }
            SSAOp::IntZExt { .. }
            | SSAOp::IntSExt { .. }
            | SSAOp::Trunc { .. }
            | SSAOp::Cast { .. } => {
                let inputs = self.operand_nodes(graph, inst, 1)?;
                let from = self.nodes[inputs[0].index()].ty.width_bits();
                let (kind, ty, valid) = match op {
                    SSAOp::IntZExt { .. } => (
                        MachineCastKind::ZeroExtend,
                        unsigned,
                        output.width_bits > from,
                    ),
                    SSAOp::IntSExt { .. } => (
                        MachineCastKind::SignExtend,
                        signed,
                        output.width_bits > from,
                    ),
                    SSAOp::Trunc { .. } => (
                        MachineCastKind::Truncate,
                        unsigned,
                        output.width_bits < from,
                    ),
                    SSAOp::Cast { .. } => (
                        MachineCastKind::BitReinterpret,
                        unsigned,
                        output.width_bits == from,
                    ),
                    _ => unreachable!(),
                };
                if !valid {
                    return Err(MachineBuildError::InvalidCastWidth {
                        inst: inst.id,
                        kind,
                        from_bits: from,
                        to_bits: output.width_bits,
                    });
                }
                Ok((
                    ty,
                    MachineExprKind::Cast {
                        kind,
                        input: inputs[0],
                    },
                ))
            }
            SSAOp::Subpiece { offset, .. } => {
                let inputs = self.operand_nodes(graph, inst, 1)?;
                let source_bits = self.nodes[inputs[0].index()].ty.width_bits();
                let lsb_bits = offset
                    .checked_mul(8)
                    .ok_or(MachineBuildError::InvalidSubpiece {
                        inst: inst.id,
                        source_bits,
                        result_bits: output.width_bits,
                        lsb_bits: u32::MAX,
                    })?;
                if lsb_bits
                    .checked_add(output.width_bits)
                    .is_none_or(|end| end > source_bits)
                {
                    return Err(MachineBuildError::InvalidSubpiece {
                        inst: inst.id,
                        source_bits,
                        result_bits: output.width_bits,
                        lsb_bits,
                    });
                }
                Ok((
                    unsigned,
                    MachineExprKind::Extract {
                        input: inputs[0],
                        lsb_bits,
                    },
                ))
            }
            SSAOp::Select { .. } => {
                if inst.inputs.len() != 3 {
                    return Err(MachineBuildError::WrongOperandCount {
                        inst: inst.id,
                        expected: 3,
                        actual: inst.inputs.len(),
                    });
                }
                let condition_value = graph
                    .value(inst.inputs[0])
                    .ok_or(MachineBuildError::MissingGraphValue(inst.inputs[0]))?;
                let condition = self.intern_boolean_value(graph, condition_value, inst.id)?;
                let if_true_value = graph
                    .value(inst.inputs[1])
                    .ok_or(MachineBuildError::MissingGraphValue(inst.inputs[1]))?;
                let if_false_value = graph
                    .value(inst.inputs[2])
                    .ok_or(MachineBuildError::MissingGraphValue(inst.inputs[2]))?;
                let if_true = self.intern_value_with_type(if_true_value, unsigned.clone())?;
                let if_false = self.intern_value_with_type(if_false_value, unsigned.clone())?;
                Ok((
                    unsigned,
                    MachineExprKind::Select {
                        condition,
                        if_true,
                        if_false,
                    },
                ))
            }
            _ => Err(MachineBuildError::UnsupportedOperation {
                inst: inst.id,
                op: Box::new(op.clone()),
            }),
        }
    }
}

fn integer_type(width_bits: u32, signedness: MachineSignedness) -> MachineType {
    MachineType::Integer {
        width_bits,
        signedness,
    }
}

pub fn machine_address_provenance(
    artifact: &SsaArtifact,
    object: ObjectId,
) -> MachineAddressProvenance {
    artifact
        .objects()
        .object(object)
        .map(|object| match &object.kind {
            ObjectKind::StackSlot { base, offset } | ObjectKind::FrameObject { base, offset } => {
                MachineAddressProvenance::Stack {
                    base: match base {
                        StackAddressBase::FramePointer => MachineStackBase::FramePointer,
                        StackAddressBase::StackPointer => MachineStackBase::StackPointer,
                    },
                    offset: *offset,
                }
            }
            ObjectKind::Parameter { index } => u32::try_from(*index)
                .map(|index| MachineAddressProvenance::Parameter { index })
                .unwrap_or(MachineAddressProvenance::Unknown),
            ObjectKind::Global { address, .. } => {
                MachineAddressProvenance::Global { address: *address }
            }
            ObjectKind::HeapAlloc { .. } | ObjectKind::EscapedUnknown => {
                MachineAddressProvenance::Unknown
            }
        })
        .unwrap_or(MachineAddressProvenance::Unknown)
}

fn binding_for_value(value: &GraphValue) -> Result<MachineValueBinding, MachineBuildError> {
    let width_bits = value
        .var
        .size
        .checked_mul(8)
        .filter(|width| *width > 0)
        .ok_or(MachineBuildError::InvalidValueWidth {
            value: value.id,
            size_bytes: value.var.size,
        })?;
    Ok(MachineValueBinding {
        value: value.id,
        width_bits,
    })
}

fn bit_vector(
    value: ValueId,
    width_bits: u32,
    bits: u64,
) -> Result<MachineBitVector, MachineBuildError> {
    if width_bits > 64 {
        return Err(MachineBuildError::ConstantTooWide { value, width_bits });
    }
    let mask = if width_bits == 64 {
        u64::MAX
    } else {
        (1u64 << width_bits) - 1
    };
    Ok(MachineBitVector {
        width_bits,
        bits: bits & mask,
    })
}

fn leaf_binding(expr: &MachineExpr) -> Option<MachineValueBinding> {
    match expr.kind {
        MachineExprKind::Source { binding } | MachineExprKind::Constant { binding, .. } => {
            Some(binding)
        }
        _ => None,
    }
}

fn machine_kind_matches_op(op: &SSAOp, kind: &MachineExprKind) -> bool {
    if let (SSAOp::Subpiece { offset, .. }, MachineExprKind::Extract { lsb_bits, .. }) = (op, kind)
    {
        return offset.checked_mul(8) == Some(*lsb_bits);
    }
    matches!(
        (op, kind),
        (SSAOp::Load { .. }, MachineExprKind::MemoryRead { .. })
            | (SSAOp::Copy { .. }, MachineExprKind::Copy { .. })
            | (
                SSAOp::IntAdd { .. },
                MachineExprKind::Arithmetic {
                    op: MachineArithmeticOp::Add,
                    mode: MachineArithmeticMode::Wrapping,
                    ..
                }
            )
            | (
                SSAOp::IntSub { .. },
                MachineExprKind::Arithmetic {
                    op: MachineArithmeticOp::Subtract,
                    mode: MachineArithmeticMode::Wrapping,
                    ..
                }
            )
            | (
                SSAOp::IntMult { .. },
                MachineExprKind::Arithmetic {
                    op: MachineArithmeticOp::Multiply,
                    mode: MachineArithmeticMode::Wrapping,
                    ..
                }
            )
            | (
                SSAOp::IntCarry { .. },
                MachineExprKind::ArithmeticFlag {
                    op: MachineArithmeticFlagOp::UnsignedCarry,
                    ..
                }
            )
            | (
                SSAOp::IntSCarry { .. },
                MachineExprKind::ArithmeticFlag {
                    op: MachineArithmeticFlagOp::SignedCarry,
                    ..
                }
            )
            | (
                SSAOp::IntSBorrow { .. },
                MachineExprKind::ArithmeticFlag {
                    op: MachineArithmeticFlagOp::SignedBorrow,
                    ..
                }
            )
            | (
                SSAOp::IntAnd { .. },
                MachineExprKind::Bitwise {
                    op: MachineBitwiseOp::And,
                    ..
                }
            )
            | (
                SSAOp::IntOr { .. },
                MachineExprKind::Bitwise {
                    op: MachineBitwiseOp::Or,
                    ..
                }
            )
            | (
                SSAOp::IntXor { .. },
                MachineExprKind::Bitwise {
                    op: MachineBitwiseOp::Xor,
                    ..
                }
            )
            | (SSAOp::IntNot { .. }, MachineExprKind::BitwiseNot { .. })
            | (SSAOp::BoolNot { .. }, MachineExprKind::BooleanNot { .. })
            | (
                SSAOp::BoolAnd { .. },
                MachineExprKind::Boolean {
                    op: MachineBooleanOp::And,
                    ..
                }
            )
            | (
                SSAOp::BoolOr { .. },
                MachineExprKind::Boolean {
                    op: MachineBooleanOp::Or,
                    ..
                }
            )
            | (
                SSAOp::BoolXor { .. },
                MachineExprKind::Boolean {
                    op: MachineBooleanOp::Xor,
                    ..
                }
            )
            | (
                SSAOp::IntLeft { .. },
                MachineExprKind::Shift {
                    kind: MachineShiftKind::Left,
                    overshift: MachineOvershiftBehavior::Zero,
                    ..
                }
            )
            | (
                SSAOp::IntRight { .. },
                MachineExprKind::Shift {
                    kind: MachineShiftKind::LogicalRight,
                    overshift: MachineOvershiftBehavior::Zero,
                    ..
                }
            )
            | (
                SSAOp::IntSRight { .. },
                MachineExprKind::Shift {
                    kind: MachineShiftKind::ArithmeticRight,
                    overshift: MachineOvershiftBehavior::SignFill,
                    ..
                }
            )
            | (
                SSAOp::IntEqual { .. },
                MachineExprKind::Compare {
                    op: MachineComparisonOp::Equal,
                    interpretation: MachineSignedness::Unsigned,
                    ..
                }
            )
            | (
                SSAOp::IntNotEqual { .. },
                MachineExprKind::Compare {
                    op: MachineComparisonOp::NotEqual,
                    interpretation: MachineSignedness::Unsigned,
                    ..
                }
            )
            | (
                SSAOp::IntLess { .. },
                MachineExprKind::Compare {
                    op: MachineComparisonOp::LessThan,
                    interpretation: MachineSignedness::Unsigned,
                    ..
                }
            )
            | (
                SSAOp::IntSLess { .. },
                MachineExprKind::Compare {
                    op: MachineComparisonOp::LessThan,
                    interpretation: MachineSignedness::Signed,
                    ..
                }
            )
            | (
                SSAOp::IntLessEqual { .. },
                MachineExprKind::Compare {
                    op: MachineComparisonOp::LessThanOrEqual,
                    interpretation: MachineSignedness::Unsigned,
                    ..
                }
            )
            | (
                SSAOp::IntSLessEqual { .. },
                MachineExprKind::Compare {
                    op: MachineComparisonOp::LessThanOrEqual,
                    interpretation: MachineSignedness::Signed,
                    ..
                }
            )
            | (
                SSAOp::IntZExt { .. },
                MachineExprKind::Cast {
                    kind: MachineCastKind::ZeroExtend,
                    ..
                }
            )
            | (
                SSAOp::IntSExt { .. },
                MachineExprKind::Cast {
                    kind: MachineCastKind::SignExtend,
                    ..
                }
            )
            | (
                SSAOp::Trunc { .. },
                MachineExprKind::Cast {
                    kind: MachineCastKind::Truncate,
                    ..
                }
            )
            | (
                SSAOp::Cast { .. },
                MachineExprKind::Cast {
                    kind: MachineCastKind::BitReinterpret,
                    ..
                }
            )
            | (SSAOp::Select { .. }, MachineExprKind::Select { .. })
    )
}

fn machine_type_matches_op(op: &SSAOp, ty: &MachineType, output_bits: u32) -> bool {
    let unsigned = integer_type(output_bits, MachineSignedness::Unsigned);
    let signed = integer_type(output_bits, MachineSignedness::Signed);
    match op {
        SSAOp::IntSRight { .. } | SSAOp::IntSExt { .. } => *ty == signed,
        SSAOp::IntEqual { .. }
        | SSAOp::IntNotEqual { .. }
        | SSAOp::IntLess { .. }
        | SSAOp::IntSLess { .. }
        | SSAOp::IntLessEqual { .. }
        | SSAOp::IntSLessEqual { .. }
        | SSAOp::IntCarry { .. }
        | SSAOp::IntSCarry { .. }
        | SSAOp::IntSBorrow { .. }
        | SSAOp::BoolNot { .. }
        | SSAOp::BoolAnd { .. }
        | SSAOp::BoolOr { .. }
        | SSAOp::BoolXor { .. } => {
            *ty == MachineType::Bool {
                storage_bits: output_bits,
            }
        }
        SSAOp::Load { .. }
        | SSAOp::Copy { .. }
        | SSAOp::IntAdd { .. }
        | SSAOp::IntSub { .. }
        | SSAOp::IntMult { .. }
        | SSAOp::IntAnd { .. }
        | SSAOp::IntOr { .. }
        | SSAOp::IntXor { .. }
        | SSAOp::IntNot { .. }
        | SSAOp::IntLeft { .. }
        | SSAOp::IntRight { .. }
        | SSAOp::IntZExt { .. }
        | SSAOp::Trunc { .. }
        | SSAOp::Cast { .. }
        | SSAOp::Subpiece { .. }
        | SSAOp::Select { .. } => *ty == unsigned,
        _ => false,
    }
}

fn value_has_boolean_producer(graph: &crate::graph::SsaGraph, value: ValueId) -> bool {
    fn visit(
        graph: &crate::graph::SsaGraph,
        value: ValueId,
        visiting: &mut BTreeSet<ValueId>,
    ) -> bool {
        if !visiting.insert(value) {
            return false;
        }
        let result = graph
            .def_inst(value)
            .and_then(|inst| graph.inst(inst))
            .is_some_and(|inst| match &inst.payload {
                InstPayload::Op(
                    SSAOp::IntEqual { .. }
                    | SSAOp::IntNotEqual { .. }
                    | SSAOp::IntLess { .. }
                    | SSAOp::IntSLess { .. }
                    | SSAOp::IntLessEqual { .. }
                    | SSAOp::IntSLessEqual { .. }
                    | SSAOp::IntCarry { .. }
                    | SSAOp::IntSCarry { .. }
                    | SSAOp::IntSBorrow { .. }
                    | SSAOp::BoolNot { .. }
                    | SSAOp::BoolAnd { .. }
                    | SSAOp::BoolOr { .. }
                    | SSAOp::BoolXor { .. },
                ) => true,
                InstPayload::Op(SSAOp::Copy { .. }) => inst
                    .inputs
                    .as_slice()
                    .first()
                    .is_some_and(|input| visit(graph, *input, visiting)),
                InstPayload::Phi { .. } => {
                    !inst.inputs.is_empty()
                        && inst
                            .inputs
                            .iter()
                            .all(|input| visit(graph, *input, visiting))
                }
                _ => false,
            });
        visiting.remove(&value);
        result
    }

    visit(graph, value, &mut BTreeSet::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SSAVar;
    use r2il::{ArchSpec, Endianness, R2ILBlock, R2ILOp, SpaceId, Varnode};

    fn artifact_with_ops(ops: impl IntoIterator<Item = R2ILOp>) -> SsaArtifact {
        let mut block = R2ILBlock::new(0x1000, 4);
        for op in ops {
            block.push(op);
        }
        SsaArtifact::raw(&[block], None).expect("test SSA artifact")
    }

    #[test]
    fn fnv_multiply_is_unsigned_64_bit_wrapping_arithmetic() {
        const FNV_OFFSET: u64 = 0xcbf29ce484222325;
        const FNV_PRIME: u64 = 0x100000001b3;
        let initial = Varnode::unique(0x10, 8);
        let folded = Varnode::unique(0x18, 8);
        let product = Varnode::unique(0x20, 8);
        let artifact = artifact_with_ops([
            R2ILOp::Copy {
                dst: initial.clone(),
                src: Varnode::constant(FNV_OFFSET, 8),
            },
            R2ILOp::IntXor {
                dst: folded.clone(),
                a: initial,
                b: Varnode::register(0, 8),
            },
            R2ILOp::IntMult {
                dst: product,
                a: folded,
                b: Varnode::constant(FNV_PRIME, 8),
            },
        ]);

        let machine = MachineFunction::from_artifact(&artifact).expect("machine function");
        let mult_inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 2)
            .expect("multiply instruction");
        let output = artifact
            .graph()
            .inst(mult_inst)
            .and_then(|inst| inst.output)
            .expect("multiply output");
        let entity = machine.entity_for_output(output).expect("multiply entity");
        let root = machine.expr(entity.root()).expect("multiply expression");
        assert_eq!(
            root.ty(),
            &MachineType::Integer {
                width_bits: 64,
                signedness: MachineSignedness::Unsigned,
            }
        );
        let MachineExprKind::Arithmetic {
            op: MachineArithmeticOp::Multiply,
            mode: MachineArithmeticMode::Wrapping,
            right,
            ..
        } = root.kind()
        else {
            panic!("expected wrapping multiply, got {:?}", root.kind());
        };
        let MachineExprKind::Constant { value, .. } =
            machine.expr(*right).expect("prime expression").kind()
        else {
            panic!("FNV prime must remain a semantic constant");
        };
        assert_eq!(value.width_bits(), 64);
        assert_eq!(value.bits(), FNV_PRIME);
        let disposition = artifact
            .obligations()
            .instruction_for_inst(mult_inst)
            .expect("multiply disposition");
        assert_eq!(entity.producer(), disposition.id);
        assert_eq!(entity.source_obligations(), &disposition.obligations);
    }

    #[test]
    fn spoofed_constant_name_is_not_semantic_constant_evidence() {
        let graph_value = GraphValue {
            id: ValueId(7),
            var: SSAVar::new("const:100000001b3", 0, 8),
            canonical_storage: None,
        };
        let mut builder = MachineBuilder::default();
        let id = builder
            .intern_value(&graph_value)
            .expect("source expression");
        assert!(matches!(
            builder.nodes[id.index()].kind,
            MachineExprKind::Source {
                binding: MachineValueBinding {
                    value: ValueId(7),
                    width_bits: 64,
                }
            }
        ));
    }

    #[test]
    fn zero_and_sign_extension_remain_distinct() {
        let byte = Varnode::register(0, 1);
        let zext = Varnode::unique(0x10, 8);
        let sext = Varnode::unique(0x18, 8);
        let artifact = artifact_with_ops([
            R2ILOp::IntZExt {
                dst: zext,
                src: byte.clone(),
            },
            R2ILOp::IntSExt {
                dst: sext,
                src: byte,
            },
        ]);
        let machine = MachineFunction::from_artifact(&artifact).expect("machine function");
        let roots = machine
            .entities()
            .iter()
            .map(|entity| machine.expr(entity.root()).expect("entity root"))
            .collect::<Vec<_>>();
        assert!(matches!(
            roots[0].kind(),
            MachineExprKind::Cast {
                kind: MachineCastKind::ZeroExtend,
                ..
            }
        ));
        assert_eq!(
            roots[0].ty().signedness(),
            Some(MachineSignedness::Unsigned)
        );
        assert!(matches!(
            roots[1].kind(),
            MachineExprKind::Cast {
                kind: MachineCastKind::SignExtend,
                ..
            }
        ));
        assert_eq!(roots[1].ty().signedness(), Some(MachineSignedness::Signed));
    }

    #[test]
    fn arithmetic_flags_remain_distinct_typed_boolean_operations() {
        let left = Varnode::register(0, 4);
        let right = Varnode::register(4, 4);
        let artifact = artifact_with_ops([
            R2ILOp::IntCarry {
                dst: Varnode::unique(0x10, 1),
                a: left.clone(),
                b: right.clone(),
            },
            R2ILOp::IntSCarry {
                dst: Varnode::unique(0x11, 1),
                a: left.clone(),
                b: right.clone(),
            },
            R2ILOp::IntSBorrow {
                dst: Varnode::unique(0x12, 1),
                a: left,
                b: right,
            },
        ]);

        let machine = MachineFunction::from_artifact(&artifact).expect("typed arithmetic flags");
        let flags = machine
            .entities()
            .iter()
            .map(|entity| machine.expr(entity.root()).expect("flag expression"))
            .collect::<Vec<_>>();
        assert_eq!(flags.len(), 3);
        assert!(flags
            .iter()
            .all(|flag| flag.ty() == &MachineType::Bool { storage_bits: 8 }));
        assert!(matches!(
            flags[0].kind(),
            MachineExprKind::ArithmeticFlag {
                op: MachineArithmeticFlagOp::UnsignedCarry,
                ..
            }
        ));
        assert!(matches!(
            flags[1].kind(),
            MachineExprKind::ArithmeticFlag {
                op: MachineArithmeticFlagOp::SignedCarry,
                ..
            }
        ));
        assert!(matches!(
            flags[2].kind(),
            MachineExprKind::ArithmeticFlag {
                op: MachineArithmeticFlagOp::SignedBorrow,
                ..
            }
        ));
    }

    #[test]
    fn boolean_not_and_select_require_a_proven_boolean_condition() {
        let compared = Varnode::unique(0x10, 1);
        let inverted = Varnode::unique(0x18, 1);
        let selected = Varnode::unique(0x20, 4);
        let true_value = Varnode::register(8, 4);
        let artifact = artifact_with_ops([
            R2ILOp::IntLess {
                dst: compared.clone(),
                a: Varnode::register(0, 4),
                b: Varnode::constant(26, 4),
            },
            R2ILOp::BoolNot {
                dst: inverted.clone(),
                src: compared,
            },
            R2ILOp::Copy {
                dst: selected.clone(),
                src: true_value.clone(),
            },
            R2ILOp::Select {
                dst: selected,
                cond: inverted,
                if_true: true_value,
                if_false: Varnode::register(12, 4),
            },
        ]);

        let machine = MachineFunction::from_artifact(&artifact).expect("typed select machine");
        let boolean = machine
            .entities()
            .iter()
            .find_map(|entity| {
                let expression = machine.expr(entity.root())?;
                matches!(expression.kind(), MachineExprKind::BooleanNot { .. })
                    .then_some(expression)
            })
            .expect("boolean-not expression");
        assert_eq!(boolean.ty(), &MachineType::Bool { storage_bits: 8 });

        let selected = machine
            .entities()
            .iter()
            .find_map(|entity| {
                let expression = machine.expr(entity.root())?;
                matches!(expression.kind(), MachineExprKind::Select { .. }).then_some(expression)
            })
            .expect("select expression");
        let MachineExprKind::Select {
            condition,
            if_true,
            if_false,
        } = selected.kind()
        else {
            unreachable!();
        };
        assert!(matches!(
            machine.expr(*condition).map(MachineExpr::ty),
            Some(MachineType::Bool { storage_bits: 8 })
        ));
        assert_eq!(
            machine.expr(*if_true).map(MachineExpr::ty),
            Some(selected.ty())
        );
        assert_eq!(
            machine.expr(*if_false).map(MachineExpr::ty),
            Some(selected.ty())
        );
    }

    #[test]
    fn select_rejects_unproven_integer_truthiness() {
        let artifact = artifact_with_ops([R2ILOp::Select {
            dst: Varnode::unique(0x20, 4),
            cond: Varnode::register(0, 1),
            if_true: Varnode::register(8, 4),
            if_false: Varnode::register(12, 4),
        }]);

        assert!(matches!(
            MachineFunction::from_artifact(&artifact),
            Err(MachineBuildError::UnsupportedOperation { op, .. })
                if matches!(*op, SSAOp::Select { .. })
        ));
    }

    #[test]
    fn corrupted_select_condition_type_is_rejected() {
        let compared = Varnode::unique(0x10, 1);
        let selected = Varnode::unique(0x20, 4);
        let true_value = Varnode::register(8, 4);
        let mut block = R2ILBlock::new(0x1010, 4);
        block.push(R2ILOp::IntLess {
            dst: compared.clone(),
            a: Varnode::register(0, 4),
            b: Varnode::constant(26, 4),
        });
        block.push(R2ILOp::Copy {
            dst: selected.clone(),
            src: true_value.clone(),
        });
        block.push(R2ILOp::Select {
            dst: selected,
            cond: compared,
            if_true: true_value,
            if_false: Varnode::register(12, 4),
        });
        let artifact = SsaArtifact::raw(&[block], None).expect("select artifact");
        let mut machine = MachineFunction::from_artifact(&artifact).expect("typed select machine");
        let root = machine
            .entities()
            .iter()
            .find_map(|entity| {
                matches!(
                    &machine.arena.nodes[entity.root().index()].kind,
                    MachineExprKind::Select { .. }
                )
                .then_some(entity.root())
            })
            .expect("select root");
        let MachineExprKind::Select { condition, .. } = &machine.arena.nodes[root.index()].kind
        else {
            unreachable!();
        };
        let condition = *condition;
        machine.arena.nodes[condition.index()].ty = integer_type(8, MachineSignedness::Unsigned);

        assert!(machine.validate_against(&artifact).is_err());
    }

    #[test]
    fn unsupported_value_operation_fails_explicitly() {
        let artifact = artifact_with_ops([R2ILOp::IntDiv {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(3, 8),
        }]);
        assert!(matches!(
            MachineFunction::from_artifact(&artifact),
            Err(MachineBuildError::UnsupportedOperation {
                op,
                ..
            }) if matches!(*op, SSAOp::IntDiv { .. })
        ));
    }

    #[test]
    fn plain_load_requires_and_retains_an_explicit_memory_model() {
        let loaded = Varnode::unique(0x10, 4);
        let mut block = R2ILBlock::new(0x1800, 4);
        block.push(R2ILOp::Load {
            dst: loaded,
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
        });
        let mut arch = ArchSpec::new("big-endian-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(Endianness::Big);
        let artifact = SsaArtifact::raw(&[block], Some(&arch)).expect("typed load artifact");
        let machine = MachineFunction::from_artifact(&artifact).expect("machine load");
        let entity = machine.entities().first().expect("load entity");
        let root = machine.expr(entity.root()).expect("load root");
        let MachineExprKind::MemoryRead {
            access,
            space,
            endianness,
            word_size_bytes,
            address,
            width_bits,
            ..
        } = root.kind()
        else {
            panic!("typed memory read expected, got {:?}", root.kind());
        };

        assert_eq!(access.ordinal, 0);
        assert_eq!(*space, MachineAddressSpace::Ram);
        assert_eq!(*endianness, MachineMemoryEndianness::Big);
        assert_eq!(*word_size_bytes, 1);
        assert_eq!(*width_bits, 32);
        assert!(matches!(
            machine.expr(*address).map(MachineExpr::ty),
            Some(MachineType::Address {
                width_bits: 64,
                space: MachineAddressSpace::Ram,
                ..
            })
        ));
        machine
            .validate_against(&artifact)
            .expect("valid machine load");
    }

    #[test]
    fn corrupted_plain_load_memory_policy_is_rejected() {
        let mut block = R2ILBlock::new(0x1810, 4);
        block.push(R2ILOp::Load {
            dst: Varnode::unique(0x10, 4),
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
        });
        let arch = ArchSpec::new("little-endian-test");
        let artifact = SsaArtifact::raw(&[block], Some(&arch)).expect("typed load artifact");
        let mut machine = MachineFunction::from_artifact(&artifact).expect("machine load");
        let root = machine.entities()[0].root();
        let MachineExprKind::MemoryRead { endianness, .. } =
            &mut machine.arena.nodes[root.index()].kind
        else {
            panic!("memory read root expected");
        };
        *endianness = MachineMemoryEndianness::Big;

        assert!(matches!(
            machine.validate_against(&artifact),
            Err(MachineBuildError::EntityMismatch(_))
        ));
    }

    #[test]
    fn partial_projection_retains_unsupported_producer_and_supported_dependent() {
        let loaded = Varnode::unique(0x10, 8);
        let sum = Varnode::unique(0x18, 8);
        let artifact = artifact_with_ops([
            R2ILOp::Load {
                dst: loaded.clone(),
                space: r2il::SpaceId::Ram,
                addr: Varnode::register(0, 8),
            },
            R2ILOp::IntAdd {
                dst: sum,
                a: loaded,
                b: Varnode::constant(1, 8),
            },
        ]);
        let projection = MachineProjection::from_artifact(&artifact).expect("partial projection");

        assert_eq!(projection.failures().len(), 1);
        assert!(matches!(
            projection.failures()[0].error(),
            MachineBuildError::UnsupportedOperation { op, .. }
                if matches!(op.as_ref(), SSAOp::Load { .. })
        ));
        assert!(projection.entities().iter().any(|entity| {
            artifact
                .graph()
                .def_inst(entity.output().value())
                .and_then(|inst| artifact.graph().inst(inst))
                .is_some_and(|inst| matches!(&inst.payload, InstPayload::Op(SSAOp::IntAdd { .. })))
        }));
        projection
            .validate_against(&artifact)
            .expect("valid partial projection");
    }

    #[test]
    fn malformed_arena_backedge_is_rejected() {
        let artifact = artifact_with_ops([R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::register(0, 8),
        }]);
        let mut machine = MachineFunction::from_artifact(&artifact).expect("machine function");
        let root = machine.entities()[0].root();
        machine.arena.nodes[root.index()].kind = MachineExprKind::Copy { input: root };

        assert_eq!(
            machine.validate_against(&artifact),
            Err(MachineBuildError::InvalidChild {
                expr: root,
                child: root,
            })
        );
    }

    #[test]
    fn corrupted_source_leaf_type_is_rejected() {
        let artifact = artifact_with_ops([R2ILOp::Copy {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::register(0, 8),
        }]);
        let mut machine = MachineFunction::from_artifact(&artifact).expect("machine function");
        let root = machine.entities()[0].root();
        let input = match &machine.arena.nodes[root.index()].kind {
            MachineExprKind::Copy { input } => *input,
            _ => panic!("expected copy root"),
        };
        machine.arena.nodes[input.index()].ty = MachineType::Address {
            width_bits: 64,
            space: MachineAddressSpace::Register,
            provenance: MachineAddressProvenance::Unknown,
        };

        assert_eq!(
            machine.validate_against(&artifact),
            Err(MachineBuildError::InvalidExpressionType { expr: input })
        );
    }

    #[test]
    fn corrupted_sign_extension_result_type_is_rejected() {
        let artifact = artifact_with_ops([R2ILOp::IntSExt {
            dst: Varnode::unique(0x10, 8),
            src: Varnode::register(0, 1),
        }]);
        let mut machine = MachineFunction::from_artifact(&artifact).expect("machine function");
        let entity = machine.entities()[0].clone();
        machine.arena.nodes[entity.root().index()].ty =
            integer_type(entity.output().width_bits(), MachineSignedness::Unsigned);

        assert!(matches!(
            machine.validate_against(&artifact),
            Err(MachineBuildError::EntityMismatch(_))
        ));
    }

    #[test]
    fn corrupted_subpiece_offset_is_rejected() {
        let artifact = artifact_with_ops([R2ILOp::Subpiece {
            dst: Varnode::unique(0x10, 4),
            src: Varnode::register(0, 8),
            offset: 4,
        }]);
        let mut machine = MachineFunction::from_artifact(&artifact).expect("machine function");
        let root = machine.entities()[0].root();
        let MachineExprKind::Extract { lsb_bits, .. } = &mut machine.arena.nodes[root.index()].kind
        else {
            panic!("expected extract root");
        };
        *lsb_bits = 0;

        assert!(matches!(
            machine.validate_against(&artifact),
            Err(MachineBuildError::EntityMismatch(_))
        ));
    }
}
