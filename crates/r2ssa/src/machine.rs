//! Ownership-safe machine expression representation.
//!
//! This module is the semantic boundary between prepared SSA and renderers. It
//! deliberately excludes presentation names and output-tree positions. Source
//! values are identified by artifact-local [`ValueId`] plus an explicit width;
//! persistent provenance is carried by canonical instruction and obligation IDs.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::function::{SsaArtifact, StackAddressBase};
use crate::graph::{
    BlockId, GraphInst, GraphValue, InstId, InstPayload, SsaGraph, UseSite, ValueId,
};
use crate::machine_context::{MachineMemoryEndianness, MachineRegisterGeometryState};
use crate::obligation::{CanonicalInstructionId, SemanticObligationId};
use crate::op::SSAOp;
use crate::semantic::{
    ObjectId, ObjectKind, ObjectModel, StructuredAccessId, StructuredMemoryAccessFact,
};
use crate::{CanonicalStorageId, CanonicalStorageSpace};

fn memory_access_authorities_match(
    graph: &SsaGraph,
    objects: &ObjectModel,
    graph_op: &SSAOp,
    prepared_op: &SSAOp,
    context_space: r2il::SpaceId,
    fact: &StructuredMemoryAccessFact,
) -> bool {
    if graph.op_site_for_inst(fact.id.inst) != Some((fact.block_addr, fact.op_index))
        || fact.id.ordinal != 0
        || fact.space != context_space
        || graph
            .inst(fact.id.inst)
            .is_none_or(|inst| !matches!(&inst.payload, InstPayload::Op(op) if op == graph_op))
        || graph_op != prepared_op
        || graph_op.memory_space() != Some(context_space)
        || objects.object_for_value(fact.address, context_space) != Some(fact.object)
        || objects
            .object(fact.object)
            .is_none_or(|object| object.kind.space() != context_space)
    {
        return false;
    }

    match graph_op {
        SSAOp::Load { dst, addr, .. } => {
            !fact.is_write
                && graph.value_id_for_var(addr) == Some(fact.address)
                && fact.value == graph.value_id_for_var(dst)
                && fact.width == dst.size
        }
        SSAOp::Store { addr, val, .. } => {
            fact.is_write
                && graph.value_id_for_var(addr) == Some(fact.address)
                && fact.value == graph.value_id_for_var(val)
                && fact.width == val.size
        }
        _ => false,
    }
}

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
            })
            .ok_or(MachineBuildError::EntityMismatch(access.inst))?;
        let source_space = artifact
            .machine_context()
            .memory_space_at(fact.block_addr, fact.op_index)
            .ok_or(MachineBuildError::MachineContextMismatch)?;
        let source_op = match &artifact
            .graph()
            .inst(access.inst)
            .ok_or(MachineBuildError::EntityMismatch(access.inst))?
            .payload
        {
            InstPayload::Op(op) => op,
            _ => return Err(MachineBuildError::EntityMismatch(access.inst)),
        };
        let prepared_op = artifact
            .function()
            .get_block(fact.block_addr)
            .and_then(|block| block.ops.get(fact.op_index))
            .ok_or(MachineBuildError::EntityMismatch(access.inst))?;
        if !memory_access_authorities_match(
            artifact.graph(),
            artifact.objects(),
            source_op,
            prepared_op,
            source_space,
            fact,
        ) {
            return Err(MachineBuildError::EntityMismatch(access.inst));
        }
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

    /// Derive the exact typed address projection for one graph use.
    ///
    /// Memory operands are contextual: the same SSA value is an integer in an
    /// arithmetic use but an address with object provenance at a certified
    /// load/store use. Keeping this lookup keyed by [`UseSite`] prevents a
    /// renderer from classifying `rsp`/`rbp` spellings or applying one address
    /// interpretation to every use of the value.
    pub fn memory_address_for_use(
        artifact: &SsaArtifact,
        site: UseSite,
    ) -> Result<Option<Self>, MachineBuildError> {
        let inst = artifact
            .graph()
            .inst(site.inst)
            .ok_or(MachineBuildError::MissingUseDisposition(site))?;
        let used_value = *inst
            .inputs
            .get(site.input_idx)
            .ok_or(MachineBuildError::MissingUseDisposition(site))?;
        let is_memory_address = site.input_idx == 0
            && matches!(
                &inst.payload,
                InstPayload::Op(SSAOp::Load { .. } | SSAOp::Store { .. })
            );
        if !is_memory_address {
            return Ok(None);
        }
        let access = StructuredAccessId {
            inst: site.inst,
            ordinal: 0,
        };
        let projected = Self::memory_address_for_access(artifact, access)?;
        if projected.binding().value() != used_value || projected.memory_access() != Some(access) {
            return Err(MachineBuildError::UseDispositionMismatch(site));
        }
        Ok(Some(projected))
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
    pub const fn zero(width_bits: u32) -> Option<Self> {
        if width_bits == 0 || width_bits > 64 {
            return None;
        }
        Some(Self {
            width_bits,
            bits: 0,
        })
    }

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

/// Result policy when an integer divisor is zero.
///
/// Raw p-code division and remainder do not model a processor trap or choose a
/// result for this case. Keeping that absence explicit prevents a consumer from
/// silently inheriting its host language's divide-by-zero behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum MachineZeroDivisorBehavior {
    Undefined,
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

/// A typed conversion applied after selecting the exact source bit slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct MachineUseConversion {
    kind: MachineCastKind,
    to_width_bits: u32,
}

impl MachineUseConversion {
    pub const fn kind(self) -> MachineCastKind {
        self.kind
    }

    pub const fn to_width_bits(self) -> u32 {
        self.to_width_bits
    }
}

/// Exact canonical-carrier bits consumed at one dense [`UseSite`] table position.
///
/// Register-backed values are expressed relative to the register geometry's
/// canonical carrier, and `carrier_width_bits` is that carrier's full extent.
/// Other values are expressed relative to their own width. Thus neither the
/// carrier extent nor the coordinate space may be inferred from the selected
/// slice alone.
/// The site and source value are deliberately not repeated here: the table
/// position is the canonical site, and the owning graph is the canonical
/// `UseSite -> ValueId` binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct MachineUseSlice {
    bit_offset: u32,
    width_bits: u32,
    carrier_width_bits: u32,
    conversion: Option<MachineUseConversion>,
}

impl MachineUseSlice {
    pub const fn bit_offset(self) -> u32 {
        self.bit_offset
    }

    pub const fn width_bits(self) -> u32 {
        self.width_bits
    }

    pub const fn carrier_width_bits(self) -> u32 {
        self.carrier_width_bits
    }

    pub const fn conversion(self) -> Option<MachineUseConversion> {
        self.conversion
    }
}

/// Why one graph use has no honest machine slice projection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum MachineUseRefusal {
    MissingRegisterGeometry,
    MalformedRegisterGeometry,
    RegisterGeometry(r2il::RegisterProjectionRefusal),
    InvalidBitRange,
    /// The value-producing instruction is outside the machine vocabulary.
    UnsupportedOperation,
    /// Operand counts, widths, or slices were internally incoherent.
    IncoherentOperation,
}

/// Complete disposition for one graph use, keyed only by its dense table cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum MachineUseDisposition {
    Exact(MachineUseSlice),
    Refused(MachineUseRefusal),
}

/// Exact effect one surviving definition has on its source-owned carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum MachineWriteProjection {
    /// The definition replaces every bit of its carrier; the definition's
    /// output width is the carrier width.
    Full,
    /// The definition replaces one carrier-relative slice and preserves bits
    /// outside it. The carrier extent is explicit because offset plus width
    /// does not identify the canonical carrier.
    Insert {
        bit_offset: u32,
        width_bits: u32,
        carrier_width_bits: u32,
    },
    /// A full-carrier definition zero-extends an exact narrower input;
    /// `to_width_bits` is the carrier width.
    ZeroExtend {
        from_width_bits: u32,
        to_width_bits: u32,
    },
}

/// Why one surviving definition has no honest carrier write projection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum MachineWriteRefusal {
    MissingRegisterGeometry,
    MalformedRegisterGeometry,
    RegisterGeometry(r2il::RegisterProjectionRefusal),
    InvalidBitRange,
    UnsupportedOperation,
    IncoherentOperation,
}

/// Complete write disposition for one output-producing [`InstId`] table cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum MachineWriteDisposition {
    Exact(MachineWriteProjection),
    Refused(MachineWriteRefusal),
}

/// One immutable machine expression node.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum MachineExprKind {
    Source {
        binding: MachineValueBinding,
        /// The machine location this value came from, when it has one. A
        /// consumer needs it to recognise that a value is a narrower read of a
        /// location it already knows, such as the low half of an argument
        /// register.
        storage: Option<CanonicalStorageId>,
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
    UnsignedDivide {
        zero_divisor: MachineZeroDivisorBehavior,
        dividend: MachineExprId,
        divisor: MachineExprId,
    },
    UnsignedRemainder {
        zero_divisor: MachineZeroDivisorBehavior,
        dividend: MachineExprId,
        divisor: MachineExprId,
    },
    Negate {
        mode: MachineArithmeticMode,
        input: MachineExprId,
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
    Concat {
        high: MachineExprId,
        low: MachineExprId,
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
            | Self::Negate { input, .. }
            | Self::Cast { input, .. }
            | Self::Extract { input, .. } => vec![*input],
            Self::Arithmetic { left, right, .. }
            | Self::ArithmeticFlag { left, right, .. }
            | Self::Bitwise { left, right, .. }
            | Self::Boolean { left, right, .. }
            | Self::Compare { left, right, .. } => vec![*left, *right],
            Self::UnsignedDivide {
                dividend, divisor, ..
            }
            | Self::UnsignedRemainder {
                dividend, divisor, ..
            } => vec![*dividend, *divisor],
            Self::Concat { high, low } => vec![*high, *low],
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
    UntrustedArtifactProvenance,
    IncompleteObligationInventory,
    MissingGraphValue(ValueId),
    MissingGraphBlock(BlockId),
    DuplicateBlockAddress(u64),
    TopologyMismatch,
    MachineContextMismatch,
    MissingInstruction(InstId),
    MissingInstructionDisposition(InstId),
    MissingUseDisposition(UseSite),
    MissingWriteDisposition(InstId),
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
    UseDispositionMismatch(UseSite),
    WriteDispositionMismatch(InstId),
    /// A source obligation has no coherent graph-instruction owner. This keeps
    /// first-class native spans keyed by exact source identity instead of
    /// coercing them into a fabricated `InstId`.
    ObligationSourceMismatch(CanonicalInstructionId),
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
    use_dispositions: Box<[Box<[MachineUseDisposition]>]>,
    /// Dense by `InstId`; `None` is reserved for graph instructions with no output.
    write_dispositions: Box<[Option<MachineWriteDisposition>]>,
}

impl MachineProjection {
    pub fn from_artifact(artifact: &SsaArtifact) -> Result<Self, MachineBuildError> {
        if !artifact.obligations().is_complete() {
            return Err(MachineBuildError::IncompleteObligationInventory);
        }
        let graph = artifact.graph();
        let mut builder = MachineBuilder::for_graph(graph);
        let mut entities = Vec::new();
        let mut failures = Vec::new();
        let mut write_dispositions = Vec::with_capacity(graph.insts.len());

        for (inst_index, inst) in graph.insts.iter().enumerate() {
            if inst.id.0 as usize != inst_index {
                return Err(MachineBuildError::TopologyMismatch);
            }
            let Some(output_id) = inst.output else {
                builder.lower_outputless_inst(graph, inst)?;
                write_dispositions.push(None);
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
                Ok(root) => {
                    let root_expr = builder
                        .nodes
                        .get(root.index())
                        .ok_or(MachineBuildError::MissingWriteDisposition(inst.id))?;
                    write_dispositions
                        .push(Some(machine_write_disposition(artifact, inst, root_expr)));
                    entities.push(MachineEntity {
                        output,
                        root,
                        producer: disposition.id,
                        source_obligations: disposition.obligations.clone(),
                    });
                }
                Err(error) if is_local_projection_failure(&error, inst.id) => {
                    builder.refuse_inst_uses(inst, use_refusal_for_error(&error))?;
                    write_dispositions.push(Some(MachineWriteDisposition::Refused(
                        write_refusal_for_error(&error),
                    )));
                    failures.push(MachineProjectionFailure {
                        output: output_id,
                        producer: disposition.id,
                        error,
                    });
                }
                Err(error) => return Err(error),
            }
        }

        let use_dispositions =
            canonical_machine_use_dispositions(artifact, builder.use_dispositions)?;
        let projection = Self {
            machine: MachineFunction {
                arena: MachineExprArena {
                    nodes: builder.nodes.into_boxed_slice(),
                },
                entities: entities.into_boxed_slice(),
            },
            failures: failures.into_boxed_slice(),
            use_dispositions: use_dispositions
                .into_iter()
                .map(Vec::into_boxed_slice)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            write_dispositions: write_dispositions.into_boxed_slice(),
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

    /// Dense O(1) lookup for the disposition of one exact graph input use.
    pub fn use_disposition(&self, site: UseSite) -> Option<&MachineUseDisposition> {
        self.use_dispositions
            .get(site.inst.0 as usize)?
            .get(site.input_idx)
    }

    /// Dense rows indexed by `InstId`, with cells indexed by input position.
    pub const fn use_dispositions(&self) -> &[Box<[MachineUseDisposition]>] {
        &self.use_dispositions
    }

    /// Dense O(1) lookup for one output-producing graph instruction.
    pub fn write_disposition(&self, inst: InstId) -> Option<&MachineWriteDisposition> {
        self.write_dispositions.get(inst.0 as usize)?.as_ref()
    }

    /// Dense rows indexed by `InstId`; `None` means the instruction has no output.
    pub const fn write_dispositions(&self) -> &[Option<MachineWriteDisposition>] {
        &self.write_dispositions
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
        self.validate_use_dispositions(artifact, &entities, &failed_outputs)?;
        self.validate_write_dispositions(artifact, &entities, &failed_outputs)?;
        Ok(())
    }

    fn validate_use_dispositions(
        &self,
        artifact: &SsaArtifact,
        entities: &BTreeMap<ValueId, &MachineEntity>,
        failures: &BTreeMap<ValueId, &MachineProjectionFailure>,
    ) -> Result<(), MachineBuildError> {
        let graph = artifact.graph();
        if self.use_dispositions.len() != graph.insts.len() {
            return Err(MachineBuildError::TopologyMismatch);
        }
        let constant_bindings = self
            .machine
            .arena
            .iter()
            .filter_map(|(_, expr)| match expr.kind() {
                MachineExprKind::Constant { binding, .. } => Some(*binding),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        for (inst_index, inst) in graph.insts.iter().enumerate() {
            if inst.id.0 as usize != inst_index {
                return Err(MachineBuildError::TopologyMismatch);
            }
            let row = &self.use_dispositions[inst_index];
            if row.len() != inst.inputs.len() {
                return Err(MachineBuildError::TopologyMismatch);
            }
            let expected_refusal = inst
                .output
                .and_then(|output| failures.get(&output))
                .map(|failure| use_refusal_for_error(failure.error()));
            let root = inst
                .output
                .and_then(|output| entities.get(&output))
                .and_then(|entity| self.machine.expr(entity.root()));
            let root_children = root.map(|root| root.kind.children());

            for (input_idx, disposition) in row.iter().enumerate() {
                let site = UseSite {
                    inst: inst.id,
                    input_idx,
                };
                let input = *inst
                    .inputs
                    .get(input_idx)
                    .ok_or(MachineBuildError::MissingUseDisposition(site))?;
                let graph_value = graph
                    .value(input)
                    .ok_or(MachineBuildError::MissingGraphValue(input))?;
                let source = binding_for_value(graph_value)?;
                let operation_relative = match (expected_refusal, root) {
                    (Some(expected), _) => MachineUseDisposition::Refused(expected),
                    (None, Some(root)) => MachineUseDisposition::Exact(
                        machine_use_slice_for_input(
                            &self.machine.arena,
                            root,
                            *root_children
                                .as_ref()
                                .and_then(|children| children.get(input_idx))
                                .ok_or(MachineBuildError::UseDispositionMismatch(site))?,
                            source,
                        )
                        .ok_or(MachineBuildError::UseDispositionMismatch(site))?,
                    ),
                    (None, None) if inst.output.is_none() => {
                        if graph_value.var.constant_bits().is_some()
                            && !constant_bindings.contains(&source)
                        {
                            return Err(MachineBuildError::UseDispositionMismatch(site));
                        }
                        MachineUseDisposition::Exact(whole_machine_use(source))
                    }
                    (None, None) => {
                        return Err(MachineBuildError::UseDispositionMismatch(site));
                    }
                };
                validate_canonical_machine_use_disposition(
                    artifact,
                    site,
                    input,
                    operation_relative,
                    *disposition,
                )?;
            }
        }
        Ok(())
    }

    fn validate_write_dispositions(
        &self,
        artifact: &SsaArtifact,
        entities: &BTreeMap<ValueId, &MachineEntity>,
        failures: &BTreeMap<ValueId, &MachineProjectionFailure>,
    ) -> Result<(), MachineBuildError> {
        let graph = artifact.graph();
        if self.write_dispositions.len() != graph.insts.len() {
            return Err(MachineBuildError::TopologyMismatch);
        }
        for (inst_index, inst) in graph.insts.iter().enumerate() {
            if inst.id.0 as usize != inst_index {
                return Err(MachineBuildError::TopologyMismatch);
            }
            let actual = self
                .write_dispositions
                .get(inst_index)
                .ok_or(MachineBuildError::MissingWriteDisposition(inst.id))?;
            let Some(output) = inst.output else {
                if actual.is_some() {
                    return Err(MachineBuildError::WriteDispositionMismatch(inst.id));
                }
                continue;
            };
            let expected = if let Some(entity) = entities.get(&output) {
                let root = self
                    .machine
                    .expr(entity.root())
                    .ok_or(MachineBuildError::WriteDispositionMismatch(inst.id))?;
                machine_write_disposition(artifact, inst, root)
            } else if let Some(failure) = failures.get(&output) {
                MachineWriteDisposition::Refused(write_refusal_for_error(failure.error()))
            } else {
                return Err(MachineBuildError::WriteDispositionMismatch(inst.id));
            };
            if *actual != Some(expected) {
                return Err(MachineBuildError::WriteDispositionMismatch(inst.id));
            }
        }
        Ok(())
    }

    fn into_machine(self) -> MachineFunction {
        self.machine
    }
}

fn is_local_projection_failure(error: &MachineBuildError, inst: InstId) -> bool {
    matches!(
        error,
        MachineBuildError::UnsupportedOperation { inst: actual, .. }
            | MachineBuildError::WrongOperandCount { inst: actual, .. }
            | MachineBuildError::WidthMismatch { inst: actual, .. }
            | MachineBuildError::InvalidCastWidth { inst: actual, .. }
            | MachineBuildError::InvalidSubpiece { inst: actual, .. }
            if *actual == inst
    )
}

fn use_refusal_for_error(error: &MachineBuildError) -> MachineUseRefusal {
    match error {
        MachineBuildError::UnsupportedOperation { .. } => MachineUseRefusal::UnsupportedOperation,
        _ => MachineUseRefusal::IncoherentOperation,
    }
}

fn write_refusal_for_error(error: &MachineBuildError) -> MachineWriteRefusal {
    match error {
        MachineBuildError::UnsupportedOperation { .. } => MachineWriteRefusal::UnsupportedOperation,
        _ => MachineWriteRefusal::IncoherentOperation,
    }
}

fn canonical_machine_use_dispositions(
    artifact: &SsaArtifact,
    operation_relative: Vec<Vec<MachineUseDisposition>>,
) -> Result<Vec<Vec<MachineUseDisposition>>, MachineBuildError> {
    let graph = artifact.graph();
    if operation_relative.len() != graph.insts.len() {
        return Err(MachineBuildError::TopologyMismatch);
    }
    let mut canonical = Vec::with_capacity(operation_relative.len());
    for (inst_index, row) in operation_relative.into_iter().enumerate() {
        let inst = graph
            .insts
            .get(inst_index)
            .ok_or(MachineBuildError::TopologyMismatch)?;
        if inst.id.0 as usize != inst_index || row.len() != inst.inputs.len() {
            return Err(MachineBuildError::TopologyMismatch);
        }
        let mut canonical_row = Vec::with_capacity(row.len());
        for (input_idx, disposition) in row.into_iter().enumerate() {
            let site = UseSite {
                inst: inst.id,
                input_idx,
            };
            let input = *inst
                .inputs
                .get(input_idx)
                .ok_or(MachineBuildError::MissingUseDisposition(site))?;
            canonical_row.push(canonical_machine_use_disposition(
                artifact,
                site,
                input,
                disposition,
            )?);
        }
        canonical.push(canonical_row);
    }
    Ok(canonical)
}

fn canonical_machine_use_disposition(
    artifact: &SsaArtifact,
    site: UseSite,
    input: ValueId,
    operation_relative: MachineUseDisposition,
) -> Result<MachineUseDisposition, MachineBuildError> {
    let MachineUseDisposition::Exact(slice) = operation_relative else {
        return Ok(operation_relative);
    };
    let graph_value = artifact
        .graph()
        .value(input)
        .ok_or(MachineBuildError::MissingGraphValue(input))?;
    let source = binding_for_value(graph_value)?;
    validate_machine_use_slice(slice, source.width_bits)
        .map_err(|_| MachineBuildError::UseDispositionMismatch(site))?;

    let Some(storage) = graph_value.canonical_storage else {
        return Ok(MachineUseDisposition::Exact(slice));
    };
    if storage.space != CanonicalStorageSpace::Register {
        return Ok(MachineUseDisposition::Exact(slice));
    }
    let geometry = match exact_register_geometry(artifact, storage) {
        Ok(geometry) => geometry,
        Err(reason) => {
            return Ok(MachineUseDisposition::Refused(
                use_refusal_for_register_geometry(reason),
            ));
        }
    };
    if geometry.width_bits != source.width_bits {
        return Ok(MachineUseDisposition::Refused(
            MachineUseRefusal::InvalidBitRange,
        ));
    }
    let slice = match compose_machine_use_slice(slice, geometry.bit_offset, geometry.carrier_bits) {
        Ok(slice) => slice,
        Err(reason) => return Ok(MachineUseDisposition::Refused(reason)),
    };
    Ok(MachineUseDisposition::Exact(slice))
}

fn validate_canonical_machine_use_disposition(
    artifact: &SsaArtifact,
    site: UseSite,
    input: ValueId,
    operation_relative: MachineUseDisposition,
    actual: MachineUseDisposition,
) -> Result<(), MachineBuildError> {
    let mismatch = || MachineBuildError::UseDispositionMismatch(site);
    let MachineUseDisposition::Exact(operation_slice) = operation_relative else {
        return (actual == operation_relative)
            .then_some(())
            .ok_or_else(mismatch);
    };
    let graph_value = artifact
        .graph()
        .value(input)
        .ok_or(MachineBuildError::MissingGraphValue(input))?;
    let source = binding_for_value(graph_value)?;
    validate_machine_use_slice(operation_slice, source.width_bits).map_err(|_| mismatch())?;

    let Some(storage) = graph_value.canonical_storage else {
        return (actual == MachineUseDisposition::Exact(operation_slice))
            .then_some(())
            .ok_or_else(mismatch);
    };
    if storage.space != CanonicalStorageSpace::Register {
        return (actual == MachineUseDisposition::Exact(operation_slice))
            .then_some(())
            .ok_or_else(mismatch);
    }

    let geometry = match exact_register_geometry(artifact, storage) {
        Ok(geometry) if geometry.width_bits == source.width_bits => geometry,
        Ok(_) => {
            return (actual == MachineUseDisposition::Refused(MachineUseRefusal::InvalidBitRange))
                .then_some(())
                .ok_or_else(mismatch);
        }
        Err(reason) => {
            let refusal = use_refusal_for_register_geometry(reason);
            return (actual == MachineUseDisposition::Refused(refusal))
                .then_some(())
                .ok_or_else(mismatch);
        }
    };
    let MachineUseDisposition::Exact(actual_slice) = actual else {
        return Err(mismatch());
    };
    let exact = actual_slice.width_bits == operation_slice.width_bits
        && actual_slice.carrier_width_bits == geometry.carrier_bits
        && actual_slice.conversion == operation_slice.conversion
        && actual_slice.bit_offset.checked_sub(geometry.bit_offset)
            == Some(operation_slice.bit_offset)
        && validate_machine_use_slice(actual_slice, geometry.carrier_bits).is_ok();
    exact.then_some(()).ok_or_else(mismatch)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MachineRegisterGeometryRefusal {
    Missing,
    Malformed,
    Upstream(r2il::RegisterProjectionRefusal),
    InvalidBitRange,
}

fn use_refusal_for_register_geometry(reason: MachineRegisterGeometryRefusal) -> MachineUseRefusal {
    match reason {
        MachineRegisterGeometryRefusal::Missing => MachineUseRefusal::MissingRegisterGeometry,
        MachineRegisterGeometryRefusal::Malformed => MachineUseRefusal::MalformedRegisterGeometry,
        MachineRegisterGeometryRefusal::Upstream(reason) => {
            MachineUseRefusal::RegisterGeometry(reason)
        }
        MachineRegisterGeometryRefusal::InvalidBitRange => MachineUseRefusal::InvalidBitRange,
    }
}

fn write_refusal_for_register_geometry(
    reason: MachineRegisterGeometryRefusal,
) -> MachineWriteRefusal {
    match reason {
        MachineRegisterGeometryRefusal::Missing => MachineWriteRefusal::MissingRegisterGeometry,
        MachineRegisterGeometryRefusal::Malformed => MachineWriteRefusal::MalformedRegisterGeometry,
        MachineRegisterGeometryRefusal::Upstream(reason) => {
            MachineWriteRefusal::RegisterGeometry(reason)
        }
        MachineRegisterGeometryRefusal::InvalidBitRange => MachineWriteRefusal::InvalidBitRange,
    }
}

fn compose_machine_use_slice(
    operation_relative: MachineUseSlice,
    carrier_bit_offset: u32,
    carrier_width_bits: u32,
) -> Result<MachineUseSlice, MachineUseRefusal> {
    let bit_offset = carrier_bit_offset
        .checked_add(operation_relative.bit_offset)
        .ok_or(MachineUseRefusal::InvalidBitRange)?;
    let canonical = MachineUseSlice {
        bit_offset,
        carrier_width_bits,
        ..operation_relative
    };
    validate_machine_use_slice(canonical, carrier_width_bits)
        .map_err(|_| MachineUseRefusal::InvalidBitRange)?;
    Ok(canonical)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ExactRegisterGeometry {
    bit_offset: u32,
    width_bits: u32,
    carrier_bits: u32,
}

fn exact_register_geometry(
    artifact: &SsaArtifact,
    written: CanonicalStorageId,
) -> Result<ExactRegisterGeometry, MachineRegisterGeometryRefusal> {
    if written.space != CanonicalStorageSpace::Register {
        return Err(MachineRegisterGeometryRefusal::InvalidBitRange);
    }
    match artifact.machine_context().register_geometry_state() {
        MachineRegisterGeometryState::Unavailable => {
            return Err(MachineRegisterGeometryRefusal::Missing);
        }
        MachineRegisterGeometryState::Malformed => {
            return Err(MachineRegisterGeometryRefusal::Malformed);
        }
        MachineRegisterGeometryState::Available => {}
    }
    let projection = artifact
        .machine_context()
        .register_projection(written)
        .ok_or(MachineRegisterGeometryRefusal::InvalidBitRange)?;
    if projection.written.offset != written.offset || projection.written.size != written.size {
        return Err(MachineRegisterGeometryRefusal::InvalidBitRange);
    }
    let r2il::RegisterProjectionDisposition::Bound { carrier, slice } = projection.disposition
    else {
        let r2il::RegisterProjectionDisposition::Refused { reason } = projection.disposition else {
            unreachable!("register projection disposition is exhaustive")
        };
        return Err(MachineRegisterGeometryRefusal::Upstream(reason));
    };
    if !carrier.contains(projection.written) {
        return Err(MachineRegisterGeometryRefusal::InvalidBitRange);
    }
    let written_bits = written
        .size
        .checked_mul(8)
        .ok_or(MachineRegisterGeometryRefusal::InvalidBitRange)?;
    let carrier_bits = carrier
        .size
        .checked_mul(8)
        .ok_or(MachineRegisterGeometryRefusal::InvalidBitRange)?;
    let bit_offset = u32::try_from(slice.lsb_bit_offset)
        .map_err(|_| MachineRegisterGeometryRefusal::InvalidBitRange)?;
    let width_bits = u32::try_from(slice.size_bits)
        .map_err(|_| MachineRegisterGeometryRefusal::InvalidBitRange)?;
    if width_bits == 0
        || width_bits != written_bits
        || bit_offset
            .checked_add(width_bits)
            .is_none_or(|end| end > carrier_bits)
        || (carrier == projection.written && (bit_offset != 0 || width_bits != carrier_bits))
    {
        return Err(MachineRegisterGeometryRefusal::InvalidBitRange);
    }
    Ok(ExactRegisterGeometry {
        bit_offset,
        width_bits,
        carrier_bits,
    })
}

fn exact_zero_extend_write(
    artifact: &SsaArtifact,
    inst: &GraphInst,
    root: &MachineExpr,
    output: ExactRegisterGeometry,
) -> Option<MachineWriteProjection> {
    if output.bit_offset != 0 || output.width_bits != output.carrier_bits {
        return None;
    }
    if !matches!(
        &root.kind,
        MachineExprKind::Cast {
            kind: MachineCastKind::ZeroExtend,
            ..
        }
    ) {
        return None;
    }
    let [input] = inst.inputs.as_slice() else {
        return None;
    };
    let graph_value = artifact.graph().value(*input)?;
    let input_width = graph_value.var.size.checked_mul(8)?;
    if input_width >= output.carrier_bits || root.ty.width_bits() != output.carrier_bits {
        return None;
    }
    Some(MachineWriteProjection::ZeroExtend {
        from_width_bits: input_width,
        to_width_bits: output.carrier_bits,
    })
}

fn machine_write_disposition(
    artifact: &SsaArtifact,
    inst: &GraphInst,
    root: &MachineExpr,
) -> MachineWriteDisposition {
    let Some(output) = inst.output else {
        return MachineWriteDisposition::Refused(MachineWriteRefusal::IncoherentOperation);
    };
    let Some(storage) = artifact
        .graph()
        .value(output)
        .and_then(|value| value.canonical_storage)
    else {
        return MachineWriteDisposition::Exact(MachineWriteProjection::Full);
    };
    if storage.space != CanonicalStorageSpace::Register {
        return MachineWriteDisposition::Exact(MachineWriteProjection::Full);
    }
    let geometry = match exact_register_geometry(artifact, storage) {
        Ok(geometry) => geometry,
        Err(reason) => {
            return MachineWriteDisposition::Refused(write_refusal_for_register_geometry(reason));
        }
    };
    if let Some(zero_extend) = exact_zero_extend_write(artifact, inst, root, geometry) {
        return MachineWriteDisposition::Exact(zero_extend);
    }
    if geometry.bit_offset == 0 && geometry.width_bits == geometry.carrier_bits {
        MachineWriteDisposition::Exact(MachineWriteProjection::Full)
    } else {
        MachineWriteDisposition::Exact(MachineWriteProjection::Insert {
            bit_offset: geometry.bit_offset,
            width_bits: geometry.width_bits,
            carrier_width_bits: geometry.carrier_bits,
        })
    }
}

fn validate_machine_use_slice(slice: MachineUseSlice, carrier_width_bits: u32) -> Result<(), ()> {
    if carrier_width_bits == 0
        || slice.carrier_width_bits != carrier_width_bits
        || slice.width_bits == 0
        || slice
            .bit_offset
            .checked_add(slice.width_bits)
            .is_none_or(|end| end > carrier_width_bits)
    {
        return Err(());
    }
    let Some(conversion) = slice.conversion else {
        return Ok(());
    };
    let valid = match conversion.kind {
        MachineCastKind::ZeroExtend | MachineCastKind::SignExtend => {
            conversion.to_width_bits > slice.width_bits
        }
        MachineCastKind::Truncate => conversion.to_width_bits < slice.width_bits,
        MachineCastKind::BitReinterpret
        | MachineCastKind::IntegerToAddress
        | MachineCastKind::AddressToInteger => conversion.to_width_bits == slice.width_bits,
    };
    valid.then_some(()).ok_or(())
}

const fn whole_machine_use(source: MachineValueBinding) -> MachineUseSlice {
    MachineUseSlice {
        bit_offset: 0,
        width_bits: source.width_bits,
        carrier_width_bits: source.width_bits,
        conversion: None,
    }
}

fn machine_use_slice_for_input(
    arena: &MachineExprArena,
    root: &MachineExpr,
    child_id: MachineExprId,
    source: MachineValueBinding,
) -> Option<MachineUseSlice> {
    let child = arena.get(child_id)?;
    if operand_leaf_binding(arena, child_id)? != source {
        return None;
    }

    if let MachineExprKind::Cast { kind, input } = &root.kind {
        if *input != child_id {
            return None;
        }
        return Some(MachineUseSlice {
            bit_offset: 0,
            width_bits: source.width_bits,
            carrier_width_bits: source.width_bits,
            conversion: Some(MachineUseConversion {
                kind: *kind,
                to_width_bits: root.ty.width_bits(),
            }),
        });
    }
    if let MachineExprKind::Extract { input, lsb_bits } = &root.kind {
        if *input != child_id {
            return None;
        }
        return Some(MachineUseSlice {
            bit_offset: *lsb_bits,
            width_bits: root.ty.width_bits(),
            carrier_width_bits: source.width_bits,
            conversion: None,
        });
    }
    if let MachineExprKind::Extract { lsb_bits, .. } = &child.kind {
        return Some(MachineUseSlice {
            bit_offset: *lsb_bits,
            width_bits: child.ty.width_bits(),
            carrier_width_bits: source.width_bits,
            conversion: None,
        });
    }
    Some(whole_machine_use(source))
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
                MachineExprKind::Source { binding, .. } => {
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
            MachineExprKind::Source { binding, .. } | MachineExprKind::Constant { binding, .. } => {
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
            MachineExprKind::UnsignedDivide {
                zero_divisor,
                dividend,
                divisor,
            }
            | MachineExprKind::UnsignedRemainder {
                zero_divisor,
                dividend,
                divisor,
            } => {
                *zero_divisor == MachineZeroDivisorBehavior::Undefined
                    && matches!(
                        expr.ty,
                        MachineType::Integer {
                            signedness: MachineSignedness::Unsigned,
                            ..
                        }
                    )
                    && child(*dividend)?.ty == expr.ty
                    && child(*divisor)?.ty == expr.ty
            }
            MachineExprKind::Negate { mode, input } => {
                *mode == MachineArithmeticMode::Wrapping
                    && matches!(
                        expr.ty,
                        MachineType::Integer {
                            signedness: MachineSignedness::Unsigned,
                            ..
                        }
                    )
                    && child(*input)?.ty == expr.ty
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
            MachineExprKind::Concat { high, low } => {
                let high = child(*high)?;
                let low = child(*low)?;
                matches!(
                    expr.ty,
                    MachineType::Integer {
                        signedness: MachineSignedness::Unsigned,
                        ..
                    }
                ) && matches!(
                    high.ty,
                    MachineType::Integer {
                        signedness: MachineSignedness::Unsigned,
                        ..
                    }
                ) && matches!(
                    low.ty,
                    MachineType::Integer {
                        signedness: MachineSignedness::Unsigned,
                        ..
                    }
                ) && high.ty.width_bits().checked_add(low.ty.width_bits())
                    == Some(expr.ty.width_bits())
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
            let binding = operand_leaf_binding(&self.arena, *child)
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
        let source_op = match &inst.payload {
            InstPayload::Op(op @ SSAOp::Load { .. }) => op,
            _ => return Err(MachineBuildError::EntityMismatch(inst.id)),
        };
        let prepared_op = artifact
            .function()
            .get_block(fact.block_addr)
            .and_then(|block| block.ops.get(fact.op_index))
            .ok_or(MachineBuildError::EntityMismatch(inst.id))?;
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
        if !memory_access_authorities_match(
            artifact.graph(),
            artifact.objects(),
            source_op,
            prepared_op,
            source_space,
            fact,
        ) || *object != fact.object
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
    use_dispositions: Vec<Vec<MachineUseDisposition>>,
}

impl MachineBuilder {
    fn for_graph(graph: &SsaGraph) -> Self {
        Self {
            use_dispositions: graph
                .insts
                .iter()
                .map(|inst| {
                    vec![
                        MachineUseDisposition::Refused(MachineUseRefusal::UnsupportedOperation);
                        inst.inputs.len()
                    ]
                })
                .collect(),
            ..Self::default()
        }
    }

    fn record_use(
        &mut self,
        graph: &SsaGraph,
        inst: &GraphInst,
        input_idx: usize,
        slice: MachineUseSlice,
    ) -> Result<(), MachineBuildError> {
        let site = UseSite {
            inst: inst.id,
            input_idx,
        };
        let input = *inst
            .inputs
            .get(input_idx)
            .ok_or(MachineBuildError::MissingUseDisposition(site))?;
        let source = binding_for_value(
            graph
                .value(input)
                .ok_or(MachineBuildError::MissingGraphValue(input))?,
        )?;
        validate_machine_use_slice(slice, source.width_bits)
            .map_err(|_| MachineBuildError::UseDispositionMismatch(site))?;
        let cell = self
            .use_dispositions
            .get_mut(inst.id.0 as usize)
            .and_then(|row| row.get_mut(input_idx))
            .ok_or(MachineBuildError::MissingUseDisposition(site))?;
        *cell = MachineUseDisposition::Exact(slice);
        Ok(())
    }

    fn record_whole_use(
        &mut self,
        graph: &SsaGraph,
        inst: &GraphInst,
        input_idx: usize,
    ) -> Result<(), MachineBuildError> {
        let input = *inst
            .inputs
            .get(input_idx)
            .ok_or(MachineBuildError::MissingUseDisposition(UseSite {
                inst: inst.id,
                input_idx,
            }))?;
        let source = binding_for_value(
            graph
                .value(input)
                .ok_or(MachineBuildError::MissingGraphValue(input))?,
        )?;
        self.record_use(graph, inst, input_idx, whole_machine_use(source))
    }

    fn refuse_inst_uses(
        &mut self,
        inst: &GraphInst,
        refusal: MachineUseRefusal,
    ) -> Result<(), MachineBuildError> {
        let row = self
            .use_dispositions
            .get_mut(inst.id.0 as usize)
            .ok_or(MachineBuildError::MissingInstruction(inst.id))?;
        if row.len() != inst.inputs.len() {
            return Err(MachineBuildError::TopologyMismatch);
        }
        row.fill(MachineUseDisposition::Refused(refusal));
        Ok(())
    }

    fn lower_outputless_inst(
        &mut self,
        graph: &SsaGraph,
        inst: &GraphInst,
    ) -> Result<(), MachineBuildError> {
        for (input_idx, input) in inst.inputs.iter().copied().enumerate() {
            let graph_value = graph
                .value(input)
                .ok_or(MachineBuildError::MissingGraphValue(input))?;
            if graph_value.var.constant_bits().is_some() {
                self.intern_value(graph_value)?;
            }
            self.record_whole_use(graph, inst, input_idx)?;
        }
        Ok(())
    }

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
            MachineExprKind::Source {
                binding,
                storage: value.canonical_storage,
            }
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
            MachineExprKind::Source {
                binding,
                storage: value.canonical_storage,
            }
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
        let mut nodes = Vec::with_capacity(expected);
        for (input_idx, value) in inst.inputs.iter().copied().enumerate() {
            let graph_value = graph
                .value(value)
                .ok_or(MachineBuildError::MissingGraphValue(value))?;
            nodes.push(self.intern_value(graph_value)?);
            self.record_whole_use(graph, inst, input_idx)?;
        }
        Ok(nodes)
    }

    fn narrowed_operand_nodes(
        &mut self,
        graph: &crate::graph::SsaGraph,
        inst: &GraphInst,
        expected: usize,
        result_bits: u32,
    ) -> Result<Vec<MachineExprId>, MachineBuildError> {
        if inst.inputs.len() != expected {
            return Err(MachineBuildError::WrongOperandCount {
                inst: inst.id,
                expected,
                actual: inst.inputs.len(),
            });
        }
        let mut inputs = Vec::with_capacity(expected);
        for input_idx in 0..expected {
            inputs.push(self.narrowed_operand_node(graph, inst, input_idx, result_bits)?);
        }
        Ok(inputs)
    }

    fn narrowed_operand_node(
        &mut self,
        graph: &crate::graph::SsaGraph,
        inst: &GraphInst,
        input_idx: usize,
        result_bits: u32,
    ) -> Result<MachineExprId, MachineBuildError> {
        let value = *inst
            .inputs
            .get(input_idx)
            .ok_or(MachineBuildError::MissingUseDisposition(UseSite {
                inst: inst.id,
                input_idx,
            }))?;
        let graph_value = graph
            .value(value)
            .ok_or(MachineBuildError::MissingGraphValue(value))?;
        let input = self.intern_value(graph_value)?;
        let input_bits = self.nodes[input.index()].ty.width_bits();
        if input_bits < result_bits {
            return Err(MachineBuildError::WidthMismatch {
                inst: inst.id,
                expected_bits: result_bits,
                actual_bits: input_bits,
            });
        }
        self.record_use(
            graph,
            inst,
            input_idx,
            MachineUseSlice {
                bit_offset: 0,
                width_bits: result_bits,
                carrier_width_bits: input_bits,
                conversion: None,
            },
        )?;
        if input_bits == result_bits {
            return Ok(input);
        }
        Ok(self.push(
            integer_type(result_bits, MachineSignedness::Unsigned),
            None,
            MachineExprKind::Extract { input, lsb_bits: 0 },
        ))
    }

    fn exact_width_operand_node(
        &mut self,
        graph: &crate::graph::SsaGraph,
        inst: &GraphInst,
        input_idx: usize,
        expected_bits: u32,
    ) -> Result<MachineExprId, MachineBuildError> {
        let value = *inst
            .inputs
            .get(input_idx)
            .ok_or(MachineBuildError::MissingUseDisposition(UseSite {
                inst: inst.id,
                input_idx,
            }))?;
        let graph_value = graph
            .value(value)
            .ok_or(MachineBuildError::MissingGraphValue(value))?;
        let actual_bits = binding_for_value(graph_value)?.width_bits;
        if actual_bits != expected_bits {
            return Err(MachineBuildError::WidthMismatch {
                inst: inst.id,
                expected_bits,
                actual_bits,
            });
        }
        let input = self.intern_value(graph_value)?;
        self.record_whole_use(graph, inst, input_idx)?;
        Ok(input)
    }

    fn exact_width_operand_nodes(
        &mut self,
        graph: &crate::graph::SsaGraph,
        inst: &GraphInst,
        expected: usize,
        expected_bits: u32,
    ) -> Result<Vec<MachineExprId>, MachineBuildError> {
        if inst.inputs.len() != expected {
            return Err(MachineBuildError::WrongOperandCount {
                inst: inst.id,
                expected,
                actual: inst.inputs.len(),
            });
        }
        let mut inputs = Vec::with_capacity(expected);
        for input_idx in 0..expected {
            inputs.push(self.exact_width_operand_node(graph, inst, input_idx, expected_bits)?);
        }
        Ok(inputs)
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
                for (input_idx, value) in inst.inputs.iter().enumerate() {
                    inputs.push(
                        self.intern_value(
                            graph
                                .value(*value)
                                .ok_or(MachineBuildError::MissingGraphValue(*value))?,
                        )?,
                    );
                    self.record_whole_use(graph, inst, input_idx)?;
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
                let prepared_op = artifact
                    .function()
                    .get_block(access.block_addr)
                    .and_then(|block| block.ops.get(access.op_index));
                if !access.provenance_complete
                    || access.is_write
                    || access.id.ordinal != 0
                    || access.value != Some(output.value)
                    || prepared_op.is_none_or(|prepared_op| {
                        source_space.is_none_or(|source_space| {
                            !memory_access_authorities_match(
                                graph,
                                artifact.objects(),
                                op,
                                prepared_op,
                                source_space,
                                access,
                            )
                        })
                    })
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
                self.record_whole_use(graph, inst, 0)?;
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
            SSAOp::IntDiv { .. } => {
                let inputs = self.exact_width_operand_nodes(graph, inst, 2, output.width_bits)?;
                Ok((
                    unsigned,
                    MachineExprKind::UnsignedDivide {
                        zero_divisor: MachineZeroDivisorBehavior::Undefined,
                        dividend: inputs[0],
                        divisor: inputs[1],
                    },
                ))
            }
            SSAOp::IntRem { .. } => {
                let inputs = self.exact_width_operand_nodes(graph, inst, 2, output.width_bits)?;
                Ok((
                    unsigned,
                    MachineExprKind::UnsignedRemainder {
                        zero_divisor: MachineZeroDivisorBehavior::Undefined,
                        dividend: inputs[0],
                        divisor: inputs[1],
                    },
                ))
            }
            SSAOp::IntNegate { .. } => {
                let inputs = self.exact_width_operand_nodes(graph, inst, 1, output.width_bits)?;
                Ok((
                    unsigned,
                    MachineExprKind::Negate {
                        mode: MachineArithmeticMode::Wrapping,
                        input: inputs[0],
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
                // Sleigh may write the low part of a wider bitwise operation
                // directly into a narrower varnode. Make that truncation
                // explicit in the typed machine expression instead of
                // accepting mismatched child widths.
                let inputs = self.narrowed_operand_nodes(graph, inst, 2, output.width_bits)?;
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
                self.record_whole_use(graph, inst, 0)?;
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
                self.record_whole_use(graph, inst, 0)?;
                self.record_whole_use(graph, inst, 1)?;
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
                if inst.inputs.len() != 2 {
                    return Err(MachineBuildError::WrongOperandCount {
                        inst: inst.id,
                        expected: 2,
                        actual: inst.inputs.len(),
                    });
                }
                // A shift does not prove a projection from a wider carrier.
                // Canonical R2IL requires the value and destination widths to
                // match; reject malformed input locally instead of inventing
                // an Extract. The count is independent and stays whole at its
                // source width.
                let value = self.exact_width_operand_node(graph, inst, 0, output.width_bits)?;
                let count_value = graph
                    .value(inst.inputs[1])
                    .ok_or(MachineBuildError::MissingGraphValue(inst.inputs[1]))?;
                let count = self.intern_value(count_value)?;
                self.record_whole_use(graph, inst, 1)?;
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
                        value,
                        count,
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
                let input = self.intern_value(input_value)?;
                let from = self.nodes[input.index()].ty.width_bits();
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
                self.record_use(
                    graph,
                    inst,
                    0,
                    MachineUseSlice {
                        bit_offset: 0,
                        width_bits: from,
                        carrier_width_bits: from,
                        conversion: Some(MachineUseConversion {
                            kind,
                            to_width_bits: output.width_bits,
                        }),
                    },
                )?;
                Ok((ty, MachineExprKind::Cast { kind, input }))
            }
            SSAOp::Subpiece { offset, .. } => {
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
                let input = self.intern_value(input_value)?;
                let source_bits = self.nodes[input.index()].ty.width_bits();
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
                self.record_use(
                    graph,
                    inst,
                    0,
                    MachineUseSlice {
                        bit_offset: lsb_bits,
                        width_bits: output.width_bits,
                        carrier_width_bits: source_bits,
                        conversion: None,
                    },
                )?;
                Ok((unsigned, MachineExprKind::Extract { input, lsb_bits }))
            }
            SSAOp::Piece { .. } => {
                if inst.inputs.len() != 2 {
                    return Err(MachineBuildError::WrongOperandCount {
                        inst: inst.id,
                        expected: 2,
                        actual: inst.inputs.len(),
                    });
                }
                let high_value = graph
                    .value(inst.inputs[0])
                    .ok_or(MachineBuildError::MissingGraphValue(inst.inputs[0]))?;
                let low_value = graph
                    .value(inst.inputs[1])
                    .ok_or(MachineBuildError::MissingGraphValue(inst.inputs[1]))?;
                let high_bits = binding_for_value(high_value)?.width_bits;
                let low_bits = binding_for_value(low_value)?.width_bits;
                let Some(actual_bits) = high_bits.checked_add(low_bits) else {
                    return Err(MachineBuildError::WidthMismatch {
                        inst: inst.id,
                        expected_bits: output.width_bits,
                        actual_bits: u32::MAX,
                    });
                };
                if actual_bits != output.width_bits {
                    return Err(MachineBuildError::WidthMismatch {
                        inst: inst.id,
                        expected_bits: output.width_bits,
                        actual_bits,
                    });
                }
                let high = self.intern_value(high_value)?;
                let low = self.intern_value(low_value)?;
                self.record_whole_use(graph, inst, 0)?;
                self.record_whole_use(graph, inst, 1)?;
                Ok((unsigned, MachineExprKind::Concat { high, low }))
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
                self.record_whole_use(graph, inst, 0)?;
                self.record_whole_use(graph, inst, 1)?;
                self.record_whole_use(graph, inst, 2)?;
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
            ObjectKind::StackSlot { base, offset, .. }
            | ObjectKind::FrameObject { base, offset, .. } => MachineAddressProvenance::Stack {
                base: match base {
                    StackAddressBase::FramePointer => MachineStackBase::FramePointer,
                    StackAddressBase::StackPointer => MachineStackBase::StackPointer,
                },
                offset: *offset,
            },
            ObjectKind::Parameter { index, .. } => u32::try_from(*index)
                .map(|index| MachineAddressProvenance::Parameter { index })
                .unwrap_or(MachineAddressProvenance::Unknown),
            ObjectKind::Global { address, .. } => {
                MachineAddressProvenance::Global { address: *address }
            }
            ObjectKind::HeapAlloc { .. } | ObjectKind::EscapedUnknown { .. } => {
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

fn operand_leaf_binding(
    arena: &MachineExprArena,
    expr: MachineExprId,
) -> Option<MachineValueBinding> {
    match arena.get(expr)?.kind {
        MachineExprKind::Source { binding, .. } | MachineExprKind::Constant { binding, .. } => {
            Some(binding)
        }
        MachineExprKind::Extract { input, lsb_bits: 0 } => operand_leaf_binding(arena, input),
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
                SSAOp::IntDiv { .. },
                MachineExprKind::UnsignedDivide {
                    zero_divisor: MachineZeroDivisorBehavior::Undefined,
                    ..
                }
            )
            | (
                SSAOp::IntRem { .. },
                MachineExprKind::UnsignedRemainder {
                    zero_divisor: MachineZeroDivisorBehavior::Undefined,
                    ..
                }
            )
            | (
                SSAOp::IntNegate { .. },
                MachineExprKind::Negate {
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
            | (SSAOp::Piece { .. }, MachineExprKind::Concat { .. })
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
        | SSAOp::IntDiv { .. }
        | SSAOp::IntRem { .. }
        | SSAOp::IntNegate { .. }
        | SSAOp::IntAnd { .. }
        | SSAOp::IntOr { .. }
        | SSAOp::IntXor { .. }
        | SSAOp::IntNot { .. }
        | SSAOp::IntLeft { .. }
        | SSAOp::IntRight { .. }
        | SSAOp::IntZExt { .. }
        | SSAOp::Trunc { .. }
        | SSAOp::Cast { .. }
        | SSAOp::Piece { .. }
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
    use r2il::{
        ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef, RegisterProjection,
        RegisterProjectionDisposition, RegisterProjectionRefusal, RegisterStorage, SpaceId,
        Varnode,
    };

    fn artifact_with_ops(ops: impl IntoIterator<Item = R2ILOp>) -> SsaArtifact {
        let mut block = R2ILBlock::new(0x1000, 4);
        for op in ops {
            block.push(op);
        }
        SsaArtifact::raw(&[block], None).expect("test SSA artifact")
    }

    fn artifact_with_arch(ops: impl IntoIterator<Item = R2ILOp>, arch: &ArchSpec) -> SsaArtifact {
        let mut block = R2ILBlock::new(0x1000, 4);
        for op in ops {
            block.push(op);
        }
        SsaArtifact::raw(&[block], Some(arch)).expect("test SSA artifact")
    }

    fn register_geometry_arch() -> ArchSpec {
        let eax = RegisterStorage { offset: 0, size: 4 };
        let rax = RegisterStorage { offset: 0, size: 8 };
        let ah = RegisterStorage { offset: 1, size: 1 };
        let mut arch = ArchSpec::new("geometry-test");
        arch.add_register(RegisterDef::new("eax", eax.offset, eax.size));
        arch.add_register(RegisterDef::new("rax", rax.offset, rax.size));
        arch.add_register(RegisterDef::new("ah", ah.offset, ah.size));
        arch.register_projections = vec![
            RegisterProjection {
                written: eax,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: rax,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 32,
                    },
                },
            },
            RegisterProjection {
                written: rax,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: rax,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 64,
                    },
                },
            },
            RegisterProjection {
                written: ah,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: rax,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 8,
                        size_bits: 8,
                    },
                },
            },
        ];
        arch
    }

    fn big_endian_register_geometry_arch() -> ArchSpec {
        let carrier = RegisterStorage { offset: 0, size: 8 };
        let high_byte = RegisterStorage { offset: 6, size: 1 };
        let mut arch = ArchSpec::new("geometry-test-be");
        arch.set_instruction_endianness(Endianness::Big);
        arch.set_memory_endianness(Endianness::Big);
        arch.add_register(RegisterDef::new("carrier", carrier.offset, carrier.size));
        arch.add_register(RegisterDef::new(
            "high_byte",
            high_byte.offset,
            high_byte.size,
        ));
        arch.register_projections = vec![
            RegisterProjection {
                written: carrier,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 64,
                    },
                },
            },
            RegisterProjection {
                written: high_byte,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 8,
                        size_bits: 8,
                    },
                },
            },
        ];
        arch
    }

    #[test]
    fn zero_bitvector_is_checked_and_exact() {
        for width_bits in [1, 8, 16, 32, 64] {
            let zero = MachineBitVector::zero(width_bits).expect("supported zero bitvector");
            assert_eq!(zero.width_bits(), width_bits);
            assert_eq!(zero.bits(), 0);
        }
        assert_eq!(MachineBitVector::zero(0), None);
        assert_eq!(MachineBitVector::zero(65), None);
        assert_eq!(MachineBitVector::zero(u32::MAX), None);
    }

    #[test]
    fn unsigned_64_bit_multiply_retains_wrapping_arithmetic() {
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
    fn narrow_bitwise_result_explicitly_extracts_low_operand_bits() {
        let artifact = artifact_with_ops([R2ILOp::IntAnd {
            dst: Varnode::unique(0x10, 4),
            a: Varnode::register(0, 8),
            b: Varnode::constant(0xff, 8),
        }]);

        let machine =
            MachineFunction::from_artifact(&artifact).expect("typed narrow bitwise expression");
        let entity = machine.entities().first().expect("bitwise entity");
        let root = machine.expr(entity.root()).expect("bitwise root");
        let MachineExprKind::Bitwise { left, right, .. } = root.kind() else {
            panic!("expected bitwise root, got {:?}", root.kind());
        };
        for input in [left, right] {
            let narrowed = machine.expr(*input).expect("narrowed operand");
            assert_eq!(
                narrowed.ty(),
                &integer_type(32, MachineSignedness::Unsigned)
            );
            let MachineExprKind::Extract { input, lsb_bits } = narrowed.kind() else {
                panic!(
                    "expected explicit low-bit extract, got {:?}",
                    narrowed.kind()
                );
            };
            assert_eq!(*lsb_bits, 0);
            assert_eq!(
                machine
                    .expr(*input)
                    .expect("wide source operand")
                    .ty()
                    .width_bits(),
                64
            );
        }
        machine
            .validate_against(&artifact)
            .expect("narrow bitwise expression remains source-bound");
    }

    #[test]
    fn shifts_require_exact_value_width_and_keep_the_count_width() {
        let artifact = artifact_with_ops([
            R2ILOp::IntLeft {
                dst: Varnode::unique(0x10, 4),
                a: Varnode::unique(0x100, 4),
                b: Varnode::constant(1, 1),
            },
            R2ILOp::IntRight {
                dst: Varnode::unique(0x18, 4),
                a: Varnode::unique(0x108, 4),
                b: Varnode::constant(2, 1),
            },
            R2ILOp::IntSRight {
                dst: Varnode::unique(0x20, 4),
                a: Varnode::unique(0x110, 4),
                b: Varnode::constant(3, 1),
            },
        ]);

        let projection =
            MachineProjection::from_artifact(&artifact).expect("typed shift projection");
        assert!(
            projection.failures().is_empty(),
            "valid shifts must not become projection refusals: {:?}",
            projection.failures()
        );
        assert_eq!(
            projection,
            MachineProjection::from_artifact(&artifact).expect("repeated shift projection")
        );

        for (op_index, expected_kind) in [
            (0, MachineShiftKind::Left),
            (1, MachineShiftKind::LogicalRight),
            (2, MachineShiftKind::ArithmeticRight),
        ] {
            let inst = artifact
                .graph()
                .inst_id_for_op_site(0x1000, op_index)
                .expect("shift instruction");
            let output = artifact
                .graph()
                .inst(inst)
                .and_then(|inst| inst.output)
                .expect("shift output");
            let root = projection
                .entity_for_output(output)
                .and_then(|entity| projection.expr(entity.root()))
                .expect("shift expression");
            let MachineExprKind::Shift {
                kind, value, count, ..
            } = root.kind()
            else {
                panic!("expected shift root, got {:?}", root.kind());
            };
            assert_eq!(*kind, expected_kind);
            assert_eq!(root.ty().width_bits(), 32);

            let value = projection.expr(*value).expect("whole shift value");
            assert_eq!(value.ty().width_bits(), 32);
            let MachineExprKind::Source { binding, .. } = value.kind() else {
                panic!(
                    "shift value must remain a whole source, got {:?}",
                    value.kind()
                );
            };
            assert_eq!(
                *binding,
                MachineValueBinding {
                    value: artifact
                        .graph()
                        .inst(inst)
                        .expect("shift instruction")
                        .inputs[0],
                    width_bits: 32,
                }
            );
            assert_eq!(
                projection
                    .expr(*count)
                    .expect("shift count source")
                    .ty()
                    .width_bits(),
                8
            );
            assert_eq!(
                exact_use(&projection, &artifact, op_index, 0),
                MachineUseSlice {
                    bit_offset: 0,
                    width_bits: 32,
                    carrier_width_bits: 32,
                    conversion: None,
                }
            );
            assert_eq!(
                exact_use(&projection, &artifact, op_index, 1),
                MachineUseSlice {
                    bit_offset: 0,
                    width_bits: 8,
                    carrier_width_bits: 8,
                    conversion: None,
                }
            );
        }
        projection
            .validate_against(&artifact)
            .expect("shift projection remains source-bound");
    }

    #[test]
    fn malformed_shift_graph_reports_instruction_width_mismatch() {
        let value = GraphValue {
            id: ValueId(0),
            var: SSAVar::initial("wide", 8),
            canonical_storage: None,
        };
        let count = GraphValue {
            id: ValueId(1),
            var: SSAVar::constant(1, 1),
            canonical_storage: None,
        };
        let inst = GraphInst {
            id: InstId(0),
            block: BlockId(0),
            ordinal: 0,
            inputs: vec![value.id, count.id],
            output: None,
            canonical_storage: None,
            payload: InstPayload::Op(SSAOp::IntRight {
                dst: SSAVar::new("result", 1, 4),
                a: value.var.clone(),
                b: count.var.clone(),
            }),
        };
        let graph = SsaGraph {
            entry: BlockId(0),
            block_order: vec![BlockId(0)],
            blocks: vec![crate::GraphBlock {
                id: BlockId(0),
                addr: 0x1000,
                size: 4,
                predecessors: Vec::new(),
                successors: Vec::new(),
                insts: vec![inst.id],
            }],
            insts: vec![inst],
            values: vec![value.clone(), count],
            def_of: vec![None, None],
            uses_of: vec![
                vec![UseSite {
                    inst: InstId(0),
                    input_idx: 0,
                }],
                vec![UseSite {
                    inst: InstId(0),
                    input_idx: 1,
                }],
            ],
            block_by_addr: [(0x1000, BlockId(0))].into(),
            value_by_var: [(value.var, ValueId(0))].into(),
            op_inst_by_site: [((0x1000, 0), InstId(0))].into(),
            op_site_by_inst: [(InstId(0), (0x1000, 0))].into(),
        };
        let inst = graph.inst(InstId(0)).expect("shift instruction");
        let mut builder = MachineBuilder::for_graph(&graph);

        for expected_bits in [32, 128] {
            assert_eq!(
                builder
                    .exact_width_operand_node(&graph, inst, 0, expected_bits)
                    .expect_err("a shift value needs explicit upstream projection evidence"),
                MachineBuildError::WidthMismatch {
                    inst: InstId(0),
                    expected_bits,
                    actual_bits: 64,
                }
            );
        }
        assert!(is_local_projection_failure(
            &MachineBuildError::WidthMismatch {
                inst: InstId(0),
                expected_bits: 32,
                actual_bits: 64,
            },
            InstId(0)
        ));
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
                },
                ..
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
        assert!(
            flags
                .iter()
                .all(|flag| flag.ty() == &MachineType::Bool { storage_bits: 8 })
        );
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
    fn divide_negate_and_piece_have_exact_machine_vocabulary() {
        let artifact = artifact_with_ops([
            R2ILOp::IntDiv {
                dst: Varnode::unique(0x10, 4),
                a: Varnode::unique(0x100, 4),
                b: Varnode::constant(0, 4),
            },
            R2ILOp::IntNegate {
                dst: Varnode::unique(0x18, 8),
                src: Varnode::unique(0x108, 8),
            },
            R2ILOp::Piece {
                dst: Varnode::unique(0x20, 8),
                hi: Varnode::unique(0x110, 4),
                lo: Varnode::unique(0x118, 4),
            },
        ]);
        let projection = MachineProjection::from_artifact(&artifact).expect("exact projection");
        assert!(projection.failures().is_empty());

        for (op_index, expected_width, expected_inputs) in
            [(0, 32, 2_usize), (1, 64, 1), (2, 64, 2)]
        {
            let inst = artifact
                .graph()
                .inst_id_for_op_site(0x1000, op_index)
                .expect("projected instruction");
            let output = artifact
                .graph()
                .inst(inst)
                .and_then(|inst| inst.output)
                .expect("projected output");
            let root = projection
                .entity_for_output(output)
                .and_then(|entity| projection.expr(entity.root()))
                .expect("projected root");
            assert_eq!(
                root.ty(),
                &integer_type(expected_width, MachineSignedness::Unsigned)
            );
            assert_eq!(root.kind().children().len(), expected_inputs);
            for input_idx in 0..expected_inputs {
                assert_eq!(
                    exact_use(&projection, &artifact, op_index, input_idx),
                    whole_machine_use(
                        binding_for_value(
                            artifact
                                .graph()
                                .value(artifact.graph().inst(inst).unwrap().inputs[input_idx])
                                .unwrap()
                        )
                        .unwrap()
                    )
                );
            }
            assert_eq!(
                projection.write_disposition(inst),
                Some(&MachineWriteDisposition::Exact(
                    MachineWriteProjection::Full
                ))
            );
        }

        let divide = projection
            .entity_for_output(artifact.graph().inst(InstId(0)).unwrap().output.unwrap())
            .and_then(|entity| projection.expr(entity.root()))
            .expect("divide root");
        assert!(matches!(
            divide.kind(),
            MachineExprKind::UnsignedDivide {
                zero_divisor: MachineZeroDivisorBehavior::Undefined,
                ..
            }
        ));
        let negate = projection
            .entity_for_output(artifact.graph().inst(InstId(1)).unwrap().output.unwrap())
            .and_then(|entity| projection.expr(entity.root()))
            .expect("negate root");
        assert!(matches!(
            negate.kind(),
            MachineExprKind::Negate {
                mode: MachineArithmeticMode::Wrapping,
                ..
            }
        ));
        let piece = projection
            .entity_for_output(artifact.graph().inst(InstId(2)).unwrap().output.unwrap())
            .and_then(|entity| projection.expr(entity.root()))
            .expect("piece root");
        assert!(matches!(piece.kind(), MachineExprKind::Concat { .. }));
        projection
            .validate_against(&artifact)
            .expect("new vocabulary remains source-bound");
    }

    #[test]
    fn divide_negate_and_piece_reject_wrong_arity_and_width() {
        let artifact = artifact_with_ops([
            R2ILOp::IntDiv {
                dst: Varnode::unique(0x10, 8),
                a: Varnode::register(0, 8),
                b: Varnode::register(8, 8),
            },
            R2ILOp::IntNegate {
                dst: Varnode::unique(0x18, 8),
                src: Varnode::register(16, 8),
            },
            R2ILOp::Piece {
                dst: Varnode::unique(0x20, 8),
                hi: Varnode::register(24, 4),
                lo: Varnode::register(28, 4),
            },
        ]);
        for (op_index, expected_arity) in [(0, 2_usize), (1, 1), (2, 2)] {
            let inst = artifact
                .graph()
                .inst_id_for_op_site(0x1000, op_index)
                .and_then(|inst| artifact.graph().inst(inst))
                .expect("test instruction");
            let InstPayload::Op(op) = &inst.payload else {
                unreachable!();
            };
            let output = binding_for_value(
                artifact
                    .graph()
                    .value(inst.output.expect("test output"))
                    .expect("test output value"),
            )
            .expect("test output binding");

            let mut wrong_arity = inst.clone();
            wrong_arity.inputs.pop();
            assert_eq!(
                MachineBuilder::for_graph(artifact.graph()).lower_op(
                    &artifact,
                    &wrong_arity,
                    op,
                    output,
                ),
                Err(MachineBuildError::WrongOperandCount {
                    inst: inst.id,
                    expected: expected_arity,
                    actual: expected_arity - 1,
                })
            );

            let wrong_width = MachineValueBinding {
                width_bits: 32,
                ..output
            };
            assert!(matches!(
                MachineBuilder::for_graph(artifact.graph()).lower_op(
                    &artifact,
                    inst,
                    op,
                    wrong_width,
                ),
                Err(MachineBuildError::WidthMismatch {
                    inst: actual,
                    expected_bits: 32,
                    actual_bits: 64,
                }) if actual == inst.id
            ));
        }
    }

    #[test]
    fn unsigned_remainder_has_exact_machine_vocabulary() {
        let artifact = artifact_with_ops([R2ILOp::IntRem {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::unique(0x100, 8),
            b: Varnode::constant(0, 8),
        }]);
        let projection = MachineProjection::from_artifact(&artifact).expect("exact remainder");
        assert!(projection.failures().is_empty());

        let inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .expect("remainder instruction");
        let graph_inst = artifact.graph().inst(inst).expect("remainder graph node");
        let entity = projection
            .entity_for_output(graph_inst.output.expect("remainder output"))
            .expect("remainder entity");
        let root = projection.expr(entity.root()).expect("remainder root");
        assert_eq!(root.ty(), &integer_type(64, MachineSignedness::Unsigned));
        let MachineExprKind::UnsignedRemainder {
            zero_divisor,
            dividend,
            divisor,
        } = root.kind()
        else {
            panic!("unsigned remainder root expected");
        };
        assert_eq!(*zero_divisor, MachineZeroDivisorBehavior::Undefined);
        assert_eq!(
            operand_leaf_binding(projection.arena(), *dividend).map(|binding| binding.value()),
            Some(graph_inst.inputs[0])
        );
        assert_eq!(
            operand_leaf_binding(projection.arena(), *divisor).map(|binding| binding.value()),
            Some(graph_inst.inputs[1])
        );
        for input_idx in 0..2 {
            assert_eq!(
                exact_use(&projection, &artifact, 0, input_idx),
                whole_machine_use(
                    binding_for_value(
                        artifact
                            .graph()
                            .value(graph_inst.inputs[input_idx])
                            .expect("remainder input"),
                    )
                    .expect("remainder input binding"),
                )
            );
        }
        assert_eq!(
            projection.write_disposition(inst),
            Some(&MachineWriteDisposition::Exact(
                MachineWriteProjection::Full
            ))
        );
        projection
            .validate_against(&artifact)
            .expect("remainder remains source-bound");
    }

    #[test]
    fn unsigned_remainder_rejects_wrong_arity_and_width() {
        let artifact = artifact_with_ops([R2ILOp::IntRem {
            dst: Varnode::unique(0x10, 8),
            a: Varnode::register(0, 8),
            b: Varnode::register(8, 8),
        }]);
        let inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .and_then(|inst| artifact.graph().inst(inst))
            .expect("remainder instruction");
        let InstPayload::Op(op) = &inst.payload else {
            unreachable!();
        };
        let output = binding_for_value(
            artifact
                .graph()
                .value(inst.output.expect("remainder output"))
                .expect("remainder output value"),
        )
        .expect("remainder output binding");

        let mut wrong_arity = inst.clone();
        wrong_arity.inputs.pop();
        assert_eq!(
            MachineBuilder::for_graph(artifact.graph()).lower_op(
                &artifact,
                &wrong_arity,
                op,
                output,
            ),
            Err(MachineBuildError::WrongOperandCount {
                inst: inst.id,
                expected: 2,
                actual: 1,
            })
        );

        let wrong_width = MachineValueBinding {
            width_bits: 32,
            ..output
        };
        assert!(matches!(
            MachineBuilder::for_graph(artifact.graph()).lower_op(
                &artifact,
                inst,
                op,
                wrong_width,
            ),
            Err(MachineBuildError::WidthMismatch {
                inst: actual,
                expected_bits: 32,
                actual_bits: 64,
            }) if actual == inst.id
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
        let load_inst = artifact
            .graph()
            .inst_id_for_op_site(0x1800, 0)
            .expect("load instruction");
        let address_use = UseSite {
            inst: load_inst,
            input_idx: 0,
        };
        let projected = MachineValueUse::memory_address_for_use(&artifact, address_use)
            .expect("certified memory-address use")
            .expect("load input zero is the address use");
        assert_eq!(
            projected.binding().value(),
            artifact
                .graph()
                .inst(load_inst)
                .expect("load graph instruction")
                .inputs[0]
        );
        assert_eq!(projected.memory_access(), Some(*access));
        assert!(matches!(
            projected.ty(),
            MachineType::Address {
                width_bits: 64,
                space: MachineAddressSpace::Ram,
                ..
            }
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
    fn memory_access_authority_rejects_each_exact_space_mismatch() {
        let artifact = artifact_with_ops([R2ILOp::Load {
            dst: Varnode::unique(0x10, 4),
            space: SpaceId::Ram,
            addr: Varnode::constant(0x4000, 8),
        }]);
        let fact = artifact
            .facts()
            .structured
            .memory_accesses
            .values()
            .next()
            .expect("load fact")
            .clone();
        let op = match &artifact
            .graph()
            .inst(fact.id.inst)
            .expect("load instruction")
            .payload
        {
            InstPayload::Op(op) => op.clone(),
            other => panic!("expected load operation, got {other:?}"),
        };
        assert!(memory_access_authorities_match(
            artifact.graph(),
            artifact.objects(),
            &op,
            &op,
            SpaceId::Ram,
            &fact,
        ));

        let mut mismatched_op = op.clone();
        let SSAOp::Load { space, .. } = &mut mismatched_op else {
            unreachable!();
        };
        *space = SpaceId::Custom(7);
        assert!(!memory_access_authorities_match(
            artifact.graph(),
            artifact.objects(),
            &mismatched_op,
            &op,
            SpaceId::Ram,
            &fact,
        ));
        assert!(!memory_access_authorities_match(
            artifact.graph(),
            artifact.objects(),
            &op,
            &mismatched_op,
            SpaceId::Ram,
            &fact,
        ));
        assert!(!memory_access_authorities_match(
            artifact.graph(),
            artifact.objects(),
            &op,
            &op,
            SpaceId::Custom(7),
            &fact,
        ));

        let mut mismatched_fact = fact.clone();
        mismatched_fact.space = SpaceId::Custom(7);
        assert!(!memory_access_authorities_match(
            artifact.graph(),
            artifact.objects(),
            &op,
            &op,
            SpaceId::Ram,
            &mismatched_fact,
        ));

        let mut mismatched_objects = artifact.objects().clone();
        mismatched_objects
            .objects
            .get_mut(&fact.object)
            .expect("load object")
            .kind = ObjectKind::EscapedUnknown {
            space: SpaceId::Custom(7),
        };
        assert!(!memory_access_authorities_match(
            artifact.graph(),
            &mismatched_objects,
            &op,
            &op,
            SpaceId::Ram,
            &fact,
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
        let failed_inst = artifact
            .graph()
            .def_inst(projection.failures()[0].output())
            .expect("failed producer instruction");
        assert_eq!(
            projection.write_disposition(failed_inst),
            Some(&MachineWriteDisposition::Refused(
                MachineWriteRefusal::UnsupportedOperation
            ))
        );
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

    fn exact_use(
        projection: &MachineProjection,
        artifact: &SsaArtifact,
        op_index: usize,
        input_idx: usize,
    ) -> MachineUseSlice {
        let inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, op_index)
            .expect("operation instruction");
        match projection
            .use_disposition(UseSite { inst, input_idx })
            .copied()
            .expect("dense use disposition")
        {
            MachineUseDisposition::Exact(slice) => slice,
            MachineUseDisposition::Refused(reason) => {
                panic!("expected exact use projection, got {reason:?}")
            }
        }
    }

    fn exact_write(
        projection: &MachineProjection,
        artifact: &SsaArtifact,
        op_index: usize,
    ) -> MachineWriteProjection {
        let inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, op_index)
            .expect("operation instruction");
        match projection
            .write_disposition(inst)
            .copied()
            .expect("dense write disposition")
        {
            MachineWriteDisposition::Exact(write) => write,
            MachineWriteDisposition::Refused(reason) => {
                panic!("expected exact write projection, got {reason:?}")
            }
        }
    }

    #[test]
    fn outputless_constant_operand_has_exact_use_and_canonical_arena_leaf() {
        let artifact = artifact_with_ops([R2ILOp::Return {
            target: Varnode::constant(0xfeed, 8),
        }]);
        let inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .expect("return instruction");
        let graph_inst = artifact
            .graph()
            .inst(inst)
            .expect("return graph instruction");
        assert_eq!(graph_inst.output, None);
        let [constant_value] = graph_inst.inputs.as_slice() else {
            panic!("return must retain its single constant operand");
        };
        let site = UseSite { inst, input_idx: 0 };

        let projection = MachineProjection::from_artifact(&artifact).expect("machine projection");
        assert_eq!(
            projection.use_disposition(site),
            Some(&MachineUseDisposition::Exact(MachineUseSlice {
                bit_offset: 0,
                width_bits: 64,
                carrier_width_bits: 64,
                conversion: None,
            }))
        );
        assert_eq!(projection.arena().len(), 1);
        let (_, expression) = projection
            .arena()
            .iter()
            .next()
            .expect("constant arena leaf");
        let MachineExprKind::Constant { binding, value } = expression.kind() else {
            panic!("outputless literal must be a canonical constant node");
        };
        assert_eq!(binding.value(), *constant_value);
        assert_eq!(binding.width_bits(), 64);
        assert_eq!(value.width_bits(), 64);
        assert_eq!(value.bits(), 0xfeed);

        let mut missing_leaf = projection.clone();
        missing_leaf.machine.arena.nodes = Vec::new().into_boxed_slice();
        assert_eq!(
            missing_leaf.validate_against(&artifact),
            Err(MachineBuildError::UseDispositionMismatch(site))
        );
    }

    #[test]
    fn dense_write_projections_cover_full_insert_high_slice_and_zero_extension() {
        let arch = register_geometry_arch();
        let full = artifact_with_arch(
            [R2ILOp::Copy {
                dst: Varnode::register(0, 8),
                src: Varnode::constant(7, 8),
            }],
            &arch,
        );
        let full_projection = MachineProjection::from_artifact(&full).expect("full projection");
        assert_eq!(
            exact_write(&full_projection, &full, 0),
            MachineWriteProjection::Full
        );

        let low = artifact_with_arch(
            [R2ILOp::Copy {
                dst: Varnode::register(0, 4),
                src: Varnode::constant(7, 4),
            }],
            &arch,
        );
        let low_projection = MachineProjection::from_artifact(&low).expect("low projection");
        assert_eq!(
            exact_write(&low_projection, &low, 0),
            MachineWriteProjection::Insert {
                bit_offset: 0,
                width_bits: 32,
                carrier_width_bits: 64,
            }
        );

        let high = artifact_with_arch(
            [R2ILOp::Copy {
                dst: Varnode::register(1, 1),
                src: Varnode::constant(7, 1),
            }],
            &arch,
        );
        let high_projection = MachineProjection::from_artifact(&high).expect("high projection");
        assert_eq!(
            exact_write(&high_projection, &high, 0),
            MachineWriteProjection::Insert {
                bit_offset: 8,
                width_bits: 8,
                carrier_width_bits: 64,
            }
        );

        let zero_extend = artifact_with_arch(
            [R2ILOp::IntZExt {
                dst: Varnode::register(0, 8),
                src: Varnode::register(0, 4),
            }],
            &arch,
        );
        let zero_projection =
            MachineProjection::from_artifact(&zero_extend).expect("zero-extension projection");
        assert_eq!(
            exact_write(&zero_projection, &zero_extend, 0),
            MachineWriteProjection::ZeroExtend {
                from_width_bits: 32,
                to_width_bits: 64,
            }
        );
        assert_eq!(
            zero_projection.write_dispositions().len(),
            zero_extend.graph().insts.len()
        );

        let external_zero_extend = artifact_with_arch(
            [R2ILOp::IntZExt {
                dst: Varnode::register(0, 8),
                src: Varnode::unique(0x80, 4),
            }],
            &arch,
        );
        let external_projection = MachineProjection::from_artifact(&external_zero_extend)
            .expect("external zero-extension projection");
        assert_eq!(
            exact_write(&external_projection, &external_zero_extend, 0),
            MachineWriteProjection::ZeroExtend {
                from_width_bits: 32,
                to_width_bits: 64,
            }
        );
    }

    #[test]
    fn register_use_slices_are_relative_to_the_canonical_carrier() {
        let arch = register_geometry_arch();
        let artifact = artifact_with_arch(
            [
                R2ILOp::Copy {
                    dst: Varnode::unique(0x10, 4),
                    src: Varnode::register(0, 4),
                },
                R2ILOp::Copy {
                    dst: Varnode::unique(0x20, 1),
                    src: Varnode::register(1, 1),
                },
            ],
            &arch,
        );
        let projection = MachineProjection::from_artifact(&artifact).expect("use projection");

        assert_eq!(
            exact_use(&projection, &artifact, 0, 0),
            MachineUseSlice {
                bit_offset: 0,
                width_bits: 32,
                carrier_width_bits: 64,
                conversion: None,
            }
        );
        assert_eq!(
            exact_use(&projection, &artifact, 1, 0),
            MachineUseSlice {
                bit_offset: 8,
                width_bits: 8,
                carrier_width_bits: 64,
                conversion: None,
            }
        );
        projection
            .validate_against(&artifact)
            .expect("carrier-relative uses remain source-bound");

        let mut corrupted = projection;
        let high_inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 1)
            .expect("high-byte copy instruction");
        let MachineUseDisposition::Exact(high_slice) =
            &mut corrupted.use_dispositions[high_inst.0 as usize][0]
        else {
            panic!("high-byte use must be exact");
        };
        high_slice.bit_offset = 0;
        assert_eq!(
            corrupted.validate_against(&artifact),
            Err(MachineBuildError::UseDispositionMismatch(UseSite {
                inst: high_inst,
                input_idx: 0,
            }))
        );

        let mut corrupted =
            MachineProjection::from_artifact(&artifact).expect("valid carrier-relative projection");
        let MachineUseDisposition::Exact(high_slice) =
            &mut corrupted.use_dispositions[high_inst.0 as usize][0]
        else {
            panic!("high-byte use must be exact");
        };
        high_slice.carrier_width_bits = 16;
        assert_eq!(
            corrupted.validate_against(&artifact),
            Err(MachineBuildError::UseDispositionMismatch(UseSite {
                inst: high_inst,
                input_idx: 0,
            }))
        );
    }

    #[test]
    fn big_endian_register_use_slice_keeps_upstream_byte_significance() {
        let arch = big_endian_register_geometry_arch();
        let artifact = artifact_with_arch(
            [R2ILOp::Copy {
                dst: Varnode::unique(0x10, 1),
                src: Varnode::register(6, 1),
            }],
            &arch,
        );
        let projection = MachineProjection::from_artifact(&artifact).expect("use projection");

        assert_eq!(
            exact_use(&projection, &artifact, 0, 0),
            MachineUseSlice {
                bit_offset: 8,
                width_bits: 8,
                carrier_width_bits: 64,
                conversion: None,
            }
        );
        projection
            .validate_against(&artifact)
            .expect("big-endian carrier-relative use remains source-bound");
    }

    #[test]
    fn register_use_slices_compose_nested_offsets_and_refuse_overflow() {
        let operation_relative = MachineUseSlice {
            bit_offset: 4,
            width_bits: 4,
            carrier_width_bits: 8,
            conversion: None,
        };
        assert_eq!(
            compose_machine_use_slice(operation_relative, 8, 64),
            Ok(MachineUseSlice {
                bit_offset: 12,
                width_bits: 4,
                carrier_width_bits: 64,
                conversion: None,
            })
        );
        assert_eq!(
            compose_machine_use_slice(operation_relative, u32::MAX, u32::MAX),
            Err(MachineUseRefusal::InvalidBitRange)
        );
    }

    #[test]
    fn register_use_projection_refuses_unavailable_and_invalid_geometry() {
        let read = |arch: &ArchSpec, source: Varnode| {
            let artifact = artifact_with_arch(
                [R2ILOp::Copy {
                    dst: Varnode::unique(0x10, source.size),
                    src: source,
                }],
                arch,
            );
            let projection = MachineProjection::from_artifact(&artifact).expect("typed refusal");
            let inst = artifact
                .graph()
                .inst_id_for_op_site(0x1000, 0)
                .expect("copy instruction");
            projection
                .use_disposition(UseSite { inst, input_idx: 0 })
                .copied()
                .expect("dense use disposition")
        };

        let mut missing = register_geometry_arch();
        missing.register_projections.clear();
        assert_eq!(
            read(&missing, Varnode::register(1, 1)),
            MachineUseDisposition::Refused(MachineUseRefusal::MissingRegisterGeometry)
        );

        let mut refused = register_geometry_arch();
        for projection in &mut refused.register_projections {
            projection.disposition = RegisterProjectionDisposition::Refused {
                reason: RegisterProjectionRefusal::MissingRegisterEndianness,
            };
        }
        assert_eq!(
            read(&refused, Varnode::register(1, 1)),
            MachineUseDisposition::Refused(MachineUseRefusal::RegisterGeometry(
                RegisterProjectionRefusal::MissingRegisterEndianness
            ))
        );

        let mut malformed = refused;
        malformed.register_projections[0].disposition = RegisterProjectionDisposition::Bound {
            carrier: RegisterStorage { offset: 0, size: 8 },
            slice: RegisterBitSlice {
                lsb_bit_offset: 0,
                size_bits: 32,
            },
        };
        assert_eq!(
            read(&malformed, Varnode::register(1, 1)),
            MachineUseDisposition::Refused(MachineUseRefusal::MalformedRegisterGeometry)
        );

        let arch = register_geometry_arch();
        assert_eq!(
            read(&arch, Varnode::register(0x80, 1)),
            MachineUseDisposition::Refused(MachineUseRefusal::RegisterGeometry(
                RegisterProjectionRefusal::NoContainingCarrier
            ))
        );
    }

    #[test]
    fn write_projection_refuses_missing_and_upstream_refused_geometry() {
        let mut missing = register_geometry_arch();
        missing.register_projections.clear();
        let missing_artifact = artifact_with_arch(
            [R2ILOp::Copy {
                dst: Varnode::register(0, 4),
                src: Varnode::constant(1, 4),
            }],
            &missing,
        );
        let missing_projection =
            MachineProjection::from_artifact(&missing_artifact).expect("typed refusal");
        let missing_inst = missing_artifact
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .expect("copy instruction");
        assert_eq!(
            missing_projection.write_disposition(missing_inst),
            Some(&MachineWriteDisposition::Refused(
                MachineWriteRefusal::MissingRegisterGeometry
            ))
        );

        let mut refused = register_geometry_arch();
        for projection in &mut refused.register_projections {
            projection.disposition = RegisterProjectionDisposition::Refused {
                reason: RegisterProjectionRefusal::MissingRegisterEndianness,
            };
        }
        let refused_artifact = artifact_with_arch(
            [R2ILOp::Copy {
                dst: Varnode::register(0, 4),
                src: Varnode::constant(1, 4),
            }],
            &refused,
        );
        let refused_projection =
            MachineProjection::from_artifact(&refused_artifact).expect("upstream refusal");
        let refused_inst = refused_artifact
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .expect("copy instruction");
        assert_eq!(
            refused_projection.write_disposition(refused_inst),
            Some(&MachineWriteDisposition::Refused(
                MachineWriteRefusal::RegisterGeometry(
                    RegisterProjectionRefusal::MissingRegisterEndianness
                )
            ))
        );

        let mut malformed = refused;
        malformed.register_projections[0].disposition = RegisterProjectionDisposition::Bound {
            carrier: RegisterStorage { offset: 0, size: 8 },
            slice: RegisterBitSlice {
                lsb_bit_offset: 0,
                size_bits: 32,
            },
        };
        let malformed_artifact = artifact_with_arch(
            [R2ILOp::Copy {
                dst: Varnode::register(0, 4),
                src: Varnode::constant(1, 4),
            }],
            &malformed,
        );
        let malformed_projection =
            MachineProjection::from_artifact(&malformed_artifact).expect("malformed refusal");
        let malformed_inst = malformed_artifact
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .expect("copy instruction");
        assert_eq!(
            malformed_projection.write_disposition(malformed_inst),
            Some(&MachineWriteDisposition::Refused(
                MachineWriteRefusal::MalformedRegisterGeometry
            ))
        );
        assert_ne!(
            missing_artifact.machine_context().semantic_identity_bytes(),
            malformed_artifact
                .machine_context()
                .semantic_identity_bytes()
        );
    }

    #[test]
    fn write_projection_uses_source_certified_unnamed_vector_lanes() {
        let q0 = RegisterStorage {
            offset: 0x5000,
            size: 16,
        };
        let s0 = RegisterStorage {
            offset: 0x5000,
            size: 4,
        };
        let q4 = RegisterStorage {
            offset: 0x5040,
            size: 16,
        };
        let b4 = RegisterStorage {
            offset: 0x5040,
            size: 1,
        };
        let mut arch = ArchSpec::new("aarch64-vector-lanes");
        for (name, storage) in [("q0", q0), ("s0", s0), ("q4", q4), ("b4", b4)] {
            arch.add_register(RegisterDef::new(name, storage.offset, storage.size));
        }
        arch.register_projections = vec![
            RegisterProjection {
                written: s0,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: q0,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 32,
                    },
                },
            },
            RegisterProjection {
                written: q0,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: q0,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 128,
                    },
                },
            },
            RegisterProjection {
                written: b4,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: q4,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 8,
                    },
                },
            },
            RegisterProjection {
                written: q4,
                disposition: RegisterProjectionDisposition::Bound {
                    carrier: q4,
                    slice: RegisterBitSlice {
                        lsb_bit_offset: 0,
                        size_bits: 128,
                    },
                },
            },
        ];
        let artifact = artifact_with_arch(
            [
                R2ILOp::IntAdd {
                    dst: Varnode::register(0x5004, 4),
                    a: Varnode::unique(0x10, 4),
                    b: Varnode::unique(0x14, 4),
                },
                R2ILOp::IntAnd {
                    dst: Varnode::register(0x5041, 1),
                    a: Varnode::unique(0x18, 1),
                    b: Varnode::unique(0x19, 1),
                },
            ],
            &arch,
        );
        let projection = MachineProjection::from_artifact(&artifact).expect("machine projection");
        let word_inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .expect("word-lane instruction");
        let byte_inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 1)
            .expect("byte-lane instruction");
        assert_eq!(
            projection.write_disposition(word_inst),
            Some(&MachineWriteDisposition::Exact(
                MachineWriteProjection::Insert {
                    bit_offset: 32,
                    width_bits: 32,
                    carrier_width_bits: 128,
                }
            ))
        );
        assert_eq!(
            projection.write_disposition(byte_inst),
            Some(&MachineWriteDisposition::Exact(
                MachineWriteProjection::Insert {
                    bit_offset: 8,
                    width_bits: 8,
                    carrier_width_bits: 128,
                }
            ))
        );
    }

    #[test]
    fn corrupted_write_disposition_is_rejected() {
        let arch = register_geometry_arch();
        let artifact = artifact_with_arch(
            [R2ILOp::Copy {
                dst: Varnode::register(0, 8),
                src: Varnode::constant(7, 8),
            }],
            &arch,
        );
        let mut projection = MachineProjection::from_artifact(&artifact).expect("projection");
        let inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .expect("copy instruction");
        projection.write_dispositions[inst.0 as usize] = Some(MachineWriteDisposition::Exact(
            MachineWriteProjection::Insert {
                bit_offset: 0,
                width_bits: 32,
                carrier_width_bits: 64,
            },
        ));
        assert_eq!(
            projection.validate_against(&artifact),
            Err(MachineBuildError::WriteDispositionMismatch(inst))
        );

        let artifact = artifact_with_arch(
            [R2ILOp::Copy {
                dst: Varnode::register(1, 1),
                src: Varnode::constant(7, 1),
            }],
            &arch,
        );
        let mut projection = MachineProjection::from_artifact(&artifact).expect("projection");
        let inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .expect("copy instruction");
        projection.write_dispositions[inst.0 as usize] = Some(MachineWriteDisposition::Exact(
            MachineWriteProjection::Insert {
                bit_offset: 8,
                width_bits: 8,
                carrier_width_bits: 16,
            },
        ));
        assert_eq!(
            projection.validate_against(&artifact),
            Err(MachineBuildError::WriteDispositionMismatch(inst))
        );
    }

    #[test]
    fn dense_use_slices_cover_whole_subpiece_narrow_bitwise_casts_and_effects() {
        let remainder = Varnode::unique(0x60, 8);
        let artifact = artifact_with_ops([
            R2ILOp::Copy {
                dst: Varnode::unique(0x10, 8),
                src: Varnode::unique(0x100, 8),
            },
            R2ILOp::Subpiece {
                dst: Varnode::unique(0x18, 4),
                src: Varnode::unique(0x108, 8),
                offset: 4,
            },
            R2ILOp::IntAnd {
                dst: Varnode::unique(0x20, 4),
                a: Varnode::unique(0x110, 8),
                b: Varnode::constant(0xff, 8),
            },
            R2ILOp::IntZExt {
                dst: Varnode::unique(0x28, 8),
                src: Varnode::unique(0x118, 1),
            },
            R2ILOp::IntSExt {
                dst: Varnode::unique(0x30, 8),
                src: Varnode::unique(0x119, 1),
            },
            R2ILOp::Trunc {
                dst: Varnode::unique(0x38, 4),
                src: Varnode::unique(0x120, 8),
            },
            R2ILOp::Cast {
                dst: Varnode::unique(0x40, 4),
                src: Varnode::unique(0x128, 4),
            },
            R2ILOp::Store {
                space: SpaceId::Ram,
                addr: Varnode::unique(0x130, 8),
                val: Varnode::unique(0x138, 4),
            },
            R2ILOp::IntRem {
                dst: remainder.clone(),
                a: Varnode::unique(0x140, 8),
                b: Varnode::constant(3, 8),
            },
            R2ILOp::Copy {
                dst: Varnode::unique(0x68, 8),
                src: remainder,
            },
            R2ILOp::Return {
                target: Varnode::unique(0x148, 8),
            },
        ]);
        let projection = MachineProjection::from_artifact(&artifact).expect("use projection");

        assert_eq!(
            projection.use_dispositions().len(),
            artifact.graph().insts.len()
        );
        for inst in &artifact.graph().insts {
            assert_eq!(
                projection.use_dispositions()[inst.id.0 as usize].len(),
                inst.inputs.len()
            );
        }

        assert_eq!(
            exact_use(&projection, &artifact, 0, 0),
            MachineUseSlice {
                bit_offset: 0,
                width_bits: 64,
                carrier_width_bits: 64,
                conversion: None,
            }
        );
        assert_eq!(
            exact_use(&projection, &artifact, 1, 0),
            MachineUseSlice {
                bit_offset: 32,
                width_bits: 32,
                carrier_width_bits: 64,
                conversion: None,
            }
        );
        for input_idx in 0..2 {
            assert_eq!(
                exact_use(&projection, &artifact, 2, input_idx),
                MachineUseSlice {
                    bit_offset: 0,
                    width_bits: 32,
                    carrier_width_bits: 64,
                    conversion: None,
                }
            );
        }
        for (op_index, kind, source_bits, target_bits) in [
            (3, MachineCastKind::ZeroExtend, 8, 64),
            (4, MachineCastKind::SignExtend, 8, 64),
            (5, MachineCastKind::Truncate, 64, 32),
            (6, MachineCastKind::BitReinterpret, 32, 32),
        ] {
            assert_eq!(
                exact_use(&projection, &artifact, op_index, 0),
                MachineUseSlice {
                    bit_offset: 0,
                    width_bits: source_bits,
                    carrier_width_bits: source_bits,
                    conversion: Some(MachineUseConversion {
                        kind,
                        to_width_bits: target_bits,
                    }),
                }
            );
        }
        assert_eq!(exact_use(&projection, &artifact, 7, 0).width_bits(), 64);
        assert_eq!(exact_use(&projection, &artifact, 7, 1).width_bits(), 32);

        let remainder_inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 8)
            .expect("remainder instruction");
        for input_idx in 0..2 {
            assert_eq!(
                exact_use(&projection, &artifact, 8, input_idx),
                whole_machine_use(
                    binding_for_value(
                        artifact
                            .graph()
                            .value(artifact.graph().inst(remainder_inst).unwrap().inputs[input_idx])
                            .unwrap()
                    )
                    .unwrap()
                )
            );
        }
        assert_eq!(
            projection.write_disposition(remainder_inst),
            Some(&MachineWriteDisposition::Exact(
                MachineWriteProjection::Full
            ))
        );
        assert_eq!(exact_use(&projection, &artifact, 9, 0).width_bits(), 64);
        assert_eq!(exact_use(&projection, &artifact, 10, 0).width_bits(), 64);
        projection
            .validate_against(&artifact)
            .expect("all dense uses remain source-bound");
    }

    #[test]
    fn incoherent_slice_is_a_refusal_and_corrupted_exact_facts_are_rejected() {
        let incoherent = artifact_with_ops([R2ILOp::Subpiece {
            dst: Varnode::unique(0x10, 4),
            src: Varnode::register(0, 4),
            offset: 2,
        }]);
        let projection = MachineProjection::from_artifact(&incoherent)
            .expect("local incoherence remains a partial projection");
        let inst = incoherent
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .expect("subpiece instruction");
        assert_eq!(
            projection.use_disposition(UseSite { inst, input_idx: 0 }),
            Some(&MachineUseDisposition::Refused(
                MachineUseRefusal::IncoherentOperation
            ))
        );

        let artifact = artifact_with_ops([
            R2ILOp::Copy {
                dst: Varnode::unique(0x20, 8),
                src: Varnode::unique(0x100, 8),
            },
            R2ILOp::IntZExt {
                dst: Varnode::unique(0x28, 8),
                src: Varnode::unique(0x108, 1),
            },
        ]);
        let mut projection =
            MachineProjection::from_artifact(&artifact).expect("valid exact projection");
        let copy_inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 0)
            .expect("copy instruction");
        let MachineUseDisposition::Exact(copy) =
            &mut projection.use_dispositions[copy_inst.0 as usize][0]
        else {
            panic!("exact copy use expected");
        };
        copy.width_bits = 56;
        assert_eq!(
            projection.validate_against(&artifact),
            Err(MachineBuildError::UseDispositionMismatch(UseSite {
                inst: copy_inst,
                input_idx: 0,
            }))
        );

        let mut projection =
            MachineProjection::from_artifact(&artifact).expect("valid exact projection");
        let cast_inst = artifact
            .graph()
            .inst_id_for_op_site(0x1000, 1)
            .expect("cast instruction");
        let MachineUseDisposition::Exact(cast) =
            &mut projection.use_dispositions[cast_inst.0 as usize][0]
        else {
            panic!("exact cast use expected");
        };
        cast.conversion = Some(MachineUseConversion {
            kind: MachineCastKind::SignExtend,
            to_width_bits: 64,
        });
        assert_eq!(
            projection.validate_against(&artifact),
            Err(MachineBuildError::UseDispositionMismatch(UseSite {
                inst: cast_inst,
                input_idx: 0,
            }))
        );

        let mut projection =
            MachineProjection::from_artifact(&artifact).expect("valid exact projection");
        projection.use_dispositions[copy_inst.0 as usize] = Box::new([]);
        assert_eq!(
            projection.validate_against(&artifact),
            Err(MachineBuildError::TopologyMismatch)
        );
    }
}
