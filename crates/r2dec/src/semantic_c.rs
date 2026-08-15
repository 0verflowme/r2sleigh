//! Machine-semantic C representation.
//!
//! This is deliberately separate from the legacy presentation AST. It lowers
//! only expression roots already bound by `r2cert` to the immutable machine
//! arena. Stable SSA values and canonical instruction IDs provide provenance;
//! names and rendered positions are never consulted as evidence.

use r2cert::{
    CERTIFICATION_SCHEMA_VERSION, CertifiedAbiParameter, CertifiedCallArgument,
    CertifiedCallArgumentOrigin, CertifiedDirectCall, CertifiedExpr, CertifiedFramePreservation,
    CertifiedMachineFunction, CertifiedMachineProjection, CertifiedMemoryStatement,
    CertifiedMemoryStatementKind, CertifiedNormalizedStackRange,
    CertifiedPrivateFrameConditionalJoin, CertifiedReturnControl,
    CertifiedReturnRegisterDefinition, CertifiedReturnRegisterOverlay, CertifiedSourceTerminator,
    CertifiedSourceTopology, CertifiedStackDiscipline, CertifiedStackSlot, EffectDisposition,
    ObligationLedger,
};
use r2ssa::{
    CallBoundarySlot, CallSiteId, CanonicalInstructionId, CanonicalStorageId,
    MachineAddressProvenance, MachineArithmeticFlagOp, MachineArithmeticMode, MachineArithmeticOp,
    MachineBitVector, MachineBitwiseOp, MachineBooleanOp, MachineCastKind, MachineComparisonOp,
    MachineEntity, MachineExpr, MachineExprId, MachineExprKind, MachineMemoryEndianness,
    MachineOvershiftBehavior, MachineProjection, MachineShiftKind, MachineSignedness,
    MachineStackBase, MachineType, MachineValueBinding, ObjectId, SemanticObligationId,
    SemanticObligationInventory, SemanticObligationKind, SourceCallSiteIdentity, SourceCarrierKind,
    SourceCarrierProjection, SourceFunctionInterface, SourceFunctionReturn, SourceMachineContext,
    SourceTypeKind, StackAddressBase, StackAddressRoot, StructuredAccessId, ValueId,
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

pub const SEMANTIC_C_SCHEMA_VERSION: u32 = 15;

/// Closed renderer-owned helper vocabulary. Membership is derived only while
/// rendering audited typed semantics and never grants certification authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SemanticCHelper {
    Mask,
    BitInsert,
    I8FromBits,
    I16FromBits,
    I32FromBits,
    I64FromBits,
    WrapAdd,
    WrapSub,
    WrapMul,
    UnsignedCarry,
    SignedCarry,
    SignedBorrow,
    ShiftLeft,
    LogicalShiftRight,
    ArithmeticShiftRight,
    SignedKey,
    SignExtend,
}

impl SemanticCHelper {
    const ORDERED: [Self; 17] = [
        Self::Mask,
        Self::BitInsert,
        Self::I8FromBits,
        Self::I16FromBits,
        Self::I32FromBits,
        Self::I64FromBits,
        Self::WrapAdd,
        Self::WrapSub,
        Self::WrapMul,
        Self::UnsignedCarry,
        Self::SignedCarry,
        Self::SignedBorrow,
        Self::ShiftLeft,
        Self::LogicalShiftRight,
        Self::ArithmeticShiftRight,
        Self::SignedKey,
        Self::SignExtend,
    ];

    const fn depends_on_mask(self) -> bool {
        matches!(
            self,
            Self::BitInsert
                | Self::WrapAdd
                | Self::WrapSub
                | Self::WrapMul
                | Self::UnsignedCarry
                | Self::SignedCarry
                | Self::SignedBorrow
                | Self::ShiftLeft
                | Self::LogicalShiftRight
                | Self::ArithmeticShiftRight
                | Self::SignedKey
                | Self::SignExtend
        )
    }

    const fn definition(self) -> &'static str {
        match self {
            Self::Mask => SEMANTIC_C_MASK_HELPER,
            Self::BitInsert => SEMANTIC_C_BIT_INSERT_HELPER,
            Self::I8FromBits => SEMANTIC_C_I8_FROM_BITS_HELPER,
            Self::I16FromBits => SEMANTIC_C_I16_FROM_BITS_HELPER,
            Self::I32FromBits => SEMANTIC_C_I32_FROM_BITS_HELPER,
            Self::I64FromBits => SEMANTIC_C_I64_FROM_BITS_HELPER,
            Self::WrapAdd => SEMANTIC_C_WRAP_ADD_HELPER,
            Self::WrapSub => SEMANTIC_C_WRAP_SUB_HELPER,
            Self::WrapMul => SEMANTIC_C_WRAP_MUL_HELPER,
            Self::UnsignedCarry => SEMANTIC_C_UCARRY_HELPER,
            Self::SignedCarry => SEMANTIC_C_SCARRY_HELPER,
            Self::SignedBorrow => SEMANTIC_C_SBORROW_HELPER,
            Self::ShiftLeft => SEMANTIC_C_SHL_HELPER,
            Self::LogicalShiftRight => SEMANTIC_C_LSHR_HELPER,
            Self::ArithmeticShiftRight => SEMANTIC_C_ASHR_HELPER,
            Self::SignedKey => SEMANTIC_C_SIGNED_KEY_HELPER,
            Self::SignExtend => SEMANTIC_C_SEXT_HELPER,
        }
    }

    pub(crate) const fn call_name(self) -> &'static str {
        match self {
            Self::Mask => "r2s_mask",
            Self::BitInsert => "r2s_bit_insert",
            Self::I8FromBits => "r2s_i8_from_bits",
            Self::I16FromBits => "r2s_i16_from_bits",
            Self::I32FromBits => "r2s_i32_from_bits",
            Self::I64FromBits => "r2s_i64_from_bits",
            Self::WrapAdd => "r2s_wrap_add",
            Self::WrapSub => "r2s_wrap_sub",
            Self::WrapMul => "r2s_wrap_mul",
            Self::UnsignedCarry => "r2s_ucarry",
            Self::SignedCarry => "r2s_scarry",
            Self::SignedBorrow => "r2s_sborrow",
            Self::ShiftLeft => "r2s_shl",
            Self::LogicalShiftRight => "r2s_lshr",
            Self::ArithmeticShiftRight => "r2s_ashr",
            Self::SignedKey => "r2s_signed_key",
            Self::SignExtend => "r2s_sext",
        }
    }
}

/// Deterministic helper dependency inventory for one generated translation unit.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct SemanticCHelperSet(BTreeSet<SemanticCHelper>);

impl SemanticCHelperSet {
    pub(crate) fn insert(&mut self, helper: SemanticCHelper) {
        if helper.depends_on_mask() {
            self.0.insert(SemanticCHelper::Mask);
        }
        self.0.insert(helper);
    }

    fn definitions(&self) -> String {
        let mut output = String::new();
        for helper in SemanticCHelper::ORDERED {
            if self.0.contains(&helper) {
                output.push_str(helper.definition());
                output.push('\n');
            }
        }
        output
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCParameter {
    index: u32,
    storage: CanonicalStorageId,
    value: Option<MachineValueBinding>,
    ty: MachineType,
}

impl SemanticCParameter {
    pub const fn index(&self) -> u32 {
        self.index
    }

    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }

    pub const fn value(&self) -> Option<MachineValueBinding> {
        self.value
    }

    pub const fn ty(&self) -> &MachineType {
        &self.ty
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCStackSlot {
    base: StackAddressBase,
    offset: i64,
    size_bytes: u32,
    object: Option<ObjectId>,
}

impl SemanticCStackSlot {
    pub const fn base(&self) -> StackAddressBase {
        self.base
    }

    pub const fn offset(&self) -> i64 {
        self.offset
    }

    pub const fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub const fn object(&self) -> Option<ObjectId> {
        self.object
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum SemanticCFunctionReturn {
    Void,
    Register {
        storage: CanonicalStorageId,
        ty: MachineType,
    },
}

/// Exact source-logical view of one physical ABI return carrier.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCReturnProjection {
    source_type_id: u32,
    carrier: SourceCarrierProjection,
    physical_ty: MachineType,
    logical_ty: MachineType,
}

impl SemanticCReturnProjection {
    pub const fn source_type_id(&self) -> u32 {
        self.source_type_id
    }

    pub const fn carrier(&self) -> SourceCarrierProjection {
        self.carrier
    }

    pub const fn physical_ty(&self) -> &MachineType {
        &self.physical_ty
    }

    pub const fn logical_ty(&self) -> &MachineType {
        &self.logical_ty
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCFunctionInterface {
    revision_identity: Box<[u8]>,
    calling_convention: String,
    parameters: Box<[SemanticCParameter]>,
    return_kind: SemanticCFunctionReturn,
    return_projection: Option<SemanticCReturnProjection>,
    stack_slots: Box<[SemanticCStackSlot]>,
}

impl SemanticCFunctionInterface {
    pub const fn revision_identity(&self) -> &[u8] {
        &self.revision_identity
    }

    pub fn calling_convention(&self) -> &str {
        &self.calling_convention
    }

    pub const fn parameters(&self) -> &[SemanticCParameter] {
        &self.parameters
    }

    pub const fn return_kind(&self) -> &SemanticCFunctionReturn {
        &self.return_kind
    }

    pub const fn return_projection(&self) -> Option<&SemanticCReturnProjection> {
        self.return_projection.as_ref()
    }

    pub const fn stack_slots(&self) -> &[SemanticCStackSlot] {
        &self.stack_slots
    }
}

fn logical_scalar_type(logical_ty: &MachineType) -> Result<&'static str, SemanticCError> {
    match logical_ty {
        MachineType::Integer {
            width_bits: 8,
            signedness: MachineSignedness::Signed,
        } => Ok("int8_t"),
        MachineType::Integer {
            width_bits: 16,
            signedness: MachineSignedness::Signed,
        } => Ok("int16_t"),
        MachineType::Integer {
            width_bits: 32,
            signedness: MachineSignedness::Signed,
        } => Ok("int32_t"),
        MachineType::Integer {
            width_bits: 64,
            signedness: MachineSignedness::Signed,
        } => Ok("int64_t"),
        MachineType::Integer {
            width_bits: 8,
            signedness: MachineSignedness::Unsigned,
        } => Ok("uint8_t"),
        MachineType::Integer {
            width_bits: 16,
            signedness: MachineSignedness::Unsigned,
        } => Ok("uint16_t"),
        MachineType::Integer {
            width_bits: 32,
            signedness: MachineSignedness::Unsigned,
        } => Ok("uint32_t"),
        MachineType::Integer {
            width_bits: 64,
            signedness: MachineSignedness::Unsigned,
        } => Ok("uint64_t"),
        _ => Err(SemanticCError::InvalidReturnProjection),
    }
}

pub(crate) fn logical_return_type(
    interface: &SemanticCFunctionInterface,
) -> Result<&'static str, SemanticCError> {
    match (interface.return_kind(), interface.return_projection()) {
        (SemanticCFunctionReturn::Void, None) => Ok("void"),
        (SemanticCFunctionReturn::Register { ty, .. }, Some(projection))
            if projection.physical_ty() == ty =>
        {
            logical_scalar_type(projection.logical_ty())
        }
        _ => Err(SemanticCError::InvalidReturnProjection),
    }
}

fn render_logical_return_value(
    logical_ty: &MachineType,
    value: &str,
    helpers: &mut SemanticCHelperSet,
) -> Result<String, SemanticCError> {
    let width = logical_ty.width_bits();
    match logical_ty {
        MachineType::Integer {
            signedness: MachineSignedness::Unsigned,
            ..
        } if matches!(width, 8 | 16 | 32 | 64) => Ok(format!("(uint{width}_t)({value})")),
        MachineType::Integer {
            signedness: MachineSignedness::Signed,
            ..
        } if matches!(width, 8 | 16 | 32 | 64) => {
            let helper = signed_from_bits_helper(width)?;
            helpers.insert(helper);
            Ok(format!("{}((uint{width}_t)({value}))", helper.call_name()))
        }
        _ => Err(SemanticCError::InvalidReturnProjection),
    }
}

pub(crate) fn render_logical_return_statement(
    interface: &SemanticCFunctionInterface,
    value: Option<&str>,
    helpers: &mut SemanticCHelperSet,
) -> Result<String, SemanticCError> {
    match (
        interface.return_kind(),
        interface.return_projection(),
        value,
    ) {
        (SemanticCFunctionReturn::Void, None, None) => Ok("return;".to_string()),
        (SemanticCFunctionReturn::Register { ty, .. }, Some(projection), Some(value))
            if projection.physical_ty() == ty =>
        {
            Ok(format!(
                "return {};",
                render_logical_return_value(projection.logical_ty(), value, helpers)?
            ))
        }
        _ => Err(SemanticCError::InvalidReturnProjection),
    }
}

fn signed_from_bits_helper(width: u32) -> Result<SemanticCHelper, SemanticCError> {
    match width {
        8 => Ok(SemanticCHelper::I8FromBits),
        16 => Ok(SemanticCHelper::I16FromBits),
        32 => Ok(SemanticCHelper::I32FromBits),
        64 => Ok(SemanticCHelper::I64FromBits),
        _ => Err(SemanticCError::InvalidReturnProjection),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum SemanticCInputOrigin {
    AbiParameter {
        index: u32,
        storage: CanonicalStorageId,
    },
    StackSlot {
        base: StackAddressBase,
        offset: i64,
        size_bytes: u32,
        object: Option<ObjectId>,
    },
    CertifiedPrivateEntryStackPointer {
        storage: CanonicalStorageId,
        header: u64,
    },
    UnclassifiedSource,
}

/// Opaque handle into a semantic-C expression arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct SemanticCExprId(u32);

impl SemanticCExprId {
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// One typed semantic-C expression.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCExpr {
    ty: MachineType,
    source_instructions: BTreeSet<CanonicalInstructionId>,
    kind: SemanticCExprKind,
}

impl SemanticCExpr {
    pub const fn ty(&self) -> &MachineType {
        &self.ty
    }

    pub const fn source_instructions(&self) -> &BTreeSet<CanonicalInstructionId> {
        &self.source_instructions
    }

    pub const fn kind(&self) -> &SemanticCExprKind {
        &self.kind
    }
}

/// C-compatible operations with their machine policies kept explicit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum SemanticCExprKind {
    Input {
        binding: MachineValueBinding,
    },
    Constant {
        binding: MachineValueBinding,
        value: MachineBitVector,
    },
    MemoryRead {
        access: StructuredAccessId,
        object: ObjectId,
        space: r2ssa::MachineAddressSpace,
        endianness: MachineMemoryEndianness,
        word_size_bytes: u32,
        address: SemanticCExprId,
        width_bits: u32,
    },
    Copy {
        input: SemanticCExprId,
    },
    Arithmetic {
        op: MachineArithmeticOp,
        mode: MachineArithmeticMode,
        left: SemanticCExprId,
        right: SemanticCExprId,
    },
    ArithmeticFlag {
        op: MachineArithmeticFlagOp,
        left: SemanticCExprId,
        right: SemanticCExprId,
    },
    Bitwise {
        op: MachineBitwiseOp,
        left: SemanticCExprId,
        right: SemanticCExprId,
    },
    BitwiseNot {
        input: SemanticCExprId,
    },
    BooleanNot {
        input: SemanticCExprId,
    },
    Boolean {
        op: MachineBooleanOp,
        left: SemanticCExprId,
        right: SemanticCExprId,
    },
    Shift {
        kind: MachineShiftKind,
        overshift: MachineOvershiftBehavior,
        value: SemanticCExprId,
        count: SemanticCExprId,
    },
    Compare {
        op: MachineComparisonOp,
        interpretation: MachineSignedness,
        left: SemanticCExprId,
        right: SemanticCExprId,
    },
    Cast {
        kind: MachineCastKind,
        input: SemanticCExprId,
    },
    Extract {
        input: SemanticCExprId,
        lsb_bits: u32,
    },
    Select {
        condition: SemanticCExprId,
        if_true: SemanticCExprId,
        if_false: SemanticCExprId,
    },
}

/// One certified output assignment in source order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCEntity {
    output: MachineValueBinding,
    root: SemanticCExprId,
    producer: CanonicalInstructionId,
    source_obligations: BTreeSet<SemanticObligationId>,
}

impl SemanticCEntity {
    pub const fn output(&self) -> MachineValueBinding {
        self.output
    }

    pub const fn root(&self) -> SemanticCExprId {
        self.root
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn source_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.source_obligations
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum SemanticCCallArgumentValue {
    Expression(SemanticCExprId),
    Constant(MachineBitVector),
    AbiParameter {
        index: u32,
        input: MachineValueBinding,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCCallArgument {
    slot: CallBoundarySlot,
    binding: MachineValueBinding,
    value: SemanticCCallArgumentValue,
    ty: MachineType,
}

impl SemanticCCallArgument {
    pub const fn slot(&self) -> CallBoundarySlot {
        self.slot
    }

    pub const fn binding(&self) -> MachineValueBinding {
        self.binding
    }

    pub const fn value(&self) -> &SemanticCCallArgumentValue {
        &self.value
    }

    pub const fn expression(&self) -> Option<SemanticCExprId> {
        match self.value {
            SemanticCCallArgumentValue::Expression(expression) => Some(expression),
            SemanticCCallArgumentValue::Constant(_)
            | SemanticCCallArgumentValue::AbiParameter { .. } => None,
        }
    }

    pub const fn ty(&self) -> &MachineType {
        &self.ty
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCDirectCall {
    producer: CanonicalInstructionId,
    call_site: CallSiteId,
    raw_identity: SourceCallSiteIdentity,
    interface_revision: Box<[u8]>,
    target_binding: MachineValueBinding,
    target: u64,
    fallthrough: u64,
    calling_convention: String,
    arguments: Box<[SemanticCCallArgument]>,
    source_obligations: BTreeSet<SemanticObligationId>,
}

impl SemanticCDirectCall {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn call_site(&self) -> CallSiteId {
        self.call_site
    }

    pub const fn raw_identity(&self) -> SourceCallSiteIdentity {
        self.raw_identity
    }

    pub const fn interface_revision(&self) -> &[u8] {
        &self.interface_revision
    }

    pub const fn target_binding(&self) -> MachineValueBinding {
        self.target_binding
    }

    pub const fn target(&self) -> u64 {
        self.target
    }

    pub const fn fallthrough(&self) -> u64 {
        self.fallthrough
    }

    pub fn calling_convention(&self) -> &str {
        &self.calling_convention
    }

    pub const fn arguments(&self) -> &[SemanticCCallArgument] {
        &self.arguments
    }

    pub const fn source_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.source_obligations
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCReturnValue {
    slot: CallBoundarySlot,
    binding: MachineValueBinding,
    producer: CanonicalInstructionId,
    expression: SemanticCExprId,
}

impl SemanticCReturnValue {
    pub const fn slot(&self) -> CallBoundarySlot {
        self.slot
    }

    pub const fn binding(&self) -> MachineValueBinding {
        self.binding
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn expression(&self) -> SemanticCExprId {
        self.expression
    }
}

/// One exact, real SSA definition participating in a composed ABI return.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCReturnRegisterDefinition {
    storage: CanonicalStorageId,
    binding: MachineValueBinding,
    producer: CanonicalInstructionId,
    expression: SemanticCExprId,
}

impl SemanticCReturnRegisterDefinition {
    pub const fn storage(&self) -> CanonicalStorageId {
        self.storage
    }

    pub const fn binding(&self) -> MachineValueBinding {
        self.binding
    }

    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn expression(&self) -> SemanticCExprId {
        self.expression
    }
}

/// One ordered contained-slice write over a composed ABI return base.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCReturnRegisterOverlay {
    definition: SemanticCReturnRegisterDefinition,
    offset_bytes: u32,
}

impl SemanticCReturnRegisterOverlay {
    pub const fn definition(&self) -> &SemanticCReturnRegisterDefinition {
        &self.definition
    }

    pub const fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }
}

/// Exact output-less reconstruction of one full-width ABI return register.
///
/// Every component names a real SSA binding and expression entity. The
/// reconstructed value deliberately has no invented binding or entity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCReturnRegisterComposition {
    slot: CallBoundarySlot,
    base: SemanticCReturnRegisterDefinition,
    overlays: Box<[SemanticCReturnRegisterOverlay]>,
}

impl SemanticCReturnRegisterComposition {
    pub const fn slot(&self) -> CallBoundarySlot {
        self.slot
    }

    pub const fn base(&self) -> &SemanticCReturnRegisterDefinition {
        &self.base
    }

    pub const fn overlays(&self) -> &[SemanticCReturnRegisterOverlay] {
        &self.overlays
    }

    pub const fn physical_width_bits(&self) -> u32 {
        self.base.binding.width_bits()
    }

    pub fn source_producers(&self) -> impl Iterator<Item = CanonicalInstructionId> + '_ {
        std::iter::once(self.base.producer).chain(
            self.overlays
                .iter()
                .map(|overlay| overlay.definition.producer),
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticCReturnOperand<'a> {
    Direct(&'a SemanticCReturnValue),
    RegisterComposition(&'a SemanticCReturnRegisterComposition),
}

impl SemanticCReturnOperand<'_> {
    pub const fn slot(self) -> CallBoundarySlot {
        match self {
            Self::Direct(value) => value.slot(),
            Self::RegisterComposition(composition) => composition.slot(),
        }
    }

    pub const fn physical_width_bits(self) -> u32 {
        match self {
            Self::Direct(value) => value.binding().width_bits(),
            Self::RegisterComposition(composition) => composition.physical_width_bits(),
        }
    }

    pub fn source_producers(self) -> BTreeSet<CanonicalInstructionId> {
        match self {
            Self::Direct(value) => BTreeSet::from([value.producer()]),
            Self::RegisterComposition(composition) => composition.source_producers().collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCReturn {
    producer: CanonicalInstructionId,
    control_target: MachineValueBinding,
    values: Box<[SemanticCReturnValue]>,
    register_compositions: Box<[SemanticCReturnRegisterComposition]>,
    source_obligations: BTreeSet<SemanticObligationId>,
}

impl SemanticCReturn {
    pub const fn producer(&self) -> CanonicalInstructionId {
        self.producer
    }

    pub const fn control_target(&self) -> MachineValueBinding {
        self.control_target
    }

    pub const fn values(&self) -> &[SemanticCReturnValue] {
        &self.values
    }

    pub const fn register_compositions(&self) -> &[SemanticCReturnRegisterComposition] {
        &self.register_compositions
    }

    pub fn single_operand(&self) -> Option<SemanticCReturnOperand<'_>> {
        match (self.values.as_ref(), self.register_compositions.as_ref()) {
            ([value], []) => Some(SemanticCReturnOperand::Direct(value)),
            ([], [composition]) => Some(SemanticCReturnOperand::RegisterComposition(composition)),
            _ => None,
        }
    }

    pub const fn source_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.source_obligations
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SemanticCScope {
    LiveValueExpressionsOnly,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SemanticCIdentityScope {
    ArtifactLocalHandles,
}

/// Partial, proof-bound semantic-C expression layer.
///
/// The serialized scope and open-obligation set make incompleteness durable;
/// this envelope is never a complete source function or a typed-output seal.
/// Its value/arena handles are explicitly artifact-local and must not enter a
/// cache or cross-artifact merge until a function revision identity exists.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCExpressionLayer {
    schema_version: u32,
    scope: SemanticCScope,
    identity_scope: SemanticCIdentityScope,
    expressions: Box<[SemanticCExpr]>,
    entities: Box<[SemanticCEntity]>,
    function_interface: Option<SemanticCFunctionInterface>,
    inputs: BTreeMap<MachineValueBinding, MachineType>,
    input_origins: BTreeMap<MachineValueBinding, SemanticCInputOrigin>,
    return_mechanics: SemanticCReturnMechanicsOwnership,
    frame_mechanics: SemanticCFrameMechanicsOwnership,
    open_obligations: BTreeSet<SemanticObligationId>,
}

/// Exact source producers whose only certified consumers are architectural
/// return-address or exit-stack-pointer roots. These remain owned by the
/// terminal return node and are deliberately absent from semantic C steps.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct SemanticCReturnMechanicsOwner {
    pub(crate) source_producer: CanonicalInstructionId,
    pub(crate) return_producers: Box<[CanonicalInstructionId]>,
    pub(crate) source_obligations: Box<[SemanticObligationId]>,
}

impl SemanticCReturnMechanicsOwner {
    pub(crate) const fn source_producer(&self) -> CanonicalInstructionId {
        self.source_producer
    }

    pub(crate) const fn return_producers(&self) -> &[CanonicalInstructionId] {
        &self.return_producers
    }

    pub(crate) const fn source_obligations(&self) -> &[SemanticObligationId] {
        &self.source_obligations
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub(crate) struct SemanticCReturnMechanicsOwnership {
    owners: Box<[SemanticCReturnMechanicsOwner]>,
}

impl SemanticCReturnMechanicsOwnership {
    pub(crate) const fn owners(&self) -> &[SemanticCReturnMechanicsOwner] {
        &self.owners
    }

    fn source_obligations(&self) -> BTreeSet<SemanticObligationId> {
        self.owners
            .iter()
            .flat_map(|owner| owner.source_obligations.iter().copied())
            .collect()
    }
}

/// Exact source producers erased only because the artifact's frame certificate
/// proves that they implement one private save/restore protocol. A producer
/// shared with terminal SP mechanics is represented here once and retains the
/// exact returns it also serves.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct SemanticCFrameMechanicsOwner {
    pub(crate) source_producer: CanonicalInstructionId,
    pub(crate) frame_pointer_storage: CanonicalStorageId,
    pub(crate) saved_range: CertifiedNormalizedStackRange,
    pub(crate) return_producers: Box<[CanonicalInstructionId]>,
    pub(crate) source_obligations: Box<[SemanticObligationId]>,
}

impl SemanticCFrameMechanicsOwner {
    pub(crate) const fn source_producer(&self) -> CanonicalInstructionId {
        self.source_producer
    }

    pub(crate) const fn frame_pointer_storage(&self) -> CanonicalStorageId {
        self.frame_pointer_storage
    }

    pub(crate) const fn saved_range(&self) -> CertifiedNormalizedStackRange {
        self.saved_range
    }

    pub(crate) const fn return_producers(&self) -> &[CanonicalInstructionId] {
        &self.return_producers
    }

    pub(crate) const fn source_obligations(&self) -> &[SemanticObligationId] {
        &self.source_obligations
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub(crate) struct SemanticCFrameMechanicsOwnership {
    owners: Box<[SemanticCFrameMechanicsOwner]>,
    authority: Option<SemanticCFrameMechanicsAuthority>,
}

impl SemanticCFrameMechanicsOwnership {
    pub(crate) const fn owners(&self) -> &[SemanticCFrameMechanicsOwner] {
        &self.owners
    }

    pub(crate) const fn authority(&self) -> Option<&SemanticCFrameMechanicsAuthority> {
        self.authority.as_ref()
    }

    fn source_obligations(&self) -> BTreeSet<SemanticObligationId> {
        self.owners
            .iter()
            .flat_map(|owner| owner.source_obligations.iter().copied())
            .collect()
    }
}

/// Sealed frame-certificate anchors retained separately from derived owners so
/// region accounting can replay exact closure rather than trusting the owner
/// manifest it is auditing.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct SemanticCFrameMechanicsAuthority {
    frame_pointer_storage: CanonicalStorageId,
    saved_range: CertifiedNormalizedStackRange,
    common_roots: BTreeSet<CanonicalInstructionId>,
    return_order: Box<[CanonicalInstructionId]>,
    restore_roots: BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    explicit_dependencies: BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
}

impl SemanticCFrameMechanicsAuthority {
    pub(crate) const fn frame_pointer_storage(&self) -> CanonicalStorageId {
        self.frame_pointer_storage
    }

    pub(crate) const fn saved_range(&self) -> CertifiedNormalizedStackRange {
        self.saved_range
    }

    pub(crate) const fn common_roots(&self) -> &BTreeSet<CanonicalInstructionId> {
        &self.common_roots
    }

    pub(crate) const fn return_order(&self) -> &[CanonicalInstructionId] {
        &self.return_order
    }

    pub(crate) const fn restore_roots(
        &self,
    ) -> &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>> {
        &self.restore_roots
    }

    pub(crate) const fn explicit_dependencies(
        &self,
    ) -> &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>> {
        &self.explicit_dependencies
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticCError {
    MissingMachineExpression(MachineExprId),
    MissingSemanticExpression(SemanticCExprId),
    MissingCertifiedExpression(CanonicalInstructionId),
    CertifiedRootMismatch(CanonicalInstructionId),
    CertifiedSourceMismatch(CanonicalInstructionId),
    UncertifiedDependency {
        producer: CanonicalInstructionId,
        dependency: CanonicalInstructionId,
    },
    PhiRequiresCertifiedStructuring(Option<CanonicalInstructionId>),
    InvalidBooleanNotType(MachineExprId),
    InvalidSelectType(MachineExprId),
    SelectRequiresValueArms(MachineExprId),
    InvalidBooleanNotExpression(SemanticCExprId),
    InvalidBooleanExpression(SemanticCExprId),
    InvalidArithmeticFlagExpression(SemanticCExprId),
    InvalidBitwiseExpression(MachineExprId),
    InvalidSelectExpression(SemanticCExprId),
    SelectRequiresValueArmExpression(SemanticCExprId),
    InvalidWidth(u32),
    InconsistentInputType(ValueId),
    UnclassifiedSourceInput(ValueId),
    InvalidCertifiedFunctionInterface,
    InvalidCertifiedPrivateFrameInput,
    InvalidReturnProjection,
    MissingReturnExpression(CanonicalInstructionId),
    ReturnBindingMismatch(CanonicalInstructionId),
    MissingCallExpression(CanonicalInstructionId),
    CallBindingMismatch(CanonicalInstructionId),
    CheckedArithmeticRequiresHelper(SemanticCExprId),
    UnsupportedShiftPolicy(SemanticCExprId),
    MemoryReadRequiresCertifiedStatement(SemanticCExprId),
    InvalidReturnMechanics(CanonicalInstructionId),
    CyclicReturnMechanics(CanonicalInstructionId),
    InvalidFrameMechanics(CanonicalInstructionId),
    CyclicFrameMechanics(CanonicalInstructionId),
}

impl std::fmt::Display for SemanticCError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "semantic C construction failed: {self:?}")
    }
}

impl std::error::Error for SemanticCError {}

#[derive(Clone, Copy)]
struct MachineView<'a>(&'a MachineProjection);

impl<'a> MachineView<'a> {
    fn entities(self) -> &'a [MachineEntity] {
        self.0.entities()
    }

    fn expr(self, id: MachineExprId) -> Option<&'a MachineExpr> {
        self.0.expr(id)
    }

    fn entity_for_producer(self, producer: CanonicalInstructionId) -> Option<&'a MachineEntity> {
        self.0.entity_for_producer(producer)
    }

    fn output_producers(self) -> BTreeMap<ValueId, CanonicalInstructionId> {
        let mut producers = self
            .entities()
            .iter()
            .map(|entity| (entity.output().value(), entity.producer()))
            .collect::<BTreeMap<_, _>>();
        producers.extend(
            self.0
                .failures()
                .iter()
                .map(|failure| (failure.output(), failure.producer())),
        );
        producers
    }
}

trait CertifiedSemanticSource {
    fn origin(&self) -> &r2cert::CertifiedArtifactOrigin;
    fn machine_view(&self) -> MachineView<'_>;
    fn source(&self) -> &SemanticObligationInventory;
    fn ledger(&self) -> &ObligationLedger;
    fn expression_for_producer(&self, producer: CanonicalInstructionId) -> Option<&CertifiedExpr>;
    fn machine_context(&self) -> &SourceMachineContext;
    fn abi_parameters(&self) -> &BTreeMap<u32, CertifiedAbiParameter>;
    fn stack_slots(&self) -> &BTreeMap<StackAddressRoot, CertifiedStackSlot>;
    fn topology(&self) -> &CertifiedSourceTopology;
    fn frame_preservation(&self) -> Option<&CertifiedFramePreservation>;
    fn return_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedReturnControl>;
    fn memory_statement_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedMemoryStatement>;
}

impl CertifiedSemanticSource for CertifiedMachineFunction {
    fn origin(&self) -> &r2cert::CertifiedArtifactOrigin {
        CertifiedMachineFunction::origin(self)
    }

    fn machine_view(&self) -> MachineView<'_> {
        MachineView(self.projection())
    }

    fn source(&self) -> &SemanticObligationInventory {
        CertifiedMachineFunction::source(self)
    }

    fn ledger(&self) -> &ObligationLedger {
        CertifiedMachineFunction::ledger(self)
    }

    fn expression_for_producer(&self, producer: CanonicalInstructionId) -> Option<&CertifiedExpr> {
        CertifiedMachineFunction::expression_for_producer(self, producer)
    }

    fn machine_context(&self) -> &SourceMachineContext {
        CertifiedMachineFunction::machine_context(self).source()
    }

    fn abi_parameters(&self) -> &BTreeMap<u32, CertifiedAbiParameter> {
        CertifiedMachineFunction::abi_parameters(self)
    }

    fn stack_slots(&self) -> &BTreeMap<StackAddressRoot, CertifiedStackSlot> {
        CertifiedMachineFunction::stack_slots(self)
    }

    fn topology(&self) -> &CertifiedSourceTopology {
        CertifiedMachineFunction::topology(self)
    }

    fn frame_preservation(&self) -> Option<&CertifiedFramePreservation> {
        CertifiedMachineFunction::frame_preservation(self)
    }

    fn return_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedReturnControl> {
        CertifiedMachineFunction::return_control_for_producer(self, producer)
    }

    fn memory_statement_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedMemoryStatement> {
        CertifiedMachineFunction::memory_statement_for_producer(self, producer)
    }
}

impl CertifiedSemanticSource for CertifiedMachineProjection {
    fn origin(&self) -> &r2cert::CertifiedArtifactOrigin {
        CertifiedMachineProjection::origin(self)
    }

    fn machine_view(&self) -> MachineView<'_> {
        MachineView(self.projection())
    }

    fn source(&self) -> &SemanticObligationInventory {
        CertifiedMachineProjection::source(self)
    }

    fn ledger(&self) -> &ObligationLedger {
        CertifiedMachineProjection::ledger(self)
    }

    fn expression_for_producer(&self, producer: CanonicalInstructionId) -> Option<&CertifiedExpr> {
        CertifiedMachineProjection::expression_for_producer(self, producer)
    }

    fn machine_context(&self) -> &SourceMachineContext {
        CertifiedMachineProjection::machine_context(self).source()
    }

    fn abi_parameters(&self) -> &BTreeMap<u32, CertifiedAbiParameter> {
        CertifiedMachineProjection::abi_parameters(self)
    }

    fn stack_slots(&self) -> &BTreeMap<StackAddressRoot, CertifiedStackSlot> {
        CertifiedMachineProjection::stack_slots(self)
    }

    fn topology(&self) -> &CertifiedSourceTopology {
        CertifiedMachineProjection::topology(self)
    }

    fn frame_preservation(&self) -> Option<&CertifiedFramePreservation> {
        CertifiedMachineProjection::frame_preservation(self)
    }

    fn return_control_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedReturnControl> {
        CertifiedMachineProjection::return_control_for_producer(self, producer)
    }

    fn memory_statement_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&CertifiedMemoryStatement> {
        CertifiedMachineProjection::memory_statement_for_producer(self, producer)
    }
}

fn exact_semantic_return_projection(
    source: &SourceFunctionInterface,
    storage: CanonicalStorageId,
) -> Result<Option<SemanticCReturnProjection>, SemanticCError> {
    let (logical, graph) = match (source.return_logical_value(), source.type_graph()) {
        (None, None) => return Ok(None),
        (Some(logical), Some(graph)) => (logical, graph),
        _ => return Err(SemanticCError::InvalidReturnProjection),
    };
    let source_type = usize::try_from(logical.type_id())
        .ok()
        .and_then(|index| graph.types().get(index))
        .filter(|source_type| source_type.id() == logical.type_id())
        .ok_or(SemanticCError::InvalidReturnProjection)?;
    let signedness = match source_type.kind() {
        SourceTypeKind::SignedInteger => MachineSignedness::Signed,
        SourceTypeKind::UnsignedInteger => MachineSignedness::Unsigned,
        SourceTypeKind::Pointer { .. } | SourceTypeKind::Struct { .. } => return Ok(None),
    };
    let physical_width = storage
        .size
        .checked_mul(8)
        .filter(|width| matches!(width, 8 | 16 | 32 | 64))
        .ok_or(SemanticCError::InvalidReturnProjection)?;
    let carrier = logical.carrier();
    let logical_width = u32::try_from(source_type.size_bits())
        .ok()
        .filter(|width| matches!(width, 8 | 16 | 32 | 64))
        .ok_or(SemanticCError::InvalidReturnProjection)?;
    let coherent_carrier = carrier.offset_bits() == 0
        && carrier.size_bits() == u64::from(logical_width)
        && match carrier.kind() {
            SourceCarrierKind::Full => logical_width == physical_width,
            SourceCarrierKind::LowBits => logical_width < physical_width,
        };
    if !coherent_carrier {
        return Err(SemanticCError::InvalidReturnProjection);
    }
    Ok(Some(SemanticCReturnProjection {
        source_type_id: logical.type_id(),
        carrier,
        physical_ty: MachineType::Integer {
            width_bits: physical_width,
            signedness: MachineSignedness::Unsigned,
        },
        logical_ty: MachineType::Integer {
            width_bits: logical_width,
            signedness,
        },
    }))
}

fn semantic_function_interface(
    certified: &impl CertifiedSemanticSource,
) -> Result<Option<SemanticCFunctionInterface>, SemanticCError> {
    let Some(source) = certified.machine_context().function_interface() else {
        if !certified.abi_parameters().is_empty() || !certified.stack_slots().is_empty() {
            return Err(SemanticCError::InvalidCertifiedFunctionInterface);
        }
        return Ok(None);
    };
    if source.parameters().len() != certified.abi_parameters().len()
        || source.stack_slots().len() != certified.stack_slots().len()
    {
        return Err(SemanticCError::InvalidCertifiedFunctionInterface);
    }
    let mut parameters = Vec::with_capacity(source.parameters().len());
    for (declared, logical_value) in source
        .parameters()
        .iter()
        .zip(source.parameter_logical_values())
    {
        let certified_parameter = certified
            .abi_parameters()
            .get(&declared.index())
            .filter(|parameter| {
                parameter.storage() == declared.storage()
                    && parameter.logical_value() == *logical_value
            })
            .ok_or(SemanticCError::InvalidCertifiedFunctionInterface)?;
        let width_bits = certified_parameter
            .graph_storage()
            .size
            .checked_mul(8)
            .filter(|width| *width > 0)
            .ok_or(SemanticCError::InvalidCertifiedFunctionInterface)?;
        let ty = certified_parameter
            .value()
            .map(|value| value.ty().clone())
            .unwrap_or(MachineType::Integer {
                width_bits,
                signedness: MachineSignedness::Unsigned,
            });
        if ty.width_bits() != width_bits {
            return Err(SemanticCError::InvalidCertifiedFunctionInterface);
        }
        parameters.push(SemanticCParameter {
            index: declared.index(),
            storage: declared.storage(),
            value: certified_parameter.value().map(|value| value.binding()),
            ty,
        });
    }
    let (return_kind, return_projection) = match source.return_kind() {
        SourceFunctionReturn::Void => {
            if source.return_logical_value().is_some() {
                return Err(SemanticCError::InvalidReturnProjection);
            }
            (SemanticCFunctionReturn::Void, None)
        }
        SourceFunctionReturn::Register { storage } => {
            let width_bits = storage
                .size
                .checked_mul(8)
                .filter(|width| *width > 0)
                .ok_or(SemanticCError::InvalidCertifiedFunctionInterface)?;
            let projection = exact_semantic_return_projection(source, storage)?;
            (
                SemanticCFunctionReturn::Register {
                    storage,
                    ty: MachineType::Integer {
                        width_bits,
                        signedness: MachineSignedness::Unsigned,
                    },
                },
                projection,
            )
        }
    };
    let mut stack_slots = Vec::with_capacity(source.stack_slots().len());
    for declared in source.stack_slots() {
        let root = StackAddressRoot {
            base: declared.base(),
            offset: declared.offset(),
        };
        let slot = certified
            .stack_slots()
            .get(&root)
            .filter(|slot| slot.size_bytes() == declared.size_bytes())
            .ok_or(SemanticCError::InvalidCertifiedFunctionInterface)?;
        stack_slots.push(SemanticCStackSlot {
            base: slot.base(),
            offset: slot.offset(),
            size_bytes: slot.size_bytes(),
            object: slot.object(),
        });
    }
    Ok(Some(SemanticCFunctionInterface {
        revision_identity: source.revision_identity().to_vec().into_boxed_slice(),
        calling_convention: source.calling_convention().to_string(),
        parameters: parameters.into_boxed_slice(),
        return_kind,
        return_projection,
        stack_slots: stack_slots.into_boxed_slice(),
    }))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CertifiedPrivateEntryStackPointerInput {
    binding: MachineValueBinding,
    ty: MachineType,
    storage: CanonicalStorageId,
    header: u64,
}

impl CertifiedPrivateEntryStackPointerInput {
    pub(crate) fn classify(
        &self,
        binding: MachineValueBinding,
        ty: &MachineType,
    ) -> SemanticCInputOrigin {
        if binding == self.binding && ty == &self.ty {
            SemanticCInputOrigin::CertifiedPrivateEntryStackPointer {
                storage: self.storage,
                header: self.header,
            }
        } else {
            SemanticCInputOrigin::UnclassifiedSource
        }
    }
}

pub(crate) fn certified_private_entry_stack_pointer_input(
    certified: &CertifiedMachineProjection,
    join: Option<&CertifiedPrivateFrameConditionalJoin>,
    stack: Option<&CertifiedStackDiscipline>,
) -> Result<CertifiedPrivateEntryStackPointerInput, SemanticCError> {
    let (Some(join), Some(stack)) = (join, stack) else {
        return Err(SemanticCError::InvalidCertifiedPrivateFrameInput);
    };
    let origin = certified.origin();
    let entry = stack.entry_stack_pointer();
    let width_bits = stack
        .stack_pointer_storage()
        .size
        .checked_mul(8)
        .ok_or(SemanticCError::InvalidCertifiedPrivateFrameInput)?;
    if origin.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || join.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || stack.schema_version() != CERTIFICATION_SCHEMA_VERSION
        || join.origin() != origin
        || stack.origin() != origin
        || join.header() != certified.topology().entry_addr()
        || certified.private_frame_conditional_join(join.header()) != Some(join)
        || certified.stack_discipline() != Some(stack)
        || entry.binding().width_bits() != width_bits
        || entry.producer().is_some()
        || entry.memory_access().is_some()
        || entry.ty().width_bits() != width_bits
    {
        return Err(SemanticCError::InvalidCertifiedPrivateFrameInput);
    }
    Ok(CertifiedPrivateEntryStackPointerInput {
        binding: entry.binding(),
        ty: entry.ty().clone(),
        storage: stack.stack_pointer_storage(),
        header: join.header(),
    })
}

fn classify_input(
    binding: MachineValueBinding,
    ty: &MachineType,
    interface: Option<&SemanticCFunctionInterface>,
    private_entry_stack_pointer: Option<&CertifiedPrivateEntryStackPointerInput>,
) -> SemanticCInputOrigin {
    if let Some(origin) =
        private_entry_stack_pointer.and_then(|input| match input.classify(binding, ty) {
            origin @ SemanticCInputOrigin::CertifiedPrivateEntryStackPointer { .. } => Some(origin),
            _ => None,
        })
    {
        return origin;
    }
    if let Some(parameter) = interface
        .into_iter()
        .flat_map(SemanticCFunctionInterface::parameters)
        .find(|parameter| parameter.value() == Some(binding))
    {
        return SemanticCInputOrigin::AbiParameter {
            index: parameter.index(),
            storage: parameter.storage(),
        };
    }
    let MachineType::Address {
        provenance: MachineAddressProvenance::Stack { base, offset },
        ..
    } = ty
    else {
        return SemanticCInputOrigin::UnclassifiedSource;
    };
    let base = match base {
        MachineStackBase::FramePointer => StackAddressBase::FramePointer,
        MachineStackBase::StackPointer => StackAddressBase::StackPointer,
    };
    interface
        .into_iter()
        .flat_map(SemanticCFunctionInterface::stack_slots)
        .find(|slot| slot.base() == base && slot.offset() == *offset)
        .map(|slot| SemanticCInputOrigin::StackSlot {
            base,
            offset: *offset,
            size_bytes: slot.size_bytes(),
            object: slot.object(),
        })
        .unwrap_or(SemanticCInputOrigin::UnclassifiedSource)
}

fn exact_expression_dependencies(
    certified: &impl CertifiedSemanticSource,
    machine: MachineView<'_>,
) -> Result<
    (
        BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
        BTreeMap<ValueId, CanonicalInstructionId>,
        BTreeMap<CanonicalInstructionId, MachineValueBinding>,
    ),
    SemanticCError,
> {
    let mut dependencies = BTreeMap::new();
    let mut output_producers = BTreeMap::new();
    let mut outputs = BTreeMap::new();
    for entity in machine.entities() {
        output_producers.insert(entity.output().value(), entity.producer());
        outputs.insert(entity.producer(), entity.output());
        let live_obligations = entity
            .source_obligations()
            .iter()
            .copied()
            .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
            .collect::<BTreeSet<_>>();
        if live_obligations.is_empty() {
            continue;
        }
        let Some(expression) = certified.expression_for_producer(entity.producer()) else {
            continue;
        };
        if live_obligations.len() != 1
            || expression.entity().producer() != entity.producer()
            || expression.entity().source_obligations() != &live_obligations
            || expression.root() != entity.root()
        {
            return Err(SemanticCError::InvalidReturnMechanics(entity.producer()));
        }
        let Some(obligation) = live_obligations.iter().next().copied() else {
            return Err(SemanticCError::InvalidReturnMechanics(entity.producer()));
        };
        let [effect] = certified.ledger().effects(obligation) else {
            return Err(SemanticCError::InvalidReturnMechanics(entity.producer()));
        };
        if effect.disposition()
            != &(EffectDisposition::AbsorbedIntoExpression {
                producer: entity.producer(),
            })
            || effect.expression_evidence() != Some(expression)
        {
            return Err(SemanticCError::InvalidReturnMechanics(entity.producer()));
        }
        if dependencies
            .insert(entity.producer(), expression.inputs().clone())
            .is_some()
        {
            return Err(SemanticCError::InvalidReturnMechanics(entity.producer()));
        }
    }
    Ok((dependencies, output_producers, outputs))
}

fn add_return_mechanics_closure(
    root: CanonicalInstructionId,
    return_producer: CanonicalInstructionId,
    dependencies: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    candidates: &mut BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
) -> Result<(), SemanticCError> {
    let mut stack = vec![(root, false)];
    let mut active = BTreeSet::new();
    let mut complete = BTreeSet::new();
    while let Some((producer, leaving)) = stack.pop() {
        candidates
            .entry(producer)
            .or_default()
            .insert(return_producer);
        if leaving {
            active.remove(&producer);
            complete.insert(producer);
            continue;
        }
        if complete.contains(&producer) {
            continue;
        }
        let Some(inputs) = dependencies.get(&producer) else {
            return Err(SemanticCError::InvalidReturnMechanics(producer));
        };
        if !active.insert(producer) {
            return Err(SemanticCError::CyclicReturnMechanics(producer));
        }
        stack.push((producer, true));
        stack.extend(inputs.iter().rev().map(|input| (*input, false)));
    }
    Ok(())
}

fn is_exact_mechanical_read(
    certified: &impl CertifiedSemanticSource,
    producer: CanonicalInstructionId,
    output: Option<MachineValueBinding>,
) -> bool {
    let Some(statement) = certified.memory_statement_for_producer(producer) else {
        return false;
    };
    let CertifiedMemoryStatementKind::Read { result } = statement.kind() else {
        return false;
    };
    if output != Some(result.binding())
        || statement.producer() != producer
        || statement.source_obligations().len() != 1
    {
        return false;
    }
    statement.source_obligations().iter().all(|obligation| {
        obligation.instruction == producer
            && obligation.kind == SemanticObligationKind::ObservableMemoryRead
            && matches!(
                certified.ledger().effects(*obligation),
                [effect]
                    if effect.disposition()
                        == &EffectDisposition::AbsorbedIntoStatement { producer }
                        && effect.statement_evidence() == Some(statement)
            )
    })
}

struct ReturnMechanicsPlan {
    candidates: BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    return_order: Vec<CanonicalInstructionId>,
}

fn backward_close_semantic_producers(
    candidates: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    dependencies: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    mut semantic: BTreeSet<CanonicalInstructionId>,
) -> Result<BTreeSet<CanonicalInstructionId>, SemanticCError> {
    let mut frontier = semantic.iter().copied().collect::<Vec<_>>();
    while let Some(producer) = frontier.pop() {
        let Some(inputs) = dependencies.get(&producer) else {
            return Err(SemanticCError::InvalidReturnMechanics(producer));
        };
        for input in inputs {
            if candidates.contains_key(input) && semantic.insert(*input) {
                frontier.push(*input);
            }
        }
    }
    Ok(semantic)
}

fn derive_return_mechanics_plan(
    certified: &impl CertifiedSemanticSource,
) -> Result<ReturnMechanicsPlan, SemanticCError> {
    let machine = certified.machine_view();
    let (dependencies, _, _) = exact_expression_dependencies(certified, machine)?;
    let interface = certified.machine_context().function_interface();
    let mut controls = Vec::new();
    for block in certified.topology().blocks() {
        if !matches!(block.terminator(), CertifiedSourceTerminator::Return) {
            continue;
        }
        let Some(producer) = block.instructions().last().copied() else {
            continue;
        };
        let Some(control) = certified.return_control_for_producer(producer) else {
            continue;
        };
        let Some(interface) = interface else {
            return Err(SemanticCError::InvalidReturnMechanics(producer));
        };
        if interface.return_address_storage() != Some(control.return_address().storage())
            || interface.stack_pointer_storage() != Some(control.exit_stack_pointer().storage())
            || control.return_address().value() != control.control_target()
        {
            return Err(SemanticCError::InvalidReturnMechanics(producer));
        }
        for obligation in control.source_obligations() {
            let [effect] = certified.ledger().effects(obligation) else {
                return Err(SemanticCError::InvalidReturnMechanics(producer));
            };
            if effect.disposition() != &(EffectDisposition::AbsorbedIntoReturn { producer })
                || effect.return_control_evidence() != Some(control)
            {
                return Err(SemanticCError::InvalidReturnMechanics(producer));
            }
        }
        controls.push(control);
    }
    if controls.is_empty() {
        return Ok(ReturnMechanicsPlan {
            candidates: BTreeMap::new(),
            return_order: Vec::new(),
        });
    }

    let return_order = controls
        .iter()
        .map(|control| control.producer())
        .collect::<Vec<_>>();
    let mut candidates =
        BTreeMap::<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>::new();
    for control in &controls {
        for root in [
            control.return_address().value().producer(),
            control
                .exit_stack_pointer()
                .value()
                .and_then(|value| value.producer()),
        ]
        .into_iter()
        .flatten()
        {
            add_return_mechanics_closure(root, control.producer(), &dependencies, &mut candidates)?;
        }
    }
    Ok(ReturnMechanicsPlan {
        candidates,
        return_order,
    })
}

fn materialize_return_mechanics(
    certified: &impl CertifiedSemanticSource,
    plan: &ReturnMechanicsPlan,
    mechanics: &BTreeSet<CanonicalInstructionId>,
    outputs: &BTreeMap<CanonicalInstructionId, MachineValueBinding>,
) -> Result<SemanticCReturnMechanicsOwnership, SemanticCError> {
    let mut owners = Vec::with_capacity(mechanics.len());
    for producer in certified
        .topology()
        .blocks()
        .iter()
        .flat_map(|block| block.instructions().iter().copied())
        .filter(|producer| mechanics.contains(producer))
    {
        let instruction = certified
            .source()
            .instructions()
            .get(&producer)
            .ok_or(SemanticCError::InvalidReturnMechanics(producer))?;
        for obligation in &instruction.obligations {
            let valid = match obligation.kind {
                SemanticObligationKind::LiveValueProducer => matches!(
                    certified.ledger().effects(*obligation),
                    [effect]
                        if effect.disposition()
                            == &EffectDisposition::AbsorbedIntoExpression { producer }
                            && effect.expression_evidence().is_some_and(|expression| {
                                expression.entity().producer() == producer
                                    && expression.entity().source_obligations().contains(obligation)
                            })
                ),
                SemanticObligationKind::ObservableMemoryRead => {
                    is_exact_mechanical_read(certified, producer, outputs.get(&producer).copied())
                }
                _ => false,
            };
            if !valid {
                return Err(SemanticCError::InvalidReturnMechanics(producer));
            }
        }
        let served = plan
            .candidates
            .get(&producer)
            .ok_or(SemanticCError::InvalidReturnMechanics(producer))?;
        let return_producers = plan
            .return_order
            .iter()
            .copied()
            .filter(|return_producer| served.contains(return_producer))
            .collect::<Vec<_>>();
        if return_producers.is_empty() {
            return Err(SemanticCError::InvalidReturnMechanics(producer));
        }
        owners.push(SemanticCReturnMechanicsOwner {
            source_producer: producer,
            return_producers: return_producers.into_boxed_slice(),
            source_obligations: instruction
                .obligations
                .iter()
                .copied()
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        });
    }
    if owners.len() != mechanics.len() {
        let producer = mechanics
            .iter()
            .copied()
            .find(|producer| {
                !owners
                    .iter()
                    .any(|owner| owner.source_producer == *producer)
            })
            .unwrap_or(plan.return_order[0]);
        return Err(SemanticCError::InvalidReturnMechanics(producer));
    }
    Ok(SemanticCReturnMechanicsOwnership {
        owners: owners.into_boxed_slice(),
    })
}

fn add_frame_mechanics_closure(
    root: CanonicalInstructionId,
    return_producer: CanonicalInstructionId,
    dependencies: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    candidates: &mut BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    active: &mut BTreeSet<CanonicalInstructionId>,
    complete: &mut BTreeSet<CanonicalInstructionId>,
) -> Result<(), SemanticCError> {
    let mut stack = vec![(root, false)];
    while let Some((producer, leaving)) = stack.pop() {
        candidates
            .entry(producer)
            .or_default()
            .insert(return_producer);
        if leaving {
            active.remove(&producer);
            complete.insert(producer);
            continue;
        }
        if active.contains(&producer) {
            return Err(SemanticCError::CyclicFrameMechanics(producer));
        }
        if complete.contains(&producer) {
            continue;
        }
        active.insert(producer);
        stack.push((producer, true));
        let Some(inputs) = dependencies.get(&producer) else {
            return Err(SemanticCError::InvalidFrameMechanics(producer));
        };
        stack.extend(inputs.iter().rev().map(|input| (*input, false)));
    }
    Ok(())
}

fn frame_statement_has_exact_ledger_owner(
    certified: &impl CertifiedSemanticSource,
    statement: &CertifiedMemoryStatement,
    obligation: SemanticObligationId,
) -> bool {
    statement.source_obligations().contains(&obligation)
        && matches!(certified.ledger().effects(obligation), [effect]
            if effect.disposition()
                == &EffectDisposition::AbsorbedIntoStatement {
                    producer: statement.producer(),
                }
                && effect.statement_evidence() == Some(statement))
}

fn merge_frame_dependency_row(
    dependencies: &mut BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    producer: CanonicalInstructionId,
    inputs: impl IntoIterator<Item = CanonicalInstructionId>,
) {
    dependencies
        .entry(producer)
        .or_default()
        .extend(inputs.into_iter().filter(|input| *input != producer));
}

fn merge_exact_frame_relation_dependency(
    dependencies: &mut BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    explicit_dependencies: &mut BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    producer: CanonicalInstructionId,
    input: Option<CanonicalInstructionId>,
) -> bool {
    if input == Some(producer) {
        return false;
    }
    let exact = input.into_iter().collect::<BTreeSet<_>>();
    if dependencies
        .get(&producer)
        .is_some_and(|inputs| inputs != &exact)
        || explicit_dependencies
            .get(&producer)
            .is_some_and(|inputs| inputs != &exact)
    {
        return false;
    }
    dependencies
        .entry(producer)
        .or_insert_with(|| exact.clone());
    explicit_dependencies.entry(producer).or_insert(exact);
    true
}

fn union_mechanics_services(
    return_services: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    frame_services: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
) -> BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>> {
    let mut combined = return_services.clone();
    for (producer, returns) in frame_services {
        combined.entry(*producer).or_default().extend(returns);
    }
    combined
}

fn semantic_mechanics_producers(
    certified: &impl CertifiedSemanticSource,
    candidates: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    dependencies: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
    output_producers: &BTreeMap<ValueId, CanonicalInstructionId>,
    outputs: &BTreeMap<CanonicalInstructionId, MachineValueBinding>,
    frame_statements: &BTreeMap<CanonicalInstructionId, &CertifiedMemoryStatement>,
    return_candidates: &BTreeMap<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>,
) -> Result<BTreeSet<CanonicalInstructionId>, SemanticCError> {
    let candidate_set = candidates.keys().copied().collect::<BTreeSet<_>>();
    let mut semantic = BTreeSet::new();
    for control in certified.topology().blocks().iter().filter_map(|block| {
        block
            .instructions()
            .last()
            .and_then(|producer| certified.return_control_for_producer(*producer))
    }) {
        for returned in control.values() {
            if let Some(producer) = returned.value().producer()
                && candidate_set.contains(&producer)
            {
                semantic.insert(producer);
            }
        }
        for composition in control.register_compositions() {
            for definition in std::iter::once(composition.base()).chain(
                composition
                    .overlays()
                    .iter()
                    .map(CertifiedReturnRegisterOverlay::definition),
            ) {
                if definition.value().producer() != Some(definition.producer()) {
                    return Err(SemanticCError::InvalidReturnMechanics(
                        definition.producer(),
                    ));
                }
                if candidate_set.contains(&definition.producer()) {
                    semantic.insert(definition.producer());
                }
            }
        }
    }
    for (producer, inputs) in dependencies {
        if candidate_set.contains(producer) {
            continue;
        }
        semantic.extend(
            inputs
                .iter()
                .copied()
                .filter(|input| candidate_set.contains(input)),
        );
    }
    let return_controls = certified
        .topology()
        .blocks()
        .iter()
        .filter_map(|block| {
            block
                .instructions()
                .last()
                .and_then(|producer| certified.return_control_for_producer(*producer))
        })
        .map(|control| (control.producer(), control))
        .collect::<BTreeMap<_, _>>();
    for obligation in certified.source().obligations().values() {
        if obligation.id.kind == SemanticObligationKind::LiveValueProducer {
            continue;
        }
        let exact_frame_statement = frame_statements
            .get(&obligation.id.instruction)
            .is_some_and(|statement| {
                frame_statement_has_exact_ledger_owner(certified, statement, obligation.id)
            });
        let exact_return_target = obligation.id.kind == SemanticObligationKind::Return
            && return_controls
                .get(&obligation.id.instruction)
                .is_some_and(|control| {
                    control.return_obligation() == obligation.id
                        && obligation.inputs == [control.control_target().binding().value()]
                });
        let exact_return_read = obligation.id.kind == SemanticObligationKind::ObservableMemoryRead
            && return_candidates.contains_key(&obligation.id.instruction)
            && is_exact_mechanical_read(
                certified,
                obligation.id.instruction,
                outputs.get(&obligation.id.instruction).copied(),
            );
        if exact_frame_statement || exact_return_target || exact_return_read {
            continue;
        }
        if candidate_set.contains(&obligation.id.instruction) {
            semantic.insert(obligation.id.instruction);
        }
        semantic.extend(obligation.inputs.iter().filter_map(|input| {
            output_producers
                .get(input)
                .copied()
                .filter(|producer| candidate_set.contains(producer))
        }));
    }
    backward_close_semantic_producers(candidates, dependencies, semantic)
}

fn derive_mechanics(
    certified: &impl CertifiedSemanticSource,
    return_plan: &ReturnMechanicsPlan,
) -> Result<
    (
        SemanticCReturnMechanicsOwnership,
        SemanticCFrameMechanicsOwnership,
    ),
    SemanticCError,
> {
    let machine = certified.machine_view();
    let (mut dependencies, output_producers, outputs) =
        exact_expression_dependencies(certified, machine)?;
    let Some(frame) = certified.frame_preservation() else {
        let all_candidates = return_plan
            .candidates
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let semantic = semantic_mechanics_producers(
            certified,
            &return_plan.candidates,
            &dependencies,
            &output_producers,
            &outputs,
            &BTreeMap::new(),
            &return_plan.candidates,
        )?;
        let mechanics = all_candidates
            .difference(&semantic)
            .copied()
            .collect::<BTreeSet<_>>();
        return Ok((
            materialize_return_mechanics(certified, return_plan, &mechanics, &outputs)?,
            SemanticCFrameMechanicsOwnership::default(),
        ));
    };
    let fallback = frame.stack_allocation().entity().producer();
    if frame.origin() != certified.origin() {
        return Err(SemanticCError::InvalidFrameMechanics(fallback));
    }
    let restore_return_set = frame
        .restores()
        .iter()
        .map(|restore| restore.return_control().producer())
        .collect::<BTreeSet<_>>();
    let frame_return_order = certified
        .topology()
        .blocks()
        .iter()
        .filter(|block| matches!(block.terminator(), CertifiedSourceTerminator::Return))
        .filter_map(|block| block.instructions().last().copied())
        .filter(|producer| restore_return_set.contains(producer))
        .collect::<Vec<_>>();
    if frame_return_order.is_empty()
        || frame_return_order.len() != frame.restores().len()
        || frame_return_order.len() != restore_return_set.len()
        || frame_return_order != return_plan.return_order
    {
        return Err(SemanticCError::InvalidFrameMechanics(fallback));
    }
    let mut common_roots = BTreeSet::new();
    let mut restore_roots =
        BTreeMap::<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>::new();
    let mut statements = BTreeMap::<CanonicalInstructionId, &CertifiedMemoryStatement>::new();
    let mut explicit_dependencies =
        BTreeMap::<CanonicalInstructionId, BTreeSet<CanonicalInstructionId>>::new();
    common_roots.insert(frame.stack_allocation().entity().producer());
    let relation = frame.frame_relation();
    let relation_producer = relation.producer();
    let relation_input = relation.input().binding();
    let relation_input_producer = relation.input().producer();
    let relation_width = frame
        .frame_pointer_storage()
        .size
        .checked_mul(8)
        .filter(|width| *width != 0)
        .ok_or(SemanticCError::InvalidFrameMechanics(relation_producer))?;
    let relation_entity = machine
        .entity_for_producer(relation_producer)
        .ok_or(SemanticCError::InvalidFrameMechanics(relation_producer))?;
    let relation_affine = relation
        .normalized_affine_relation()
        .ok_or(SemanticCError::InvalidFrameMechanics(relation_producer))?;
    let input_is_exact = match relation_input_producer {
        Some(producer) => {
            output_producers.get(&relation_input.value()) == Some(&producer)
                && outputs.get(&producer) == Some(&relation_input)
        }
        None => !output_producers.contains_key(&relation_input.value()),
    };
    if relation.storage() != frame.frame_pointer_storage()
        || relation_affine.base_storage() != frame.stack_pointer_storage()
        || relation_affine.width_bits() != relation_width
        || relation.input().binding().width_bits() != relation_width
        || relation.output().width_bits() != relation_width
        || relation_entity.root() != relation.root()
        || relation_entity.output() != relation.output()
        || !input_is_exact
        || !merge_exact_frame_relation_dependency(
            &mut dependencies,
            &mut explicit_dependencies,
            relation_producer,
            relation_input_producer,
        )
    {
        return Err(SemanticCError::InvalidFrameMechanics(relation_producer));
    }
    common_roots.insert(relation_producer);
    for copy in frame.entry_save_copies() {
        common_roots.insert(copy.entity().producer());
    }
    common_roots.insert(frame.entry_save().producer());
    statements.insert(frame.entry_save().producer(), frame.entry_save());
    let mut entry_save_inputs = BTreeSet::new();
    if let Some(producer) = frame.entry_save().address().producer() {
        common_roots.insert(producer);
        entry_save_inputs.insert(producer);
    }
    if let CertifiedMemoryStatementKind::Write { value } = frame.entry_save().kind()
        && let Some(producer) = value.producer()
    {
        common_roots.insert(producer);
        entry_save_inputs.insert(producer);
    }
    merge_frame_dependency_row(
        &mut explicit_dependencies,
        frame.entry_save().producer(),
        entry_save_inputs,
    );
    for restore in frame.restores() {
        let return_producer = restore.return_control().producer();
        let roots = restore_roots.entry(return_producer).or_default();
        if let Some(return_address_read) = restore.return_address_read() {
            roots.insert(return_address_read.producer());
            statements.insert(return_address_read.producer(), return_address_read);
            let mut return_address_read_inputs = BTreeSet::new();
            if let Some(producer) = return_address_read.address().producer() {
                roots.insert(producer);
                return_address_read_inputs.insert(producer);
            }
            merge_frame_dependency_row(
                &mut explicit_dependencies,
                return_address_read.producer(),
                return_address_read_inputs,
            );
        }
        roots.insert(restore.restore_read().producer());
        statements.insert(restore.restore_read().producer(), restore.restore_read());
        let mut restore_read_inputs = BTreeSet::new();
        if let Some(producer) = restore.restore_read().address().producer() {
            roots.insert(producer);
            restore_read_inputs.insert(producer);
        }
        merge_frame_dependency_row(
            &mut explicit_dependencies,
            restore.restore_read().producer(),
            restore_read_inputs,
        );
        for copy in restore.restore_copies() {
            roots.insert(copy.producer());
            let mut copy_inputs = BTreeSet::new();
            if let Some(producer) = copy.input().producer() {
                roots.insert(producer);
                copy_inputs.insert(producer);
            }
            merge_frame_dependency_row(&mut explicit_dependencies, copy.producer(), copy_inputs);
        }
        roots.insert(restore.restore_assignment().producer());
        let mut assignment_inputs = BTreeSet::new();
        if let Some(producer) = restore.restore_assignment().input().producer() {
            roots.insert(producer);
            assignment_inputs.insert(producer);
        }
        merge_frame_dependency_row(
            &mut explicit_dependencies,
            restore.restore_assignment().producer(),
            assignment_inputs,
        );
    }
    for (producer, inputs) in &explicit_dependencies {
        merge_frame_dependency_row(&mut dependencies, *producer, inputs.iter().copied());
    }
    let mut candidates = BTreeMap::new();
    for return_producer in &frame_return_order {
        let mut complete = BTreeSet::new();
        for root in &common_roots {
            add_frame_mechanics_closure(
                *root,
                *return_producer,
                &dependencies,
                &mut candidates,
                &mut BTreeSet::new(),
                &mut complete,
            )?;
        }
        for root in restore_roots.get(return_producer).into_iter().flatten() {
            add_frame_mechanics_closure(
                *root,
                *return_producer,
                &dependencies,
                &mut candidates,
                &mut BTreeSet::new(),
                &mut complete,
            )?;
        }
    }
    if candidates.is_empty() {
        return Err(SemanticCError::InvalidFrameMechanics(fallback));
    }
    let all_candidate_services = union_mechanics_services(&return_plan.candidates, &candidates);
    let semantic = semantic_mechanics_producers(
        certified,
        &all_candidate_services,
        &dependencies,
        &output_producers,
        &outputs,
        &statements,
        &return_plan.candidates,
    )?;
    let mechanics = candidates
        .keys()
        .filter(|producer| !semantic.contains(producer))
        .copied()
        .collect::<BTreeSet<_>>();
    let mut owners = Vec::with_capacity(mechanics.len());
    for producer in certified
        .topology()
        .blocks()
        .iter()
        .flat_map(|block| block.instructions().iter().copied())
        .filter(|producer| mechanics.contains(producer))
    {
        let instruction = certified
            .source()
            .instructions()
            .get(&producer)
            .ok_or(SemanticCError::InvalidFrameMechanics(producer))?;
        for obligation in &instruction.obligations {
            let valid = match obligation.kind {
                SemanticObligationKind::LiveValueProducer => matches!(
                    certified.ledger().effects(*obligation),
                    [effect]
                        if effect.disposition()
                            == &EffectDisposition::AbsorbedIntoExpression { producer }
                            && effect.expression_evidence().is_some_and(|expression| {
                                expression.entity().producer() == producer
                                    && expression.entity().source_obligations().contains(obligation)
                            })
                ),
                SemanticObligationKind::ObservableMemoryRead
                | SemanticObligationKind::ObservableMemoryWrite => {
                    statements.get(&producer).is_some_and(|statement| {
                        frame_statement_has_exact_ledger_owner(certified, statement, *obligation)
                    }) || (obligation.kind == SemanticObligationKind::ObservableMemoryRead
                        && return_plan.candidates.contains_key(&producer)
                        && is_exact_mechanical_read(
                            certified,
                            producer,
                            outputs.get(&producer).copied(),
                        ))
                }
                _ => false,
            };
            if !valid {
                return Err(SemanticCError::InvalidFrameMechanics(producer));
            }
        }
        owners.push(SemanticCFrameMechanicsOwner {
            source_producer: producer,
            frame_pointer_storage: frame.frame_pointer_storage(),
            saved_range: frame.saved_range(),
            return_producers: return_plan
                .return_order
                .iter()
                .copied()
                .filter(|return_producer| {
                    all_candidate_services
                        .get(&producer)
                        .is_some_and(|served| served.contains(return_producer))
                })
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            source_obligations: instruction
                .obligations
                .iter()
                .copied()
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        });
    }
    if owners.len() != mechanics.len() {
        return Err(SemanticCError::InvalidFrameMechanics(fallback));
    }
    let return_mechanics = return_plan
        .candidates
        .keys()
        .copied()
        .filter(|producer| !semantic.contains(producer) && !mechanics.contains(producer))
        .collect::<BTreeSet<_>>();
    Ok((
        materialize_return_mechanics(certified, return_plan, &return_mechanics, &outputs)?,
        SemanticCFrameMechanicsOwnership {
            owners: owners.into_boxed_slice(),
            authority: Some(SemanticCFrameMechanicsAuthority {
                frame_pointer_storage: frame.frame_pointer_storage(),
                saved_range: frame.saved_range(),
                common_roots,
                return_order: frame_return_order.into_boxed_slice(),
                restore_roots,
                explicit_dependencies,
            }),
        },
    ))
}

impl SemanticCExpressionLayer {
    /// Lower the certified live-value seam into an immutable semantic-C arena.
    ///
    /// Effect, control, return, and loop-state obligations remain open in
    /// `r2cert`; this expression layer cannot authorize a complete C function.
    pub fn from_certified(certified: &CertifiedMachineFunction) -> Result<Self, SemanticCError> {
        Self::from_source(certified)
    }

    /// Lower all supported values from a certified partial machine projection.
    ///
    /// Failed producers and their transitive dependents stay absent from the C
    /// arena and remain explicit in `open_obligations`.
    pub fn from_projection(certified: &CertifiedMachineProjection) -> Result<Self, SemanticCError> {
        Self::from_source(certified)
    }

    pub(crate) fn from_private_frame_conditional_join(
        certified: &CertifiedMachineProjection,
        join: &CertifiedPrivateFrameConditionalJoin,
        stack: &CertifiedStackDiscipline,
    ) -> Result<Self, SemanticCError> {
        let input =
            certified_private_entry_stack_pointer_input(certified, Some(join), Some(stack))?;
        Self::from_source_with_private_entry_stack_pointer(certified, Some(&input))
    }

    fn from_source(certified: &impl CertifiedSemanticSource) -> Result<Self, SemanticCError> {
        Self::from_source_with_private_entry_stack_pointer(certified, None)
    }

    fn from_source_with_private_entry_stack_pointer(
        certified: &impl CertifiedSemanticSource,
        private_entry_stack_pointer: Option<&CertifiedPrivateEntryStackPointerInput>,
    ) -> Result<Self, SemanticCError> {
        let function_interface = semantic_function_interface(certified)?;
        let machine = certified.machine_view();
        let return_plan = derive_return_mechanics_plan(certified)?;
        let (return_mechanics, frame_mechanics) = derive_mechanics(certified, &return_plan)?;
        let mechanical_producers = return_mechanics
            .owners()
            .iter()
            .map(SemanticCReturnMechanicsOwner::source_producer)
            .chain(
                frame_mechanics
                    .owners()
                    .iter()
                    .map(SemanticCFrameMechanicsOwner::source_producer),
            )
            .collect::<BTreeSet<_>>();
        let output_producers = machine.output_producers();
        let certified_producers = machine
            .entities()
            .iter()
            .filter(|entity| !mechanical_producers.contains(&entity.producer()))
            .filter_map(|entity| {
                certified
                    .expression_for_producer(entity.producer())
                    .map(|_| entity.producer())
            })
            .collect::<BTreeSet<_>>();
        let mut root_outputs = BTreeMap::new();
        for entity in machine.entities() {
            if root_outputs
                .insert(entity.root(), (entity.output(), entity.producer()))
                .is_some()
            {
                return Err(SemanticCError::InvalidBitwiseExpression(entity.root()));
            }
        }
        let mut builder = SemanticCBuilder {
            machine,
            output_producers: &output_producers,
            certified_producers: &certified_producers,
            root_outputs,
            translated: BTreeMap::new(),
            expressions: Vec::new(),
            inputs: BTreeMap::new(),
        };
        let mut entities = Vec::new();

        for machine_entity in machine.entities() {
            if mechanical_producers.contains(&machine_entity.producer()) {
                continue;
            }
            let live_obligations = machine_entity
                .source_obligations()
                .iter()
                .copied()
                .filter(|id| id.kind == SemanticObligationKind::LiveValueProducer)
                .collect::<BTreeSet<_>>();
            if live_obligations.is_empty() {
                continue;
            }
            let Some(expression) = certified.expression_for_producer(machine_entity.producer())
            else {
                if live_obligations.iter().all(|obligation| {
                    let effects = certified.ledger().effects(*obligation);
                    effects.len() == 1
                        && matches!(
                            effects[0].disposition(),
                            EffectDisposition::Residualized { .. }
                                | EffectDisposition::Refused { .. }
                        )
                }) {
                    continue;
                }
                return Err(SemanticCError::MissingCertifiedExpression(
                    machine_entity.producer(),
                ));
            };
            if expression.root() != machine_entity.root()
                || expression.entity().producer() != machine_entity.producer()
            {
                return Err(SemanticCError::CertifiedRootMismatch(
                    machine_entity.producer(),
                ));
            }
            if expression.entity().source_obligations() != &live_obligations {
                return Err(SemanticCError::CertifiedSourceMismatch(
                    machine_entity.producer(),
                ));
            }
            for obligation in &live_obligations {
                let [effect] = certified.ledger().effects(*obligation) else {
                    return Err(SemanticCError::MissingCertifiedExpression(
                        machine_entity.producer(),
                    ));
                };
                if effect.disposition()
                    != &(EffectDisposition::AbsorbedIntoExpression {
                        producer: machine_entity.producer(),
                    })
                {
                    return Err(SemanticCError::CertifiedSourceMismatch(
                        machine_entity.producer(),
                    ));
                }
            }

            let root = builder.translate(machine_entity.root())?;
            let mut expected_sources = expression.inputs().clone();
            expected_sources.insert(machine_entity.producer());
            if builder.expressions[root.index()].source_instructions != expected_sources {
                return Err(SemanticCError::CertifiedSourceMismatch(
                    machine_entity.producer(),
                ));
            }
            entities.push(SemanticCEntity {
                output: machine_entity.output(),
                root,
                producer: machine_entity.producer(),
                source_obligations: live_obligations,
            });
        }

        let absorbed_expressions = entities
            .iter()
            .flat_map(|entity| entity.source_obligations.iter().copied())
            .collect::<BTreeSet<_>>();
        let mut mechanical_obligations = return_mechanics.source_obligations();
        mechanical_obligations.extend(frame_mechanics.source_obligations());
        let open_obligations = certified
            .source()
            .obligations()
            .keys()
            .copied()
            .filter(|id| !absorbed_expressions.contains(id) && !mechanical_obligations.contains(id))
            .collect();
        let input_origins = builder
            .inputs
            .iter()
            .map(|(binding, ty)| {
                (
                    *binding,
                    classify_input(
                        *binding,
                        ty,
                        function_interface.as_ref(),
                        private_entry_stack_pointer,
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        if function_interface.is_some()
            && input_origins
                .iter()
                .find(|(_, origin)| matches!(origin, SemanticCInputOrigin::UnclassifiedSource))
                .is_some_and(|(binding, _)| {
                    let _ = binding;
                    true
                })
        {
            let value = input_origins
                .iter()
                .find_map(|(binding, origin)| {
                    matches!(origin, SemanticCInputOrigin::UnclassifiedSource)
                        .then_some(binding.value())
                })
                .ok_or(SemanticCError::InvalidCertifiedFunctionInterface)?;
            return Err(SemanticCError::UnclassifiedSourceInput(value));
        }
        Ok(Self {
            schema_version: SEMANTIC_C_SCHEMA_VERSION,
            scope: SemanticCScope::LiveValueExpressionsOnly,
            identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
            expressions: builder.expressions.into_boxed_slice(),
            entities: entities.into_boxed_slice(),
            function_interface,
            inputs: builder.inputs,
            input_origins,
            return_mechanics,
            frame_mechanics,
            open_obligations,
        })
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> SemanticCScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub fn expr(&self, id: SemanticCExprId) -> Option<&SemanticCExpr> {
        self.expressions.get(id.index())
    }

    pub const fn entities(&self) -> &[SemanticCEntity] {
        &self.entities
    }

    pub const fn function_interface(&self) -> Option<&SemanticCFunctionInterface> {
        self.function_interface.as_ref()
    }

    pub fn entity_for_producer(
        &self,
        producer: CanonicalInstructionId,
    ) -> Option<&SemanticCEntity> {
        self.entities
            .iter()
            .find(|entity| entity.producer == producer)
    }

    pub const fn inputs(&self) -> &BTreeMap<MachineValueBinding, MachineType> {
        &self.inputs
    }

    pub const fn input_origins(&self) -> &BTreeMap<MachineValueBinding, SemanticCInputOrigin> {
        &self.input_origins
    }

    pub(crate) const fn return_mechanics(&self) -> &SemanticCReturnMechanicsOwnership {
        &self.return_mechanics
    }

    pub(crate) const fn frame_mechanics(&self) -> &SemanticCFrameMechanicsOwnership {
        &self.frame_mechanics
    }

    pub const fn open_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.open_obligations
    }

    pub(crate) fn expr_type(&self, id: SemanticCExprId) -> Result<&MachineType, SemanticCError> {
        self.expr(id)
            .map(SemanticCExpr::ty)
            .ok_or(SemanticCError::MissingSemanticExpression(id))
    }

    pub(crate) fn render_expr(
        &self,
        id: SemanticCExprId,
        helpers: &mut SemanticCHelperSet,
    ) -> Result<String, SemanticCError> {
        let rendered = self.render_expr_inner(id, None, helpers)?;
        Ok(rendered.source)
    }

    pub(crate) fn render_return_operand_with_helpers(
        &self,
        operand: SemanticCReturnOperand<'_>,
        helpers: &mut SemanticCHelperSet,
    ) -> Result<String, SemanticCError> {
        match operand {
            SemanticCReturnOperand::Direct(value) => Ok(value_name(value.binding())),
            SemanticCReturnOperand::RegisterComposition(composition) => {
                let total_width = composition.physical_width_bits();
                supported_width(total_width)?;
                let ctype = storage_type(self.expr_type(composition.base.expression())?)?;
                let mut rendered = value_name(composition.base.binding());
                for overlay in composition.overlays() {
                    let width = overlay.definition.binding().width_bits();
                    let lsb_bits = overlay.offset_bytes.checked_mul(8).ok_or(
                        SemanticCError::ReturnBindingMismatch(composition.base.producer()),
                    )?;
                    if width == 0
                        || lsb_bits
                            .checked_add(width)
                            .is_none_or(|end| end > total_width)
                    {
                        return Err(SemanticCError::ReturnBindingMismatch(
                            composition.base.producer(),
                        ));
                    }
                    let helper = SemanticCHelper::BitInsert;
                    helpers.insert(helper);
                    rendered = format!(
                        "{}((uint64_t)({rendered}), (uint64_t)({}), {lsb_bits}U, {width}U, {total_width}U)",
                        helper.call_name(),
                        value_name(overlay.definition.binding())
                    );
                }
                Ok(format!("(({ctype})({rendered}))"))
            }
        }
    }

    fn render_expr_inner(
        &self,
        id: SemanticCExprId,
        substitution: Option<(MachineValueBinding, &str)>,
        helpers: &mut SemanticCHelperSet,
    ) -> Result<RenderedSemanticExpr, SemanticCError> {
        let expr = self
            .expr(id)
            .ok_or(SemanticCError::MissingSemanticExpression(id))?;
        let width = expr.ty.width_bits();
        let ctype = storage_type(&expr.ty)?;
        let mut child = |child| self.render_expr_inner(child, substitution, helpers);
        let rendered = match &expr.kind {
            SemanticCExprKind::Input { binding } => {
                if let Some((expected, replacement)) = substitution
                    && expected == *binding
                {
                    RenderedSemanticExpr {
                        source: replacement.to_string(),
                        substitutions: 1,
                    }
                } else {
                    RenderedSemanticExpr {
                        source: value_name(*binding),
                        substitutions: 0,
                    }
                }
            }
            SemanticCExprKind::Constant { value, .. } => RenderedSemanticExpr {
                source: format!("(({ctype})UINT64_C(0x{:x}))", value.bits()),
                substitutions: 0,
            },
            SemanticCExprKind::MemoryRead { .. } => {
                return Err(SemanticCError::MemoryReadRequiresCertifiedStatement(id));
            }
            SemanticCExprKind::Copy { input } => {
                let input = child(*input)?;
                RenderedSemanticExpr {
                    source: format!("(({ctype})({}))", input.source),
                    substitutions: input.substitutions,
                }
            }
            SemanticCExprKind::Arithmetic {
                op,
                mode: MachineArithmeticMode::Wrapping,
                left,
                right,
            } => {
                let helper = match op {
                    MachineArithmeticOp::Add => SemanticCHelper::WrapAdd,
                    MachineArithmeticOp::Subtract => SemanticCHelper::WrapSub,
                    MachineArithmeticOp::Multiply => SemanticCHelper::WrapMul,
                };
                let left = child(*left)?;
                let right = child(*right)?;
                helpers.insert(helper);
                let helper = helper.call_name();
                RenderedSemanticExpr {
                    source: format!(
                        "(({ctype}){helper}((uint64_t)({}), (uint64_t)({}), {width}U))",
                        left.source, right.source
                    ),
                    substitutions: left.substitutions.saturating_add(right.substitutions),
                }
            }
            SemanticCExprKind::Arithmetic {
                mode: MachineArithmeticMode::Checked,
                ..
            } => return Err(SemanticCError::CheckedArithmeticRequiresHelper(id)),
            SemanticCExprKind::ArithmeticFlag { op, left, right } => {
                if !matches!(expr.ty(), MachineType::Bool { .. }) {
                    return Err(SemanticCError::InvalidArithmeticFlagExpression(id));
                }
                let input_width = self.expr_type(*left)?.width_bits();
                if input_width == 0 || self.expr_type(*right)?.width_bits() != input_width {
                    return Err(SemanticCError::InvalidArithmeticFlagExpression(id));
                }
                let helper = match op {
                    MachineArithmeticFlagOp::UnsignedCarry => SemanticCHelper::UnsignedCarry,
                    MachineArithmeticFlagOp::SignedCarry => SemanticCHelper::SignedCarry,
                    MachineArithmeticFlagOp::SignedBorrow => SemanticCHelper::SignedBorrow,
                };
                let left = child(*left)?;
                let right = child(*right)?;
                helpers.insert(helper);
                let helper = helper.call_name();
                RenderedSemanticExpr {
                    source: format!(
                        "(({ctype}){helper}((uint64_t)({}), (uint64_t)({}), {input_width}U))",
                        left.source, right.source
                    ),
                    substitutions: left.substitutions.saturating_add(right.substitutions),
                }
            }
            SemanticCExprKind::Bitwise { op, left, right } => {
                let operator = match op {
                    MachineBitwiseOp::And => "&",
                    MachineBitwiseOp::Or => "|",
                    MachineBitwiseOp::Xor => "^",
                };
                let left = child(*left)?;
                let right = child(*right)?;
                RenderedSemanticExpr {
                    source: format!(
                        "(({ctype})((uint64_t)({}) {operator} (uint64_t)({})))",
                        left.source, right.source
                    ),
                    substitutions: left.substitutions.saturating_add(right.substitutions),
                }
            }
            SemanticCExprKind::BitwiseNot { input } => {
                let input = child(*input)?;
                RenderedSemanticExpr {
                    source: format!("(({ctype})(~(uint64_t)({})))", input.source),
                    substitutions: input.substitutions,
                }
            }
            SemanticCExprKind::BooleanNot { input } => {
                if !matches!(expr.ty(), MachineType::Bool { .. })
                    || self.expr_type(*input)? != &expr.ty
                {
                    return Err(SemanticCError::InvalidBooleanNotExpression(id));
                }
                let input = child(*input)?;
                RenderedSemanticExpr {
                    source: format!(
                        "(({ctype})(((uint64_t)({}) == UINT64_C(0)) ? 1U : 0U))",
                        input.source
                    ),
                    substitutions: input.substitutions,
                }
            }
            SemanticCExprKind::Boolean { op, left, right } => {
                if !matches!(expr.ty(), MachineType::Bool { .. })
                    || self.expr_type(*left)? != expr.ty()
                    || self.expr_type(*right)? != expr.ty()
                {
                    return Err(SemanticCError::InvalidBooleanExpression(id));
                }
                let left = child(*left)?;
                let right = child(*right)?;
                let condition = match op {
                    MachineBooleanOp::And => format!(
                        "((uint64_t)({}) != UINT64_C(0) && (uint64_t)({}) != UINT64_C(0))",
                        left.source, right.source
                    ),
                    MachineBooleanOp::Or => format!(
                        "((uint64_t)({}) != UINT64_C(0) || (uint64_t)({}) != UINT64_C(0))",
                        left.source, right.source
                    ),
                    MachineBooleanOp::Xor => format!(
                        "(((uint64_t)({}) != UINT64_C(0)) != ((uint64_t)({}) != UINT64_C(0)))",
                        left.source, right.source
                    ),
                };
                RenderedSemanticExpr {
                    source: format!("(({ctype})(({condition}) ? 1U : 0U))"),
                    substitutions: left.substitutions.saturating_add(right.substitutions),
                }
            }
            SemanticCExprKind::Shift {
                kind,
                overshift,
                value,
                count,
            } => {
                let helper = match (kind, overshift) {
                    (MachineShiftKind::Left, MachineOvershiftBehavior::Zero) => {
                        SemanticCHelper::ShiftLeft
                    }
                    (MachineShiftKind::LogicalRight, MachineOvershiftBehavior::Zero) => {
                        SemanticCHelper::LogicalShiftRight
                    }
                    (MachineShiftKind::ArithmeticRight, MachineOvershiftBehavior::SignFill) => {
                        SemanticCHelper::ArithmeticShiftRight
                    }
                    _ => return Err(SemanticCError::UnsupportedShiftPolicy(id)),
                };
                let value = child(*value)?;
                let count = child(*count)?;
                helpers.insert(helper);
                let helper = helper.call_name();
                RenderedSemanticExpr {
                    source: format!(
                        "(({ctype}){helper}((uint64_t)({}), (uint64_t)({}), {width}U))",
                        value.source, count.source
                    ),
                    substitutions: value.substitutions.saturating_add(count.substitutions),
                }
            }
            SemanticCExprKind::Compare {
                op,
                interpretation,
                left,
                right,
            } => {
                let comparison_width = self.expr_type(*left)?.width_bits();
                let left = child(*left)?;
                let right = child(*right)?;
                if *interpretation == MachineSignedness::Signed
                    && matches!(
                        op,
                        MachineComparisonOp::LessThan | MachineComparisonOp::LessThanOrEqual
                    )
                {
                    helpers.insert(SemanticCHelper::SignedKey);
                }
                let signed_key = SemanticCHelper::SignedKey.call_name();
                let condition = match (op, interpretation) {
                    (MachineComparisonOp::Equal, _) => {
                        format!(
                            "((uint64_t)({}) == (uint64_t)({}))",
                            left.source, right.source
                        )
                    }
                    (MachineComparisonOp::NotEqual, _) => {
                        format!(
                            "((uint64_t)({}) != (uint64_t)({}))",
                            left.source, right.source
                        )
                    }
                    (MachineComparisonOp::LessThan, MachineSignedness::Unsigned) => {
                        format!(
                            "((uint64_t)({}) < (uint64_t)({}))",
                            left.source, right.source
                        )
                    }
                    (MachineComparisonOp::LessThanOrEqual, MachineSignedness::Unsigned) => {
                        format!(
                            "((uint64_t)({}) <= (uint64_t)({}))",
                            left.source, right.source
                        )
                    }
                    (MachineComparisonOp::LessThan, MachineSignedness::Signed) => format!(
                        "({signed_key}((uint64_t)({}), {comparison_width}U) < {signed_key}((uint64_t)({}), {comparison_width}U))",
                        left.source, right.source
                    ),
                    (MachineComparisonOp::LessThanOrEqual, MachineSignedness::Signed) => format!(
                        "({signed_key}((uint64_t)({}), {comparison_width}U) <= {signed_key}((uint64_t)({}), {comparison_width}U))",
                        left.source, right.source
                    ),
                };
                RenderedSemanticExpr {
                    source: format!("(({ctype})(({condition}) ? 1U : 0U))"),
                    substitutions: left.substitutions.saturating_add(right.substitutions),
                }
            }
            SemanticCExprKind::Cast { kind, input } => {
                let input_expr = child(*input)?;
                let input_width = self.expr_type(*input)?.width_bits();
                let source = match kind {
                    MachineCastKind::SignExtend => {
                        let helper = SemanticCHelper::SignExtend;
                        helpers.insert(helper);
                        format!(
                            "(({ctype}){}((uint64_t)({}), {input_width}U, {width}U))",
                            helper.call_name(),
                            input_expr.source
                        )
                    }
                    MachineCastKind::ZeroExtend
                    | MachineCastKind::Truncate
                    | MachineCastKind::BitReinterpret
                    | MachineCastKind::IntegerToAddress
                    | MachineCastKind::AddressToInteger => {
                        format!("(({ctype})({}))", input_expr.source)
                    }
                };
                RenderedSemanticExpr {
                    source,
                    substitutions: input_expr.substitutions,
                }
            }
            SemanticCExprKind::Extract { input, lsb_bits } => {
                let input = child(*input)?;
                RenderedSemanticExpr {
                    source: format!("(({ctype})((uint64_t)({}) >> {lsb_bits}U))", input.source),
                    substitutions: input.substitutions,
                }
            }
            SemanticCExprKind::Select {
                condition,
                if_true,
                if_false,
            } => {
                if !matches!(self.expr_type(*condition)?, MachineType::Bool { .. })
                    || self.expr_type(*if_true)? != &expr.ty
                    || self.expr_type(*if_false)? != &expr.ty
                {
                    return Err(SemanticCError::InvalidSelectExpression(id));
                }
                if !matches!(
                    self.expr(*if_true).map(SemanticCExpr::kind),
                    Some(SemanticCExprKind::Input { .. } | SemanticCExprKind::Constant { .. })
                ) || !matches!(
                    self.expr(*if_false).map(SemanticCExpr::kind),
                    Some(SemanticCExprKind::Input { .. } | SemanticCExprKind::Constant { .. })
                ) {
                    return Err(SemanticCError::SelectRequiresValueArmExpression(id));
                }
                let condition = child(*condition)?;
                let if_true = child(*if_true)?;
                let if_false = child(*if_false)?;
                RenderedSemanticExpr {
                    source: format!(
                        "(({ctype})(((uint64_t)({}) != UINT64_C(0)) ? ({}) : ({})))",
                        condition.source, if_true.source, if_false.source
                    ),
                    substitutions: condition
                        .substitutions
                        .saturating_add(if_true.substitutions)
                        .saturating_add(if_false.substitutions),
                }
            }
        };
        Ok(rendered)
    }
}

struct RenderedSemanticExpr {
    source: String,
    substitutions: usize,
}

fn semantic_call_argument_leaf<'a>(
    argument: &CertifiedCallArgument,
    layer: &'a SemanticCExpressionLayer,
) -> Option<&'a SemanticCExpr> {
    let producer = argument.value().producer()?;
    let entity = layer
        .entity_for_producer(producer)
        .filter(|entity| entity.output() == argument.value().binding())?;
    let mut expression = entity.root();
    let mut visited = BTreeSet::new();
    while visited.insert(expression) {
        let semantic = layer.expr(expression)?;
        match semantic.kind() {
            SemanticCExprKind::Copy { input } => expression = *input,
            _ => return Some(semantic),
        }
    }
    None
}

pub(crate) fn semantic_call_from_control(
    call: &CertifiedDirectCall,
    layer: &SemanticCExpressionLayer,
) -> Result<SemanticCDirectCall, SemanticCError> {
    let mut arguments = Vec::with_capacity(call.arguments().len());
    for argument in call.arguments() {
        let value = match argument.origin() {
            CertifiedCallArgumentOrigin::Produced { producer } => {
                if argument.value().producer() != Some(*producer) {
                    return Err(SemanticCError::CallBindingMismatch(call.producer()));
                }
                let entity = layer
                    .entity_for_producer(*producer)
                    .filter(|entity| entity.output() == argument.value().binding())
                    .ok_or(SemanticCError::MissingCallExpression(*producer))?;
                if layer.expr(entity.root()).map(SemanticCExpr::ty) != Some(argument.value().ty()) {
                    return Err(SemanticCError::CallBindingMismatch(call.producer()));
                }
                SemanticCCallArgumentValue::Expression(entity.root())
            }
            CertifiedCallArgumentOrigin::Constant { value }
                if value.width_bits() == argument.value().ty().width_bits()
                    && (argument.value().constant() == Some(*value)
                        || semantic_call_argument_leaf(argument, layer).is_some_and(
                            |expression| {
                                expression.ty() == argument.value().ty()
                                    && matches!(
                                        expression.kind(),
                                        SemanticCExprKind::Constant {
                                            value: expression_value,
                                            ..
                                        } if expression_value == value
                                    )
                            },
                        )) =>
            {
                SemanticCCallArgumentValue::Constant(*value)
            }
            CertifiedCallArgumentOrigin::AbiParameter { index } => {
                let parameter = layer
                    .function_interface()
                    .and_then(|interface| interface.parameters().get(*index as usize))
                    .filter(|parameter| {
                        parameter.index() == *index
                            && parameter.ty() == argument.value().ty()
                            && matches!(
                                argument.slot(),
                                CallBoundarySlot::Register { storage, .. }
                                    if storage == parameter.storage()
                            )
                    })
                    .ok_or(SemanticCError::CallBindingMismatch(call.producer()))?;
                let input = parameter
                    .value()
                    .filter(|input| {
                        *input == argument.value().binding()
                            || semantic_call_argument_leaf(argument, layer).is_some_and(
                                |expression| {
                                    expression.ty() == argument.value().ty()
                                        && matches!(
                                            expression.kind(),
                                            SemanticCExprKind::Input { binding }
                                                if *binding == *input
                                        )
                                },
                            )
                    })
                    .ok_or(SemanticCError::CallBindingMismatch(call.producer()))?;
                SemanticCCallArgumentValue::AbiParameter {
                    index: *index,
                    input,
                }
            }
            _ => return Err(SemanticCError::CallBindingMismatch(call.producer())),
        };
        arguments.push(SemanticCCallArgument {
            slot: argument.slot(),
            binding: argument.value().binding(),
            value,
            ty: argument.value().ty().clone(),
        });
    }
    Ok(SemanticCDirectCall {
        producer: call.producer(),
        call_site: call.call_site(),
        raw_identity: call.raw_identity(),
        interface_revision: call.interface_revision().to_vec().into_boxed_slice(),
        target_binding: call.target_value().binding(),
        target: call.target(),
        fallthrough: call.fallthrough(),
        calling_convention: call.calling_convention().to_string(),
        arguments: arguments.into_boxed_slice(),
        source_obligations: call.source_obligations(),
    })
}

pub(crate) fn semantic_return_from_control(
    control: &CertifiedReturnControl,
    layer: &SemanticCExpressionLayer,
) -> Result<SemanticCReturn, SemanticCError> {
    let interface = layer
        .function_interface()
        .ok_or(SemanticCError::InvalidCertifiedFunctionInterface)?;
    match (
        interface.return_kind(),
        control.values(),
        control.register_compositions(),
    ) {
        (SemanticCFunctionReturn::Void, [], []) => {}
        (SemanticCFunctionReturn::Register { storage, ty }, [returned], [])
            if returned.slot()
                == (CallBoundarySlot::Register {
                    index: 0,
                    storage: *storage,
                })
                && returned.value().ty() == ty => {}
        (SemanticCFunctionReturn::Register { storage, ty }, [], [composition])
            if composition.slot()
                == (CallBoundarySlot::Register {
                    index: 0,
                    storage: *storage,
                })
                && composition.base().storage() == *storage
                && composition.base().value().ty() == ty => {}
        _ => return Err(SemanticCError::ReturnBindingMismatch(control.producer())),
    }
    let mut values = Vec::with_capacity(control.values().len());
    for returned in control.values() {
        let producer = returned
            .value()
            .producer()
            .ok_or(SemanticCError::MissingReturnExpression(control.producer()))?;
        let entity = layer
            .entity_for_producer(producer)
            .filter(|entity| entity.output() == returned.value().binding())
            .ok_or(SemanticCError::MissingReturnExpression(producer))?;
        if layer.expr(entity.root()).map(SemanticCExpr::ty) != Some(returned.value().ty()) {
            return Err(SemanticCError::ReturnBindingMismatch(control.producer()));
        }
        values.push(SemanticCReturnValue {
            slot: returned.slot(),
            binding: returned.value().binding(),
            producer,
            expression: entity.root(),
        });
    }
    let mut register_compositions = Vec::with_capacity(control.register_compositions().len());
    for composition in control.register_compositions() {
        let base = semantic_return_register_definition(composition.base(), layer)?;
        let CallBoundarySlot::Register {
            storage: slot_storage,
            ..
        } = composition.slot()
        else {
            return Err(SemanticCError::ReturnBindingMismatch(control.producer()));
        };
        if base.storage != slot_storage {
            return Err(SemanticCError::ReturnBindingMismatch(control.producer()));
        }
        let mut overlays = Vec::with_capacity(composition.overlays().len());
        for overlay in composition.overlays() {
            let definition = semantic_return_register_definition(overlay.definition(), layer)?;
            if definition.storage.space != base.storage.space
                || definition.storage.offset.checked_sub(base.storage.offset)
                    != Some(u64::from(overlay.offset_bytes()))
                || u64::from(overlay.offset_bytes())
                    .checked_add(u64::from(definition.storage.size))
                    .is_none_or(|end| end > u64::from(base.storage.size))
            {
                return Err(SemanticCError::ReturnBindingMismatch(control.producer()));
            }
            overlays.push(SemanticCReturnRegisterOverlay {
                definition,
                offset_bytes: overlay.offset_bytes(),
            });
        }
        if overlays.is_empty() {
            return Err(SemanticCError::ReturnBindingMismatch(control.producer()));
        }
        register_compositions.push(SemanticCReturnRegisterComposition {
            slot: composition.slot(),
            base,
            overlays: overlays.into_boxed_slice(),
        });
    }
    Ok(SemanticCReturn {
        producer: control.producer(),
        control_target: control.control_target().binding(),
        values: values.into_boxed_slice(),
        register_compositions: register_compositions.into_boxed_slice(),
        source_obligations: control.source_obligations(),
    })
}

fn semantic_return_register_definition(
    definition: &CertifiedReturnRegisterDefinition,
    layer: &SemanticCExpressionLayer,
) -> Result<SemanticCReturnRegisterDefinition, SemanticCError> {
    let producer = definition.producer();
    if definition.value().producer() != Some(producer)
        || definition.storage().size.checked_mul(8)
            != Some(definition.value().binding().width_bits())
    {
        return Err(SemanticCError::ReturnBindingMismatch(producer));
    }
    let entity = layer
        .entity_for_producer(producer)
        .filter(|entity| entity.output() == definition.value().binding())
        .ok_or(SemanticCError::MissingReturnExpression(producer))?;
    if layer.expr(entity.root()).map(SemanticCExpr::ty) != Some(definition.value().ty()) {
        return Err(SemanticCError::ReturnBindingMismatch(producer));
    }
    Ok(SemanticCReturnRegisterDefinition {
        storage: definition.storage(),
        binding: definition.value().binding(),
        producer,
        expression: entity.root(),
    })
}

struct SemanticCBuilder<'a> {
    machine: MachineView<'a>,
    output_producers: &'a BTreeMap<ValueId, CanonicalInstructionId>,
    certified_producers: &'a BTreeSet<CanonicalInstructionId>,
    root_outputs: BTreeMap<MachineExprId, (MachineValueBinding, CanonicalInstructionId)>,
    translated: BTreeMap<MachineExprId, SemanticCExprId>,
    expressions: Vec<SemanticCExpr>,
    inputs: BTreeMap<MachineValueBinding, MachineType>,
}

fn exact_self_xor_zero_value(
    machine_id: MachineExprId,
    output_ty: &MachineType,
    input_ty: &MachineType,
    binding_width_bits: u32,
) -> Result<MachineBitVector, SemanticCError> {
    if !matches!(output_ty, MachineType::Integer { .. })
        || input_ty != output_ty
        || binding_width_bits != output_ty.width_bits()
    {
        return Err(SemanticCError::InvalidBitwiseExpression(machine_id));
    }
    MachineBitVector::zero(binding_width_bits)
        .ok_or(SemanticCError::InvalidBitwiseExpression(machine_id))
}

impl SemanticCBuilder<'_> {
    fn exact_self_xor_zero(
        &self,
        machine_id: MachineExprId,
        machine_expr: &MachineExpr,
    ) -> Result<Option<(MachineExprId, MachineValueBinding, MachineBitVector)>, SemanticCError>
    {
        let MachineExprKind::Bitwise {
            op: MachineBitwiseOp::Xor,
            left,
            right,
        } = machine_expr.kind()
        else {
            return Ok(None);
        };
        if left != right {
            return Ok(None);
        }
        let child = self
            .machine
            .expr(*left)
            .ok_or(SemanticCError::MissingMachineExpression(*left))?;
        let (binding, producer) = self
            .root_outputs
            .get(&machine_id)
            .copied()
            .ok_or(SemanticCError::InvalidBitwiseExpression(machine_id))?;
        if machine_expr.origin() != Some(producer) {
            return Err(SemanticCError::InvalidBitwiseExpression(machine_id));
        }
        let value = exact_self_xor_zero_value(
            machine_id,
            machine_expr.ty(),
            child.ty(),
            binding.width_bits(),
        )?;
        Ok(Some((*left, binding, value)))
    }

    fn collect_sources_without_translation(
        &self,
        root: MachineExprId,
        source_instructions: &mut BTreeSet<CanonicalInstructionId>,
    ) -> Result<(), SemanticCError> {
        let mut pending = vec![root];
        let mut visited = BTreeSet::new();
        while let Some(machine_id) = pending.pop() {
            if !visited.insert(machine_id) {
                continue;
            }
            let expression = self
                .machine
                .expr(machine_id)
                .ok_or(SemanticCError::MissingMachineExpression(machine_id))?;
            supported_width(expression.ty().width_bits())?;
            if let Some(origin) = expression.origin() {
                source_instructions.insert(origin);
            }
            match expression.kind() {
                MachineExprKind::Source { binding } => {
                    if let Some(dependency) = self.output_producers.get(&binding.value()).copied() {
                        if !self.certified_producers.contains(&dependency) {
                            return Err(SemanticCError::UncertifiedDependency {
                                producer: expression.origin().unwrap_or(dependency),
                                dependency,
                            });
                        }
                        source_instructions.insert(dependency);
                    }
                }
                MachineExprKind::Constant { .. } => {}
                MachineExprKind::MemoryRead { address, .. } => pending.push(*address),
                MachineExprKind::Copy { input }
                | MachineExprKind::BitwiseNot { input }
                | MachineExprKind::BooleanNot { input }
                | MachineExprKind::Cast { input, .. }
                | MachineExprKind::Extract { input, .. } => pending.push(*input),
                MachineExprKind::Arithmetic { left, right, .. }
                | MachineExprKind::ArithmeticFlag { left, right, .. }
                | MachineExprKind::Bitwise { left, right, .. }
                | MachineExprKind::Boolean { left, right, .. }
                | MachineExprKind::Compare { left, right, .. } => {
                    pending.push(*left);
                    pending.push(*right);
                }
                MachineExprKind::Shift { value, count, .. } => {
                    pending.push(*value);
                    pending.push(*count);
                }
                MachineExprKind::Select {
                    condition,
                    if_true,
                    if_false,
                } => {
                    pending.push(*condition);
                    pending.push(*if_true);
                    pending.push(*if_false);
                }
                MachineExprKind::Phi { .. } => {
                    return Err(SemanticCError::PhiRequiresCertifiedStructuring(
                        expression.origin(),
                    ));
                }
            }
        }
        Ok(())
    }

    fn translate(&mut self, machine_id: MachineExprId) -> Result<SemanticCExprId, SemanticCError> {
        if let Some(id) = self.translated.get(&machine_id).copied() {
            return Ok(id);
        }
        let machine_expr = self
            .machine
            .expr(machine_id)
            .ok_or(SemanticCError::MissingMachineExpression(machine_id))?;
        supported_width(machine_expr.ty().width_bits())?;
        if let MachineExprKind::Phi { .. } = machine_expr.kind() {
            return Err(SemanticCError::PhiRequiresCertifiedStructuring(
                machine_expr.origin(),
            ));
        }

        let mut source_instructions = BTreeSet::new();
        if let Some(origin) = machine_expr.origin() {
            source_instructions.insert(origin);
        }
        let kind = match machine_expr.kind() {
            MachineExprKind::Source { binding } => {
                if let Some(dependency) = self.output_producers.get(&binding.value()).copied() {
                    if !self.certified_producers.contains(&dependency) {
                        let producer = machine_expr.origin().unwrap_or(dependency);
                        return Err(SemanticCError::UncertifiedDependency {
                            producer,
                            dependency,
                        });
                    }
                    source_instructions.insert(dependency);
                } else if let Some(existing) =
                    self.inputs.insert(*binding, machine_expr.ty().clone())
                    && existing != *machine_expr.ty()
                {
                    return Err(SemanticCError::InconsistentInputType(binding.value()));
                }
                SemanticCExprKind::Input { binding: *binding }
            }
            MachineExprKind::Constant { binding, value } => SemanticCExprKind::Constant {
                binding: *binding,
                value: *value,
            },
            MachineExprKind::MemoryRead {
                access,
                object,
                space,
                endianness,
                word_size_bytes,
                address,
                width_bits,
            } => SemanticCExprKind::MemoryRead {
                access: *access,
                object: *object,
                space: *space,
                endianness: *endianness,
                word_size_bytes: *word_size_bytes,
                address: self.translate_child(*address, &mut source_instructions)?,
                width_bits: *width_bits,
            },
            MachineExprKind::Copy { input } => SemanticCExprKind::Copy {
                input: self.translate_child(*input, &mut source_instructions)?,
            },
            MachineExprKind::Arithmetic {
                op,
                mode,
                left,
                right,
            } => SemanticCExprKind::Arithmetic {
                op: *op,
                mode: *mode,
                left: self.translate_child(*left, &mut source_instructions)?,
                right: self.translate_child(*right, &mut source_instructions)?,
            },
            MachineExprKind::ArithmeticFlag { op, left, right } => {
                if !matches!(machine_expr.ty(), MachineType::Bool { .. }) {
                    return Err(SemanticCError::InvalidArithmeticFlagExpression(
                        SemanticCExprId(u32::MAX),
                    ));
                }
                SemanticCExprKind::ArithmeticFlag {
                    op: *op,
                    left: self.translate_child(*left, &mut source_instructions)?,
                    right: self.translate_child(*right, &mut source_instructions)?,
                }
            }
            MachineExprKind::Bitwise { op, left, right } => {
                if let Some((input, binding, value)) =
                    self.exact_self_xor_zero(machine_id, machine_expr)?
                {
                    self.collect_sources_without_translation(input, &mut source_instructions)?;
                    SemanticCExprKind::Constant { binding, value }
                } else {
                    SemanticCExprKind::Bitwise {
                        op: *op,
                        left: self.translate_child(*left, &mut source_instructions)?,
                        right: self.translate_child(*right, &mut source_instructions)?,
                    }
                }
            }
            MachineExprKind::BitwiseNot { input } => SemanticCExprKind::BitwiseNot {
                input: self.translate_child(*input, &mut source_instructions)?,
            },
            MachineExprKind::BooleanNot { input } => {
                let output_ty = machine_expr.ty().clone();
                let input_ty = self
                    .machine
                    .expr(*input)
                    .ok_or(SemanticCError::MissingMachineExpression(*input))?
                    .ty()
                    .clone();
                validate_boolean_not_types(machine_id, &output_ty, &input_ty)?;
                let input = self.translate_child(*input, &mut source_instructions)?;
                if self.expressions[input.index()].ty != output_ty {
                    return Err(SemanticCError::InvalidBooleanNotType(machine_id));
                }
                SemanticCExprKind::BooleanNot { input }
            }
            MachineExprKind::Boolean { op, left, right } => {
                let output_ty = machine_expr.ty().clone();
                if !matches!(output_ty, MachineType::Bool { .. })
                    || self
                        .machine
                        .expr(*left)
                        .is_none_or(|input| input.ty() != &output_ty)
                    || self
                        .machine
                        .expr(*right)
                        .is_none_or(|input| input.ty() != &output_ty)
                {
                    return Err(SemanticCError::InvalidBooleanExpression(SemanticCExprId(
                        u32::MAX,
                    )));
                }
                SemanticCExprKind::Boolean {
                    op: *op,
                    left: self.translate_child(*left, &mut source_instructions)?,
                    right: self.translate_child(*right, &mut source_instructions)?,
                }
            }
            MachineExprKind::Shift {
                kind,
                overshift,
                value,
                count,
            } => SemanticCExprKind::Shift {
                kind: *kind,
                overshift: *overshift,
                value: self.translate_child(*value, &mut source_instructions)?,
                count: self.translate_child(*count, &mut source_instructions)?,
            },
            MachineExprKind::Compare {
                op,
                interpretation,
                left,
                right,
            } => SemanticCExprKind::Compare {
                op: *op,
                interpretation: *interpretation,
                left: self.translate_child(*left, &mut source_instructions)?,
                right: self.translate_child(*right, &mut source_instructions)?,
            },
            MachineExprKind::Cast { kind, input } => SemanticCExprKind::Cast {
                kind: *kind,
                input: self.translate_child(*input, &mut source_instructions)?,
            },
            MachineExprKind::Extract { input, lsb_bits } => SemanticCExprKind::Extract {
                input: self.translate_child(*input, &mut source_instructions)?,
                lsb_bits: *lsb_bits,
            },
            MachineExprKind::Select {
                condition,
                if_true,
                if_false,
            } => {
                let output_ty = machine_expr.ty().clone();
                let condition_ty = self
                    .machine
                    .expr(*condition)
                    .ok_or(SemanticCError::MissingMachineExpression(*condition))?
                    .ty()
                    .clone();
                let if_true_ty = self
                    .machine
                    .expr(*if_true)
                    .ok_or(SemanticCError::MissingMachineExpression(*if_true))?
                    .ty()
                    .clone();
                let if_false_ty = self
                    .machine
                    .expr(*if_false)
                    .ok_or(SemanticCError::MissingMachineExpression(*if_false))?
                    .ty()
                    .clone();
                validate_select_types(
                    machine_id,
                    &output_ty,
                    &condition_ty,
                    &if_true_ty,
                    &if_false_ty,
                )?;
                let condition = self.translate_child(*condition, &mut source_instructions)?;
                let if_true = self.translate_child(*if_true, &mut source_instructions)?;
                let if_false = self.translate_child(*if_false, &mut source_instructions)?;
                if !matches!(
                    self.expressions[condition.index()].ty,
                    MachineType::Bool { .. }
                ) || self.expressions[if_true.index()].ty != output_ty
                    || self.expressions[if_false.index()].ty != output_ty
                {
                    return Err(SemanticCError::InvalidSelectType(machine_id));
                }
                require_select_value_arms(machine_id, &self.expressions, if_true, if_false)?;
                // Arms are already-produced values. Their entities execute in
                // certified source order before this pure, lazy C ternary.
                SemanticCExprKind::Select {
                    condition,
                    if_true,
                    if_false,
                }
            }
            MachineExprKind::Phi { .. } => unreachable!(),
        };
        let id = SemanticCExprId(self.expressions.len() as u32);
        self.expressions.push(SemanticCExpr {
            ty: machine_expr.ty().clone(),
            source_instructions,
            kind,
        });
        self.translated.insert(machine_id, id);
        Ok(id)
    }

    fn translate_child(
        &mut self,
        child: MachineExprId,
        sources: &mut BTreeSet<CanonicalInstructionId>,
    ) -> Result<SemanticCExprId, SemanticCError> {
        let child = self.translate(child)?;
        sources.extend(
            self.expressions[child.index()]
                .source_instructions
                .iter()
                .copied(),
        );
        Ok(child)
    }
}

fn validate_boolean_not_types(
    machine_id: MachineExprId,
    output: &MachineType,
    input: &MachineType,
) -> Result<(), SemanticCError> {
    if matches!(output, MachineType::Bool { .. }) && input == output {
        Ok(())
    } else {
        Err(SemanticCError::InvalidBooleanNotType(machine_id))
    }
}

fn validate_select_types(
    machine_id: MachineExprId,
    output: &MachineType,
    condition: &MachineType,
    if_true: &MachineType,
    if_false: &MachineType,
) -> Result<(), SemanticCError> {
    if matches!(condition, MachineType::Bool { .. }) && if_true == output && if_false == output {
        Ok(())
    } else {
        Err(SemanticCError::InvalidSelectType(machine_id))
    }
}

fn require_select_value_arms(
    machine_id: MachineExprId,
    expressions: &[SemanticCExpr],
    if_true: SemanticCExprId,
    if_false: SemanticCExprId,
) -> Result<(), SemanticCError> {
    let is_value = |id: SemanticCExprId| {
        expressions.get(id.index()).is_some_and(|expression| {
            matches!(
                expression.kind,
                SemanticCExprKind::Input { .. } | SemanticCExprKind::Constant { .. }
            )
        })
    };
    if is_value(if_true) && is_value(if_false) {
        Ok(())
    } else {
        Err(SemanticCError::SelectRequiresValueArms(machine_id))
    }
}

fn supported_width(width: u32) -> Result<(), SemanticCError> {
    if matches!(width, 8 | 16 | 32 | 64) {
        Ok(())
    } else {
        Err(SemanticCError::InvalidWidth(width))
    }
}

pub(crate) fn storage_type(ty: &MachineType) -> Result<&'static str, SemanticCError> {
    supported_width(ty.width_bits())?;
    // Machine values are stored as unsigned bit patterns. Signedness and
    // address interpretation remain in the AST and are applied by explicit
    // operations, so ordinary C arithmetic cannot introduce signed UB.
    match ty.width_bits() {
        8 => Ok("uint8_t"),
        16 => Ok("uint16_t"),
        32 => Ok("uint32_t"),
        64 => Ok("uint64_t"),
        width => Err(SemanticCError::InvalidWidth(width)),
    }
}

pub(crate) fn value_name(binding: MachineValueBinding) -> String {
    format!("v_{}", binding.value().0)
}

const SEMANTIC_C_MASK_HELPER: &str = r#"static inline uint64_t r2s_mask(unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	return width >= 64U ? UINT64_MAX : ((UINT64_C(1) << width) - UINT64_C(1));
}
"#;

const SEMANTIC_C_BIT_INSERT_HELPER: &str = r#"static inline uint64_t r2s_bit_insert(uint64_t base, uint64_t value, unsigned lsb, unsigned width, unsigned total_width) {
	uint64_t value_mask = r2s_mask(width);
	uint64_t field_mask = value_mask << lsb;
	return ((base & ~field_mask) | ((value & value_mask) << lsb)) & r2s_mask(total_width);
}
"#;

const SEMANTIC_C_I8_FROM_BITS_HELPER: &str = r#"static inline int8_t r2s_i8_from_bits(uint8_t bits) {
	return bits <= INT8_MAX ? (int8_t)bits : (int8_t)(-INT8_C(1) - (int16_t)(UINT8_MAX - bits));
}
"#;

const SEMANTIC_C_I16_FROM_BITS_HELPER: &str = r#"static inline int16_t r2s_i16_from_bits(uint16_t bits) {
	return bits <= INT16_MAX ? (int16_t)bits : (int16_t)(-INT16_C(1) - (int32_t)(UINT16_MAX - bits));
}
"#;

const SEMANTIC_C_I32_FROM_BITS_HELPER: &str = r#"static inline int32_t r2s_i32_from_bits(uint32_t bits) {
	return bits <= INT32_MAX ? (int32_t)bits : (int32_t)(-INT32_C(1) - (int64_t)(UINT32_MAX - bits));
}
"#;

const SEMANTIC_C_I64_FROM_BITS_HELPER: &str = r#"static inline int64_t r2s_i64_from_bits(uint64_t bits) {
	return bits <= INT64_MAX ? (int64_t)bits : -INT64_C(1) - (int64_t)(UINT64_MAX - bits);
}
"#;

const SEMANTIC_C_WRAP_ADD_HELPER: &str = r#"static inline uint64_t r2s_wrap_add(uint64_t left, uint64_t right, unsigned width) {
	return (left + right) & r2s_mask(width);
}
"#;

const SEMANTIC_C_WRAP_SUB_HELPER: &str = r#"static inline uint64_t r2s_wrap_sub(uint64_t left, uint64_t right, unsigned width) {
	return (left - right) & r2s_mask(width);
}
"#;

const SEMANTIC_C_WRAP_MUL_HELPER: &str = r#"static inline uint64_t r2s_wrap_mul(uint64_t left, uint64_t right, unsigned width) {
	return (left * right) & r2s_mask(width);
}
"#;

const SEMANTIC_C_UCARRY_HELPER: &str = r#"static inline uint64_t r2s_ucarry(uint64_t left, uint64_t right, unsigned width) {
	uint64_t mask = r2s_mask(width);
	left &= mask;
	right &= mask;
	return left > (mask - right) ? UINT64_C(1) : UINT64_C(0);
}
"#;

const SEMANTIC_C_SCARRY_HELPER: &str = r#"static inline uint64_t r2s_scarry(uint64_t left, uint64_t right, unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	if (width > 64U) {
		width = 64U;
	}
	uint64_t mask = r2s_mask(width);
	uint64_t sign = UINT64_C(1) << (width - 1U);
	left &= mask;
	right &= mask;
	uint64_t result = (left + right) & mask;
	return ((~(left ^ right) & (left ^ result) & sign) != 0U) ? UINT64_C(1) : UINT64_C(0);
}
"#;

const SEMANTIC_C_SBORROW_HELPER: &str = r#"static inline uint64_t r2s_sborrow(uint64_t left, uint64_t right, unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	if (width > 64U) {
		width = 64U;
	}
	uint64_t mask = r2s_mask(width);
	uint64_t sign = UINT64_C(1) << (width - 1U);
	left &= mask;
	right &= mask;
	uint64_t result = (left - right) & mask;
	return (((left ^ right) & (left ^ result) & sign) != 0U) ? UINT64_C(1) : UINT64_C(0);
}
"#;

const SEMANTIC_C_SHL_HELPER: &str = r#"static inline uint64_t r2s_shl(uint64_t value, uint64_t count, unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	if (width > 64U) {
		width = 64U;
	}
	return count >= width ? UINT64_C(0) : ((value << count) & r2s_mask(width));
}
"#;

const SEMANTIC_C_LSHR_HELPER: &str = r#"static inline uint64_t r2s_lshr(uint64_t value, uint64_t count, unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	if (width > 64U) {
		width = 64U;
	}
	return count >= width ? UINT64_C(0) : ((value & r2s_mask(width)) >> count);
}
"#;

const SEMANTIC_C_ASHR_HELPER: &str = r#"static inline uint64_t r2s_ashr(uint64_t value, uint64_t count, unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	if (width > 64U) {
		width = 64U;
	}
	uint64_t mask = r2s_mask(width);
	uint64_t sign = UINT64_C(1) << (width - 1U);
	value &= mask;
	if (count >= width) {
		return (value & sign) != 0U ? mask : UINT64_C(0);
	}
	if (count == 0U) {
		return value;
	}
	uint64_t result = value >> count;
	if ((value & sign) != 0U) {
		result |= mask ^ ((UINT64_C(1) << (width - count)) - UINT64_C(1));
	}
	return result & mask;
}
"#;

const SEMANTIC_C_SIGNED_KEY_HELPER: &str = r#"static inline uint64_t r2s_signed_key(uint64_t value, unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	if (width > 64U) {
		width = 64U;
	}
	return (value & r2s_mask(width)) ^ (UINT64_C(1) << (width - 1U));
}
"#;

const SEMANTIC_C_SEXT_HELPER: &str = r#"static inline uint64_t r2s_sext(uint64_t value, unsigned from_width, unsigned to_width) {
	if (from_width == 0U || to_width == 0U) {
		return UINT64_C(0);
	}
	if (from_width > 64U) {
		from_width = 64U;
	}
	if (to_width > 64U) {
		to_width = 64U;
	}
	uint64_t from_mask = r2s_mask(from_width);
	uint64_t to_mask = r2s_mask(to_width);
	if (to_width <= from_width) {
		return value & to_mask;
	}
	uint64_t sign = UINT64_C(1) << (from_width - 1U);
	value &= from_mask;
	return ((value & sign) != 0U ? (value | (to_mask ^ from_mask)) : value) & to_mask;
}
"#;

pub(crate) fn insert_semantic_c_helpers(
    output: &mut String,
    insertion: usize,
    helpers: &SemanticCHelperSet,
) {
    debug_assert!(insertion <= output.len() && output.is_char_boundary(insertion));
    output.insert_str(insertion, &helpers.definitions());
}

#[cfg(test)]
mod return_mechanics_tests {
    use super::*;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
    use r2ssa::{
        CanonicalInstructionSite, CanonicalStorageSpace, SourceLogicalValue, SourceType,
        SourceTypeGraph, SsaArtifact,
    };

    fn id(ordinal: u64) -> CanonicalInstructionId {
        CanonicalInstructionId {
            block_addr: 0x1000,
            site: CanonicalInstructionSite::Op(ordinal),
        }
    }

    fn block_id(block_addr: u64, ordinal: u64) -> CanonicalInstructionId {
        CanonicalInstructionId {
            block_addr,
            site: CanonicalInstructionSite::Op(ordinal),
        }
    }

    fn translate_projection_root(
        projection: &MachineProjection,
        producer: CanonicalInstructionId,
    ) -> (SemanticCExpr, BTreeMap<MachineValueBinding, MachineType>) {
        let output_producers = MachineView(projection).output_producers();
        let certified_producers = projection
            .entities()
            .iter()
            .map(MachineEntity::producer)
            .collect::<BTreeSet<_>>();
        let root_outputs = projection
            .entities()
            .iter()
            .map(|entity| (entity.root(), (entity.output(), entity.producer())))
            .collect();
        let root = projection
            .entity_for_producer(producer)
            .expect("translated producer")
            .root();
        let mut builder = SemanticCBuilder {
            machine: MachineView(projection),
            output_producers: &output_producers,
            certified_producers: &certified_producers,
            root_outputs,
            translated: BTreeMap::new(),
            expressions: Vec::new(),
            inputs: BTreeMap::new(),
        };
        let translated = builder.translate(root).expect("semantic translation");
        (
            builder.expressions[translated.index()].clone(),
            builder.inputs,
        )
    }

    fn xor_projection(
        width_bytes: u32,
        left: Varnode,
        right: Varnode,
    ) -> (MachineProjection, CanonicalInstructionId) {
        let block_addr = 0x4200 + u64::from(width_bytes);
        let mut block = R2ILBlock::new(block_addr, 4);
        block.push(R2ILOp::IntXor {
            dst: Varnode::unique(0x100, width_bytes),
            a: left,
            b: right,
        });
        let artifact = SsaArtifact::raw(&[block], None).expect("self-XOR SSA artifact");
        (
            MachineProjection::from_artifact(&artifact).expect("self-XOR machine projection"),
            block_id(block_addr, 0),
        )
    }

    #[test]
    fn exact_self_xor_becomes_bound_zero_without_source_input() {
        for width_bytes in [1, 2, 4, 8] {
            let source = Varnode::register(0, width_bytes);
            let (projection, producer) = xor_projection(width_bytes, source.clone(), source);
            let expected_binding = projection
                .entity_for_producer(producer)
                .expect("self-XOR entity")
                .output();
            let (expression, inputs) = translate_projection_root(&projection, producer);

            assert_eq!(
                expression.source_instructions(),
                &BTreeSet::from([producer])
            );
            assert!(inputs.is_empty());
            assert!(matches!(
                expression.kind(),
                SemanticCExprKind::Constant { binding, value }
                    if *binding == expected_binding
                        && value.width_bits() == width_bytes * 8
                        && value.bits() == 0
            ));
        }
    }

    #[test]
    fn self_xor_retains_exact_child_and_result_producers() {
        let block_addr = 0x4210;
        let copied = Varnode::unique(0x80, 4);
        let mut block = R2ILBlock::new(block_addr, 4);
        block.push(R2ILOp::Copy {
            dst: copied.clone(),
            src: Varnode::register(0, 4),
        });
        block.push(R2ILOp::IntXor {
            dst: Varnode::unique(0x100, 4),
            a: copied.clone(),
            b: copied,
        });
        let artifact = SsaArtifact::raw(&[block], None).expect("dependent self-XOR artifact");
        let projection =
            MachineProjection::from_artifact(&artifact).expect("dependent self-XOR projection");
        let producer = block_id(block_addr, 1);
        let (expression, inputs) = translate_projection_root(&projection, producer);

        assert_eq!(
            expression.source_instructions(),
            &BTreeSet::from([block_id(block_addr, 0), producer])
        );
        assert!(inputs.is_empty());
        assert!(matches!(
            expression.kind(),
            SemanticCExprKind::Constant { value, .. } if value.bits() == 0
        ));
    }

    #[test]
    fn distinct_xor_inputs_are_not_annihilated() {
        let (projection, producer) =
            xor_projection(4, Varnode::register(0, 4), Varnode::register(8, 4));
        let (expression, inputs) = translate_projection_root(&projection, producer);

        assert!(matches!(
            expression.kind(),
            SemanticCExprKind::Bitwise {
                op: MachineBitwiseOp::Xor,
                left,
                right,
            } if left != right
        ));
        assert_eq!(inputs.len(), 2);
    }

    #[test]
    fn self_xor_type_and_width_mutations_refuse() {
        let source = Varnode::register(0, 4);
        let (projection, producer) = xor_projection(4, source.clone(), source);
        let expression = projection
            .entity_for_producer(producer)
            .expect("self-XOR entity")
            .root();
        let unsigned32 = MachineType::Integer {
            width_bits: 32,
            signedness: MachineSignedness::Unsigned,
        };
        let unsigned64 = MachineType::Integer {
            width_bits: 64,
            signedness: MachineSignedness::Unsigned,
        };
        let address32 = MachineType::Address {
            width_bits: 32,
            space: r2ssa::MachineAddressSpace::Ram,
            provenance: MachineAddressProvenance::Unknown,
        };

        assert!(matches!(
            exact_self_xor_zero_value(expression, &unsigned32, &unsigned64, 32),
            Err(SemanticCError::InvalidBitwiseExpression(id)) if id == expression
        ));
        assert!(matches!(
            exact_self_xor_zero_value(expression, &unsigned32, &unsigned32, 64),
            Err(SemanticCError::InvalidBitwiseExpression(id)) if id == expression
        ));
        assert!(matches!(
            exact_self_xor_zero_value(expression, &address32, &address32, 32),
            Err(SemanticCError::InvalidBitwiseExpression(id)) if id == expression
        ));
    }

    fn logical_return_interface(
        kind: SourceTypeKind,
        carrier_kind: SourceCarrierKind,
        carrier_bits: u64,
    ) -> SourceFunctionInterface {
        let storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        SourceFunctionInterface::new_with_logical_types(
            b"logical-return-projection:v1".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Register { storage },
            [],
            [],
            Some(SourceLogicalValue::new(
                0,
                SourceCarrierProjection::new(carrier_kind, 0, carrier_bits),
            )),
            Some(
                SourceTypeGraph::new([SourceType::new(0, kind, carrier_bits, carrier_bits)], [])
                    .expect("scalar source type"),
            ),
        )
        .expect("coherent logical return interface")
    }

    #[test]
    fn exact_logical_return_projection_preserves_physical_and_logical_widths() {
        let storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let unsigned = logical_return_interface(
            SourceTypeKind::UnsignedInteger,
            SourceCarrierKind::LowBits,
            32,
        );
        let projection = exact_semantic_return_projection(&unsigned, storage)
            .expect("valid unsigned projection")
            .expect("logical return projection");
        assert_eq!(projection.physical_ty().width_bits(), 64);
        assert_eq!(
            projection.logical_ty(),
            &MachineType::Integer {
                width_bits: 32,
                signedness: MachineSignedness::Unsigned,
            }
        );

        let signed = logical_return_interface(
            SourceTypeKind::SignedInteger,
            SourceCarrierKind::LowBits,
            32,
        );
        assert_eq!(
            exact_semantic_return_projection(&signed, storage)
                .expect("valid signed projection")
                .expect("logical return projection")
                .logical_ty(),
            &MachineType::Integer {
                width_bits: 32,
                signedness: MachineSignedness::Signed,
            }
        );

        let full =
            logical_return_interface(SourceTypeKind::UnsignedInteger, SourceCarrierKind::Full, 64);
        assert_eq!(
            exact_semantic_return_projection(&full, storage)
                .expect("valid full-width projection")
                .expect("logical return projection")
                .logical_ty()
                .width_bits(),
            64
        );
    }

    fn semantic_return_interface(
        kind: SourceTypeKind,
        carrier_kind: SourceCarrierKind,
        carrier_bits: u64,
    ) -> SemanticCFunctionInterface {
        let source = logical_return_interface(kind, carrier_kind, carrier_bits);
        let SourceFunctionReturn::Register { storage } = source.return_kind() else {
            unreachable!("logical return fixture is register-backed")
        };
        let projection = exact_semantic_return_projection(&source, storage)
            .expect("valid return projection")
            .expect("logical return projection");
        SemanticCFunctionInterface {
            revision_identity: source.revision_identity().into(),
            calling_convention: source.calling_convention().to_string(),
            parameters: Box::new([]),
            return_kind: SemanticCFunctionReturn::Register {
                storage,
                ty: projection.physical_ty().clone(),
            },
            return_projection: Some(projection),
            stack_slots: Box::new([]),
        }
    }

    #[test]
    fn shared_logical_return_renderer_is_exact_for_every_certified_route() {
        let mut helpers = SemanticCHelperSet::default();
        let unsigned = semantic_return_interface(
            SourceTypeKind::UnsignedInteger,
            SourceCarrierKind::LowBits,
            32,
        );
        assert_eq!(logical_return_type(&unsigned), Ok("uint32_t"));
        assert_eq!(
            render_logical_return_statement(&unsigned, Some("v_7"), &mut helpers),
            Ok("return (uint32_t)(v_7);".to_string())
        );
        assert!(helpers.definitions().is_empty());

        let signed = semantic_return_interface(
            SourceTypeKind::SignedInteger,
            SourceCarrierKind::LowBits,
            32,
        );
        assert_eq!(logical_return_type(&signed), Ok("int32_t"));
        assert_eq!(
            render_logical_return_statement(&signed, Some("v_7"), &mut helpers),
            Ok("return r2s_i32_from_bits((uint32_t)(v_7));".to_string())
        );
        assert!(
            helpers
                .definitions()
                .contains("static inline int32_t r2s_i32_from_bits")
        );

        let void = SemanticCFunctionInterface {
            revision_identity: b"void-return:v1".to_vec().into_boxed_slice(),
            calling_convention: "test-abi".to_string(),
            parameters: Box::new([]),
            return_kind: SemanticCFunctionReturn::Void,
            return_projection: None,
            stack_slots: Box::new([]),
        };
        assert_eq!(logical_return_type(&void), Ok("void"));
        assert_eq!(
            render_logical_return_statement(&void, None, &mut helpers),
            Ok("return;".to_string())
        );
        assert_eq!(
            render_logical_return_statement(&void, Some("v_1"), &mut helpers),
            Err(SemanticCError::InvalidReturnProjection)
        );

        let mut missing = signed;
        missing.return_projection = None;
        assert_eq!(
            logical_return_type(&missing),
            Err(SemanticCError::InvalidReturnProjection)
        );
        assert_eq!(
            render_logical_return_statement(&missing, Some("v_7"), &mut helpers),
            Err(SemanticCError::InvalidReturnProjection)
        );
    }

    #[test]
    fn typed_helper_inventory_emits_zero_helpers_for_empty_set() {
        assert!(SemanticCHelperSet::default().definitions().is_empty());
    }

    #[test]
    fn typed_helper_inventory_does_not_infer_dependencies_from_c_text() {
        let mut output = "/* r2s_wrap_add( is not authority */\nvoid f(void) {}\n".to_string();
        let expected = output.clone();
        insert_semantic_c_helpers(&mut output, 0, &SemanticCHelperSet::default());
        assert_eq!(output, expected);
    }

    #[test]
    fn typed_helper_inventory_emits_only_selected_signed_families_in_order() {
        let mut helpers = SemanticCHelperSet::default();
        helpers.insert(SemanticCHelper::I64FromBits);
        helpers.insert(SemanticCHelper::I8FromBits);
        let definitions = helpers.definitions();
        let i8 = definitions.find("r2s_i8_from_bits").expect("i8 helper");
        let i64 = definitions.find("r2s_i64_from_bits").expect("i64 helper");
        assert!(i8 < i64);
        assert!(!definitions.contains("r2s_i16_from_bits"));
        assert!(!definitions.contains("r2s_i32_from_bits"));
        assert!(!definitions.contains("r2s_mask"));
    }

    #[test]
    fn typed_helper_inventory_closes_mask_dependency_before_dependent() {
        let mut helpers = SemanticCHelperSet::default();
        helpers.insert(SemanticCHelper::WrapAdd);
        let definitions = helpers.definitions();
        let mask = definitions.find("r2s_mask").expect("mask dependency");
        let wrap = definitions.find("r2s_wrap_add").expect("selected helper");
        assert!(mask < wrap);
        assert!(!definitions.contains("r2s_wrap_sub"));
    }

    #[test]
    fn missing_or_noncanonical_logical_return_projection_refuses_typed_projection() {
        let storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let missing = SourceFunctionInterface::new(
            b"missing-logical-return:v1".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Register { storage },
            [],
        )
        .expect("physical-only interface");
        assert_eq!(
            exact_semantic_return_projection(&missing, storage).expect("missing is not malformed"),
            None
        );

        let malformed = SourceFunctionInterface::new_with_logical_types(
            b"noncanonical-logical-return:v1".to_vec(),
            "test-abi",
            [],
            SourceFunctionReturn::Register { storage },
            [],
            [],
            Some(SourceLogicalValue::new(
                0,
                SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 64),
            )),
            Some(
                SourceTypeGraph::new(
                    [SourceType::new(0, SourceTypeKind::UnsignedInteger, 64, 64)],
                    [],
                )
                .expect("scalar source type"),
            ),
        );
        assert!(malformed.is_err());
    }

    #[test]
    fn structural_return_mechanics_closure_uses_only_exact_producer_edges() {
        let leaf = id(0);
        let shared = id(1);
        let return_address = id(2);
        let exit_stack_pointer = id(3);
        let returned = id(4);
        let mut dependencies = BTreeMap::from([
            (leaf, BTreeSet::new()),
            (shared, BTreeSet::from([leaf])),
            (return_address, BTreeSet::from([shared])),
            (exit_stack_pointer, BTreeSet::from([shared])),
            (returned, BTreeSet::from([shared])),
        ]);
        let return_producer = id(5);
        let mut candidates = BTreeMap::new();
        add_return_mechanics_closure(
            return_address,
            return_producer,
            &dependencies,
            &mut candidates,
        )
        .expect("return-address closure");
        add_return_mechanics_closure(
            exit_stack_pointer,
            return_producer,
            &dependencies,
            &mut candidates,
        )
        .expect("exit-stack-pointer closure");
        assert_eq!(
            candidates.keys().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([leaf, shared, return_address, exit_stack_pointer])
        );
        assert!(!candidates.contains_key(&returned));
        assert!(
            candidates
                .values()
                .all(|owners| owners == &BTreeSet::from([return_producer]))
        );

        dependencies.remove(&leaf);
        let mut malformed = BTreeMap::new();
        assert!(matches!(
            add_return_mechanics_closure(
                return_address,
                return_producer,
                &dependencies,
                &mut malformed,
            ),
            Err(SemanticCError::InvalidReturnMechanics(producer)) if producer == leaf
        ));
    }

    #[test]
    fn shared_return_value_producers_and_ancestors_remain_semantic() {
        let leaf = id(0);
        let shared = id(1);
        let overlay = id(2);
        let return_address = id(3);
        let exit_stack_pointer = id(4);
        let return_producer = id(5);
        let dependencies = BTreeMap::from([
            (leaf, BTreeSet::new()),
            (shared, BTreeSet::from([leaf])),
            (overlay, BTreeSet::from([shared])),
            (return_address, BTreeSet::from([overlay])),
            (exit_stack_pointer, BTreeSet::from([shared])),
        ]);
        let mut candidates = BTreeMap::new();
        add_return_mechanics_closure(
            return_address,
            return_producer,
            &dependencies,
            &mut candidates,
        )
        .expect("return-address closure");
        add_return_mechanics_closure(
            exit_stack_pointer,
            return_producer,
            &dependencies,
            &mut candidates,
        )
        .expect("exit-stack-pointer closure");

        let semantic = backward_close_semantic_producers(
            &candidates,
            &dependencies,
            BTreeSet::from([shared, overlay]),
        )
        .expect("composed return components close over their dependencies");
        assert_eq!(semantic, BTreeSet::from([leaf, shared, overlay]));
        assert_eq!(
            candidates
                .keys()
                .copied()
                .filter(|producer| !semantic.contains(producer))
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([return_address, exit_stack_pointer])
        );
    }

    fn composed_operand_fixture() -> (
        SemanticCExpressionLayer,
        SemanticCReturnRegisterComposition,
        SemanticCReturnValue,
    ) {
        let mut block = R2ILBlock::new(0x4100, 4);
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(0, 8),
        });
        block.push(R2ILOp::Copy {
            dst: Varnode::register(0, 1),
            src: Varnode::constant(1, 1),
        });
        let mut arch = ArchSpec::new("semantic-composed-return-test");
        arch.add_register(RegisterDef::new("rax", 0, 8));
        arch.add_register(RegisterDef::sub("al", 0, 1, "rax"));
        let artifact = SsaArtifact::for_decompile(&[block], Some(&arch))
            .expect("prepared composed-return component artifact");
        let projection = MachineProjection::from_artifact(&artifact)
            .expect("machine projection for composed-return components");
        let base_producer = block_id(0x4100, 0);
        let overlay_producer = block_id(0x4100, 1);
        let base_binding = projection
            .entity_for_producer(base_producer)
            .expect("base entity")
            .output();
        let overlay_binding = projection
            .entity_for_producer(overlay_producer)
            .expect("overlay entity")
            .output();
        let base_ty = MachineType::Integer {
            width_bits: 64,
            signedness: MachineSignedness::Unsigned,
        };
        let overlay_ty = MachineType::Integer {
            width_bits: 8,
            signedness: MachineSignedness::Unsigned,
        };
        let expressions = vec![
            SemanticCExpr {
                ty: base_ty.clone(),
                source_instructions: BTreeSet::from([base_producer]),
                kind: SemanticCExprKind::Input {
                    binding: base_binding,
                },
            },
            SemanticCExpr {
                ty: overlay_ty.clone(),
                source_instructions: BTreeSet::from([overlay_producer]),
                kind: SemanticCExprKind::Input {
                    binding: overlay_binding,
                },
            },
        ];
        let entities = vec![
            SemanticCEntity {
                output: base_binding,
                root: SemanticCExprId(0),
                producer: base_producer,
                source_obligations: BTreeSet::new(),
            },
            SemanticCEntity {
                output: overlay_binding,
                root: SemanticCExprId(1),
                producer: overlay_producer,
                source_obligations: BTreeSet::new(),
            },
        ];
        let layer = SemanticCExpressionLayer {
            schema_version: SEMANTIC_C_SCHEMA_VERSION,
            scope: SemanticCScope::LiveValueExpressionsOnly,
            identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
            expressions: expressions.into_boxed_slice(),
            entities: entities.into_boxed_slice(),
            function_interface: None,
            inputs: BTreeMap::from([(base_binding, base_ty), (overlay_binding, overlay_ty)]),
            input_origins: BTreeMap::new(),
            return_mechanics: SemanticCReturnMechanicsOwnership::default(),
            frame_mechanics: SemanticCFrameMechanicsOwnership::default(),
            open_obligations: BTreeSet::new(),
        };
        let base_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 0,
            size: 8,
        };
        let composition = SemanticCReturnRegisterComposition {
            slot: CallBoundarySlot::Register {
                index: 0,
                storage: base_storage,
            },
            base: SemanticCReturnRegisterDefinition {
                storage: base_storage,
                binding: base_binding,
                producer: base_producer,
                expression: SemanticCExprId(0),
            },
            overlays: vec![SemanticCReturnRegisterOverlay {
                definition: SemanticCReturnRegisterDefinition {
                    storage: CanonicalStorageId {
                        space: CanonicalStorageSpace::Register,
                        offset: 0,
                        size: 1,
                    },
                    binding: overlay_binding,
                    producer: overlay_producer,
                    expression: SemanticCExprId(1),
                },
                offset_bytes: 0,
            }]
            .into_boxed_slice(),
        };
        let direct = SemanticCReturnValue {
            slot: composition.slot,
            binding: base_binding,
            producer: base_producer,
            expression: SemanticCExprId(0),
        };
        (layer, composition, direct)
    }

    #[test]
    fn composed_return_operand_has_no_fake_binding_and_renders_ordered_insert() {
        let (layer, composition, direct) = composed_operand_fixture();
        let base_name = value_name(composition.base().binding());
        let overlay_name = value_name(composition.overlays()[0].definition().binding());
        assert_eq!(
            composition.source_producers().collect::<Vec<_>>(),
            vec![
                composition.base().producer(),
                composition.overlays()[0].definition().producer()
            ]
        );
        assert_eq!(composition.physical_width_bits(), 64);
        assert_eq!(
            layer
                .render_return_operand_with_helpers(
                    SemanticCReturnOperand::RegisterComposition(&composition),
                    &mut SemanticCHelperSet::default(),
                )
                .expect("exact composed return rendering"),
            format!(
                "((uint64_t)(r2s_bit_insert((uint64_t)({base_name}), (uint64_t)({overlay_name}), 0U, 8U, 64U)))"
            )
        );
        assert_eq!(
            layer
                .render_return_operand_with_helpers(
                    SemanticCReturnOperand::Direct(&direct),
                    &mut SemanticCHelperSet::default(),
                )
                .expect("direct return stays unchanged"),
            value_name(direct.binding())
        );
        let mut helpers = SemanticCHelperSet::default();
        layer
            .render_return_operand_with_helpers(
                SemanticCReturnOperand::RegisterComposition(&composition),
                &mut helpers,
            )
            .expect("typed helper inventory");
        let definitions = helpers.definitions();
        assert!(definitions.contains("static inline uint64_t r2s_mask"));
        assert!(definitions.contains("static inline uint64_t r2s_bit_insert"));
        assert!(!definitions.contains("r2s_wrap_add"));
    }

    #[test]
    fn composed_return_operand_uses_real_binding_for_bound_zero_base() {
        let (mut layer, composition, _) = composed_operand_fixture();
        let base = composition.base();
        layer.expressions[base.expression().index()].kind = SemanticCExprKind::Constant {
            binding: base.binding(),
            value: MachineBitVector::zero(base.binding().width_bits())
                .expect("valid composed base width"),
        };
        layer.inputs.remove(&base.binding());

        let overlay_name = value_name(composition.overlays()[0].definition().binding());
        assert_eq!(
            layer
                .render_expr(base.expression(), &mut SemanticCHelperSet::default())
                .expect("bound zero expression"),
            "((uint64_t)UINT64_C(0x0))"
        );
        let rendered = layer
            .render_return_operand_with_helpers(
                SemanticCReturnOperand::RegisterComposition(&composition),
                &mut SemanticCHelperSet::default(),
            )
            .expect("composed return with exact zero base");
        assert_eq!(
            rendered,
            format!(
                "((uint64_t)(r2s_bit_insert((uint64_t)({}), (uint64_t)({overlay_name}), 0U, 8U, 64U)))",
                value_name(base.binding())
            )
        );
        assert!(!layer.inputs.contains_key(&base.binding()));
    }

    #[test]
    fn composed_return_operand_refuses_out_of_bounds_overlay_and_shape_collisions() {
        let (layer, mut composition, direct) = composed_operand_fixture();
        composition.overlays[0].offset_bytes = 8;
        assert!(matches!(
            layer.render_return_operand_with_helpers(
                SemanticCReturnOperand::RegisterComposition(&composition),
                &mut SemanticCHelperSet::default(),
            ),
            Err(SemanticCError::ReturnBindingMismatch(_))
        ));

        let composed = SemanticCReturn {
            producer: id(9),
            control_target: direct.binding(),
            values: Box::new([]),
            register_compositions: vec![composition.clone()].into_boxed_slice(),
            source_obligations: BTreeSet::new(),
        };
        assert!(matches!(
            composed.single_operand(),
            Some(SemanticCReturnOperand::RegisterComposition(_))
        ));
        let collided = SemanticCReturn {
            values: vec![direct].into_boxed_slice(),
            ..composed
        };
        assert!(collided.single_operand().is_none());
    }

    #[test]
    fn cyclic_duplicate_and_reordered_return_mechanics_do_not_mint_authority() {
        let first = id(0);
        let second = id(1);
        let return_producer = id(2);
        let dependencies = BTreeMap::from([
            (first, BTreeSet::from([second])),
            (second, BTreeSet::from([first])),
        ]);
        assert!(matches!(
            add_return_mechanics_closure(
                first,
                return_producer,
                &dependencies,
                &mut BTreeMap::new(),
            ),
            Err(SemanticCError::CyclicReturnMechanics(_))
        ));

        let owner = |producer| SemanticCReturnMechanicsOwner {
            source_producer: producer,
            return_producers: vec![return_producer].into_boxed_slice(),
            source_obligations: Vec::new().into_boxed_slice(),
        };
        let canonical = SemanticCReturnMechanicsOwnership {
            owners: vec![owner(first), owner(second)].into_boxed_slice(),
        };
        let reordered = SemanticCReturnMechanicsOwnership {
            owners: vec![owner(second), owner(first)].into_boxed_slice(),
        };
        let duplicated = SemanticCReturnMechanicsOwnership {
            owners: vec![owner(first), owner(first), owner(second)].into_boxed_slice(),
        };
        assert_ne!(canonical, reordered);
        assert_ne!(canonical, duplicated);
    }

    #[test]
    fn frame_closure_tracks_shared_and_arm_local_return_service_exactly() {
        let common_leaf = block_id(0x1000, 0);
        let common_save = block_id(0x1000, 1);
        let shared_restore_input = block_id(0x2000, 0);
        let left_restore = block_id(0x2000, 1);
        let right_restore = block_id(0x3000, 0);
        let left_return = block_id(0x2000, 2);
        let right_return = block_id(0x3000, 1);
        let dependencies = BTreeMap::from([
            (common_leaf, BTreeSet::new()),
            (common_save, BTreeSet::from([common_leaf])),
            (shared_restore_input, BTreeSet::from([common_leaf])),
            (left_restore, BTreeSet::from([shared_restore_input])),
            (right_restore, BTreeSet::from([shared_restore_input])),
        ]);
        let mut candidates = BTreeMap::new();
        for return_producer in [left_return, right_return] {
            let mut complete = BTreeSet::new();
            add_frame_mechanics_closure(
                common_save,
                return_producer,
                &dependencies,
                &mut candidates,
                &mut BTreeSet::new(),
                &mut complete,
            )
            .expect("common frame closure");
            add_frame_mechanics_closure(
                if return_producer == left_return {
                    left_restore
                } else {
                    right_restore
                },
                return_producer,
                &dependencies,
                &mut candidates,
                &mut BTreeSet::new(),
                &mut complete,
            )
            .expect("arm-local restore closure");
        }

        assert_eq!(
            candidates.get(&common_save),
            Some(&BTreeSet::from([left_return, right_return]))
        );
        assert_eq!(
            candidates.get(&shared_restore_input),
            Some(&BTreeSet::from([left_return, right_return]))
        );
        assert_eq!(
            candidates.get(&left_restore),
            Some(&BTreeSet::from([left_return]))
        );
        assert_eq!(
            candidates.get(&right_restore),
            Some(&BTreeSet::from([right_return]))
        );

        let return_only = block_id(0x1000, 9);
        let combined = union_mechanics_services(
            &BTreeMap::from([
                (shared_restore_input, BTreeSet::from([left_return])),
                (return_only, BTreeSet::from([right_return])),
            ]),
            &candidates,
        );
        assert_eq!(
            combined.get(&shared_restore_input),
            Some(&BTreeSet::from([left_return, right_return]))
        );
        assert_eq!(
            combined.get(&return_only),
            Some(&BTreeSet::from([right_return]))
        );
    }

    #[test]
    fn frame_closure_cycles_and_semantic_outside_uses_cannot_be_erased() {
        let leaf = id(10);
        let shared = id(11);
        let restore = id(12);
        let return_producer = id(13);
        let dependencies = BTreeMap::from([
            (leaf, BTreeSet::new()),
            (shared, BTreeSet::from([leaf])),
            (restore, BTreeSet::from([shared])),
        ]);
        let mut candidates = BTreeMap::new();
        add_frame_mechanics_closure(
            restore,
            return_producer,
            &dependencies,
            &mut candidates,
            &mut BTreeSet::new(),
            &mut BTreeSet::new(),
        )
        .expect("acyclic frame closure");
        let semantic =
            backward_close_semantic_producers(&candidates, &dependencies, BTreeSet::from([shared]))
                .expect("outside use closes over its dependencies");
        assert_eq!(semantic, BTreeSet::from([leaf, shared]));
        assert!(!semantic.contains(&restore));

        let cycle_dependencies = BTreeMap::from([
            (leaf, BTreeSet::from([shared])),
            (shared, BTreeSet::from([leaf])),
        ]);
        assert!(matches!(
            add_frame_mechanics_closure(
                leaf,
                return_producer,
                &cycle_dependencies,
                &mut BTreeMap::new(),
                &mut BTreeSet::new(),
                &mut BTreeSet::new(),
            ),
            Err(SemanticCError::CyclicFrameMechanics(_))
        ));

        let unknown = id(14);
        assert!(matches!(
            add_frame_mechanics_closure(
                unknown,
                return_producer,
                &dependencies,
                &mut BTreeMap::new(),
                &mut BTreeSet::new(),
                &mut BTreeSet::new(),
            ),
            Err(SemanticCError::InvalidFrameMechanics(producer)) if producer == unknown
        ));
        let explicit_leaf_dependencies = BTreeMap::from([(unknown, BTreeSet::new())]);
        add_frame_mechanics_closure(
            unknown,
            return_producer,
            &explicit_leaf_dependencies,
            &mut BTreeMap::new(),
            &mut BTreeSet::new(),
            &mut BTreeSet::new(),
        )
        .expect("only an explicit sealed dependency row may terminate the closure");

        let address = id(15);
        let input = id(16);
        let mut explicit = BTreeMap::new();
        merge_frame_dependency_row(&mut explicit, unknown, [unknown, address]);
        merge_frame_dependency_row(&mut explicit, unknown, [unknown, input]);
        assert_eq!(
            explicit.get(&unknown),
            Some(&BTreeSet::from([address, input]))
        );
    }

    #[test]
    fn exact_frame_relation_dependency_preserves_sealed_empty_and_input_rows() {
        let relation = id(20);
        let input = id(21);
        let wrong = id(22);

        let mut dependencies = BTreeMap::new();
        let mut explicit = BTreeMap::new();
        assert!(merge_exact_frame_relation_dependency(
            &mut dependencies,
            &mut explicit,
            relation,
            None,
        ));
        assert_eq!(dependencies.get(&relation), Some(&BTreeSet::new()));
        assert_eq!(explicit.get(&relation), Some(&BTreeSet::new()));
        let return_producer = id(23);
        let mut candidates = BTreeMap::new();
        add_frame_mechanics_closure(
            relation,
            return_producer,
            &dependencies,
            &mut candidates,
            &mut BTreeSet::new(),
            &mut BTreeSet::new(),
        )
        .expect("the sealed empty relation row is an intentional mechanical leaf");
        assert_eq!(
            candidates.get(&relation),
            Some(&BTreeSet::from([return_producer]))
        );
        assert!(matches!(
            add_frame_mechanics_closure(
                relation,
                return_producer,
                &BTreeMap::new(),
                &mut BTreeMap::new(),
                &mut BTreeSet::new(),
                &mut BTreeSet::new(),
            ),
            Err(SemanticCError::InvalidFrameMechanics(producer)) if producer == relation
        ));

        let mut dependencies = BTreeMap::from([(relation, BTreeSet::from([input]))]);
        let mut explicit = BTreeMap::new();
        assert!(merge_exact_frame_relation_dependency(
            &mut dependencies,
            &mut explicit,
            relation,
            Some(input),
        ));
        assert_eq!(explicit.get(&relation), Some(&BTreeSet::from([input])));

        let original_dependencies = BTreeMap::from([(relation, BTreeSet::from([wrong]))]);
        let mut dependencies = original_dependencies.clone();
        let mut explicit = BTreeMap::new();
        assert!(!merge_exact_frame_relation_dependency(
            &mut dependencies,
            &mut explicit,
            relation,
            Some(input),
        ));
        assert_eq!(dependencies, original_dependencies);
        assert!(explicit.is_empty());

        let mut dependencies = BTreeMap::new();
        let mut explicit = BTreeMap::new();
        assert!(!merge_exact_frame_relation_dependency(
            &mut dependencies,
            &mut explicit,
            relation,
            Some(relation),
        ));
        assert!(dependencies.is_empty());
        assert!(explicit.is_empty());
    }
}
