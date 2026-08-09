//! Machine-semantic C representation.
//!
//! This is deliberately separate from the legacy presentation AST. It lowers
//! only expression roots already bound by `r2cert` to the immutable machine
//! arena. Stable SSA values and canonical instruction IDs provide provenance;
//! names and rendered positions are never consulted as evidence.

use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
use std::fmt::Write as _;

use r2cert::{
    CertifiedAbiParameter, CertifiedCallArgument, CertifiedCallArgumentOrigin,
    CertifiedConditionalReturnCarrier, CertifiedConditionalReturnFunnelControl,
    CertifiedDirectCall, CertifiedExpr, CertifiedMachineFunction, CertifiedMachineProjection,
    CertifiedReturnControl, CertifiedStackSlot, EffectDisposition, ObligationLedger,
};
use r2ssa::{
    CallBoundarySlot, CallSiteId, CanonicalInstructionId, CanonicalStorageId,
    MachineAddressProvenance, MachineArithmeticFlagOp, MachineArithmeticMode, MachineArithmeticOp,
    MachineBitVector, MachineBitwiseOp, MachineBooleanOp, MachineCastKind, MachineComparisonOp,
    MachineEntity, MachineExpr, MachineExprId, MachineExprKind, MachineMemoryEndianness,
    MachineOvershiftBehavior, MachineProjection, MachineShiftKind, MachineSignedness,
    MachineStackBase, MachineType, MachineValueBinding, MachineValueUse, ObjectId,
    SemanticObligationId,
    SemanticObligationInventory, SemanticObligationKind, SourceCallSiteIdentity,
    SourceFunctionReturn, SourceMachineContext, StackAddressBase, StackAddressRoot,
    StructuredAccessId, ValueId,
};
use serde::Serialize;

pub const SEMANTIC_C_SCHEMA_VERSION: u32 = 7;

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

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCFunctionInterface {
    revision_identity: Box<[u8]>,
    calling_convention: String,
    parameters: Box<[SemanticCParameter]>,
    return_kind: SemanticCFunctionReturn,
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

    pub const fn stack_slots(&self) -> &[SemanticCStackSlot] {
        &self.stack_slots
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
    ConditionalReturnCarrier {
        producer: CanonicalInstructionId,
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

impl SemanticCExprKind {
    fn children(&self) -> Vec<SemanticCExprId> {
        match self {
            Self::Input { .. } | Self::Constant { .. } => Vec::new(),
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
        }
    }
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
    expression: SemanticCExprId,
}

impl SemanticCReturnValue {
    pub const fn slot(&self) -> CallBoundarySlot {
        self.slot
    }

    pub const fn binding(&self) -> MachineValueBinding {
        self.binding
    }

    pub const fn expression(&self) -> SemanticCExprId {
        self.expression
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCReturn {
    producer: CanonicalInstructionId,
    control_target: MachineValueBinding,
    values: Box<[SemanticCReturnValue]>,
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
/// this envelope is never a complete source function or a `CertifiedC` claim.
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
    open_obligations: BTreeSet<SemanticObligationId>,
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
    InvalidSelectExpression(SemanticCExprId),
    SelectRequiresValueArmExpression(SemanticCExprId),
    InvalidWidth(u32),
    InconsistentInputType(ValueId),
    UnclassifiedSourceInput(ValueId),
    InvalidCertifiedFunctionInterface,
    MissingReturnExpression(CanonicalInstructionId),
    ReturnBindingMismatch(CanonicalInstructionId),
    MissingCallExpression(CanonicalInstructionId),
    CallBindingMismatch(CanonicalInstructionId),
    #[cfg(test)]
    UnknownEntity(CanonicalInstructionId),
    #[cfg(test)]
    DependencyOrder {
        producer: CanonicalInstructionId,
        value: ValueId,
    },
    CheckedArithmeticRequiresHelper(SemanticCExprId),
    UnsupportedShiftPolicy(SemanticCExprId),
    MemoryReadRequiresCertifiedStatement(SemanticCExprId),
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
    fn machine_view(&self) -> MachineView<'_>;
    fn source(&self) -> &SemanticObligationInventory;
    fn ledger(&self) -> &ObligationLedger;
    fn expression_for_producer(&self, producer: CanonicalInstructionId) -> Option<&CertifiedExpr>;
    fn machine_context(&self) -> &SourceMachineContext;
    fn abi_parameters(&self) -> &BTreeMap<u32, CertifiedAbiParameter>;
    fn stack_slots(&self) -> &BTreeMap<StackAddressRoot, CertifiedStackSlot>;
}

impl CertifiedSemanticSource for CertifiedMachineFunction {
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
}

impl CertifiedSemanticSource for CertifiedMachineProjection {
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
    for declared in source.parameters() {
        let certified_parameter = certified
            .abi_parameters()
            .get(&declared.index())
            .filter(|parameter| parameter.storage() == declared.storage())
            .ok_or(SemanticCError::InvalidCertifiedFunctionInterface)?;
        let width_bits = declared
            .storage()
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
    let return_kind = match source.return_kind() {
        SourceFunctionReturn::Void => SemanticCFunctionReturn::Void,
        SourceFunctionReturn::Register { storage } => {
            let width_bits = storage
                .size
                .checked_mul(8)
                .filter(|width| *width > 0)
                .ok_or(SemanticCError::InvalidCertifiedFunctionInterface)?;
            SemanticCFunctionReturn::Register {
                storage,
                ty: MachineType::Integer {
                    width_bits,
                    signedness: MachineSignedness::Unsigned,
                },
            }
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
        stack_slots: stack_slots.into_boxed_slice(),
    }))
}

fn classify_input(
    binding: MachineValueBinding,
    ty: &MachineType,
    interface: Option<&SemanticCFunctionInterface>,
) -> SemanticCInputOrigin {
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

impl SemanticCExpressionLayer {
    /// Lower the certified live-value seam into an immutable semantic-C arena.
    ///
    /// Effect, control, return, and loop-state obligations remain open in
    /// `r2cert`; this expression layer cannot authorize a complete C function.
    pub fn from_certified(certified: &CertifiedMachineFunction) -> Result<Self, SemanticCError> {
        Self::from_source(certified, None, None)
    }

    /// Lower expressions for one sealed conditional-return funnel.
    ///
    /// The carrier is admitted as an explicit local input only when every
    /// obligation owned by it has the exact conditional-return-state ledger
    /// disposition and the same sealed carrier evidence.
    pub fn from_conditional_return_funnel(
        certified: &CertifiedMachineFunction,
        control: &CertifiedConditionalReturnFunnelControl,
    ) -> Result<Self, SemanticCError> {
        if control.origin() != certified.origin() {
            return Err(SemanticCError::InvalidCertifiedFunctionInterface);
        }
        let carrier = control.carrier();
        let evidence_is_exact = carrier.source_obligations().iter().all(|obligation| {
            matches!(certified.ledger().effects(*obligation), [effect]
                if effect.disposition()
                    == &EffectDisposition::AbsorbedIntoConditionalReturnState {
                        producer: carrier.producer(),
                    }
                    && effect.conditional_return_state_evidence() == Some(carrier))
        });
        if carrier.source_obligations().is_empty() || !evidence_is_exact {
            return Err(SemanticCError::CertifiedSourceMismatch(carrier.producer()));
        }
        let selected_producers = [
            control.branch_control().condition().producer(),
            control.true_candidate().value().producer(),
            control.false_candidate().value().producer(),
        ]
        .into_iter()
        .flatten()
        .chain(
            control
                .return_value_chain()
                .iter()
                .filter_map(MachineValueUse::producer),
        )
        .collect::<BTreeSet<_>>();
        Self::from_source(certified, Some(carrier), Some(&selected_producers))
    }

    /// Lower all supported values from a certified partial machine projection.
    ///
    /// Failed producers and their transitive dependents stay absent from the C
    /// arena and remain explicit in `open_obligations`.
    pub fn from_projection(certified: &CertifiedMachineProjection) -> Result<Self, SemanticCError> {
        Self::from_source(certified, None, None)
    }

    fn from_source(
        certified: &impl CertifiedSemanticSource,
        conditional_carrier: Option<&CertifiedConditionalReturnCarrier>,
        selected_producers: Option<&BTreeSet<CanonicalInstructionId>>,
    ) -> Result<Self, SemanticCError> {
        let function_interface = semantic_function_interface(certified)?;
        let machine = certified.machine_view();
        let output_producers = machine.output_producers();
        let mut certified_producers = machine
            .entities()
            .iter()
            .filter_map(|entity| {
                certified
                    .expression_for_producer(entity.producer())
                    .map(|_| entity.producer())
            })
            .collect::<BTreeSet<_>>();
        let conditional_carrier_inputs = conditional_carrier
            .map(|carrier| {
                let binding = match carrier {
                    CertifiedConditionalReturnCarrier::RegisterPhi(state) => state.phi().binding(),
                    CertifiedConditionalReturnCarrier::PrivateStackScalar(state) => {
                        state.loaded_value().binding()
                    }
                };
                BTreeMap::from([(binding, carrier.producer())])
            })
            .unwrap_or_default();
        certified_producers.extend(conditional_carrier_inputs.values().copied());

        let mut builder = SemanticCBuilder {
            machine,
            output_producers: &output_producers,
            certified_producers: &certified_producers,
            conditional_carrier_inputs: &conditional_carrier_inputs,
            translated: BTreeMap::new(),
            expressions: Vec::new(),
            inputs: BTreeMap::new(),
        };
        let mut entities = Vec::new();

        for machine_entity in machine.entities() {
            if selected_producers
                .is_some_and(|selected| !selected.contains(&machine_entity.producer()))
            {
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
            let carrier_owned = conditional_carrier.is_some_and(|carrier| {
                !live_obligations.is_empty()
                    && live_obligations.iter().all(|obligation| {
                        carrier.source_obligations().contains(obligation)
                            && matches!(certified.ledger().effects(*obligation), [effect]
                                if effect.disposition()
                                    == &EffectDisposition::AbsorbedIntoConditionalReturnState {
                                        producer: carrier.producer(),
                                    }
                                    && effect.conditional_return_state_evidence()
                                        == Some(carrier))
                    })
            });
            if carrier_owned {
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
        let open_obligations = certified
            .source()
            .obligations()
            .keys()
            .copied()
            .filter(|id| !absorbed_expressions.contains(id))
            .collect();
        let input_origins = builder
            .inputs
            .iter()
            .map(|(binding, ty)| {
                (
                    *binding,
                    conditional_carrier_inputs
                        .get(binding)
                        .copied()
                        .map(|producer| SemanticCInputOrigin::ConditionalReturnCarrier { producer })
                        .unwrap_or_else(|| {
                            classify_input(*binding, ty, function_interface.as_ref())
                        }),
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

    #[cfg(test)]
    pub(crate) fn replace_expr_kind_for_test(
        &mut self,
        id: SemanticCExprId,
        kind: SemanticCExprKind,
    ) -> Result<(), SemanticCError> {
        let expression = self
            .expressions
            .get_mut(id.index())
            .ok_or(SemanticCError::MissingSemanticExpression(id))?;
        expression.kind = kind;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn replace_expr_type_for_test(
        &mut self,
        id: SemanticCExprId,
        ty: MachineType,
    ) -> Result<(), SemanticCError> {
        let expression = self
            .expressions
            .get_mut(id.index())
            .ok_or(SemanticCError::MissingSemanticExpression(id))?;
        expression.ty = ty;
        Ok(())
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

    pub const fn open_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        &self.open_obligations
    }

    /// Render a conservative C11 expression kernel for the compiler test gate.
    ///
    /// This stays test-only until effect, control, and return obligations are
    /// closed by certified structuring. Production callers receive only the
    /// typed AST and cannot mistake a value-expression kernel for a decompiled
    /// source function. Machine values are evaluated as unsigned bit patterns;
    /// signed interpretation is confined to explicit helpers.
    #[cfg(test)]
    fn render_test_entity_translation_unit(
        &self,
        output_producer: CanonicalInstructionId,
    ) -> Result<String, SemanticCError> {
        const FUNCTION_NAME: &str = "semantic_c_test_kernel";
        let return_index = self
            .entities
            .iter()
            .position(|entity| entity.producer == output_producer)
            .ok_or(SemanticCError::UnknownEntity(output_producer))?;
        let entities = &self.entities[..=return_index];
        let return_entity = &entities[return_index];
        let return_type = storage_type(self.expr_type(return_entity.root)?)?;
        let mut required_inputs = BTreeSet::new();
        for entity in entities {
            required_inputs.extend(
                self.source_bindings(entity.root)?
                    .into_iter()
                    .filter(|binding| self.inputs.contains_key(binding)),
            );
        }
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        output.push_str(SEMANTIC_C_HELPERS);
        write!(&mut output, "\n{} {}(", return_type, FUNCTION_NAME)
            .expect("String writes cannot fail");
        if required_inputs.is_empty() {
            output.push_str("void");
        } else {
            for (index, binding) in required_inputs.iter().enumerate() {
                if index > 0 {
                    output.push_str(", ");
                }
                write!(
                    &mut output,
                    "{} {}",
                    storage_type(
                        self.inputs
                            .get(binding)
                            .ok_or(SemanticCError::InconsistentInputType(binding.value()))?
                    )?,
                    value_name(*binding)
                )
                .expect("String writes cannot fail");
            }
        }
        output.push_str(") {\n");

        let mut defined = required_inputs;
        for entity in entities {
            for binding in self.source_bindings(entity.root)? {
                if !defined.contains(&binding) {
                    return Err(SemanticCError::DependencyOrder {
                        producer: entity.producer,
                        value: binding.value(),
                    });
                }
            }
            let expression = self.render_expr(entity.root)?;
            writeln!(
                &mut output,
                "\t{} {} = {};",
                storage_type(self.expr_type(entity.root)?)?,
                value_name(entity.output),
                expression
            )
            .expect("String writes cannot fail");
            defined.insert(entity.output);
        }
        writeln!(
            &mut output,
            "\treturn {};",
            value_name(return_entity.output)
        )
        .expect("String writes cannot fail");
        output.push_str("}\n");
        Ok(output)
    }

    pub(crate) fn expr_type(&self, id: SemanticCExprId) -> Result<&MachineType, SemanticCError> {
        self.expr(id)
            .map(SemanticCExpr::ty)
            .ok_or(SemanticCError::MissingSemanticExpression(id))
    }

    pub(crate) fn source_bindings(
        &self,
        root: SemanticCExprId,
    ) -> Result<BTreeSet<MachineValueBinding>, SemanticCError> {
        let mut result = BTreeSet::new();
        let mut ready = vec![root];
        let mut visited = BTreeSet::new();
        while let Some(id) = ready.pop() {
            if !visited.insert(id) {
                continue;
            }
            let expr = self
                .expr(id)
                .ok_or(SemanticCError::MissingSemanticExpression(id))?;
            match expr.kind {
                SemanticCExprKind::Input { binding } => {
                    result.insert(binding);
                }
                SemanticCExprKind::Constant { .. } => {}
                _ => ready.extend(expr.kind.children()),
            }
        }
        Ok(result)
    }

    pub(crate) fn render_expr(&self, id: SemanticCExprId) -> Result<String, SemanticCError> {
        self.render_expr_inner(id, None)
            .map(|rendered| rendered.source)
    }

    /// Render one semantic expression while replacing only exact input nodes
    /// carrying `binding`. The returned count is derived from AST identity,
    /// never from generated names or textual occurrences.
    pub(crate) fn render_expr_substituting_input(
        &self,
        id: SemanticCExprId,
        binding: MachineValueBinding,
        replacement: &str,
    ) -> Result<(String, usize), SemanticCError> {
        self.render_expr_inner(id, Some((binding, replacement)))
            .map(|rendered| (rendered.source, rendered.substitutions))
    }

    fn render_expr_inner(
        &self,
        id: SemanticCExprId,
        substitution: Option<(MachineValueBinding, &str)>,
    ) -> Result<RenderedSemanticExpr, SemanticCError> {
        let expr = self
            .expr(id)
            .ok_or(SemanticCError::MissingSemanticExpression(id))?;
        let width = expr.ty.width_bits();
        let ctype = storage_type(&expr.ty)?;
        let child = |child| self.render_expr_inner(child, substitution);
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
                    MachineArithmeticOp::Add => "r2s_wrap_add",
                    MachineArithmeticOp::Subtract => "r2s_wrap_sub",
                    MachineArithmeticOp::Multiply => "r2s_wrap_mul",
                };
                let left = child(*left)?;
                let right = child(*right)?;
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
                    MachineArithmeticFlagOp::UnsignedCarry => "r2s_ucarry",
                    MachineArithmeticFlagOp::SignedCarry => "r2s_scarry",
                    MachineArithmeticFlagOp::SignedBorrow => "r2s_sborrow",
                };
                let left = child(*left)?;
                let right = child(*right)?;
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
                    (MachineShiftKind::Left, MachineOvershiftBehavior::Zero) => "r2s_shl",
                    (MachineShiftKind::LogicalRight, MachineOvershiftBehavior::Zero) => "r2s_lshr",
                    (MachineShiftKind::ArithmeticRight, MachineOvershiftBehavior::SignFill) => {
                        "r2s_ashr"
                    }
                    _ => return Err(SemanticCError::UnsupportedShiftPolicy(id)),
                };
                let value = child(*value)?;
                let count = child(*count)?;
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
                        "(r2s_signed_key((uint64_t)({}), {comparison_width}U) < r2s_signed_key((uint64_t)({}), {comparison_width}U))",
                        left.source, right.source
                    ),
                    (MachineComparisonOp::LessThanOrEqual, MachineSignedness::Signed) => format!(
                        "(r2s_signed_key((uint64_t)({}), {comparison_width}U) <= r2s_signed_key((uint64_t)({}), {comparison_width}U))",
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
                    MachineCastKind::SignExtend => format!(
                        "(({ctype})r2s_sext((uint64_t)({}), {input_width}U, {width}U))",
                        input_expr.source
                    ),
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
    match (interface.return_kind(), control.values()) {
        (SemanticCFunctionReturn::Void, []) => {}
        (SemanticCFunctionReturn::Register { storage, ty }, [returned])
            if returned.slot()
                == (CallBoundarySlot::Register {
                    index: 0,
                    storage: *storage,
                })
                && returned.value().ty() == ty => {}
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
            expression: entity.root(),
        });
    }
    Ok(SemanticCReturn {
        producer: control.producer(),
        control_target: control.control_target().binding(),
        values: values.into_boxed_slice(),
        source_obligations: control.source_obligations(),
    })
}

struct SemanticCBuilder<'a> {
    machine: MachineView<'a>,
    output_producers: &'a BTreeMap<ValueId, CanonicalInstructionId>,
    certified_producers: &'a BTreeSet<CanonicalInstructionId>,
    conditional_carrier_inputs: &'a BTreeMap<MachineValueBinding, CanonicalInstructionId>,
    translated: BTreeMap<MachineExprId, SemanticCExprId>,
    expressions: Vec<SemanticCExpr>,
    inputs: BTreeMap<MachineValueBinding, MachineType>,
}

impl SemanticCBuilder<'_> {
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
                if let Some(dependency) = self.conditional_carrier_inputs.get(binding).copied() {
                    source_instructions.insert(dependency);
                    if let Some(existing) = self.inputs.insert(*binding, machine_expr.ty().clone())
                        && existing != *machine_expr.ty()
                    {
                        return Err(SemanticCError::InconsistentInputType(binding.value()));
                    }
                } else if let Some(dependency) =
                    self.output_producers.get(&binding.value()).copied()
                {
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
            MachineExprKind::Bitwise { op, left, right } => SemanticCExprKind::Bitwise {
                op: *op,
                left: self.translate_child(*left, &mut source_instructions)?,
                right: self.translate_child(*right, &mut source_instructions)?,
            },
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
                    return Err(SemanticCError::InvalidBooleanExpression(
                        SemanticCExprId(u32::MAX),
                    ));
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

pub(crate) const SEMANTIC_C_HELPERS: &str = r#"static inline uint64_t r2s_mask(unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	return width >= 64U ? UINT64_MAX : ((UINT64_C(1) << width) - UINT64_C(1));
}

static inline uint64_t r2s_wrap_add(uint64_t left, uint64_t right, unsigned width) {
	return (left + right) & r2s_mask(width);
}

static inline uint64_t r2s_wrap_sub(uint64_t left, uint64_t right, unsigned width) {
	return (left - right) & r2s_mask(width);
}

static inline uint64_t r2s_wrap_mul(uint64_t left, uint64_t right, unsigned width) {
	return (left * right) & r2s_mask(width);
}

static inline uint64_t r2s_ucarry(uint64_t left, uint64_t right, unsigned width) {
	uint64_t mask = r2s_mask(width);
	left &= mask;
	right &= mask;
	return left > (mask - right) ? UINT64_C(1) : UINT64_C(0);
}

static inline uint64_t r2s_scarry(uint64_t left, uint64_t right, unsigned width) {
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

static inline uint64_t r2s_sborrow(uint64_t left, uint64_t right, unsigned width) {
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

static inline uint64_t r2s_shl(uint64_t value, uint64_t count, unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	if (width > 64U) {
		width = 64U;
	}
	return count >= width ? UINT64_C(0) : ((value << count) & r2s_mask(width));
}

static inline uint64_t r2s_lshr(uint64_t value, uint64_t count, unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	if (width > 64U) {
		width = 64U;
	}
	return count >= width ? UINT64_C(0) : ((value & r2s_mask(width)) >> count);
}

static inline uint64_t r2s_ashr(uint64_t value, uint64_t count, unsigned width) {
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

static inline uint64_t r2s_signed_key(uint64_t value, unsigned width) {
	if (width == 0U) {
		return UINT64_C(0);
	}
	if (width > 64U) {
		width = 64U;
	}
	return (value & r2s_mask(width)) ^ (UINT64_C(1) << (width - 1U));
}

static inline uint64_t r2s_sext(uint64_t value, unsigned from_width, unsigned to_width) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use r2cert::{CertifiedMachineFunction, CertifiedMachineProjection};
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
    use r2ssa::{
        CanonicalStorageSpace, InstPayload, SSAOp, SourceAbiParameterSpec, SourceCallArgumentSpec,
        SourceCallResult, SourceCallSiteInterface, SourceFunctionInterface, SsaArtifact,
    };
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    fn compile_semantic_c(source: &str) {
        let mut compiler = Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Wpedantic",
                "-Wno-unused-function",
                "-Werror",
                "-fsyntax-only",
                "-x",
                "c",
                "-",
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("C compiler required for semantic-C gate");
        compiler
            .stdin
            .as_mut()
            .expect("compiler stdin")
            .write_all(source.as_bytes())
            .expect("write semantic C");
        let result = compiler.wait_with_output().expect("compile semantic C");
        assert!(
            result.status.success(),
            "generated semantic C did not compile: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }

    fn fnv_artifact() -> SsaArtifact {
        const FNV_OFFSET: u64 = 0xcbf29ce484222325;
        const FNV_PRIME: u64 = 0x100000001b3;
        let initial = Varnode::unique(0x10, 8);
        let mixed = Varnode::unique(0x18, 8);
        let product = Varnode::unique(0x20, 8);
        let mut block = R2ILBlock::new(0x1000, 4);
        block.push(R2ILOp::Copy {
            dst: initial.clone(),
            src: Varnode::constant(FNV_OFFSET, 8),
        });
        block.push(R2ILOp::IntXor {
            dst: mixed.clone(),
            a: initial,
            b: Varnode::register(0, 8),
        });
        block.push(R2ILOp::IntMult {
            dst: product.clone(),
            a: mixed,
            b: Varnode::constant(FNV_PRIME, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(8, 8),
            val: product,
        });
        SsaArtifact::raw(&[block], None).expect("FNV artifact")
    }

    fn reverse_le_bool_not_select_fnv_artifact() -> SsaArtifact {
        const FNV_OFFSET: u64 = 0xcbf29ce484222325;
        const FNV_PRIME: u64 = 0x100000001b3;
        let input = Varnode::register(0, 8);
        let reverse_le = Varnode::unique(0x30, 1);
        let inverted = Varnode::unique(0x38, 1);
        let adjusted = Varnode::unique(0x40, 8);
        let selected = Varnode::unique(0x48, 8);
        let mixed = Varnode::unique(0x50, 8);
        let product = Varnode::unique(0x58, 8);
        let mut block = R2ILBlock::new(0x1100, 4);
        block.push(R2ILOp::IntLessEqual {
            dst: reverse_le.clone(),
            a: Varnode::constant(0x1a, 8),
            b: input.clone(),
        });
        block.push(R2ILOp::BoolNot {
            dst: inverted.clone(),
            src: reverse_le,
        });
        block.push(R2ILOp::IntAdd {
            dst: adjusted.clone(),
            a: input.clone(),
            b: Varnode::constant(0x20, 8),
        });
        block.push(R2ILOp::Select {
            dst: selected.clone(),
            cond: inverted,
            if_true: adjusted,
            if_false: input,
        });
        block.push(R2ILOp::IntXor {
            dst: mixed.clone(),
            a: selected,
            b: Varnode::constant(FNV_OFFSET, 8),
        });
        block.push(R2ILOp::IntMult {
            dst: product.clone(),
            a: mixed,
            b: Varnode::constant(FNV_PRIME, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(8, 8),
            val: product,
        });
        SsaArtifact::raw(&[block], None).expect("reverse-LE FNV-shaped artifact")
    }

    #[test]
    fn input_substitution_preserves_a_distinct_prefix_name_binding() {
        let mut arch = ArchSpec::new("semantic-input-identity-test");
        let mut parameters = Vec::new();
        for index in 0..=10_u32 {
            let offset = u64::from(index) * 8;
            arch.add_register(RegisterDef::new(format!("p{index}"), offset, 8));
            parameters.push(SourceAbiParameterSpec::new(
                index,
                CanonicalStorageId {
                    space: CanonicalStorageSpace::Register,
                    offset,
                    size: 8,
                },
            ));
        }
        let mut block = R2ILBlock::new(0x1080, 4);
        for index in 0..=10_u64 {
            block.push(R2ILOp::Copy {
                dst: Varnode::unique(0x100 + index * 8, 8),
                src: Varnode::register(index * 8, 8),
            });
        }
        let sum = Varnode::unique(0x200, 8);
        block.push(R2ILOp::IntAdd {
            dst: sum.clone(),
            // The decoy is deliberately rendered first. A textual replacement
            // of the shorter target name would corrupt this distinct binding.
            a: Varnode::register(10 * 8, 8),
            b: Varnode::register(8, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::constant(0x9000, 8),
            val: sum,
        });
        let interface = SourceFunctionInterface::new(
            b"semantic-input-identity-v1".to_vec(),
            "test-register-abi",
            parameters,
            SourceFunctionReturn::Void,
            [],
        )
        .expect("identity test interface");
        let artifact = SsaArtifact::raw_with_interface(&[block], Some(&arch), interface)
            .expect("identity test artifact");
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified identity test");
        let semantic =
            SemanticCExpressionLayer::from_certified(&certified).expect("semantic identity test");
        let interface = semantic.function_interface().expect("function interface");
        let target = interface.parameters()[1].value().expect("target input");
        let decoy = interface.parameters()[10].value().expect("decoy input");
        let target_name = value_name(target);
        let decoy_name = value_name(decoy);
        assert!(decoy_name.starts_with(&target_name));
        let entity = semantic
            .entities()
            .iter()
            .find(|entity| {
                semantic
                    .source_bindings(entity.root())
                    .is_ok_and(|bindings| bindings == BTreeSet::from([target, decoy]))
            })
            .expect("two-input arithmetic expression");
        let (rendered, substitutions) = semantic
            .render_expr_substituting_input(entity.root(), target, "R2S_EXACT_TARGET")
            .expect("identity substitution");
        assert_eq!(substitutions, 1);
        assert!(rendered.contains(&format!("(uint64_t)({decoy_name})")));
        assert!(rendered.contains("(uint64_t)(R2S_EXACT_TARGET)"));
    }

    #[test]
    fn fnv_lowering_keeps_unsigned_wrapping_multiply_and_bitvector_constant() {
        let artifact = fnv_artifact();
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        assert!(!certified.finish().authorizes_certified_c());
        let semantic =
            SemanticCExpressionLayer::from_certified(&certified).expect("semantic C expressions");
        assert_eq!(semantic.scope(), SemanticCScope::LiveValueExpressionsOnly);
        assert_eq!(
            semantic.identity_scope(),
            SemanticCIdentityScope::ArtifactLocalHandles
        );
        for id in certified
            .source()
            .obligations()
            .keys()
            .filter(|id| id.kind != SemanticObligationKind::LiveValueProducer)
        {
            assert!(semantic.open_obligations().contains(id));
        }
        let multiply = semantic.entities().last().expect("multiply entity");
        let expression = semantic.expr(multiply.root()).expect("multiply root");
        assert_eq!(
            expression.ty(),
            &MachineType::Integer {
                width_bits: 64,
                signedness: MachineSignedness::Unsigned,
            }
        );
        assert!(matches!(
            expression.kind(),
            SemanticCExprKind::Arithmetic {
                op: MachineArithmeticOp::Multiply,
                mode: MachineArithmeticMode::Wrapping,
                ..
            }
        ));
        assert!(
            multiply
                .source_obligations()
                .iter()
                .all(|id| id.kind == SemanticObligationKind::LiveValueProducer)
        );

        let source = semantic
            .render_test_entity_translation_unit(multiply.producer())
            .expect("rendered semantic C");
        assert!(source.contains("uint64_t semantic_c_test_kernel("));
        assert!(source.contains("r2s_wrap_mul"));
        assert!(source.contains("UINT64_C(0x100000001b3)"));
        assert!(!source.contains(" int64_t "));

        compile_semantic_c(&source);
    }

    #[test]
    fn reverse_le_boolean_not_select_chain_is_typed_ordered_and_c11_safe() {
        let artifact = reverse_le_bool_not_select_fnv_artifact();
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("certified reverse-LE projection");
        let semantic = SemanticCExpressionLayer::from_projection(&certified)
            .expect("semantic reverse-LE projection");
        let boolean = semantic
            .entities()
            .iter()
            .find(|entity| {
                matches!(
                    semantic.expr(entity.root()).map(SemanticCExpr::kind),
                    Some(SemanticCExprKind::BooleanNot { .. })
                )
            })
            .expect("boolean-not entity");
        assert_eq!(
            semantic.expr(boolean.root()).map(SemanticCExpr::ty),
            Some(&MachineType::Bool { storage_bits: 8 })
        );

        let select = semantic
            .entities()
            .iter()
            .find(|entity| {
                matches!(
                    semantic.expr(entity.root()).map(SemanticCExpr::kind),
                    Some(SemanticCExprKind::Select { .. })
                )
            })
            .expect("select entity");
        let SemanticCExprKind::Select {
            condition,
            if_true,
            if_false,
        } = semantic.expr(select.root()).expect("select root").kind()
        else {
            unreachable!();
        };
        assert!(matches!(
            semantic.expr(*condition).map(SemanticCExpr::kind),
            Some(SemanticCExprKind::Input { .. })
        ));
        assert!(matches!(
            semantic.expr(*if_true).map(SemanticCExpr::kind),
            Some(SemanticCExprKind::Input { .. })
        ));
        assert!(matches!(
            semantic.expr(*if_false).map(SemanticCExpr::kind),
            Some(SemanticCExprKind::Input { .. })
        ));
        assert_eq!(
            semantic
                .source_bindings(select.root())
                .expect("select sources"),
            BTreeSet::from([
                match semantic.expr(*condition).expect("condition").kind() {
                    SemanticCExprKind::Input { binding } => *binding,
                    _ => unreachable!(),
                },
                match semantic.expr(*if_true).expect("true arm").kind() {
                    SemanticCExprKind::Input { binding } => *binding,
                    _ => unreachable!(),
                },
                match semantic.expr(*if_false).expect("false arm").kind() {
                    SemanticCExprKind::Input { binding } => *binding,
                    _ => unreachable!(),
                },
            ])
        );

        let product = semantic.entities().last().expect("FNV product entity");
        let source = semantic
            .render_test_entity_translation_unit(product.producer())
            .expect("rendered reverse-LE chain");
        assert!(source.contains("== UINT64_C(0)) ? 1U : 0U"));
        assert!(source.contains("!= UINT64_C(0)) ? ("));
        assert!(source.contains("r2s_wrap_mul"));
        let select_definition = source
            .find(&format!(" {} = ", value_name(select.output())))
            .expect("select definition");
        for arm in [condition, if_true] {
            let SemanticCExprKind::Input { binding } =
                semantic.expr(*arm).expect("produced select input").kind()
            else {
                unreachable!();
            };
            assert!(
                source
                    .find(&format!(" {} = ", value_name(*binding)))
                    .is_some_and(|definition| definition < select_definition),
                "produced Select dependencies must be assigned before its ternary"
            );
        }
        compile_semantic_c(&source);
    }

    #[test]
    fn boolean_not_and_select_type_guards_reject_mismatches() {
        let artifact = reverse_le_bool_not_select_fnv_artifact();
        let certified = CertifiedMachineProjection::from_artifact(&artifact).expect("projection");
        let machine = certified.projection();
        let boolean = machine
            .entities()
            .iter()
            .find(|entity| {
                machine.expr(entity.root()).is_some_and(|expression| {
                    matches!(expression.kind(), MachineExprKind::BooleanNot { .. })
                })
            })
            .expect("boolean-not entity")
            .root();
        let select = machine
            .entities()
            .iter()
            .find(|entity| {
                machine.expr(entity.root()).is_some_and(|expression| {
                    matches!(expression.kind(), MachineExprKind::Select { .. })
                })
            })
            .expect("select entity")
            .root();
        let bool8 = MachineType::Bool { storage_bits: 8 };
        let unsigned8 = MachineType::Integer {
            width_bits: 8,
            signedness: MachineSignedness::Unsigned,
        };
        let unsigned64 = MachineType::Integer {
            width_bits: 64,
            signedness: MachineSignedness::Unsigned,
        };
        assert_eq!(
            validate_boolean_not_types(boolean, &bool8, &unsigned8),
            Err(SemanticCError::InvalidBooleanNotType(boolean))
        );
        assert_eq!(
            validate_select_types(select, &unsigned64, &unsigned8, &unsigned64, &unsigned64),
            Err(SemanticCError::InvalidSelectType(select))
        );
        assert_eq!(
            validate_select_types(select, &unsigned64, &bool8, &unsigned8, &unsigned64),
            Err(SemanticCError::InvalidSelectType(select))
        );
    }

    #[test]
    fn select_value_arm_gate_rejects_a_corrupted_memory_read_arm() {
        let artifact = reverse_le_bool_not_select_fnv_artifact();
        let certified = CertifiedMachineProjection::from_artifact(&artifact).expect("projection");
        let machine_select = certified
            .projection()
            .entities()
            .iter()
            .find(|entity| {
                certified
                    .projection()
                    .expr(entity.root())
                    .is_some_and(|expression| {
                        matches!(expression.kind(), MachineExprKind::Select { .. })
                    })
            })
            .expect("machine select entity")
            .root();
        let mut semantic =
            SemanticCExpressionLayer::from_projection(&certified).expect("semantic projection");
        let select = semantic
            .entities()
            .iter()
            .find(|entity| {
                matches!(
                    semantic.expr(entity.root()).map(SemanticCExpr::kind),
                    Some(SemanticCExprKind::Select { .. })
                )
            })
            .expect("select entity")
            .root();
        let SemanticCExprKind::Select {
            if_true, if_false, ..
        } = semantic.expr(select).expect("select root").kind()
        else {
            unreachable!();
        };
        let (if_true, if_false) = (*if_true, *if_false);
        semantic
            .replace_expr_kind_for_test(
                if_true,
                SemanticCExprKind::MemoryRead {
                    access: StructuredAccessId {
                        inst: r2ssa::InstId(0),
                        ordinal: 0,
                    },
                    object: ObjectId(0),
                    space: r2ssa::MachineAddressSpace::Ram,
                    endianness: MachineMemoryEndianness::Little,
                    word_size_bytes: 1,
                    address: if_false,
                    width_bits: 64,
                },
            )
            .expect("corrupt true arm");
        assert_eq!(
            require_select_value_arms(machine_select, &semantic.expressions, if_true, if_false),
            Err(SemanticCError::SelectRequiresValueArms(machine_select))
        );
        assert!(matches!(
            semantic.render_expr(select),
            Err(SemanticCError::SelectRequiresValueArmExpression(id)) if id == select
        ));
    }

    #[test]
    fn partial_projection_keeps_supported_values_and_opens_unsupported_dependencies() {
        let independent = Varnode::unique(0x10, 8);
        let loaded = Varnode::unique(0x18, 8);
        let dependent = Varnode::unique(0x20, 8);
        let mut block = R2ILBlock::new(0x1800, 4);
        block.push(R2ILOp::Copy {
            dst: independent.clone(),
            src: Varnode::constant(7, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(8, 8),
            val: independent,
        });
        block.push(R2ILOp::Load {
            dst: loaded.clone(),
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
        });
        block.push(R2ILOp::IntAdd {
            dst: dependent,
            a: loaded,
            b: Varnode::constant(1, 8),
        });
        let artifact = SsaArtifact::raw(&[block], None).expect("partial artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("certified partial projection");
        let semantic = SemanticCExpressionLayer::from_projection(&certified)
            .expect("partial semantic expressions");

        assert_eq!(semantic.entities().len(), 1);
        assert!(
            !semantic.open_obligations().contains(
                semantic.entities()[0]
                    .source_obligations()
                    .iter()
                    .next()
                    .unwrap()
            )
        );
        for producer in certified.residual_producers() {
            let instruction = certified
                .source()
                .instructions()
                .get(producer)
                .expect("residual source instruction");
            assert!(
                instruction
                    .obligations
                    .iter()
                    .all(|obligation| semantic.open_obligations().contains(obligation))
            );
        }
    }

    #[test]
    fn direct_void_call_preserves_constant_register_argument_value() {
        let target = Varnode::ram(0x7200, 8);
        let mut entry = R2ILBlock::new(0x7100, 4);
        entry.push(R2ILOp::Copy {
            dst: Varnode::register(8, 8),
            src: Varnode::constant(0x2a, 8),
        });
        entry.push(R2ILOp::Call {
            target: target.clone(),
        });
        let fallthrough = R2ILBlock::new(0x7104, 4);
        let mut arch = ArchSpec::new("semantic-call-constant-test");
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        let argument_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 8,
            size: 8,
        };
        let identity =
            SourceCallSiteIdentity::new(0x7100, 1, CanonicalStorageId::from_varnode(&target));
        let interface = SourceCallSiteInterface::new(
            b"semantic-call-constant-revision-1".to_vec(),
            identity,
            true,
            "test-call-abi",
            [SourceCallArgumentSpec::new(0, argument_storage)],
            false,
            false,
            SourceCallResult::Void,
        )
        .expect("callsite interface");
        let artifact = SsaArtifact::raw_with_interfaces(
            &[entry, fallthrough],
            Some(&arch),
            None,
            vec![interface],
        )
        .expect("constant call artifact");
        let certified =
            CertifiedMachineProjection::from_artifact(&artifact).expect("constant call projection");
        let instruction = artifact
            .graph()
            .insts
            .iter()
            .find(|instruction| matches!(instruction.payload, InstPayload::Op(SSAOp::Call { .. })))
            .expect("call instruction");
        let producer = artifact
            .obligations()
            .instruction_for_inst(instruction.id)
            .expect("call disposition")
            .id;
        let witness = certified
            .direct_call_for_producer(producer)
            .expect("certified direct call");
        let semantic = SemanticCExpressionLayer::from_projection(&certified)
            .expect("semantic expression layer");
        let call = semantic_call_from_control(witness, &semantic).expect("semantic direct call");
        let [argument] = call.arguments() else {
            panic!("one exact call argument expected");
        };

        assert!(matches!(
            argument.value(),
            SemanticCCallArgumentValue::Constant(value)
                if value.width_bits() == 64 && value.bits() == 0x2a
        ));
        assert_eq!(argument.binding(), witness.arguments()[0].value().binding());
        assert_eq!(argument.slot(), witness.arguments()[0].slot());
        assert_eq!(argument.ty(), witness.arguments()[0].value().ty());
        assert_eq!(call.source_obligations(), &witness.source_obligations());
        assert_eq!(call.producer(), producer);
        assert_eq!(call.target(), 0x7200);
        assert_eq!(call.fallthrough(), 0x7104);
    }

    #[test]
    fn direct_void_call_preserves_exact_caller_abi_parameter_argument() {
        let target = Varnode::ram(0x7220, 8);
        let parameter = Varnode::register(8, 8);
        let mut entry = R2ILBlock::new(0x7120, 4);
        entry.push(R2ILOp::Copy {
            dst: parameter.clone(),
            src: parameter,
        });
        entry.push(R2ILOp::Call {
            target: target.clone(),
        });
        let fallthrough = R2ILBlock::new(0x7124, 4);
        let mut arch = ArchSpec::new("semantic-call-parameter-test");
        arch.add_register(RegisterDef::new("rdi", 8, 8));
        let argument_storage = CanonicalStorageId {
            space: CanonicalStorageSpace::Register,
            offset: 8,
            size: 8,
        };
        let revision = b"semantic-call-parameter-revision-1";
        let function_interface = SourceFunctionInterface::new(
            revision.to_vec(),
            "test-call-abi",
            [SourceAbiParameterSpec::new(0, argument_storage)],
            SourceFunctionReturn::Void,
            [],
        )
        .expect("function interface");
        let identity =
            SourceCallSiteIdentity::new(0x7120, 1, CanonicalStorageId::from_varnode(&target));
        let call_interface = SourceCallSiteInterface::new(
            revision.to_vec(),
            identity,
            true,
            "test-call-abi",
            [SourceCallArgumentSpec::new(0, argument_storage)],
            false,
            false,
            SourceCallResult::Void,
        )
        .expect("callsite interface");
        let artifact = SsaArtifact::raw_with_interfaces(
            &[entry, fallthrough],
            Some(&arch),
            Some(function_interface),
            vec![call_interface],
        )
        .expect("parameter call artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("parameter call projection");
        let instruction = artifact
            .graph()
            .insts
            .iter()
            .find(|instruction| matches!(instruction.payload, InstPayload::Op(SSAOp::Call { .. })))
            .expect("call instruction");
        let producer = artifact
            .obligations()
            .instruction_for_inst(instruction.id)
            .expect("call disposition")
            .id;
        let witness = certified
            .direct_call_for_producer(producer)
            .expect("certified direct call");
        assert_eq!(
            witness.arguments()[0].origin(),
            &CertifiedCallArgumentOrigin::AbiParameter { index: 0 }
        );
        let semantic = SemanticCExpressionLayer::from_projection(&certified)
            .expect("semantic expression layer");
        let call = semantic_call_from_control(witness, &semantic).expect("semantic direct call");
        let [argument] = call.arguments() else {
            panic!("one exact call argument expected");
        };

        assert_eq!(
            argument.value(),
            &SemanticCCallArgumentValue::AbiParameter {
                index: 0,
                input: semantic
                    .function_interface()
                    .expect("function interface")
                    .parameters()[0]
                    .value()
                    .expect("parameter input"),
            }
        );
        assert_eq!(argument.binding(), witness.arguments()[0].value().binding());
        assert_eq!(argument.slot(), witness.arguments()[0].slot());
        assert_eq!(argument.ty(), witness.arguments()[0].value().ty());
        assert_eq!(call.source_obligations(), &witness.source_obligations());
        assert!(semantic.function_interface().is_some_and(|interface| {
            interface.parameters().len() == 1
                && interface.parameters()[0].index() == 0
                && interface.parameters()[0].storage() == argument_storage
        }));
    }

    #[test]
    fn phi_refuses_before_c_rendering() {
        let accumulator = Varnode::register(0, 8);
        let mut entry = R2ILBlock::new(0x2000, 4);
        entry.push(R2ILOp::Copy {
            dst: accumulator.clone(),
            src: Varnode::constant(0, 8),
        });
        entry.push(R2ILOp::Branch {
            target: Varnode::ram(0x2010, 8),
        });
        let mut header = R2ILBlock::new(0x2010, 4);
        header.push(R2ILOp::CBranch {
            target: Varnode::ram(0x2020, 8),
            cond: Varnode::constant(1, 1),
        });
        let mut exit = R2ILBlock::new(0x2014, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let mut latch = R2ILBlock::new(0x2020, 4);
        latch.push(R2ILOp::IntAdd {
            dst: accumulator.clone(),
            a: accumulator,
            b: Varnode::constant(1, 8),
        });
        latch.push(R2ILOp::Branch {
            target: Varnode::ram(0x2010, 8),
        });
        let artifact =
            SsaArtifact::raw(&[entry, header, exit, latch], None).expect("loop artifact");
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        assert!(matches!(
            SemanticCExpressionLayer::from_certified(&certified),
            Err(SemanticCError::PhiRequiresCertifiedStructuring(_))
        ));
    }

    #[test]
    fn signed_comparison_uses_operand_width_not_boolean_storage_width() {
        let result = Varnode::unique(0x10, 1);
        let mut block = R2ILBlock::new(0x3000, 4);
        block.push(R2ILOp::IntSLess {
            dst: result.clone(),
            a: Varnode::register(0, 8),
            b: Varnode::register(8, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(16, 8),
            val: result,
        });
        let artifact = SsaArtifact::raw(&[block], None).expect("comparison artifact");
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let semantic =
            SemanticCExpressionLayer::from_certified(&certified).expect("semantic C expressions");
        let source = semantic
            .render_test_entity_translation_unit(semantic.entities()[0].producer())
            .expect("rendered semantic C");
        assert!(source.contains("r2s_signed_key"));
        assert!(source.contains("r2s_signed_key((uint64_t)(v_"));
        assert!(source.contains(", 64U) < r2s_signed_key"));
        assert!(source.contains("uint8_t semantic_c_test_kernel("));
        compile_semantic_c(&source);
    }

    #[test]
    fn arithmetic_shift_cast_and_extract_kernels_compile_strict_c11() {
        let wide = Varnode::unique(0x10, 8);
        let difference = Varnode::unique(0x18, 8);
        let shifted_left = Varnode::unique(0x20, 8);
        let shifted_right = Varnode::unique(0x28, 8);
        let shifted_signed = Varnode::unique(0x30, 8);
        let byte = Varnode::unique(0x38, 1);
        let signed_wide = Varnode::unique(0x40, 8);
        let narrow32 = Varnode::unique(0x48, 4);
        let wide32 = Varnode::unique(0x50, 8);
        let narrow16 = Varnode::unique(0x58, 2);
        let wide16 = Varnode::unique(0x60, 8);
        let narrow8 = Varnode::unique(0x68, 1);
        let zero_wide = Varnode::unique(0x70, 8);
        let address = Varnode::register(24, 8);
        let mut block = R2ILBlock::new(0x4000, 4);
        block.push(R2ILOp::IntAdd {
            dst: wide.clone(),
            a: Varnode::register(0, 8),
            b: Varnode::constant(u64::MAX, 8),
        });
        block.push(R2ILOp::IntSub {
            dst: difference.clone(),
            a: wide,
            b: Varnode::register(8, 8),
        });
        block.push(R2ILOp::IntLeft {
            dst: shifted_left.clone(),
            a: difference,
            b: Varnode::register(16, 8),
        });
        block.push(R2ILOp::IntRight {
            dst: shifted_right.clone(),
            a: shifted_left,
            b: Varnode::register(16, 8),
        });
        block.push(R2ILOp::IntSRight {
            dst: shifted_signed.clone(),
            a: shifted_right,
            b: Varnode::register(16, 8),
        });
        block.push(R2ILOp::Subpiece {
            dst: byte.clone(),
            src: shifted_signed,
            offset: 0,
        });
        block.push(R2ILOp::IntSExt {
            dst: signed_wide.clone(),
            src: byte,
        });
        block.push(R2ILOp::Trunc {
            dst: narrow32.clone(),
            src: signed_wide.clone(),
        });
        block.push(R2ILOp::IntZExt {
            dst: wide32.clone(),
            src: narrow32,
        });
        block.push(R2ILOp::Trunc {
            dst: narrow16.clone(),
            src: wide32,
        });
        block.push(R2ILOp::IntZExt {
            dst: wide16.clone(),
            src: narrow16,
        });
        block.push(R2ILOp::Trunc {
            dst: narrow8.clone(),
            src: wide16,
        });
        block.push(R2ILOp::IntZExt {
            dst: zero_wide.clone(),
            src: narrow8,
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: address,
            val: zero_wide,
        });

        let artifact = SsaArtifact::raw(&[block], None).expect("operation artifact");
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let semantic =
            SemanticCExpressionLayer::from_certified(&certified).expect("semantic C expressions");
        let target = semantic.entities().last().expect("last expression");
        let source = semantic
            .render_test_entity_translation_unit(target.producer())
            .expect("rendered semantic C");

        for expected in [
            "r2s_wrap_add",
            "r2s_wrap_sub",
            "r2s_shl",
            "r2s_lshr",
            "r2s_ashr",
            "r2s_sext",
            "uint8_t",
            "uint16_t",
            "uint32_t",
            "uint64_t",
        ] {
            assert!(source.contains(expected), "missing {expected} in {source}");
        }
        compile_semantic_c(&source);
    }
}
