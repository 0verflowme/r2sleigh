//! Closed semantic-C functions with certified plain RAM memory effects.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFICATION_SCHEMA_VERSION, CERTIFIED_PLAIN_RAM_MEMORY_RETURN_CONTRACT_VERSION,
    CertifiedArtifactOrigin, CertifiedFramePreservation, CertifiedMachineProjection,
    CertifiedMemoryExecutionPolicy, CertifiedMemoryStatement, CertifiedMemoryStatementKind,
    CertifiedNormalizedStackRange, CertifiedPrivateFrameValueFlow, CertifiedPrivateStackRegion,
    CertifiedSourceTerminator, CertifiedStackDiscipline, CertifiedTypedRegionKind,
    LedgerClosureError, TypedRegionMapping, certify_plain_ram_memory_return_region,
};
use r2ssa::{
    CanonicalInstructionId, MachineAddressSpace, MachineBuildError, MachineMemoryEndianness,
    MachineType, MachineValueBinding, MachineValueUse, ObjectId, SemanticInstructionState,
    SsaArtifact, TrustedSsaArtifact,
};
use serde::Serialize;

use crate::certified_region::{
    CertifiedSingleBlockAccounting, CertifiedTypedOutputSeal, RegionBuildError,
    RegionObligationDisposition, TypedOutputSealError,
};
use crate::semantic_c::{
    SemanticCError, SemanticCExprId, SemanticCExprKind, SemanticCFunctionReturn,
    SemanticCHelperSet, SemanticCInputOrigin, SemanticCReturn, insert_semantic_c_helpers,
    logical_return_type, render_logical_parameter_declarations, render_logical_return_statement,
    render_parameter_graph_binding_prologue, storage_type, value_name,
};
use crate::semantic_stmt::{SemanticCBlockStepLayer, SemanticCStatementError};

pub const CERTIFIED_MEMORY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_PLAIN_RAM_MEMORY_RETURN_CONTRACT_VERSION;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedMemorySemanticCFunctionScope {
    SingleTerminalReturnBlockWithPlainRamMemory,
}

/// One exact private stack interval projected as a source-ordered C local.
/// The name is renderer-owned; object, range, width, and accesses are retained
/// only from the source-owned stack-discipline and MemorySSA certificates.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct CertifiedPrivateStackLocal {
    local_index: u32,
    object: ObjectId,
    range: CertifiedNormalizedStackRange,
    width_bits: u32,
    memory_order: Box<[CanonicalInstructionId]>,
    address_producers: BTreeSet<CanonicalInstructionId>,
    region: CertifiedPrivateStackRegion,
    load_flows: Box<[CertifiedPrivateFrameValueFlow]>,
}

impl CertifiedPrivateStackLocal {
    pub(crate) const fn local_index(&self) -> u32 {
        self.local_index
    }

    pub(crate) const fn object(&self) -> ObjectId {
        self.object
    }

    pub(crate) const fn range(&self) -> CertifiedNormalizedStackRange {
        self.range
    }

    pub(crate) const fn width_bits(&self) -> u32 {
        self.width_bits
    }

    pub(crate) const fn memory_order(&self) -> &[CanonicalInstructionId] {
        &self.memory_order
    }

    pub(crate) fn address_producers(&self) -> &BTreeSet<CanonicalInstructionId> {
        &self.address_producers
    }

    pub(crate) const fn load_flows(&self) -> &[CertifiedPrivateFrameValueFlow] {
        &self.load_flows
    }
}

/// A sealed complete function for the narrow plain-RAM helper ABI.
///
/// The duplicated memory and return manifests are intentional mutation guards:
/// rendering is permitted only while they exactly match the source-ordered
/// typed block and the final source return.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedMemorySemanticCFunction {
    schema_version: u32,
    scope: CertifiedMemorySemanticCFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    layer: SemanticCBlockStepLayer,
    memory_order: Box<[CanonicalInstructionId]>,
    private_stack_locals: Box<[CertifiedPrivateStackLocal]>,
    private_stack_discipline: Option<CertifiedStackDiscipline>,
    frame_preservation: Option<CertifiedFramePreservation>,
    return_producer: CanonicalInstructionId,
    returned_value: Option<MachineValueBinding>,
    typed_output_seal: CertifiedTypedOutputSeal,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CertifiedMemorySemanticCFunctionError {
    Machine(MachineBuildError),
    Region(RegionBuildError),
    Statement(SemanticCStatementError),
    LedgerClosure(LedgerClosureError),
    TypedOutputSeal(TypedOutputSealError),
    MissingFunctionInterface,
    NotClosedTerminalReturn,
    MissingMemory,
    UnsupportedInput,
    UnsupportedMemory(CanonicalInstructionId),
    UnsupportedPrivateStack(CanonicalInstructionId),
    InvalidReturn,
    UndefinedValue(MachineValueBinding),
    InvalidFunction(Vec<String>),
    SemanticC(SemanticCError),
}

impl std::fmt::Display for CertifiedMemorySemanticCFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "certified memory semantic C function failed: {self:?}")
    }
}

impl std::error::Error for CertifiedMemorySemanticCFunctionError {}

impl From<MachineBuildError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RegionBuildError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: RegionBuildError) -> Self {
        Self::Region(error)
    }
}

impl From<SemanticCStatementError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<LedgerClosureError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: LedgerClosureError) -> Self {
        Self::LedgerClosure(error)
    }
}

impl From<TypedOutputSealError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: TypedOutputSealError) -> Self {
        Self::TypedOutputSeal(error)
    }
}

impl From<SemanticCError> for CertifiedMemorySemanticCFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

fn typed_region_mappings(accounting: &CertifiedSingleBlockAccounting) -> Vec<TypedRegionMapping> {
    accounting
        .mappings()
        .iter()
        .filter_map(|mapping| {
            let [effect] = accounting.ledger().effects(mapping.obligation()) else {
                return None;
            };
            Some(TypedRegionMapping::new(
                mapping.obligation(),
                effect.disposition().clone(),
            ))
        })
        .collect()
}

fn memory_order(layer: &SemanticCBlockStepLayer) -> Vec<CanonicalInstructionId> {
    layer
        .steps()
        .iter()
        .filter_map(|step| step.memory().map(|_| step.source()))
        .collect()
}

fn private_stack_locals(
    artifact: &SsaArtifact,
    certified: &CertifiedMachineProjection,
    layer: &SemanticCBlockStepLayer,
) -> Result<Vec<CertifiedPrivateStackLocal>, CertifiedMemorySemanticCFunctionError> {
    let Some(stack) = certified.stack_discipline() else {
        return Ok(Vec::new());
    };
    if stack.origin() != certified.origin() {
        return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
            vec!["private stack discipline origin mismatch".to_string()],
        ));
    }

    let mut access_regions = BTreeMap::new();
    for (region_index, region) in stack.private_regions().iter().enumerate() {
        let [object] = region.objects() else {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["private stack local does not name exactly one object".to_string()],
            ));
        };
        let range = region.accessed_range();
        let width_bits = range.size_bytes().checked_mul(8).ok_or_else(|| {
            CertifiedMemorySemanticCFunctionError::InvalidFunction(vec![
                "private stack local width overflow".to_string(),
            ])
        })?;
        if !matches!(width_bits, 8 | 16 | 32 | 64) {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["private stack local has an unsupported scalar width".to_string()],
            ));
        }
        for access in region.accesses() {
            let statement = access.statement();
            if statement.object() != *object
                || access.range() != range
                || statement.width_bits() != width_bits
            {
                return Err(
                    CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(
                        statement.producer(),
                    ),
                );
            }
            if access_regions
                .insert(statement.access(), (region_index, access))
                .is_some()
            {
                return Err(
                    CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(
                        statement.producer(),
                    ),
                );
            }
        }
    }

    let mut selected = vec![Vec::new(); stack.private_regions().len()];
    let mut selected_flows = vec![Vec::new(); stack.private_regions().len()];
    let mut selected_address_producers = vec![BTreeSet::new(); stack.private_regions().len()];
    let mut allowed_address_users = BTreeMap::new();
    let mut initialized = vec![false; stack.private_regions().len()];
    for step in layer.steps() {
        let Some(reference) = step.memory() else {
            continue;
        };
        let statement = layer.resolve_memory_statement(reference).ok_or(
            CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
        )?;
        let Some((region_index, access)) = access_regions.get(&statement.access()).copied() else {
            continue;
        };
        if access.statement() != statement || step.source() != statement.producer() {
            return Err(
                CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(step.source()),
            );
        }
        if let Some(producer) = statement.address().producer() {
            let definition = artifact
                .graph()
                .def_inst(statement.address().binding().value())
                .ok_or(
                    CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(step.source()),
                )?;
            let source = artifact
                .obligations()
                .instruction_for_inst(definition)
                .ok_or(
                    CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(step.source()),
                )?;
            let instruction = artifact.graph().inst(definition).ok_or(
                CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(step.source()),
            )?;
            if source.id != producer
                || instruction.output != Some(statement.address().binding().value())
            {
                return Err(
                    CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(step.source()),
                );
            }
            selected_address_producers[region_index].insert(producer);
            allowed_address_users
                .entry(statement.address().binding().value())
                .or_insert_with(BTreeSet::new)
                .insert(statement.access().inst);
        }
        match statement.kind() {
            CertifiedMemoryStatementKind::Write { .. } => initialized[region_index] = true,
            CertifiedMemoryStatementKind::Read { .. } => {
                if !initialized[region_index] {
                    return Err(
                        CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(
                            step.source(),
                        ),
                    );
                }
                let region = &stack.private_regions()[region_index];
                let flow = certified
                    .private_frame_value_flow(statement.access())
                    .ok_or(
                        CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(
                            step.source(),
                        ),
                    )?;
                if flow.origin() != certified.origin()
                    || flow.region() != region
                    || flow.object() != statement.object()
                    || flow.range() != access.range()
                    || flow.load().statement() != statement
                    || flow.root_version().object != statement.object()
                    || flow.definition(flow.root_version()).is_none()
                {
                    return Err(
                        CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(
                            step.source(),
                        ),
                    );
                }
                selected_flows[region_index].push(flow.clone());
            }
        }
        selected[region_index].push(step.source());
    }

    for (address, allowed_users) in allowed_address_users {
        if artifact
            .graph()
            .use_sites(address)
            .iter()
            .any(|use_site| !allowed_users.contains(&use_site.inst))
        {
            let producer = artifact
                .graph()
                .def_inst(address)
                .and_then(|definition| artifact.obligations().instruction_for_inst(definition))
                .map_or(
                    CanonicalInstructionId {
                        block_addr: artifact.function().entry,
                        site: r2ssa::CanonicalInstructionSite::Op(0),
                    },
                    |source| source.id,
                );
            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(producer));
        }
    }

    let mut locals = Vec::new();
    for (region_index, region) in stack.private_regions().iter().enumerate() {
        let order = std::mem::take(&mut selected[region_index]);
        let flows = std::mem::take(&mut selected_flows[region_index]);
        let address_producers = std::mem::take(&mut selected_address_producers[region_index]);
        if order.is_empty() {
            continue;
        }
        let [object] = region.objects() else {
            unreachable!("private regions were validated above")
        };
        let width_bits = region
            .accessed_range()
            .size_bytes()
            .checked_mul(8)
            .expect("private region width was validated above");
        locals.push(CertifiedPrivateStackLocal {
            local_index: u32::try_from(region_index).map_err(|_| {
                CertifiedMemorySemanticCFunctionError::InvalidFunction(vec![
                    "private stack local index overflow".to_string(),
                ])
            })?,
            object: *object,
            range: region.accessed_range(),
            width_bits,
            memory_order: order.into_boxed_slice(),
            address_producers,
            region: region.clone(),
            load_flows: flows.into_boxed_slice(),
        });
    }
    Ok(locals)
}

impl CertifiedMemorySemanticCFunction {
    /// Construct the complete proof chain internally from one immutable trusted
    /// source artifact. No caller-supplied permit or typed node can cross this seam.
    pub fn from_artifact(
        trusted: &TrustedSsaArtifact,
    ) -> Result<Self, CertifiedMemorySemanticCFunctionError> {
        let function = Self::build_from_artifact(trusted)?;
        function.render_body()?;
        Ok(function)
    }

    /// Build the exact source-ordered memory substrate for a stronger typed
    /// renderer whose signature and lvalue spelling are sealed separately.
    pub(crate) fn from_artifact_for_typed_layer(
        trusted: &TrustedSsaArtifact,
    ) -> Result<Self, CertifiedMemorySemanticCFunctionError> {
        Self::build_from_artifact(trusted)
    }

    fn build_from_artifact(
        trusted: &TrustedSsaArtifact,
    ) -> Result<Self, CertifiedMemorySemanticCFunctionError> {
        let certified = CertifiedMachineProjection::from_artifact(trusted)?;
        let accounting = CertifiedSingleBlockAccounting::from_projection(&certified)?;
        let accounting_audit = accounting.audit();
        if !accounting_audit.has_exact_source_accounting() {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["source accounting does not exactly cover the selected artifact".to_string()],
            ));
        }
        if accounting_audit.has_residuals()
            || accounting.mappings().iter().any(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::Residualized { .. }
                )
            })
        {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["source accounting retains residual obligations".to_string()],
            ));
        }
        if accounting.expression_layer().function_interface().is_none() {
            return Err(CertifiedMemorySemanticCFunctionError::MissingFunctionInterface);
        }
        if accounting
            .expression_layer()
            .input_origins()
            .values()
            .any(|origin| {
                matches!(
                    origin,
                    SemanticCInputOrigin::StackSlot { .. }
                        | SemanticCInputOrigin::UnclassifiedSource
                )
            })
        {
            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedInput);
        }
        let Some(block) = accounting.source_block() else {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["source accounting does not select exactly one block".to_string()],
            ));
        };
        if accounting.topology().entry_addr() != block.addr()
            || !block.predecessors().is_empty()
            || !matches!(block.terminator(), CertifiedSourceTerminator::Return)
            || !block.successors().is_empty()
            || !accounting.direct_calls().is_empty()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
            || accounting.instructions().iter().any(|instruction| {
                instruction.state() == SemanticInstructionState::UnsupportedUnknown
                    || matches!(
                        instruction.source().site,
                        r2ssa::CanonicalInstructionSite::Phi(_)
                    )
            })
        {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["source block is not one closed supported terminal-return block".to_string()],
            ));
        }
        let [returned] = accounting.semantic_returns() else {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidReturn);
        };
        if accounting.return_controls().len() != 1
            || block.instructions().last() != Some(&returned.producer())
        {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidReturn);
        }
        let returned_value = match returned.values() {
            [] => None,
            [value] => Some(value.binding()),
            _ => return Err(CertifiedMemorySemanticCFunctionError::InvalidReturn),
        };
        let return_producer = returned.producer();
        let layer = SemanticCBlockStepLayer::from_accounting(accounting)?;
        if layer.steps().last().map(|step| step.source()) != Some(return_producer) {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidReturn);
        }
        let memory_order = memory_order(&layer);
        if memory_order.is_empty() {
            return Err(CertifiedMemorySemanticCFunctionError::MissingMemory);
        }
        let private_stack_locals = private_stack_locals(trusted.artifact(), &certified, &layer)?;
        let private_stack_discipline = (!private_stack_locals.is_empty())
            .then(|| certified.stack_discipline().cloned())
            .flatten();
        let frame_preservation = (!private_stack_locals.is_empty())
            .then(|| certified.frame_preservation().cloned())
            .flatten();
        let mappings = typed_region_mappings(layer.accounting());
        let ledger_closure = certify_plain_ram_memory_return_region(
            layer.accounting().origin(),
            layer.accounting().ledger(),
            mappings,
        )?;
        let typed_output_seal = CertifiedTypedOutputSeal::new(
            ledger_closure,
            CertifiedTypedRegionKind::PlainRamMemoryTerminalReturnFunction,
            CERTIFIED_MEMORY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            [layer.accounting()],
        )?;
        let function = Self {
            schema_version: CERTIFIED_MEMORY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            scope:
                CertifiedMemorySemanticCFunctionScope::SingleTerminalReturnBlockWithPlainRamMemory,
            name: format!("certified_mem_sub_{:x}", layer.accounting().block_addr()),
            origin: layer.accounting().origin().clone(),
            layer,
            memory_order: memory_order.into_boxed_slice(),
            private_stack_locals: private_stack_locals.into_boxed_slice(),
            private_stack_discipline,
            frame_preservation,
            return_producer,
            returned_value,
            typed_output_seal,
        };
        let audit = function.audit();
        if !audit.has_exact_closed_memory_return() {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                audit.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> CertifiedMemorySemanticCFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn layer(&self) -> &SemanticCBlockStepLayer {
        &self.layer
    }

    pub const fn memory_order(&self) -> &[CanonicalInstructionId] {
        &self.memory_order
    }

    pub(crate) fn private_stack_access_map(
        &self,
    ) -> Result<
        BTreeMap<CanonicalInstructionId, &CertifiedPrivateStackLocal>,
        CertifiedMemorySemanticCFunctionError,
    > {
        let mut accesses = BTreeMap::new();
        for local in &self.private_stack_locals {
            for producer in local.memory_order() {
                if accesses.insert(*producer, local).is_some() {
                    return Err(
                        CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(*producer),
                    );
                }
            }
        }
        Ok(accesses)
    }

    pub(crate) const fn private_stack_locals(&self) -> &[CertifiedPrivateStackLocal] {
        &self.private_stack_locals
    }

    pub(crate) fn non_private_memory_order(
        &self,
    ) -> Result<Vec<CanonicalInstructionId>, CertifiedMemorySemanticCFunctionError> {
        let private = self.private_stack_access_map()?;
        Ok(self
            .memory_order
            .iter()
            .filter(|producer| !private.contains_key(producer))
            .copied()
            .collect())
    }

    pub(crate) fn private_stack_address_producers(&self) -> BTreeSet<CanonicalInstructionId> {
        self.private_stack_locals
            .iter()
            .flat_map(|local| local.address_producers().iter().copied())
            .collect()
    }

    pub(crate) fn private_stack_transport_producers(&self) -> BTreeSet<CanonicalInstructionId> {
        let mut producers = self
            .private_stack_discipline
            .iter()
            .flat_map(|stack| {
                stack
                    .assignments()
                    .iter()
                    .map(|assignment| assignment.producer())
            })
            .collect::<BTreeSet<_>>();
        if let Some(frame) = &self.frame_preservation {
            producers.insert(frame.frame_relation().producer());
            producers.extend(
                frame
                    .entry_save_copies()
                    .iter()
                    .map(|copy| copy.entity().producer()),
            );
            for restore in frame.restores() {
                producers.extend(restore.restore_copies().iter().map(|copy| copy.producer()));
                producers.insert(restore.restore_assignment().producer());
            }
        }
        producers
    }

    pub fn returned(&self) -> Option<&SemanticCReturn> {
        self.layer
            .accounting()
            .semantic_returns()
            .iter()
            .find(|returned| returned.producer() == self.return_producer)
    }

    pub fn audit(&self) -> CertifiedMemorySemanticCFunctionAuditReport {
        let mut invalid = Vec::new();
        let accounting = self.layer.accounting();
        if self.schema_version != CERTIFIED_MEMORY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION {
            invalid.push("memory function schema mismatch".to_string());
        }
        if self.scope
            != CertifiedMemorySemanticCFunctionScope::SingleTerminalReturnBlockWithPlainRamMemory
        {
            invalid.push("memory function scope mismatch".to_string());
        }
        if self.origin != *accounting.origin() {
            invalid.push("memory function origin mismatch".to_string());
        }
        if !self.typed_output_seal.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::PlainRamMemoryTerminalReturnFunction,
            CERTIFIED_MEMORY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            [accounting],
        ) {
            invalid.push("memory function typed-output seal mismatch".to_string());
        }
        if !self.layer.audit().has_exact_source_order()
            || !accounting.audit().has_exact_source_accounting()
            || accounting.audit().has_residuals()
        {
            invalid.push("memory function source accounting is not exact".to_string());
        }
        let Some(block) = accounting.source_block() else {
            invalid.push("memory function has no source block".to_string());
            return CertifiedMemorySemanticCFunctionAuditReport { invalid };
        };
        if accounting.topology().entry_addr() != block.addr()
            || !block.predecessors().is_empty()
            || !matches!(block.terminator(), CertifiedSourceTerminator::Return)
            || !block.successors().is_empty()
            || block.instructions().last() != Some(&self.return_producer)
            || self.layer.steps().last().map(|step| step.source()) != Some(self.return_producer)
            || !accounting.direct_calls().is_empty()
            || !accounting.direct_controls().is_empty()
            || !accounting.conditional_controls().is_empty()
        {
            invalid.push("memory function is not one closed terminal-return block".to_string());
        }
        if accounting.instructions().iter().any(|instruction| {
            instruction.state() == SemanticInstructionState::UnsupportedUnknown
                || matches!(
                    instruction.source().site,
                    r2ssa::CanonicalInstructionSite::Phi(_)
                )
        }) {
            invalid.push("memory function contains unsupported source semantics".to_string());
        }
        if accounting
            .expression_layer()
            .input_origins()
            .values()
            .any(|origin| {
                matches!(
                    origin,
                    SemanticCInputOrigin::StackSlot { .. }
                        | SemanticCInputOrigin::UnclassifiedSource
                )
            })
        {
            invalid.push("memory function contains a stack or unclassified input".to_string());
        }
        let actual_memory_order = memory_order(&self.layer);
        if actual_memory_order.is_empty()
            || actual_memory_order.as_slice() != self.memory_order.as_ref()
        {
            invalid.push("memory effect manifest differs from source order".to_string());
        }
        if let Err(error) = self.validate_private_stack_manifest() {
            invalid.push(format!("private stack local manifest is invalid: {error}"));
        }
        let returned = self.returned();
        let actual_returned_value = returned.and_then(|returned| match returned.values() {
            [] => Some(None),
            [value] => Some(Some(value.binding())),
            _ => None,
        });
        if accounting.semantic_returns().len() != 1
            || accounting.return_controls().len() != 1
            || actual_returned_value != Some(self.returned_value)
        {
            invalid.push(
                "returned value manifest differs from the exact interface return".to_string(),
            );
        }
        if let Err(error) = self.validate_render_sequence() {
            invalid.push(format!("memory render sequence is invalid: {error}"));
        }
        CertifiedMemorySemanticCFunctionAuditReport { invalid }
    }

    fn validate_private_stack_manifest(&self) -> Result<(), CertifiedMemorySemanticCFunctionError> {
        let mut local_indices = BTreeSet::new();
        let mut statements = BTreeMap::new();
        for step in self.layer.steps() {
            let Some(reference) = step.memory() else {
                continue;
            };
            let statement = self.layer.resolve_memory_statement(reference).ok_or(
                CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
            )?;
            statements.insert(step.source(), statement);
        }
        let access_map = self.private_stack_access_map()?;
        match (
            &self.private_stack_discipline,
            self.private_stack_locals.is_empty(),
        ) {
            (None, true) => {}
            (Some(stack), false)
                if stack.schema_version() == CERTIFICATION_SCHEMA_VERSION
                    && stack.origin() == &self.origin => {}
            _ => {
                return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                    vec!["private stack discipline owner mismatch".to_string()],
                ));
            }
        }
        if self
            .frame_preservation
            .as_ref()
            .is_some_and(|frame| frame.origin() != &self.origin)
        {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["private frame-preservation owner mismatch".to_string()],
            ));
        }
        let mut address_producers = BTreeSet::new();
        for local in &self.private_stack_locals {
            if !local_indices.insert(local.local_index())
                || local.region.objects() != [local.object()]
                || local.region.accessed_range() != local.range()
                || self.private_stack_discipline.as_ref().is_none_or(|stack| {
                    !stack
                        .private_regions()
                        .iter()
                        .any(|region| region == &local.region)
                })
                || local.range().size_bytes().checked_mul(8) != Some(local.width_bits())
                || local.memory_order().is_empty()
            {
                return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                    vec!["private stack local identity mismatch".to_string()],
                ));
            }
            if local
                .address_producers()
                .iter()
                .any(|producer| !address_producers.insert(*producer))
            {
                return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                    vec!["private stack address producer is shared across locals".to_string()],
                ));
            }
            let mut load_flows = local
                .load_flows
                .iter()
                .map(|flow| (flow.load().statement().access(), flow))
                .collect::<BTreeMap<_, _>>();
            if load_flows.len() != local.load_flows.len() {
                return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                    vec!["private stack local repeats a load-flow certificate".to_string()],
                ));
            }
            for producer in local.memory_order() {
                let statement = statements.get(producer).copied().ok_or(
                    CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(*producer),
                )?;
                let access = local
                    .region
                    .accesses()
                    .iter()
                    .find(|access| access.statement() == statement)
                    .ok_or(
                        CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(*producer),
                    )?;
                if statement.object() != local.object()
                    || statement.width_bits() != local.width_bits()
                    || access.range() != local.range()
                {
                    return Err(
                        CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(*producer),
                    );
                }
                if statement
                    .address()
                    .producer()
                    .is_some_and(|producer| !local.address_producers().contains(&producer))
                {
                    return Err(
                        CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(*producer),
                    );
                }
                if matches!(statement.kind(), CertifiedMemoryStatementKind::Read { .. }) {
                    let flow = load_flows.remove(&statement.access()).ok_or(
                        CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(*producer),
                    )?;
                    if flow.origin() != &self.origin
                        || flow.region() != &local.region
                        || flow.object() != local.object()
                        || flow.range() != local.range()
                        || flow.load().statement() != statement
                        || flow.root_version().object != local.object()
                        || flow.definition(flow.root_version()).is_none()
                    {
                        return Err(
                            CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(
                                *producer,
                            ),
                        );
                    }
                }
            }
            if !load_flows.is_empty() {
                return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                    vec!["private stack local retains an unused load-flow certificate".to_string()],
                ));
            }
        }
        if access_map
            .keys()
            .any(|producer| !self.memory_order.contains(producer))
        {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["private stack local access is absent from memory order".to_string()],
            ));
        }
        for producer in address_producers {
            let entity = self
                .layer
                .steps()
                .iter()
                .find(|step| step.source() == producer)
                .and_then(|step| step.value())
                .and_then(|reference| self.layer.resolve_value(reference))
                .ok_or(CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(producer))?;
            if !self.private_stack_locals.iter().any(|local| {
                local.memory_order().iter().any(|memory_producer| {
                    statements.get(memory_producer).is_some_and(|statement| {
                        statement.address().producer() == Some(producer)
                            && statement.address().binding() == entity.output()
                    })
                })
            }) {
                return Err(
                    CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(producer),
                );
            }
        }
        Ok(())
    }

    /// Render strict C11. Public RAM stays behind the declared helper ABI;
    /// exact private stack regions are scalar-replaced only while their sealed
    /// stack-discipline and MemorySSA witnesses remain intact.
    pub fn render_certified_c(&self) -> Result<String, CertifiedMemorySemanticCFunctionError> {
        let report = self.audit();
        if !report.has_exact_closed_memory_return() {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                report.invalid,
            ));
        }
        self.render_body()
    }

    fn render_body(&self) -> Result<String, CertifiedMemorySemanticCFunctionError> {
        self.validate_render_sequence()?;
        let expressions = self.layer.accounting().expression_layer();
        let interface = expressions
            .function_interface()
            .ok_or(CertifiedMemorySemanticCFunctionError::MissingFunctionInterface)?;
        let return_type = logical_return_type(interface)?;
        let mut output = String::new();
        let mut helpers = SemanticCHelperSet::default();
        output.push_str("#include <stdint.h>\n\n");
        let helper_insertion = output.len();
        output.push('\n');
        output.push_str(PLAIN_RAM_HELPER_DECLARATIONS);
        write!(&mut output, "\n{return_type} {}(", self.name).expect("String writes cannot fail");
        output.push_str(&render_logical_parameter_declarations(interface)?);
        output.push_str(") {\n");
        output.push_str(&render_parameter_graph_binding_prologue(interface)?);
        let mut defined = interface
            .parameters()
            .iter()
            .filter_map(|parameter| parameter.value())
            .collect::<BTreeSet<_>>();
        let mut materialized = expressions.materialized_expression_roots(&defined)?;
        let private_stack = self.private_stack_access_map()?;
        let private_stack_address_producers = self.private_stack_address_producers();
        let private_stack_transport_producers = self.private_stack_transport_producers();
        let mut initialized_private_stack = BTreeSet::new();
        for step in self.layer.steps() {
            if let Some(reference) = step.memory() {
                let statement = self.layer.resolve_memory_statement(reference).ok_or(
                    CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
                )?;
                if let Some(local) = private_stack.get(&step.source()) {
                    let local_name = private_stack_local_name(local);
                    match statement.kind() {
                        CertifiedMemoryStatementKind::Read { result } => {
                            let root = expressions.memory_read_root(statement)?;
                            let ty = storage_type(result.ty())?;
                            writeln!(
                                &mut output,
                                "\t{ty} {} = ({ty}){local_name};",
                                value_name(result.binding()),
                            )
                            .expect("String writes cannot fail");
                            defined.insert(result.binding());
                            if let Some(root) = root
                                && materialized.insert(root, result.binding()).is_some()
                            {
                                return Err(
                                    CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                                        step.source(),
                                    ),
                                );
                            }
                        }
                        CertifiedMemoryStatementKind::Write { value } => {
                            let ty = storage_type(value.ty())?;
                            if initialized_private_stack.insert(local.local_index()) {
                                writeln!(
                                    &mut output,
                                    "\t{ty} {local_name} = ({ty})({});",
                                    render_value_use(value),
                                )
                                .expect("String writes cannot fail");
                            } else {
                                writeln!(
                                    &mut output,
                                    "\t{local_name} = ({ty})({});",
                                    render_value_use(value),
                                )
                                .expect("String writes cannot fail");
                            }
                        }
                    }
                    continue;
                }
                let helper = memory_helper_name(statement);
                let address = render_value_use(statement.address());
                match statement.kind() {
                    CertifiedMemoryStatementKind::Read { result } => {
                        let root = expressions.memory_read_root(statement)?;
                        writeln!(
                            &mut output,
                            "\t{} {} = {helper}((uint64_t)({address}));",
                            storage_type(result.ty())?,
                            value_name(result.binding())
                        )
                        .expect("String writes cannot fail");
                        defined.insert(result.binding());
                        if let Some(root) = root
                            && materialized.insert(root, result.binding()).is_some()
                        {
                            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                                step.source(),
                            ));
                        }
                    }
                    CertifiedMemoryStatementKind::Write { value } => {
                        writeln!(
                            &mut output,
                            "\t{helper}((uint64_t)({address}), ({})({}));",
                            storage_type(value.ty())?,
                            render_value_use(value)
                        )
                        .expect("String writes cannot fail");
                    }
                }
                continue;
            }
            if private_stack_address_producers.contains(&step.source())
                || private_stack_transport_producers.contains(&step.source())
            {
                continue;
            }
            let Some(reference) = step.value() else {
                continue;
            };
            let entity = self.layer.resolve_value(reference).ok_or(
                CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
            )?;
            writeln!(
                &mut output,
                "\t{} {} = {};",
                storage_type(expressions.expr_type(entity.root())?)?,
                value_name(entity.output()),
                expressions.render_expr_with_materialized_roots(
                    entity.root(),
                    &materialized,
                    &mut helpers,
                )?
            )
            .expect("String writes cannot fail");
            defined.insert(entity.output());
            if materialized
                .insert(entity.root(), entity.output())
                .is_some()
            {
                return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                    step.source(),
                ));
            }
        }
        let returned_name = self.returned_value.map(value_name);
        writeln!(
            &mut output,
            "\t{}",
            render_logical_return_statement(interface, returned_name.as_deref(), &mut helpers)?
        )
        .expect("String writes cannot fail");
        output.push_str("}\n");
        insert_semantic_c_helpers(&mut output, helper_insertion, &helpers);
        Ok(output)
    }

    fn validate_render_sequence(&self) -> Result<(), CertifiedMemorySemanticCFunctionError> {
        let expressions = self.layer.accounting().expression_layer();
        let interface = expressions
            .function_interface()
            .ok_or(CertifiedMemorySemanticCFunctionError::MissingFunctionInterface)?;
        let mut defined = interface
            .parameters()
            .iter()
            .filter_map(|parameter| parameter.value())
            .collect::<BTreeSet<_>>();
        let mut observed_memory = Vec::new();
        let private_stack = self.private_stack_access_map()?;
        let private_stack_address_producers = self.private_stack_address_producers();
        let private_stack_transport_producers = self.private_stack_transport_producers();
        let mut initialized_private_stack = BTreeSet::new();
        let mut materialized = expressions.materialized_expression_roots(&defined)?;
        for step in self.layer.steps() {
            if let Some(reference) = step.memory() {
                let statement = self.layer.resolve_memory_statement(reference).ok_or(
                    CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
                )?;
                validate_memory_statement(statement)?;
                let private_local = private_stack.get(&step.source()).copied();
                if let Some(local) = private_local {
                    if local.object() != statement.object()
                        || local.width_bits() != statement.width_bits()
                    {
                        return Err(
                            CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(
                                step.source(),
                            ),
                        );
                    }
                } else {
                    require_value_use_defined(statement.address(), &defined)?;
                }
                observed_memory.push(statement.producer());
                match statement.kind() {
                    CertifiedMemoryStatementKind::Read { result } => {
                        if private_local.is_some_and(|local| {
                            !initialized_private_stack.contains(&local.local_index())
                        }) {
                            return Err(
                                CertifiedMemorySemanticCFunctionError::UnsupportedPrivateStack(
                                    step.source(),
                                ),
                            );
                        }
                        let root = expressions.memory_read_root(statement)?;
                        let entity = step
                            .value()
                            .and_then(|reference| self.layer.resolve_value(reference));
                        if entity.is_some_and(|entity| {
                            entity.output() != result.binding() || Some(entity.root()) != root
                        }) {
                            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                                step.source(),
                            ));
                        }
                        if let Some(root) = root
                            && materialized.insert(root, result.binding()).is_some()
                        {
                            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                                step.source(),
                            ));
                        }
                        defined.insert(result.binding());
                    }
                    CertifiedMemoryStatementKind::Write { value } => {
                        if step.value().is_some() {
                            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                                step.source(),
                            ));
                        }
                        require_value_use_defined(value, &defined)?;
                        if let Some(local) = private_local {
                            initialized_private_stack.insert(local.local_index());
                        }
                    }
                }
                continue;
            }
            if private_stack_address_producers.contains(&step.source())
                || private_stack_transport_producers.contains(&step.source())
            {
                continue;
            }
            if let Some(reference) = step.value() {
                let entity = self.layer.resolve_value(reference).ok_or(
                    CertifiedMemorySemanticCFunctionError::UnsupportedMemory(step.source()),
                )?;
                let mut inputs = BTreeSet::new();
                collect_expression_inputs(
                    expressions,
                    entity.root(),
                    &materialized,
                    &mut BTreeSet::new(),
                    &mut inputs,
                )?;
                if let Some(undefined) = inputs.iter().find(|binding| !defined.contains(binding)) {
                    return Err(CertifiedMemorySemanticCFunctionError::UndefinedValue(
                        *undefined,
                    ));
                }
                expressions.render_expr_with_materialized_roots(
                    entity.root(),
                    &materialized,
                    &mut SemanticCHelperSet::default(),
                )?;
                defined.insert(entity.output());
                if materialized
                    .insert(entity.root(), entity.output())
                    .is_some()
                {
                    return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                        step.source(),
                    ));
                }
            }
        }
        if observed_memory.as_slice() != self.memory_order.as_ref() {
            return Err(CertifiedMemorySemanticCFunctionError::InvalidFunction(
                vec!["memory effect order mismatch".to_string()],
            ));
        }
        match (interface.return_kind(), self.returned_value) {
            (SemanticCFunctionReturn::Void, None) => {}
            (SemanticCFunctionReturn::Register { ty, .. }, Some(binding))
                if binding.width_bits() == ty.width_bits() && defined.contains(&binding) => {}
            _ => return Err(CertifiedMemorySemanticCFunctionError::InvalidReturn),
        }
        Ok(())
    }
}

pub(crate) fn private_stack_local_name(local: &CertifiedPrivateStackLocal) -> String {
    format!("r2s_stack_{}", local.local_index())
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedMemorySemanticCFunctionAuditReport {
    invalid: Vec<String>,
}

impl CertifiedMemorySemanticCFunctionAuditReport {
    pub fn has_exact_closed_memory_return(&self) -> bool {
        self.invalid.is_empty()
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }
}

fn validate_memory_statement(
    statement: &CertifiedMemoryStatement,
) -> Result<(), CertifiedMemorySemanticCFunctionError> {
    if statement.space() != MachineAddressSpace::Ram
        || statement.word_size_bytes() != 1
        || !matches!(statement.width_bits(), 8 | 16 | 32 | 64)
        || !matches!(
            statement.endianness(),
            MachineMemoryEndianness::Little | MachineMemoryEndianness::Big
        )
        || statement.execution() != CertifiedMemoryExecutionPolicy::ExactlyOnceInSourceOrder
        || !matches!(
            statement.address().ty(),
            MachineType::Address {
                space: MachineAddressSpace::Ram,
                width_bits: 8 | 16 | 32 | 64,
                ..
            }
        )
    {
        return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
            statement.producer(),
        ));
    }
    Ok(())
}

fn require_value_use_defined(
    value: &MachineValueUse,
    defined: &BTreeSet<MachineValueBinding>,
) -> Result<(), CertifiedMemorySemanticCFunctionError> {
    if value.constant().is_none() && !defined.contains(&value.binding()) {
        return Err(CertifiedMemorySemanticCFunctionError::UndefinedValue(
            value.binding(),
        ));
    }
    Ok(())
}

fn collect_expression_inputs(
    expressions: &crate::semantic_c::SemanticCExpressionLayer,
    expression: SemanticCExprId,
    materialized: &BTreeMap<SemanticCExprId, MachineValueBinding>,
    visited: &mut BTreeSet<SemanticCExprId>,
    inputs: &mut BTreeSet<MachineValueBinding>,
) -> Result<(), CertifiedMemorySemanticCFunctionError> {
    if !visited.insert(expression) {
        return Ok(());
    }
    if let Some(binding) = materialized.get(&expression) {
        inputs.insert(*binding);
        return Ok(());
    }
    let expression =
        expressions
            .expr(expression)
            .ok_or(CertifiedMemorySemanticCFunctionError::SemanticC(
                SemanticCError::MissingSemanticExpression(expression),
            ))?;
    match expression.kind() {
        SemanticCExprKind::Input { binding } => {
            inputs.insert(*binding);
        }
        SemanticCExprKind::Constant { .. } => {}
        SemanticCExprKind::MemoryRead { .. } => {
            eprintln!("unmaterialized memory read expression {expression:?}");
            return Err(CertifiedMemorySemanticCFunctionError::UnsupportedMemory(
                expression
                    .source_instructions()
                    .iter()
                    .next_back()
                    .copied()
                    .unwrap_or(CanonicalInstructionId {
                        block_addr: 0,
                        site: r2ssa::CanonicalInstructionSite::Op(0),
                    }),
            ));
        }
        SemanticCExprKind::Copy { input }
        | SemanticCExprKind::BitwiseNot { input }
        | SemanticCExprKind::BooleanNot { input }
        | SemanticCExprKind::Cast { input, .. }
        | SemanticCExprKind::Extract { input, .. } => {
            collect_expression_inputs(expressions, *input, materialized, visited, inputs)?;
        }
        SemanticCExprKind::Arithmetic { left, right, .. }
        | SemanticCExprKind::ArithmeticFlag { left, right, .. }
        | SemanticCExprKind::Bitwise { left, right, .. }
        | SemanticCExprKind::Boolean { left, right, .. }
        | SemanticCExprKind::Compare { left, right, .. } => {
            collect_expression_inputs(expressions, *left, materialized, visited, inputs)?;
            collect_expression_inputs(expressions, *right, materialized, visited, inputs)?;
        }
        SemanticCExprKind::Shift { value, count, .. } => {
            collect_expression_inputs(expressions, *value, materialized, visited, inputs)?;
            collect_expression_inputs(expressions, *count, materialized, visited, inputs)?;
        }
        SemanticCExprKind::Select {
            condition,
            if_true,
            if_false,
        } => {
            collect_expression_inputs(expressions, *condition, materialized, visited, inputs)?;
            collect_expression_inputs(expressions, *if_true, materialized, visited, inputs)?;
            collect_expression_inputs(expressions, *if_false, materialized, visited, inputs)?;
        }
    }
    Ok(())
}

pub(crate) fn render_value_use(value: &MachineValueUse) -> String {
    value.constant().map_or_else(
        || value_name(value.binding()),
        |constant| format!("UINT64_C(0x{:x})", constant.bits()),
    )
}

pub(crate) fn memory_helper_name(statement: &CertifiedMemoryStatement) -> &'static str {
    match (
        statement.kind(),
        statement.endianness(),
        statement.width_bits(),
    ) {
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Little, 8) => {
            "r2s_ram_read_le_u8"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Little, 16) => {
            "r2s_ram_read_le_u16"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Little, 32) => {
            "r2s_ram_read_le_u32"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Little, 64) => {
            "r2s_ram_read_le_u64"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Big, 8) => {
            "r2s_ram_read_be_u8"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Big, 16) => {
            "r2s_ram_read_be_u16"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Big, 32) => {
            "r2s_ram_read_be_u32"
        }
        (CertifiedMemoryStatementKind::Read { .. }, MachineMemoryEndianness::Big, 64) => {
            "r2s_ram_read_be_u64"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Little, 8) => {
            "r2s_ram_write_le_u8"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Little, 16) => {
            "r2s_ram_write_le_u16"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Little, 32) => {
            "r2s_ram_write_le_u32"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Little, 64) => {
            "r2s_ram_write_le_u64"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Big, 8) => {
            "r2s_ram_write_be_u8"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Big, 16) => {
            "r2s_ram_write_be_u16"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Big, 32) => {
            "r2s_ram_write_be_u32"
        }
        (CertifiedMemoryStatementKind::Write { .. }, MachineMemoryEndianness::Big, 64) => {
            "r2s_ram_write_be_u64"
        }
        _ => unreachable!("memory statement is validated before helper selection"),
    }
}

pub(crate) const PLAIN_RAM_HELPER_DECLARATIONS: &str = r#"extern uint8_t r2s_ram_read_le_u8(uint64_t byte_address);
extern uint16_t r2s_ram_read_le_u16(uint64_t byte_address);
extern uint32_t r2s_ram_read_le_u32(uint64_t byte_address);
extern uint64_t r2s_ram_read_le_u64(uint64_t byte_address);
extern uint8_t r2s_ram_read_be_u8(uint64_t byte_address);
extern uint16_t r2s_ram_read_be_u16(uint64_t byte_address);
extern uint32_t r2s_ram_read_be_u32(uint64_t byte_address);
extern uint64_t r2s_ram_read_be_u64(uint64_t byte_address);
extern void r2s_ram_write_le_u8(uint64_t byte_address, uint8_t value);
extern void r2s_ram_write_le_u16(uint64_t byte_address, uint16_t value);
extern void r2s_ram_write_le_u32(uint64_t byte_address, uint32_t value);
extern void r2s_ram_write_le_u64(uint64_t byte_address, uint64_t value);
extern void r2s_ram_write_be_u8(uint64_t byte_address, uint8_t value);
extern void r2s_ram_write_be_u16(uint64_t byte_address, uint16_t value);
extern void r2s_ram_write_be_u32(uint64_t byte_address, uint32_t value);
extern void r2s_ram_write_be_u64(uint64_t byte_address, uint64_t value);
"#;
