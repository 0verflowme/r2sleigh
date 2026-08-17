//! Closed semantic-C composition for one exact guarded region: one conditional
//! entry whose taken edge skips a single guarded arm, and one shared join that
//! ends in the sole terminal return.
//!
//! The guard contract admits no value merge. Any phi in the sealed source is
//! rejected by the ledger closure, and the renderer additionally scopes
//! arm-defined names to the guarded body so a join that consumed an arm
//! definition can never be rendered.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use r2cert::{
    CERTIFIED_GUARDED_TERMINAL_RETURN_CONTRACT_VERSION, CertifiedArtifactOrigin,
    CertifiedMachineProjection, CertifiedMemoryStatementKind, CertifiedSourceTerminator,
    CertifiedTypedRegionKind, LedgerClosureError, TypedRegionMapping,
    certify_guarded_terminal_return_region,
};
use r2ssa::{
    CanonicalInstructionId, MachineBuildError, MachineValueBinding, MachineValueUse,
    SemanticObligationId, TrustedSsaArtifact,
};
use serde::Serialize;

use crate::certified_control::{
    CertifiedConditionalTransferBlockRegion, ConditionalTransferRegionError,
};
use crate::certified_region::{
    CertifiedSingleBlockAccounting, CertifiedTypedOutputSeal, RegionBuildError,
    RegionObligationMapping, TypedOutputSealError,
};
use crate::semantic_c::{
    SemanticCError, SemanticCHelperSet, SemanticCInputOrigin,
    insert_semantic_c_helpers, logical_return_type, render_logical_parameter_declarations,
    render_logical_return_statement, render_parameter_graph_binding_prologue, storage_type,
    value_name,
};
use crate::semantic_memory_function::{
    PLAIN_RAM_HELPER_DECLARATIONS, memory_helper_name, render_value_use,
};
use crate::semantic_stmt::{SemanticCBlockStepLayer, SemanticCStatementError};

pub const CERTIFIED_GUARDED_RETURN_FUNCTION_SCHEMA_VERSION: u32 =
    CERTIFIED_GUARDED_TERMINAL_RETURN_CONTRACT_VERSION;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum GuardedReturnFunctionScope {
    ClosedThreeBlockGuardWithSharedTerminalReturn,
}

/// Which header edge enters the guarded arm.
///
/// The machine condition is never re-polarized: an arm on the false edge is
/// rendered as an explicit zero test rather than a logical negation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum GuardPolarity {
    ArmOnTrue,
    ArmOnFalse,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedGuardedReturnFunction {
    schema_version: u32,
    scope: GuardedReturnFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    header: CertifiedConditionalTransferBlockRegion,
    arm: SemanticCBlockStepLayer,
    join: SemanticCBlockStepLayer,
    arm_addr: u64,
    join_addr: u64,
    polarity: GuardPolarity,
    merges: Box<[GuardRegionMerge]>,
    return_producer: CanonicalInstructionId,
    mappings: Box<[RegionObligationMapping]>,
    typed_output_seal: CertifiedTypedOutputSeal,
}

#[derive(Debug, Clone, PartialEq)]
pub enum GuardedReturnFunctionError {
    Machine(MachineBuildError),
    Accounting(RegionBuildError),
    Conditional(ConditionalTransferRegionError),
    Statement(SemanticCStatementError),
    LedgerClosure(LedgerClosureError),
    TypedOutputSeal(TypedOutputSealError),
    SemanticC(SemanticCError),
    NotGuardedTopology,
    InvalidGuardedArm(u64),
    InvalidJoin(u64),
    InvalidComposition(Vec<String>),
    MissingFunctionInterface,
    MissingCondition,
    MissingReturnedEntity,
    /// A merge at the join carries a value on some edge that the region cannot
    /// assign, because nothing on that edge defines it.
    UnassignableMerge(CanonicalInstructionId),
    UndefinedValueUse(CanonicalInstructionId),
    UnsupportedMemory(CanonicalInstructionId),
}

impl std::fmt::Display for GuardedReturnFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "guarded-return function composition failed: {self:?}")
    }
}

impl std::error::Error for GuardedReturnFunctionError {}

impl From<MachineBuildError> for GuardedReturnFunctionError {
    fn from(error: MachineBuildError) -> Self {
        Self::Machine(error)
    }
}

impl From<RegionBuildError> for GuardedReturnFunctionError {
    fn from(error: RegionBuildError) -> Self {
        Self::Accounting(error)
    }
}

impl From<ConditionalTransferRegionError> for GuardedReturnFunctionError {
    fn from(error: ConditionalTransferRegionError) -> Self {
        Self::Conditional(error)
    }
}

impl From<SemanticCStatementError> for GuardedReturnFunctionError {
    fn from(error: SemanticCStatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<LedgerClosureError> for GuardedReturnFunctionError {
    fn from(error: LedgerClosureError) -> Self {
        Self::LedgerClosure(error)
    }
}

impl From<TypedOutputSealError> for GuardedReturnFunctionError {
    fn from(error: TypedOutputSealError) -> Self {
        Self::TypedOutputSeal(error)
    }
}

impl From<SemanticCError> for GuardedReturnFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

fn typed_region_mappings(
    accountings: [&CertifiedSingleBlockAccounting; 3],
) -> Vec<TypedRegionMapping> {
    accountings
        .into_iter()
        .flat_map(CertifiedSingleBlockAccounting::mappings)
        .filter_map(|mapping| {
            let [effect] = accountings[0].ledger().effects(mapping.obligation()) else {
                return None;
            };
            Some(TypedRegionMapping::new(
                mapping.obligation(),
                effect.disposition().clone(),
            ))
        })
        .collect()
}

/// One two-way merge the region owns: a C variable declared with the value the
/// header edge carries and reassigned with the value the arm edge carries.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct GuardRegionMerge {
    binding: MachineValueBinding,
    header_binding: MachineValueBinding,
    arm_binding: MachineValueBinding,
    storage_type: &'static str,
}

impl GuardRegionMerge {
    pub const fn binding(&self) -> MachineValueBinding {
        self.binding
    }

    pub const fn header_binding(&self) -> MachineValueBinding {
        self.header_binding
    }

    pub const fn arm_binding(&self) -> MachineValueBinding {
        self.arm_binding
    }
}

/// Binding this layer defines for one sealed value, if any.
fn defined_binding_for_value(
    layer: &SemanticCBlockStepLayer,
    value: r2ssa::ValueId,
) -> Option<MachineValueBinding> {
    layer.steps().iter().find_map(|step| {
        let entity = layer.resolve_value(step.value()?)?;
        (entity.output().value() == value).then(|| entity.output())
    })
}

/// Split the two header successors into the guarded arm and the shared join.
///
/// The arm is the successor whose only successor is the other header successor.
/// A shape where both or neither successor qualifies is not a guard.
fn guard_arm_and_join(
    topology: &r2cert::CertifiedSourceTopology,
    true_target: u64,
    false_target: u64,
) -> Result<(u64, u64, GuardPolarity), GuardedReturnFunctionError> {
    let reaches = |from: u64, to: u64| {
        topology
            .block(from)
            .is_some_and(|block| block.successors() == [to])
    };
    let true_is_arm = reaches(true_target, false_target);
    let false_is_arm = reaches(false_target, true_target);
    match (true_is_arm, false_is_arm) {
        (true, false) => Ok((true_target, false_target, GuardPolarity::ArmOnTrue)),
        (false, true) => Ok((false_target, true_target, GuardPolarity::ArmOnFalse)),
        _ => Err(GuardedReturnFunctionError::NotGuardedTopology),
    }
}

impl CertifiedGuardedReturnFunction {
    pub fn from_artifact(trusted: &TrustedSsaArtifact) -> Result<Self, GuardedReturnFunctionError> {
        let certified = CertifiedMachineProjection::from_artifact(trusted)?;
        Self::from_projection(&certified)
    }

    pub fn from_projection(
        certified: &CertifiedMachineProjection,
    ) -> Result<Self, GuardedReturnFunctionError> {
        let header_addr = certified.topology().entry_addr();
        let header_block = certified
            .topology()
            .block(header_addr)
            .ok_or(GuardedReturnFunctionError::NotGuardedTopology)?;
        let (true_target, false_target) = match header_block.terminator() {
            CertifiedSourceTerminator::ConditionalBranch {
                true_target,
                false_target,
            } => (*true_target, *false_target),
            _ => return Err(GuardedReturnFunctionError::NotGuardedTopology),
        };
        let (arm_addr, join_addr, polarity) =
            guard_arm_and_join(certified.topology(), true_target, false_target)?;

        let join_phis = certified.two_way_join_phis();
        let header = CertifiedConditionalTransferBlockRegion::from_accounting(
            CertifiedSingleBlockAccounting::from_projection_block_with_join_phis(
                certified,
                header_addr,
                join_phis,
            )?,
        )?;
        let arm_accounting = CertifiedSingleBlockAccounting::from_projection_block_with_join_phis(
            certified, arm_addr, join_phis,
        )?;
        validate_guarded_arm(&arm_accounting, join_addr)?;
        let arm = SemanticCBlockStepLayer::from_accounting(arm_accounting)?;
        let join_accounting = CertifiedSingleBlockAccounting::from_projection_block_with_join_phis(
            certified, join_addr, join_phis,
        )?;
        let return_producer = validate_join(&join_accounting)?;
        let join = SemanticCBlockStepLayer::from_accounting(join_accounting)?;

        let mut merges = Vec::new();
        for (binding, origin) in join.accounting().expression_layer().input_origins() {
            let SemanticCInputOrigin::RegionAssignedJoinValue { join_block, .. } = origin else {
                continue;
            };
            let phi = join_phis
                .values()
                .find(|phi| phi.output() == binding.value())
                .filter(|phi| *join_block == join_addr && phi.join_block() == join_addr)
                .ok_or(GuardedReturnFunctionError::NotGuardedTopology)?;
            let header_edge = phi
                .incoming_from(header_addr)
                .ok_or(GuardedReturnFunctionError::NotGuardedTopology)?;
            let arm_edge = phi
                .incoming_from(arm_addr)
                .ok_or(GuardedReturnFunctionError::NotGuardedTopology)?;
            let header_binding = defined_binding_for_value(header.body(), header_edge.value())
                .ok_or(GuardedReturnFunctionError::UnassignableMerge(phi.producer()))?;
            let arm_binding = defined_binding_for_value(&arm, arm_edge.value())
                .or_else(|| defined_binding_for_value(header.body(), arm_edge.value()))
                .ok_or(GuardedReturnFunctionError::UnassignableMerge(phi.producer()))?;
            merges.push(GuardRegionMerge {
                binding: *binding,
                header_binding,
                arm_binding,
                storage_type: storage_type(
                    join.accounting()
                        .expression_layer()
                        .inputs()
                        .get(binding)
                        .map(|(ty, _)| ty)
                        .ok_or(GuardedReturnFunctionError::NotGuardedTopology)?,
                )?,
            });
        }
        let merges = merges.into_boxed_slice();

        let mappings = header
            .mappings()
            .iter()
            .chain(arm.accounting().mappings())
            .chain(join.accounting().mappings())
            .cloned()
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let typed_mappings = typed_region_mappings([
            header.body().accounting(),
            arm.accounting(),
            join.accounting(),
        ]);
        let ledger_closure = certify_guarded_terminal_return_region(
            certified.origin(),
            certified.ledger(),
            typed_mappings,
            certified.two_way_join_phis(),
            header_addr,
            arm_addr,
            join_addr,
        )?;
        let typed_output_seal = CertifiedTypedOutputSeal::new(
            ledger_closure,
            CertifiedTypedRegionKind::GuardedTerminalReturnFunction,
            CERTIFIED_GUARDED_RETURN_FUNCTION_SCHEMA_VERSION,
            [
                header.body().accounting(),
                arm.accounting(),
                join.accounting(),
            ],
        )?;
        let function = Self {
            schema_version: CERTIFIED_GUARDED_RETURN_FUNCTION_SCHEMA_VERSION,
            scope: GuardedReturnFunctionScope::ClosedThreeBlockGuardWithSharedTerminalReturn,
            name: format!("certified_sub_{header_addr:x}"),
            origin: certified.origin().clone(),
            header,
            arm,
            join,
            arm_addr,
            join_addr,
            polarity,
            merges,
            return_producer,
            mappings,
            typed_output_seal,
        };
        let report = function.audit();
        if !report.has_exact_guarded_return() {
            return Err(GuardedReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> GuardedReturnFunctionScope {
        self.scope
    }

    pub const fn polarity(&self) -> GuardPolarity {
        self.polarity
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn header(&self) -> &CertifiedConditionalTransferBlockRegion {
        &self.header
    }

    pub const fn arm(&self) -> &SemanticCBlockStepLayer {
        &self.arm
    }

    pub const fn join(&self) -> &SemanticCBlockStepLayer {
        &self.join
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub const fn typed_output_seal(&self) -> &CertifiedTypedOutputSeal {
        &self.typed_output_seal
    }

    pub fn audit(&self) -> GuardedReturnFunctionAuditReport {
        let mut invalid = Vec::new();
        let header_accounting = self.header.body().accounting();
        let arm_accounting = self.arm.accounting();
        let join_accounting = self.join.accounting();
        if self.schema_version != CERTIFIED_GUARDED_RETURN_FUNCTION_SCHEMA_VERSION {
            invalid.push("guarded-return schema mismatch".to_string());
        }
        if self.scope != GuardedReturnFunctionScope::ClosedThreeBlockGuardWithSharedTerminalReturn {
            invalid.push("guarded-return scope mismatch".to_string());
        }
        if self.origin != *header_accounting.origin()
            || self.origin != *arm_accounting.origin()
            || self.origin != *join_accounting.origin()
        {
            invalid.push("children do not share one exact artifact origin".to_string());
        }
        let interfaces = [
            header_accounting.expression_layer().function_interface(),
            arm_accounting.expression_layer().function_interface(),
            join_accounting.expression_layer().function_interface(),
        ];
        if interfaces[0].is_none()
            || interfaces[0] != interfaces[1]
            || interfaces[0] != interfaces[2]
        {
            invalid.push("children do not share one exact function interface revision".to_string());
        }
        if !self
            .header
            .audit()
            .has_exact_conditional_transfer_accounting()
            || self.header.has_remaining_obligation_residuals()
        {
            invalid.push("nested conditional region is not exact".to_string());
        }
        for (layer, label) in [(&self.arm, "guarded arm"), (&self.join, "join")] {
            let report = layer.accounting().audit();
            if !report.has_exact_source_accounting() || report.has_residuals() {
                invalid.push(format!("{label} accounting is not exact"));
            }
            if !layer.audit().has_exact_source_order() {
                invalid.push(format!("{label} step order is not exact"));
            }
        }
        let topology = self.origin.topology();
        let header_addr = header_accounting.block_addr();
        let selected = BTreeSet::from([header_addr, self.arm_addr, self.join_addr]);
        if topology.entry_addr() != header_addr
            || selected.len() != 3
            || topology.blocks().len() != 3
            || topology
                .blocks()
                .iter()
                .map(|block| block.addr())
                .collect::<BTreeSet<_>>()
                != selected
            || arm_accounting.block_addr() != self.arm_addr
            || join_accounting.block_addr() != self.join_addr
        {
            invalid.push("guarded topology is not the exact selected three blocks".to_string());
        }
        let transfer = self.header.transfer();
        let expected_arm_edge = match self.polarity {
            GuardPolarity::ArmOnTrue => transfer.true_target(),
            GuardPolarity::ArmOnFalse => transfer.false_target(),
        };
        let expected_join_edge = match self.polarity {
            GuardPolarity::ArmOnTrue => transfer.false_target(),
            GuardPolarity::ArmOnFalse => transfer.true_target(),
        };
        if expected_arm_edge != self.arm_addr || expected_join_edge != self.join_addr {
            invalid.push("guard polarity does not match the certified conditional".to_string());
        }
        if !self.typed_output_seal.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::GuardedTerminalReturnFunction,
            CERTIFIED_GUARDED_RETURN_FUNCTION_SCHEMA_VERSION,
            [header_accounting, arm_accounting, join_accounting],
        ) {
            invalid.push("typed-output seal does not match the closed composition".to_string());
        }
        let counted = counts(self.mappings.iter().map(RegionObligationMapping::obligation));
        let duplicate = counted
            .iter()
            .filter(|(_, count)| **count > 1)
            .map(|(obligation, _)| *obligation)
            .collect::<Vec<_>>();
        let mapped = counted.keys().copied().collect::<BTreeSet<_>>();
        let source = self
            .origin
            .source()
            .obligations()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        GuardedReturnFunctionAuditReport {
            missing: source.difference(&mapped).copied().collect(),
            duplicate,
            unexpected: mapped.difference(&source).copied().collect(),
            invalid,
        }
    }

    pub fn render_certified_c(&self) -> Result<String, GuardedReturnFunctionError> {
        let report = self.audit();
        if !report.has_exact_guarded_return() {
            return Err(GuardedReturnFunctionError::InvalidComposition(
                report.invalid,
            ));
        }
        let interface = self
            .header
            .body()
            .accounting()
            .expression_layer()
            .function_interface()
            .ok_or(GuardedReturnFunctionError::MissingFunctionInterface)?;
        let mut output = String::new();
        let mut helpers = SemanticCHelperSet::default();
        output.push_str("#include <stdint.h>\n\n");
        if self.has_memory_statements() {
            output.push_str(PLAIN_RAM_HELPER_DECLARATIONS);
        }
        let helper_insertion = output.len();
        write!(
            &mut output,
            "\n{} {}(",
            logical_return_type(interface)?,
            self.name
        )
        .expect("String writes cannot fail");
        output.push_str(&render_logical_parameter_declarations(interface)?);
        output.push_str(") {\n");
        output.push_str(&render_parameter_graph_binding_prologue(interface)?);

        let mut defined = interface
            .parameters()
            .iter()
            .filter_map(|parameter| parameter.value())
            .collect::<BTreeSet<_>>();
        let region_assigned = self
            .merges
            .iter()
            .map(GuardRegionMerge::binding)
            .collect::<BTreeSet<_>>();
        render_block_steps(
            &mut output,
            self.header.body(),
            "\t",
            &mut defined,
            &region_assigned,
            &mut helpers,
        )?;
        for merge in &self.merges {
            require_defined(merge.header_binding, &defined, self.return_producer)?;
            writeln!(
                &mut output,
                "\t{} {} = {};",
                merge.storage_type,
                value_name(merge.binding),
                value_name(merge.header_binding)
            )
            .expect("String writes cannot fail");
            defined.insert(merge.binding);
        }

        let condition = self.render_condition()?;
        let test = match self.polarity {
            GuardPolarity::ArmOnTrue => {
                format!("(uint8_t)({condition}) != UINT8_C(0)")
            }
            GuardPolarity::ArmOnFalse => {
                format!("(uint8_t)({condition}) == UINT8_C(0)")
            }
        };
        writeln!(&mut output, "\tif ({test}) {{").expect("String writes cannot fail");
        // Arm definitions leave C scope at the closing brace. Restoring the
        // pre-arm set is what makes a join that consumed an arm definition
        // fail to render instead of silently reading a merged value.
        let pre_arm = defined.clone();
        render_block_steps(
            &mut output,
            &self.arm,
            "\t\t",
            &mut defined,
            &region_assigned,
            &mut helpers,
        )?;
        for merge in &self.merges {
            require_defined(merge.arm_binding, &defined, self.return_producer)?;
            writeln!(
                &mut output,
                "\t\t{} = {};",
                value_name(merge.binding),
                value_name(merge.arm_binding)
            )
            .expect("String writes cannot fail");
        }
        defined = pre_arm;
        output.push_str("\t}\n");

        render_block_steps(
            &mut output,
            &self.join,
            "\t",
            &mut defined,
            &region_assigned,
            &mut helpers,
        )?;
        let returned = self
            .join
            .accounting()
            .semantic_returns()
            .iter()
            .find(|returned| returned.producer() == self.return_producer)
            .ok_or(GuardedReturnFunctionError::MissingReturnedEntity)?;
        match returned.values() {
            [] => writeln!(
                &mut output,
                "\t{}",
                render_logical_return_statement(interface, None, &mut helpers)?
            )
            .expect("String writes cannot fail"),
            [value] => {
                require_defined(value.binding(), &defined, self.return_producer)?;
                writeln!(
                    &mut output,
                    "\t{}",
                    render_logical_return_statement(
                        interface,
                        Some(&value_name(value.binding())),
                        &mut helpers,
                    )?
                )
                .expect("String writes cannot fail")
            }
            _ => return Err(GuardedReturnFunctionError::MissingReturnedEntity),
        }
        output.push_str("}\n");
        insert_semantic_c_helpers(&mut output, helper_insertion, &helpers);
        Ok(output)
    }

    fn has_memory_statements(&self) -> bool {
        [self.header.body(), &self.arm, &self.join]
            .into_iter()
            .any(|layer| !layer.accounting().memory_statements().is_empty())
    }

    fn render_condition(&self) -> Result<String, GuardedReturnFunctionError> {
        let condition = self.header.transfer().condition();
        if let Some(value) = condition.constant() {
            return Ok(format!("((uint8_t)UINT64_C(0x{:x}))", value.bits()));
        }
        let binding = condition.binding();
        let expressions = self.header.body().accounting().expression_layer();
        let produced = self.header.body().steps().iter().any(|step| {
            step.value().is_some_and(|reference| {
                self.header
                    .body()
                    .resolve_value(reference)
                    .is_some_and(|entity| entity.output() == binding)
            })
        });
        let abi_input = expressions
            .input_origins()
            .get(&binding)
            .is_some_and(|origin| matches!(origin, SemanticCInputOrigin::AbiParameter { .. }));
        if binding.width_bits() == 8 && (produced || abi_input) {
            Ok(value_name(binding))
        } else {
            Err(GuardedReturnFunctionError::MissingCondition)
        }
    }
}

fn validate_guarded_arm(
    accounting: &CertifiedSingleBlockAccounting,
    join_addr: u64,
) -> Result<(), GuardedReturnFunctionError> {
    let block_addr = accounting.block_addr();
    let invalid = || GuardedReturnFunctionError::InvalidGuardedArm(block_addr);
    let block = accounting.source_block().ok_or_else(invalid)?;
    let reaches_join = match block.terminator() {
        CertifiedSourceTerminator::Branch { target } => *target == join_addr,
        CertifiedSourceTerminator::Fallthrough { next } => *next == join_addr,
        _ => false,
    };
    if !reaches_join
        || block.successors() != [join_addr]
        || !accounting.direct_calls().is_empty()
        || !accounting.conditional_controls().is_empty()
        || !accounting.switch_controls().is_empty()
        || !accounting.return_controls().is_empty()
        || !accounting.semantic_returns().is_empty()
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_join(
    accounting: &CertifiedSingleBlockAccounting,
) -> Result<CanonicalInstructionId, GuardedReturnFunctionError> {
    let block_addr = accounting.block_addr();
    let invalid = || GuardedReturnFunctionError::InvalidJoin(block_addr);
    let block = accounting.source_block().ok_or_else(invalid)?;
    let [returned] = accounting.semantic_returns() else {
        return Err(invalid());
    };
    if accounting.return_controls().len() != 1
        || !matches!(block.terminator(), CertifiedSourceTerminator::Return)
        || !block.successors().is_empty()
        || block.instructions().last() != Some(&returned.producer())
        || !accounting.direct_calls().is_empty()
        || !accounting.direct_controls().is_empty()
        || !accounting.conditional_controls().is_empty()
        || !accounting.switch_controls().is_empty()
    {
        return Err(invalid());
    }
    Ok(returned.producer())
}

fn require_defined(
    binding: MachineValueBinding,
    defined: &BTreeSet<MachineValueBinding>,
    producer: CanonicalInstructionId,
) -> Result<(), GuardedReturnFunctionError> {
    if defined.contains(&binding) {
        Ok(())
    } else {
        Err(GuardedReturnFunctionError::UndefinedValueUse(producer))
    }
}

fn require_use_defined(
    value: &MachineValueUse,
    defined: &BTreeSet<MachineValueBinding>,
    producer: CanonicalInstructionId,
) -> Result<(), GuardedReturnFunctionError> {
    if value.constant().is_some() {
        return Ok(());
    }
    require_defined(value.binding(), defined, producer)
}

/// Render one block's exact source steps, threading the set of C names already
/// in scope so every use is proved defined before it is emitted.
fn render_block_steps(
    output: &mut String,
    layer: &SemanticCBlockStepLayer,
    indent: &str,
    defined: &mut BTreeSet<MachineValueBinding>,
    region_assigned: &BTreeSet<MachineValueBinding>,
    helpers: &mut SemanticCHelperSet,
) -> Result<(), GuardedReturnFunctionError> {
    let expressions = layer.accounting().expression_layer();
    let mut materialized = expressions.materialized_expression_roots(defined)?;
    for step in layer.steps() {
        if let Some(reference) = step.memory() {
            let statement = layer
                .resolve_memory_statement(reference)
                .ok_or(GuardedReturnFunctionError::UnsupportedMemory(step.source()))?;
            require_use_defined(statement.address(), defined, step.source())?;
            let helper = memory_helper_name(statement);
            let address = render_value_use(statement.address());
            match statement.kind() {
                CertifiedMemoryStatementKind::Read { result } => {
                    writeln!(
                        output,
                        "{indent}{} {} = {helper}((uint64_t)({address}));",
                        storage_type(result.ty())?,
                        value_name(result.binding())
                    )
                    .expect("String writes cannot fail");
                    defined.insert(result.binding());
                    if let Some(root) = expressions.memory_read_root(statement)?
                        && materialized.insert(root, result.binding()).is_some()
                    {
                        return Err(GuardedReturnFunctionError::UnsupportedMemory(step.source()));
                    }
                }
                CertifiedMemoryStatementKind::Write { value } => {
                    require_use_defined(value, defined, step.source())?;
                    writeln!(
                        output,
                        "{indent}{helper}((uint64_t)({address}), ({})({}));",
                        storage_type(value.ty())?,
                        render_value_use(value)
                    )
                    .expect("String writes cannot fail");
                }
            }
            continue;
        }
        let Some(reference) = step.value() else {
            continue;
        };
        let entity = layer
            .resolve_value(reference)
            .ok_or(GuardedReturnFunctionError::UnsupportedMemory(step.source()))?;
        // A region-assigned merge is declared and reassigned by the region on
        // each incoming edge, so its own step emits nothing here.
        if region_assigned.contains(&entity.output()) {
            continue;
        }
        writeln!(
            output,
            "{indent}{} {} = {};",
            storage_type(expressions.expr_type(entity.root())?)?,
            value_name(entity.output()),
            expressions.render_expr_with_materialized_roots(entity.root(), &materialized, helpers)?
        )
        .expect("String writes cannot fail");
        defined.insert(entity.output());
        materialized.insert(entity.root(), entity.output());
    }
    Ok(())
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut result = BTreeMap::new();
    for value in values {
        *result.entry(value).or_default() += 1;
    }
    result
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct GuardedReturnFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl GuardedReturnFunctionAuditReport {
    pub fn has_exact_guarded_return(&self) -> bool {
        self.missing.is_empty()
            && self.duplicate.is_empty()
            && self.unexpected.is_empty()
            && self.invalid.is_empty()
    }

    pub fn missing(&self) -> &[SemanticObligationId] {
        &self.missing
    }

    pub fn duplicate(&self) -> &[SemanticObligationId] {
        &self.duplicate
    }

    pub fn unexpected(&self) -> &[SemanticObligationId] {
        &self.unexpected
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }
}
