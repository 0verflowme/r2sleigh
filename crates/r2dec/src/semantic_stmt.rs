//! Source-ordered semantic-C block steps.
//!
//! This layer owns source-ordered value and certified-memory references. It has
//! no block-exit/control node, call/return semantics, executable-C claim, or
//! rendering permission. Exact obligation dispositions, including any retained
//! terminal-control evidence, remain owned by the embedded accounting envelope.

use std::collections::{BTreeMap, BTreeSet};

use r2ssa::{CanonicalInstructionId, SemanticInstructionState};
use serde::Serialize;

use r2cert::CertifiedMemoryStatement;

use crate::certified_region::{CertifiedSingleBlockAccounting, RegionObligationDisposition};
use crate::semantic_c::{SemanticCEntity, SemanticCIdentityScope};

pub const SEMANTIC_C_STATEMENT_SCHEMA_VERSION: u32 = 3;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SemanticCStatementScope {
    SourceOrderedBindingsWithCertifiedMemoryAndOpenBlockExit,
}

/// Stable reference to one sealed memory statement on the same source step.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct SemanticCMemoryStatementRef {
    producer: CanonicalInstructionId,
}

impl SemanticCMemoryStatementRef {
    pub const fn producer(self) -> CanonicalInstructionId {
        self.producer
    }
}

/// Stable reference to a value entity in the owned expression layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct SemanticCEntityRef {
    producer: CanonicalInstructionId,
}

impl SemanticCEntityRef {
    pub const fn producer(self) -> CanonicalInstructionId {
        self.producer
    }
}

/// One canonical source instruction in topology order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCSourceStep {
    source: CanonicalInstructionId,
    state: SemanticInstructionState,
    value: Option<SemanticCEntityRef>,
    memory: Option<SemanticCMemoryStatementRef>,
}

impl SemanticCSourceStep {
    pub const fn source(&self) -> CanonicalInstructionId {
        self.source
    }

    pub const fn state(&self) -> SemanticInstructionState {
        self.state
    }

    pub const fn value(&self) -> Option<SemanticCEntityRef> {
        self.value
    }

    pub const fn memory(&self) -> Option<SemanticCMemoryStatementRef> {
        self.memory
    }
}

/// Partial semantic-C statement layer for one canonical block.
///
/// Residual effects remain mappings in `accounting`; this type is not an
/// executable C region and grants no rendering permission.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCBlockStepLayer {
    schema_version: u32,
    scope: SemanticCStatementScope,
    identity_scope: SemanticCIdentityScope,
    accounting: CertifiedSingleBlockAccounting,
    steps: Box<[SemanticCSourceStep]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticCStatementError {
    InvalidAccounting,
    InvalidConstructedLayer(Vec<String>),
}

impl std::fmt::Display for SemanticCStatementError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "semantic C statement construction failed: {self:?}")
    }
}

impl std::error::Error for SemanticCStatementError {}

impl SemanticCBlockStepLayer {
    pub fn from_accounting(
        accounting: CertifiedSingleBlockAccounting,
    ) -> Result<Self, SemanticCStatementError> {
        if !accounting.audit().has_exact_source_accounting() {
            return Err(SemanticCStatementError::InvalidAccounting);
        }
        let steps = accounting
            .instructions()
            .iter()
            .map(|instruction| SemanticCSourceStep {
                source: instruction.source(),
                state: instruction.state(),
                value: instruction
                    .expression_producer()
                    .map(|producer| SemanticCEntityRef { producer }),
                memory: instruction
                    .statement_producer()
                    .map(|producer| SemanticCMemoryStatementRef { producer }),
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let layer = Self {
            schema_version: SEMANTIC_C_STATEMENT_SCHEMA_VERSION,
            scope:
                SemanticCStatementScope::SourceOrderedBindingsWithCertifiedMemoryAndOpenBlockExit,
            identity_scope: SemanticCIdentityScope::ArtifactLocalHandles,
            accounting,
            steps,
        };
        let report = layer.audit();
        if !report.has_exact_source_order() {
            return Err(SemanticCStatementError::InvalidConstructedLayer(
                report.invalid,
            ));
        }
        Ok(layer)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> SemanticCStatementScope {
        self.scope
    }

    pub const fn identity_scope(&self) -> SemanticCIdentityScope {
        self.identity_scope
    }

    pub const fn accounting(&self) -> &CertifiedSingleBlockAccounting {
        &self.accounting
    }

    pub const fn steps(&self) -> &[SemanticCSourceStep] {
        &self.steps
    }

    pub fn resolve_value(&self, reference: SemanticCEntityRef) -> Option<&SemanticCEntity> {
        if !self.steps.iter().any(|step| step.value == Some(reference)) {
            return None;
        }
        self.accounting
            .expression_layer()
            .entity_for_producer(reference.producer)
    }

    pub fn resolve_memory_statement(
        &self,
        reference: SemanticCMemoryStatementRef,
    ) -> Option<&CertifiedMemoryStatement> {
        if !self.steps.iter().any(|step| step.memory == Some(reference)) {
            return None;
        }
        self.accounting
            .memory_statement_for_producer(reference.producer)
    }

    /// This layer never owns a block exit, even when its embedded accounting
    /// has no residual obligation mappings.
    pub const fn requires_control_region(&self) -> bool {
        true
    }

    pub fn audit(&self) -> SemanticCStepAuditReport {
        let accounting_report = self.accounting.audit();
        let expected_order = self
            .accounting
            .instructions()
            .iter()
            .map(|instruction| instruction.source())
            .collect::<Vec<_>>();
        let actual_counts = counts(self.steps.iter().map(SemanticCSourceStep::source));
        let expected = expected_order.iter().copied().collect::<BTreeSet<_>>();
        let missing = expected
            .iter()
            .copied()
            .filter(|source| !actual_counts.contains_key(source))
            .collect::<Vec<_>>();
        let duplicate = actual_counts
            .iter()
            .filter_map(|(source, count)| (*count > 1).then_some(*source))
            .collect::<Vec<_>>();
        let unexpected = actual_counts
            .keys()
            .copied()
            .filter(|source| !expected.contains(source))
            .collect::<Vec<_>>();
        let actual_order = self
            .steps
            .iter()
            .map(SemanticCSourceStep::source)
            .collect::<Vec<_>>();
        let mut invalid = Vec::new();

        if !accounting_report.has_exact_source_accounting() {
            invalid.push("embedded block accounting is not exact".to_string());
        }
        if self.schema_version != SEMANTIC_C_STATEMENT_SCHEMA_VERSION {
            invalid.push("statement schema version mismatch".to_string());
        }
        if self.scope
            != SemanticCStatementScope::SourceOrderedBindingsWithCertifiedMemoryAndOpenBlockExit
        {
            invalid.push("statement scope mismatch".to_string());
        }
        if self.identity_scope != self.accounting.identity_scope() {
            invalid.push("statement identity scope mismatch".to_string());
        }
        if actual_order != expected_order {
            invalid.push("source step order does not match certified topology".to_string());
        }

        let instructions = self
            .accounting
            .instructions()
            .iter()
            .map(|instruction| (instruction.source(), instruction))
            .collect::<BTreeMap<_, _>>();
        for step in &self.steps {
            let Some(instruction) = instructions.get(&step.source) else {
                continue;
            };
            if step.state != instruction.state() {
                invalid.push(format!("source state mismatch for {}", step.source));
            }
            let expected_value = instruction
                .expression_producer()
                .map(|producer| SemanticCEntityRef { producer });
            if step.value != expected_value {
                invalid.push(format!("value reference mismatch for {}", step.source));
            }
            let expected_memory = instruction
                .statement_producer()
                .map(|producer| SemanticCMemoryStatementRef { producer });
            if step.memory != expected_memory {
                invalid.push(format!("memory reference mismatch for {}", step.source));
            }
            let absorbed = self
                .accounting
                .mappings()
                .iter()
                .filter_map(|mapping| match mapping.disposition() {
                    RegionObligationDisposition::AbsorbedIntoExpression { producer }
                        if *producer == step.source =>
                    {
                        Some(mapping.obligation())
                    }
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            match step.value {
                Some(reference) => {
                    let entity = self.resolve_value(reference);
                    if reference.producer != step.source
                        || entity.is_none_or(|entity| {
                            entity.producer() != step.source
                                || entity.source_obligations() != &absorbed
                        })
                    {
                        invalid.push(format!(
                            "value reference is not grounded for {}",
                            step.source
                        ));
                    }
                }
                None if !absorbed.is_empty() => invalid.push(format!(
                    "absorbed value obligations have no step reference for {}",
                    step.source
                )),
                None => {}
            }
            let absorbed_memory = self
                .accounting
                .mappings()
                .iter()
                .filter_map(|mapping| match mapping.disposition() {
                    RegionObligationDisposition::AbsorbedIntoStatement { producer }
                        if *producer == step.source =>
                    {
                        Some(mapping.obligation())
                    }
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            match step.memory {
                Some(reference) => {
                    let statement = self.resolve_memory_statement(reference);
                    if reference.producer != step.source
                        || statement.is_none_or(|statement| {
                            statement.producer() != step.source
                                || statement.source_obligations() != &absorbed_memory
                        })
                    {
                        invalid.push(format!(
                            "memory reference is not grounded for {}",
                            step.source
                        ));
                    }
                }
                None if !absorbed_memory.is_empty() => invalid.push(format!(
                    "absorbed memory obligations have no step reference for {}",
                    step.source
                )),
                None => {}
            }
            if !absorbed.is_disjoint(&absorbed_memory) {
                invalid.push(format!(
                    "expression and memory statement overlap obligations for {}",
                    step.source
                ));
            }
        }

        SemanticCStepAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
            // This source-step layer deliberately owns no block exit. Even an
            // obligation-free fallthrough remains open until a control-region
            // layer accounts for topology.
            requires_control_region: true,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SemanticCStepAuditReport {
    missing: Vec<CanonicalInstructionId>,
    duplicate: Vec<CanonicalInstructionId>,
    unexpected: Vec<CanonicalInstructionId>,
    invalid: Vec<String>,
    requires_control_region: bool,
}

impl SemanticCStepAuditReport {
    pub fn has_exact_source_order(&self) -> bool {
        self.missing.is_empty()
            && self.duplicate.is_empty()
            && self.unexpected.is_empty()
            && self.invalid.is_empty()
    }

    pub fn missing(&self) -> &[CanonicalInstructionId] {
        &self.missing
    }

    pub fn duplicate(&self) -> &[CanonicalInstructionId] {
        &self.duplicate
    }

    pub fn unexpected(&self) -> &[CanonicalInstructionId] {
        &self.unexpected
    }

    pub fn invalid(&self) -> &[String] {
        &self.invalid
    }

    /// Whether a separate control region must account for the open block exit.
    /// This is independent of residual obligation count.
    pub const fn requires_control_region(&self) -> bool {
        self.requires_control_region
    }
}

fn counts<T: Ord>(values: impl IntoIterator<Item = T>) -> BTreeMap<T, usize> {
    let mut result = BTreeMap::new();
    for value in values {
        *result.entry(value).or_default() += 1;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use r2cert::{CertifiedMachineFunction, CertifiedMachineProjection};
    use r2il::{ArchSpec, Endianness, R2ILBlock, R2ILOp, SpaceId, Varnode};
    use r2ssa::SsaArtifact;

    fn supported_accounting() -> CertifiedSingleBlockAccounting {
        let value = Varnode::unique(0x10, 8);
        let mut block = R2ILBlock::new(0x6000, 4);
        block.push(R2ILOp::IntMult {
            dst: value.clone(),
            a: Varnode::register(0, 8),
            b: Varnode::constant(0x100000001b3, 8),
        });
        block.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(8, 8),
            val: value,
        });
        block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let artifact = SsaArtifact::raw(&[block], None).expect("supported artifact");
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        CertifiedSingleBlockAccounting::from_certified(&certified).expect("source accounting")
    }

    fn typed_memory_accounting() -> CertifiedSingleBlockAccounting {
        let address = Varnode::register(0, 8);
        let loaded = Varnode::unique(0x10, 4);
        let mut block = R2ILBlock::new(0x6050, 4);
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
        let mut arch = ArchSpec::new("semantic-memory-test");
        arch.addr_size = 8;
        arch.set_memory_endianness(Endianness::Little);
        let artifact = SsaArtifact::raw(&[block], Some(&arch)).expect("typed memory artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("certified memory projection");
        CertifiedSingleBlockAccounting::from_projection(&certified)
            .expect("typed memory accounting")
    }

    #[test]
    fn load_and_store_steps_own_exact_memory_statements_without_hiding_expression_openness() {
        let accounting = typed_memory_accounting();
        let memory_mappings = accounting
            .mappings()
            .iter()
            .filter(|mapping| {
                matches!(
                    mapping.disposition(),
                    RegionObligationDisposition::AbsorbedIntoStatement { .. }
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(memory_mappings.len(), 2);
        assert!(memory_mappings.iter().all(|mapping| {
            accounting
                .expression_layer()
                .open_obligations()
                .contains(&mapping.obligation())
        }));

        let layer = SemanticCBlockStepLayer::from_accounting(accounting).expect("memory steps");
        let report = layer.audit();
        assert!(report.has_exact_source_order(), "{report:?}");
        assert!(
            report.requires_control_region(),
            "block exit remains unstructured"
        );
        assert_eq!(layer.steps().len(), 2);
        let load = &layer.steps()[0];
        let store = &layer.steps()[1];
        assert!(load.value().is_some());
        assert!(load.memory().is_some());
        assert!(store.value().is_none());
        assert!(store.memory().is_some());
        assert!(
            layer
                .resolve_memory_statement(load.memory().expect("load memory ref"))
                .is_some()
        );
        assert!(
            layer
                .resolve_memory_statement(store.memory().expect("store memory ref"))
                .is_some()
        );

        let mut missing_reference = layer.clone();
        missing_reference.steps[0].memory = None;
        let report = missing_reference.audit();
        assert!(!report.has_exact_source_order());
        assert!(
            report
                .invalid()
                .iter()
                .any(|reason| reason.contains("memory reference"))
        );
    }

    #[test]
    fn source_steps_reference_values_only_by_stable_producer() {
        let layer =
            SemanticCBlockStepLayer::from_accounting(supported_accounting()).expect("step layer");
        let report = layer.audit();

        assert!(report.has_exact_source_order(), "{report:?}");
        assert!(report.requires_control_region());
        assert_eq!(layer.steps().len(), layer.accounting().instructions().len());
        let value_step = layer
            .steps()
            .iter()
            .find(|step| step.value().is_some())
            .expect("value step");
        let reference = value_step.value().expect("value reference");
        assert_eq!(reference.producer(), value_step.source());
        assert!(layer.resolve_value(reference).is_some());
    }

    #[test]
    fn deleting_or_reordering_source_steps_fails_audit() {
        let mut deleted =
            SemanticCBlockStepLayer::from_accounting(supported_accounting()).expect("step layer");
        let removed = deleted.steps[0].source;
        let mut steps = deleted.steps.to_vec();
        steps.remove(0);
        deleted.steps = steps.into_boxed_slice();
        let report = deleted.audit();
        assert!(!report.has_exact_source_order());
        assert!(report.missing().contains(&removed));

        let mut reordered =
            SemanticCBlockStepLayer::from_accounting(supported_accounting()).expect("step layer");
        reordered.steps.swap(0, 1);
        let report = reordered.audit();
        assert!(!report.has_exact_source_order());
        assert!(
            report
                .invalid()
                .iter()
                .any(|reason| reason.contains("source step order"))
        );
    }

    #[test]
    fn unsupported_value_chain_remains_steps_with_residuals() {
        let loaded = Varnode::unique(0x10, 8);
        let sum = Varnode::unique(0x18, 8);
        let mut block = R2ILBlock::new(0x6100, 4);
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
        let artifact = SsaArtifact::raw(&[block], None).expect("unsupported artifact");
        let certified = CertifiedMachineProjection::from_artifact(&artifact)
            .expect("certified partial projection");
        let accounting = CertifiedSingleBlockAccounting::from_projection(&certified)
            .expect("partial accounting");
        let layer = SemanticCBlockStepLayer::from_accounting(accounting).expect("step layer");
        let report = layer.audit();

        assert!(report.has_exact_source_order(), "{report:?}");
        assert!(report.requires_control_region());
        assert!(layer.steps().iter().all(|step| step.value().is_none()));
    }

    #[test]
    fn block_local_resolver_rejects_another_blocks_value_reference() {
        let first_value = Varnode::unique(0x10, 8);
        let second_value = Varnode::unique(0x18, 8);
        let mut first = R2ILBlock::new(0x6200, 4);
        first.push(R2ILOp::Copy {
            dst: first_value.clone(),
            src: Varnode::constant(1, 8),
        });
        first.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(0, 8),
            val: first_value,
        });
        first.push(R2ILOp::Branch {
            target: Varnode::ram(0x6210, 8),
        });
        let mut second = R2ILBlock::new(0x6210, 4);
        second.push(R2ILOp::Copy {
            dst: second_value.clone(),
            src: Varnode::constant(2, 8),
        });
        second.push(R2ILOp::Store {
            space: SpaceId::Ram,
            addr: Varnode::register(8, 8),
            val: second_value,
        });
        let artifact = SsaArtifact::raw(&[first, second], None).expect("two-block artifact");
        let certified =
            CertifiedMachineFunction::from_artifact(&artifact).expect("certified machine");
        let first = SemanticCBlockStepLayer::from_accounting(
            CertifiedSingleBlockAccounting::from_certified_block(&certified, 0x6200)
                .expect("first accounting"),
        )
        .expect("first step layer");
        let second = SemanticCBlockStepLayer::from_accounting(
            CertifiedSingleBlockAccounting::from_certified_block(&certified, 0x6210)
                .expect("second accounting"),
        )
        .expect("second step layer");
        let second_reference = second
            .steps()
            .iter()
            .find_map(SemanticCSourceStep::value)
            .expect("second value reference");

        assert!(second.resolve_value(second_reference).is_some());
        assert!(first.resolve_value(second_reference).is_none());
    }
}
