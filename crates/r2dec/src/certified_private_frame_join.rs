//! Proof-bound rewrite inputs for one certified private-frame conditional join.
//!
//! This module seals only an artifact-local substitution plan. It does not
//! authorize C rendering, relax memory-read handling, or close typed-output
//! obligations.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use r2cert::{
    CERTIFICATION_SCHEMA_VERSION, CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION,
    CertifiedArtifactOrigin, CertifiedControlTruthiness, CertifiedLedgerClosure,
    CertifiedMachineProjection, CertifiedMemoryStatement, CertifiedMemoryStatementKind,
    CertifiedPrivateFrameConditionalArm, CertifiedPrivateFrameConditionalJoin,
    CertifiedPrivateFrameStore, CertifiedPrivateFrameValueFlow, CertifiedStackDiscipline,
    CertifiedTypedRegionKind, LedgerClosureError, TypedRegionMapping,
    certify_private_frame_conditional_join_region,
};
use r2ssa::{
    CanonicalInstructionId, CanonicalStorageId, MachineBitVector, MachineBuildError, MachineType,
    MachineValueBinding, MachineValueUse, SemanticObligationId, StructuredAccessId,
    TrustedSsaArtifact,
};
use serde::Serialize;

use crate::certified_region::{
    CertifiedSingleBlockAccounting, CertifiedTypedOutputSeal, RegionBuildError,
    RegionObligationMapping, TypedOutputSealError,
};
use crate::semantic_c::{
    SEMANTIC_C_SCHEMA_VERSION, SemanticCEntity, SemanticCError, SemanticCExprId, SemanticCExprKind,
    SemanticCExpressionLayer, SemanticCInputOrigin, SemanticCMemoryRewrite, SemanticCReturnOperand,
    SemanticCTypedLeaf, insert_semantic_c_helpers, logical_return_type,
    render_logical_return_statement, semantic_return_from_control, storage_type, value_name,
};

pub const CERTIFIED_PRIVATE_FRAME_JOIN_REWRITE_SCHEMA_VERSION: u32 = 1;
pub const CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_FUNCTION_SCHEMA_VERSION: u32 = 1;

/// This certificate is an incomplete, non-rendering rewrite plan only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedPrivateFrameConditionalJoinRewriteScope {
    ProofBoundRewritePlanOnly,
}

/// Exact source of a value substituted for one private-frame load.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CertifiedPrivateFrameJoinValueOrigin {
    Produced {
        producer: CanonicalInstructionId,
        root: SemanticCExprId,
    },
    Constant(MachineBitVector),
    AbiParameter {
        index: u32,
        storage: CanonicalStorageId,
    },
}

/// One exact typed machine value and its sealed semantic-C representation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameJoinValue {
    value: MachineValueUse,
    origin: CertifiedPrivateFrameJoinValueOrigin,
}

impl CertifiedPrivateFrameJoinValue {
    pub const fn value(&self) -> &MachineValueUse {
        &self.value
    }

    pub const fn origin(&self) -> &CertifiedPrivateFrameJoinValueOrigin {
        &self.origin
    }
}

/// Exact direct store-to-load substitution used by the condition DAG.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameDirectSubstitution {
    load_access: StructuredAccessId,
    load_result: MachineValueUse,
    load_root: SemanticCExprId,
    replacement: CertifiedPrivateFrameJoinValue,
}

impl CertifiedPrivateFrameDirectSubstitution {
    pub const fn load_access(&self) -> StructuredAccessId {
        self.load_access
    }

    pub const fn load_result(&self) -> &MachineValueUse {
        &self.load_result
    }

    pub const fn load_root(&self) -> SemanticCExprId {
        self.load_root
    }

    pub const fn replacement(&self) -> &CertifiedPrivateFrameJoinValue {
        &self.replacement
    }
}

/// Exact polarity-preserving select replacing the shared joined load.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CertifiedPrivateFrameJoinedSelect {
    condition: MachineValueUse,
    condition_root: SemanticCExprId,
    truthiness: CertifiedControlTruthiness,
    true_value: CertifiedPrivateFrameJoinValue,
    false_value: CertifiedPrivateFrameJoinValue,
    load_access: StructuredAccessId,
    load_result: MachineValueUse,
    load_root: SemanticCExprId,
    return_root: SemanticCExprId,
}

impl CertifiedPrivateFrameJoinedSelect {
    pub const fn condition(&self) -> &MachineValueUse {
        &self.condition
    }

    pub const fn condition_root(&self) -> SemanticCExprId {
        self.condition_root
    }

    pub const fn truthiness(&self) -> CertifiedControlTruthiness {
        self.truthiness
    }

    pub const fn true_value(&self) -> &CertifiedPrivateFrameJoinValue {
        &self.true_value
    }

    pub const fn false_value(&self) -> &CertifiedPrivateFrameJoinValue {
        &self.false_value
    }

    pub const fn load_access(&self) -> StructuredAccessId {
        self.load_access
    }

    pub const fn load_result(&self) -> &MachineValueUse {
        &self.load_result
    }

    pub const fn load_root(&self) -> SemanticCExprId {
        self.load_root
    }

    pub const fn return_root(&self) -> SemanticCExprId {
        self.return_root
    }
}

/// Artifact-bound, non-rendering private-frame conditional-join rewrite plan.
///
/// `expression_layer.open_obligations()` remains authoritative: this type is
/// intentionally not a complete semantic-C function or a typed-output seal.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedPrivateFrameConditionalJoinRewrite {
    schema_version: u32,
    scope: CertifiedPrivateFrameConditionalJoinRewriteScope,
    origin: CertifiedArtifactOrigin,
    machine_join: CertifiedPrivateFrameConditionalJoin,
    expression_layer: SemanticCExpressionLayer,
    direct_substitutions: Box<[CertifiedPrivateFrameDirectSubstitution]>,
    joined_select: CertifiedPrivateFrameJoinedSelect,
    ledger_closure: CertifiedLedgerClosure,
}

impl CertifiedPrivateFrameConditionalJoinRewrite {
    /// Build only from genuine audited ingress. No detached certificate or
    /// caller-authored rewrite input is accepted at this public boundary.
    pub fn from_artifact(
        trusted: &TrustedSsaArtifact,
    ) -> Result<Self, PrivateFrameConditionalJoinRewriteError> {
        let projection = CertifiedMachineProjection::from_artifact(trusted)
            .map_err(PrivateFrameConditionalJoinRewriteError::MachineProjection)?;
        let header = projection.topology().entry_addr();
        if projection.private_frame_conditional_joins().len() != 1 {
            return Err(PrivateFrameConditionalJoinRewriteError::MissingExactJoin);
        }
        let join = projection
            .private_frame_conditional_join(header)
            .ok_or(PrivateFrameConditionalJoinRewriteError::MissingExactJoin)?;
        let stack = projection
            .stack_discipline()
            .ok_or(PrivateFrameConditionalJoinRewriteError::MissingStackDiscipline)?;
        Self::from_certified_parts(trusted, &projection, join, stack)
    }

    fn from_certified_parts(
        trusted: &TrustedSsaArtifact,
        projection: &CertifiedMachineProjection,
        join: &CertifiedPrivateFrameConditionalJoin,
        stack: &CertifiedStackDiscipline,
    ) -> Result<Self, PrivateFrameConditionalJoinRewriteError> {
        if projection.origin().schema_version() != CERTIFICATION_SCHEMA_VERSION
            || join.schema_version() != CERTIFICATION_SCHEMA_VERSION
            || join.origin() != projection.origin()
            || stack.schema_version() != CERTIFICATION_SCHEMA_VERSION
            || stack.origin() != projection.origin()
            || join.header() != projection.topology().entry_addr()
            || projection.private_frame_conditional_join(join.header()) != Some(join)
            || projection.stack_discipline() != Some(stack)
        {
            return Err(PrivateFrameConditionalJoinRewriteError::InvalidAuthority);
        }

        let expression_layer =
            SemanticCExpressionLayer::from_private_frame_conditional_join(projection, join, stack)
                .map_err(PrivateFrameConditionalJoinRewriteError::SemanticC)?;
        if expression_layer.schema_version() != SEMANTIC_C_SCHEMA_VERSION {
            return Err(PrivateFrameConditionalJoinRewriteError::InvalidAuthority);
        }

        let output_index = EntityOutputIndex::new(&expression_layer);
        let mut direct_substitutions = Vec::with_capacity(join.auxiliary_direct_flows().len());
        let auxiliary_flows = canonicalize_by_access(
            join.auxiliary_direct_flows()
                .iter()
                .map(|(access, flow)| (*access, flow))
                .collect(),
        )?;
        for (access, flow) in auxiliary_flows {
            direct_substitutions.push(direct_substitution(access, flow, &expression_layer)?);
        }

        let joined_select = joined_select(
            join,
            &expression_layer,
            &output_index,
            &direct_substitutions,
        )?;
        let produced_store_roots = direct_substitutions
            .iter()
            .map(CertifiedPrivateFrameDirectSubstitution::replacement)
            .chain([joined_select.true_value(), joined_select.false_value()])
            .filter_map(|value| match value.origin() {
                CertifiedPrivateFrameJoinValueOrigin::Produced { root, .. } => Some(*root),
                CertifiedPrivateFrameJoinValueOrigin::Constant(_)
                | CertifiedPrivateFrameJoinValueOrigin::AbiParameter { .. } => None,
            });
        let store_value_memory = expanded_memory_accesses_from_roots(
            &expression_layer,
            &output_index,
            produced_store_roots,
        )?;
        if let Some(access) = store_value_memory.first() {
            return Err(PrivateFrameConditionalJoinRewriteError::StoreValueReadsMemory(*access));
        }

        let mappings = exact_typed_region_mappings(projection)?;
        let ledger_closure = certify_private_frame_conditional_join_region(
            trusted.artifact(),
            projection.origin(),
            projection.ledger(),
            mappings.clone(),
            join,
        )
        .map_err(PrivateFrameConditionalJoinRewriteError::LedgerClosure)?;
        if !ledger_closure.matches_ledger(
            projection.origin(),
            CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction,
            CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION,
            &mappings,
        ) {
            return Err(PrivateFrameConditionalJoinRewriteError::InvalidAuthority);
        }

        Ok(Self {
            schema_version: CERTIFIED_PRIVATE_FRAME_JOIN_REWRITE_SCHEMA_VERSION,
            scope: CertifiedPrivateFrameConditionalJoinRewriteScope::ProofBoundRewritePlanOnly,
            origin: projection.origin().clone(),
            machine_join: join.clone(),
            expression_layer,
            direct_substitutions: direct_substitutions.into_boxed_slice(),
            joined_select,
            ledger_closure,
        })
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> CertifiedPrivateFrameConditionalJoinRewriteScope {
        self.scope
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn machine_join(&self) -> &CertifiedPrivateFrameConditionalJoin {
        &self.machine_join
    }

    pub const fn expression_layer(&self) -> &SemanticCExpressionLayer {
        &self.expression_layer
    }

    pub const fn direct_substitutions(&self) -> &[CertifiedPrivateFrameDirectSubstitution] {
        &self.direct_substitutions
    }

    pub const fn joined_select(&self) -> &CertifiedPrivateFrameJoinedSelect {
        &self.joined_select
    }

    pub const fn ledger_closure(&self) -> &CertifiedLedgerClosure {
        &self.ledger_closure
    }

    pub const fn open_obligations(&self) -> &BTreeSet<SemanticObligationId> {
        self.expression_layer.open_obligations()
    }
}

/// Closed render authority for the exact private-frame conditional-join
/// function. The nested rewrite remains non-rendering on its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum CertifiedPrivateFrameConditionalJoinFunctionScope {
    ClosedSourceAccountedPrivateFrameConditionalJoin,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct CertifiedPrivateFrameConditionalJoinFunction {
    schema_version: u32,
    scope: CertifiedPrivateFrameConditionalJoinFunctionScope,
    name: String,
    origin: CertifiedArtifactOrigin,
    rewrite: CertifiedPrivateFrameConditionalJoinRewrite,
    accountings: Box<[CertifiedSingleBlockAccounting]>,
    mappings: Box<[RegionObligationMapping]>,
    typed_output_seal: CertifiedTypedOutputSeal,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PrivateFrameConditionalJoinFunctionError {
    MachineProjection(MachineBuildError),
    Rewrite(PrivateFrameConditionalJoinRewriteError),
    Accounting(RegionBuildError),
    TypedOutputSeal(TypedOutputSealError),
    SemanticC(SemanticCError),
    MissingExactJoin,
    MissingStackDiscipline,
    MissingFunctionInterface,
    InvalidComposition(Vec<String>),
}

impl std::fmt::Display for PrivateFrameConditionalJoinFunctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "private-frame conditional-join function failed: {self:?}"
        )
    }
}

impl std::error::Error for PrivateFrameConditionalJoinFunctionError {}

impl From<PrivateFrameConditionalJoinRewriteError> for PrivateFrameConditionalJoinFunctionError {
    fn from(error: PrivateFrameConditionalJoinRewriteError) -> Self {
        Self::Rewrite(error)
    }
}

impl From<RegionBuildError> for PrivateFrameConditionalJoinFunctionError {
    fn from(error: RegionBuildError) -> Self {
        Self::Accounting(error)
    }
}

impl From<TypedOutputSealError> for PrivateFrameConditionalJoinFunctionError {
    fn from(error: TypedOutputSealError) -> Self {
        Self::TypedOutputSeal(error)
    }
}

impl From<SemanticCError> for PrivateFrameConditionalJoinFunctionError {
    fn from(error: SemanticCError) -> Self {
        Self::SemanticC(error)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PrivateFrameConditionalJoinFunctionAuditReport {
    missing: Vec<SemanticObligationId>,
    duplicate: Vec<SemanticObligationId>,
    unexpected: Vec<SemanticObligationId>,
    invalid: Vec<String>,
}

impl PrivateFrameConditionalJoinFunctionAuditReport {
    pub fn has_exact_private_frame_conditional_join(&self) -> bool {
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

fn private_join_value_leaf(
    layer: &SemanticCExpressionLayer,
    value: &CertifiedPrivateFrameJoinValue,
) -> Result<SemanticCTypedLeaf, PrivateFrameConditionalJoinFunctionError> {
    match value.origin() {
        CertifiedPrivateFrameJoinValueOrigin::Produced { producer, root }
            if value.value().producer() == Some(*producer) =>
        {
            Ok(layer.expanded_root_leaf(value.value(), *root, value.value().ty())?)
        }
        CertifiedPrivateFrameJoinValueOrigin::Constant(bits)
            if value.value().constant() == Some(*bits) =>
        {
            Ok(layer.expanded_constant_leaf(value.value())?)
        }
        CertifiedPrivateFrameJoinValueOrigin::AbiParameter { index, storage }
            if layer.input_origins().get(&value.value().binding())
                == Some(&SemanticCInputOrigin::AbiParameter {
                    index: *index,
                    storage: *storage,
                }) =>
        {
            Ok(layer.expanded_abi_input_leaf(value.value())?)
        }
        _ => Err(
            PrivateFrameConditionalJoinFunctionError::InvalidComposition(vec![
                "rewrite value origin no longer matches the sealed expression layer".to_string(),
            ]),
        ),
    }
}

fn private_join_memory_rewrites(
    rewrite: &CertifiedPrivateFrameConditionalJoinRewrite,
) -> Result<Vec<SemanticCMemoryRewrite>, PrivateFrameConditionalJoinFunctionError> {
    let layer = rewrite.expression_layer();
    let mut rewrites = Vec::with_capacity(rewrite.direct_substitutions().len() + 1);
    for substitution in rewrite.direct_substitutions() {
        rewrites.push(layer.direct_memory_rewrite(
            substitution.load_root(),
            substitution.load_access(),
            private_join_value_leaf(layer, substitution.replacement())?,
        )?);
    }
    let joined = rewrite.joined_select();
    if joined.truthiness() != CertifiedControlTruthiness::NonZeroIsTrue {
        return Err(
            PrivateFrameConditionalJoinFunctionError::InvalidComposition(vec![
                "joined select truthiness is not nonzero-is-true".to_string(),
            ]),
        );
    }
    let condition_ty = layer
        .expr(joined.condition_root())
        .ok_or(SemanticCError::MissingSemanticExpression(
            joined.condition_root(),
        ))?
        .ty();
    let condition =
        layer.expanded_root_leaf(joined.condition(), joined.condition_root(), condition_ty)?;
    rewrites.push(layer.nonzero_select_memory_rewrite(
        joined.load_root(),
        joined.load_access(),
        condition,
        private_join_value_leaf(layer, joined.true_value())?,
        private_join_value_leaf(layer, joined.false_value())?,
    )?);
    Ok(rewrites)
}

fn exact_rendered_private_join_return(
    rewrite: &CertifiedPrivateFrameConditionalJoinRewrite,
) -> Result<crate::semantic_c::SemanticCExpandedRender, PrivateFrameConditionalJoinFunctionError> {
    let rewrites = private_join_memory_rewrites(rewrite)?;
    let rendered = rewrite
        .expression_layer()
        .render_expanded_expr(rewrite.joined_select().return_root(), &rewrites)?;
    let expected = rewrite
        .direct_substitutions()
        .iter()
        .map(CertifiedPrivateFrameDirectSubstitution::load_access)
        .chain([rewrite.joined_select().load_access()])
        .collect::<BTreeSet<_>>();
    let consumed = rendered
        .consumed_rewrites()
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    if rendered.consumed_rewrites().len() != expected.len() || consumed != expected {
        return Err(
            PrivateFrameConditionalJoinFunctionError::InvalidComposition(vec![
                "expanded return did not consume the exact private-load manifest".to_string(),
            ]),
        );
    }
    Ok(rendered)
}

impl CertifiedPrivateFrameConditionalJoinFunction {
    pub fn from_artifact(
        trusted: &TrustedSsaArtifact,
    ) -> Result<Self, PrivateFrameConditionalJoinFunctionError> {
        let projection = CertifiedMachineProjection::from_artifact(trusted)
            .map_err(PrivateFrameConditionalJoinFunctionError::MachineProjection)?;
        let header = projection.topology().entry_addr();
        if projection.private_frame_conditional_joins().len() != 1 {
            return Err(PrivateFrameConditionalJoinFunctionError::MissingExactJoin);
        }
        let join = projection
            .private_frame_conditional_join(header)
            .ok_or(PrivateFrameConditionalJoinFunctionError::MissingExactJoin)?;
        let stack = projection
            .stack_discipline()
            .ok_or(PrivateFrameConditionalJoinFunctionError::MissingStackDiscipline)?;
        let rewrite = CertifiedPrivateFrameConditionalJoinRewrite::from_certified_parts(
            trusted,
            &projection,
            join,
            stack,
        )?;
        let accountings = projection
            .topology()
            .blocks()
            .iter()
            .map(|block| {
                CertifiedSingleBlockAccounting::from_private_frame_conditional_join_rewrite_block(
                    &projection,
                    &rewrite,
                    block.addr(),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mappings = accountings
            .iter()
            .flat_map(CertifiedSingleBlockAccounting::mappings)
            .cloned()
            .collect::<Vec<_>>();
        let typed_output_seal = CertifiedTypedOutputSeal::new(
            rewrite.ledger_closure().clone(),
            CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction,
            CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION,
            &accountings,
        )?;
        let function = Self {
            schema_version: CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_FUNCTION_SCHEMA_VERSION,
            scope: CertifiedPrivateFrameConditionalJoinFunctionScope::ClosedSourceAccountedPrivateFrameConditionalJoin,
            name: format!("certified_sub_{header:x}"),
            origin: projection.origin().clone(),
            rewrite,
            accountings: accountings.into_boxed_slice(),
            mappings: mappings.into_boxed_slice(),
            typed_output_seal,
        };
        let report = function.audit();
        if !report.has_exact_private_frame_conditional_join() {
            return Err(
                PrivateFrameConditionalJoinFunctionError::InvalidComposition(report.invalid),
            );
        }
        Ok(function)
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub const fn scope(&self) -> CertifiedPrivateFrameConditionalJoinFunctionScope {
        self.scope
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn origin(&self) -> &CertifiedArtifactOrigin {
        &self.origin
    }

    pub const fn rewrite(&self) -> &CertifiedPrivateFrameConditionalJoinRewrite {
        &self.rewrite
    }

    pub const fn accountings(&self) -> &[CertifiedSingleBlockAccounting] {
        &self.accountings
    }

    pub const fn mappings(&self) -> &[RegionObligationMapping] {
        &self.mappings
    }

    pub fn audit(&self) -> PrivateFrameConditionalJoinFunctionAuditReport {
        let mut invalid = Vec::new();
        let topology = self.origin.topology();
        let expected_blocks = topology
            .blocks()
            .iter()
            .map(|block| block.addr())
            .collect::<Vec<_>>();
        let actual_blocks = self
            .accountings
            .iter()
            .map(CertifiedSingleBlockAccounting::block_addr)
            .collect::<Vec<_>>();
        if self.schema_version != CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_FUNCTION_SCHEMA_VERSION {
            invalid.push("private-frame conditional-join function schema mismatch".to_string());
        }
        if self.scope
            != CertifiedPrivateFrameConditionalJoinFunctionScope::ClosedSourceAccountedPrivateFrameConditionalJoin
        {
            invalid.push("private-frame conditional-join function scope mismatch".to_string());
        }
        if self.name != format!("certified_sub_{:x}", topology.entry_addr()) {
            invalid.push("function name is not derived from the exact entry address".to_string());
        }
        if self.rewrite.origin() != &self.origin
            || self.rewrite.schema_version() != CERTIFIED_PRIVATE_FRAME_JOIN_REWRITE_SCHEMA_VERSION
            || self.rewrite.scope()
                != CertifiedPrivateFrameConditionalJoinRewriteScope::ProofBoundRewritePlanOnly
            || self.rewrite.machine_join().origin() != &self.origin
            || self.rewrite.machine_join().header() != topology.entry_addr()
            || self.rewrite.ledger_closure().origin() != &self.origin
        {
            invalid.push("rewrite does not match the retained function authority".to_string());
        }
        if actual_blocks != expected_blocks
            || self.accountings.len() != topology.blocks().len()
            || self.accountings.iter().any(|accounting| {
                accounting.origin() != &self.origin
                    || accounting.expression_layer() != self.rewrite.expression_layer()
                    || !accounting.audit().has_exact_source_accounting()
                    || accounting.audit().has_residuals()
            })
        {
            invalid.push("source-ordered block accounting is not exact".to_string());
        }

        let expected_mappings = self
            .accountings
            .iter()
            .flat_map(CertifiedSingleBlockAccounting::mappings)
            .cloned()
            .collect::<Vec<_>>();
        let expected_obligations = self
            .origin
            .source()
            .obligations()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let mut counts = BTreeMap::<SemanticObligationId, usize>::new();
        for mapping in &self.mappings {
            *counts.entry(mapping.obligation()).or_default() += 1;
        }
        let actual_obligations = counts.keys().copied().collect::<BTreeSet<_>>();
        let missing = expected_obligations
            .difference(&actual_obligations)
            .copied()
            .collect();
        let unexpected = actual_obligations
            .difference(&expected_obligations)
            .copied()
            .collect();
        let duplicate = counts
            .iter()
            .filter_map(|(obligation, count)| (*count != 1).then_some(*obligation))
            .collect();
        if self.mappings.as_ref() != expected_mappings.as_slice()
            || self.mappings.len() != expected_obligations.len()
            || self
                .mappings
                .iter()
                .any(|mapping| mapping.owner().is_none())
        {
            invalid.push("combined typed-owner mapping union is not exact".to_string());
        }
        if !self.typed_output_seal.matches_region(
            &self.origin,
            CertifiedTypedRegionKind::PrivateFrameConditionalJoinFunction,
            CERTIFIED_PRIVATE_FRAME_CONDITIONAL_JOIN_CONTRACT_VERSION,
            self.accountings.iter(),
        ) {
            invalid.push("typed-output seal does not match the private join region".to_string());
        }
        if exact_rendered_private_join_return(&self.rewrite).is_err() {
            invalid.push("private join expanded-return rewrite is not exact".to_string());
        }
        PrivateFrameConditionalJoinFunctionAuditReport {
            missing,
            duplicate,
            unexpected,
            invalid,
        }
    }

    pub fn render_certified_c(&self) -> Result<String, PrivateFrameConditionalJoinFunctionError> {
        let report = self.audit();
        if !report.has_exact_private_frame_conditional_join() {
            return Err(
                PrivateFrameConditionalJoinFunctionError::InvalidComposition(report.invalid),
            );
        }
        let interface = self
            .rewrite
            .expression_layer()
            .function_interface()
            .ok_or(PrivateFrameConditionalJoinFunctionError::MissingFunctionInterface)?;
        let mut rendered = exact_rendered_private_join_return(&self.rewrite)?;
        let expression = rendered.expression().to_string();
        let returned =
            render_logical_return_statement(interface, Some(&expression), rendered.helpers_mut())?;
        let mut output = String::new();
        output.push_str("#include <stdint.h>\n\n");
        let helper_insertion = output.len();
        write!(
            &mut output,
            "\n{} {}(",
            logical_return_type(interface)?,
            self.name
        )
        .expect("String writes cannot fail");
        if interface.parameters().is_empty() {
            output.push_str("void");
        } else {
            for (position, parameter) in interface.parameters().iter().enumerate() {
                if position > 0 {
                    output.push_str(", ");
                }
                let name = parameter
                    .value()
                    .map(value_name)
                    .unwrap_or_else(|| format!("arg_{}", parameter.index()));
                write!(&mut output, "{} {name}", storage_type(parameter.ty())?)
                    .expect("String writes cannot fail");
            }
        }
        writeln!(&mut output, ") {{\n\t{returned}\n}}").expect("String writes cannot fail");
        insert_semantic_c_helpers(&mut output, helper_insertion, rendered.helpers());
        Ok(output)
    }
}

#[cfg(test)]
pub(crate) fn certified_private_frame_join_rewrite_from_parts_for_test(
    trusted: &TrustedSsaArtifact,
    projection: &CertifiedMachineProjection,
    join: &CertifiedPrivateFrameConditionalJoin,
    stack: &CertifiedStackDiscipline,
) -> Result<CertifiedPrivateFrameConditionalJoinRewrite, PrivateFrameConditionalJoinRewriteError> {
    CertifiedPrivateFrameConditionalJoinRewrite::from_certified_parts(
        trusted, projection, join, stack,
    )
}

#[cfg(test)]
pub(crate) fn canonical_private_frame_accesses_for_test(
    accesses: impl IntoIterator<Item = StructuredAccessId>,
) -> Result<Vec<StructuredAccessId>, PrivateFrameConditionalJoinRewriteError> {
    canonicalize_by_access(accesses.into_iter().map(|access| (access, ())).collect())
        .map(|items| items.into_iter().map(|(access, ())| access).collect())
}

#[cfg(test)]
pub(crate) fn private_frame_condition_accesses_for_test(
    rewrite: &CertifiedPrivateFrameConditionalJoinRewrite,
) -> Result<Vec<StructuredAccessId>, PrivateFrameConditionalJoinRewriteError> {
    let index = EntityOutputIndex::new(rewrite.expression_layer());
    expanded_memory_nodes(
        rewrite.expression_layer(),
        &index,
        [rewrite.joined_select().condition_root()],
    )
    .map(|memory| memory.into_keys().collect())
}

#[derive(Debug, Clone, PartialEq)]
pub enum PrivateFrameConditionalJoinRewriteError {
    MachineProjection(MachineBuildError),
    MissingExactJoin,
    MissingStackDiscipline,
    InvalidAuthority,
    SemanticC(SemanticCError),
    InvalidDirectFlow(StructuredAccessId),
    InvalidJoinedFlow(StructuredAccessId),
    MissingValueExpression(MachineValueBinding),
    AmbiguousEntityOutput(MachineValueBinding),
    AmbiguousMemoryRead(StructuredAccessId),
    StoreValueReadsMemory(StructuredAccessId),
    CyclicExpression(SemanticCExprId),
    InvalidValueOrigin(MachineValueBinding),
    LedgerMapping(SemanticObligationId),
    LedgerClosure(LedgerClosureError),
}

impl std::fmt::Display for PrivateFrameConditionalJoinRewriteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private-frame conditional-join rewrite failed: {self:?}")
    }
}

impl std::error::Error for PrivateFrameConditionalJoinRewriteError {}

fn canonicalize_by_access<T>(
    mut items: Vec<(StructuredAccessId, T)>,
) -> Result<Vec<(StructuredAccessId, T)>, PrivateFrameConditionalJoinRewriteError> {
    items.sort_by_key(|(access, _)| *access);
    if let Some(access) = items
        .windows(2)
        .find_map(|pair| (pair[0].0 == pair[1].0).then_some(pair[0].0))
    {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidDirectFlow(
            access,
        ));
    }
    Ok(items)
}

fn exact_typed_region_mappings(
    projection: &CertifiedMachineProjection,
) -> Result<Vec<TypedRegionMapping>, PrivateFrameConditionalJoinRewriteError> {
    projection
        .source()
        .obligations()
        .keys()
        .map(|obligation| {
            let [effect] = projection.ledger().effects(*obligation) else {
                return Err(PrivateFrameConditionalJoinRewriteError::LedgerMapping(
                    *obligation,
                ));
            };
            Ok(TypedRegionMapping::new(
                *obligation,
                effect.disposition().clone(),
            ))
        })
        .collect()
}

fn statement_load(statement: &CertifiedMemoryStatement) -> Option<&MachineValueUse> {
    match statement.kind() {
        CertifiedMemoryStatementKind::Read { result } => Some(result),
        CertifiedMemoryStatementKind::Write { .. } => None,
    }
}

fn statement_store(statement: &CertifiedMemoryStatement) -> Option<&MachineValueUse> {
    match statement.kind() {
        CertifiedMemoryStatementKind::Write { value } => Some(value),
        CertifiedMemoryStatementKind::Read { .. } => None,
    }
}

fn exact_entity(
    layer: &SemanticCExpressionLayer,
    binding: MachineValueBinding,
    producer: CanonicalInstructionId,
) -> Result<&SemanticCEntity, PrivateFrameConditionalJoinRewriteError> {
    let mut entities = layer
        .entities()
        .iter()
        .filter(|entity| entity.output() == binding && entity.producer() == producer);
    let entity = entities
        .next()
        .ok_or(PrivateFrameConditionalJoinRewriteError::MissingValueExpression(binding))?;
    if entities.next().is_some() {
        return Err(PrivateFrameConditionalJoinRewriteError::AmbiguousEntityOutput(binding));
    }
    Ok(entity)
}

fn exact_value_root(
    value: &MachineValueUse,
    layer: &SemanticCExpressionLayer,
) -> Result<SemanticCExprId, PrivateFrameConditionalJoinRewriteError> {
    let producer = value
        .producer()
        .ok_or(PrivateFrameConditionalJoinRewriteError::MissingValueExpression(value.binding()))?;
    let entity = exact_entity(layer, value.binding(), producer)?;
    if layer
        .expr(entity.root())
        .map(|expression| expression.ty().width_bits())
        != Some(value.ty().width_bits())
    {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidValueOrigin(
            value.binding(),
        ));
    }
    Ok(entity.root())
}

fn exact_load_root(
    statement: &CertifiedMemoryStatement,
    layer: &SemanticCExpressionLayer,
) -> Result<(MachineValueUse, SemanticCExprId), PrivateFrameConditionalJoinRewriteError> {
    let result = statement_load(statement).ok_or(
        PrivateFrameConditionalJoinRewriteError::InvalidDirectFlow(statement.access()),
    )?;
    if result.binding().width_bits() != statement.width_bits()
        || result.ty().width_bits() != statement.width_bits()
        || result.producer() != Some(statement.producer())
    {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidDirectFlow(
            statement.access(),
        ));
    }
    let entity = exact_entity(layer, result.binding(), statement.producer())?;
    let expression = layer
        .expr(entity.root())
        .ok_or(PrivateFrameConditionalJoinRewriteError::MissingValueExpression(result.binding()))?;
    if expression.ty() != result.ty()
        || !matches!(
            expression.kind(),
            SemanticCExprKind::MemoryRead {
                access,
                object,
                space,
                endianness,
                word_size_bytes,
                width_bits,
                ..
            } if *access == statement.access()
                && *object == statement.object()
                && *space == statement.space()
                && *endianness == statement.endianness()
                && *word_size_bytes == statement.word_size_bytes()
                && *width_bits == statement.width_bits()
        )
    {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidDirectFlow(
            statement.access(),
        ));
    }
    Ok((result.clone(), entity.root()))
}

fn exact_join_value(
    value: &MachineValueUse,
    layer: &SemanticCExpressionLayer,
) -> Result<CertifiedPrivateFrameJoinValue, PrivateFrameConditionalJoinRewriteError> {
    if value.binding().width_bits() == 0 || value.ty().width_bits() != value.binding().width_bits()
    {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidValueOrigin(
            value.binding(),
        ));
    }
    let origin = match (value.producer(), value.constant(), value.memory_access()) {
        (Some(producer), None, _) => {
            let entity = exact_entity(layer, value.binding(), producer)?;
            if layer.expr(entity.root()).map(|expression| expression.ty()) != Some(value.ty()) {
                return Err(PrivateFrameConditionalJoinRewriteError::InvalidValueOrigin(
                    value.binding(),
                ));
            }
            CertifiedPrivateFrameJoinValueOrigin::Produced {
                producer,
                root: entity.root(),
            }
        }
        (None, Some(bits), None) if bits.width_bits() == value.binding().width_bits() => {
            CertifiedPrivateFrameJoinValueOrigin::Constant(bits)
        }
        (None, None, None) => {
            let mut parameters = layer
                .function_interface()
                .into_iter()
                .flat_map(|interface| interface.parameters())
                .filter(|parameter| {
                    parameter.value() == Some(value.binding())
                        && parameter.ty() == value.ty()
                        && parameter.storage().size.checked_mul(8)
                            == Some(value.binding().width_bits())
                });
            let parameter = parameters.next().ok_or(
                PrivateFrameConditionalJoinRewriteError::InvalidValueOrigin(value.binding()),
            )?;
            if parameters.next().is_some() {
                return Err(PrivateFrameConditionalJoinRewriteError::InvalidValueOrigin(
                    value.binding(),
                ));
            }
            CertifiedPrivateFrameJoinValueOrigin::AbiParameter {
                index: parameter.index(),
                storage: parameter.storage(),
            }
        }
        _ => {
            return Err(PrivateFrameConditionalJoinRewriteError::InvalidValueOrigin(
                value.binding(),
            ));
        }
    };
    Ok(CertifiedPrivateFrameJoinValue {
        value: value.clone(),
        origin,
    })
}

fn direct_substitution(
    access: StructuredAccessId,
    flow: &CertifiedPrivateFrameValueFlow,
    layer: &SemanticCExpressionLayer,
) -> Result<CertifiedPrivateFrameDirectSubstitution, PrivateFrameConditionalJoinRewriteError> {
    let load = flow.load().statement();
    let definition = flow
        .definition(flow.root_version())
        .and_then(|definition| definition.store())
        .filter(|store| {
            flow.definitions().len() == 1
                && store.next_version() == flow.root_version()
                && statement_store(store.statement()).is_some()
        })
        .ok_or(PrivateFrameConditionalJoinRewriteError::InvalidDirectFlow(
            access,
        ))?;
    if access != load.access() {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidDirectFlow(
            access,
        ));
    }
    let (load_result, load_root) = exact_load_root(load, layer)?;
    let replacement = exact_store_value(definition, layer)?;
    if replacement.value().ty() != load_result.ty()
        || replacement.value().binding().width_bits() != load_result.binding().width_bits()
    {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidDirectFlow(
            access,
        ));
    }
    Ok(CertifiedPrivateFrameDirectSubstitution {
        load_access: access,
        load_result,
        load_root,
        replacement,
    })
}

fn exact_store_value(
    store: &CertifiedPrivateFrameStore,
    layer: &SemanticCExpressionLayer,
) -> Result<CertifiedPrivateFrameJoinValue, PrivateFrameConditionalJoinRewriteError> {
    let value = statement_store(store.statement()).ok_or(
        PrivateFrameConditionalJoinRewriteError::InvalidDirectFlow(store.statement().access()),
    )?;
    if value.binding().width_bits() != store.statement().width_bits()
        || value.ty().width_bits() != store.statement().width_bits()
    {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidValueOrigin(
            value.binding(),
        ));
    }
    exact_join_value(value, layer)
}

fn arm_store_is_exact_definition(
    flow: &CertifiedPrivateFrameValueFlow,
    arm: &CertifiedPrivateFrameConditionalArm,
) -> bool {
    flow.definition(arm.store().next_version())
        .and_then(|definition| definition.store())
        == Some(arm.store())
}

fn joined_select(
    join: &CertifiedPrivateFrameConditionalJoin,
    layer: &SemanticCExpressionLayer,
    output_index: &EntityOutputIndex,
    direct_substitutions: &[CertifiedPrivateFrameDirectSubstitution],
) -> Result<CertifiedPrivateFrameJoinedSelect, PrivateFrameConditionalJoinRewriteError> {
    let flow = join.joined_flow();
    let access = flow.load().statement().access();
    let phi = flow
        .definition(flow.root_version())
        .and_then(|definition| definition.phi())
        .filter(|phi| phi.block_addr() == join.join_block() && phi.inputs().len() == 2)
        .ok_or(PrivateFrameConditionalJoinRewriteError::InvalidJoinedFlow(
            access,
        ))?;
    if join.condition().true_target() != join.true_arm().entry_target()
        || join.condition().false_target() != join.false_arm().entry_target()
        || join.true_arm().store().next_version() == join.false_arm().store().next_version()
        || !arm_store_is_exact_definition(flow, join.true_arm())
        || !arm_store_is_exact_definition(flow, join.false_arm())
    {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidJoinedFlow(
            access,
        ));
    }
    let phi_input = |arm: &CertifiedPrivateFrameConditionalArm| {
        let mut inputs = phi.inputs().iter().filter(|input| {
            input.predecessor() == arm.store_block()
                && input.version() == arm.store().next_version()
        });
        let input = inputs.next();
        (input.is_some() && inputs.next().is_none()).then_some(())
    };
    if phi_input(join.true_arm()).is_none() || phi_input(join.false_arm()).is_none() {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidJoinedFlow(
            access,
        ));
    }

    let condition = join.condition().condition();
    let condition_root = exact_value_root(condition, layer)?;
    let condition_memory = expanded_memory_nodes(layer, output_index, [condition_root])?;
    let auxiliary_accesses = direct_substitutions
        .iter()
        .map(CertifiedPrivateFrameDirectSubstitution::load_access)
        .collect::<BTreeSet<_>>();
    if condition.binding().width_bits() != 8
        || condition.ty().width_bits() != 8
        || join.condition().truthiness() != CertifiedControlTruthiness::NonZeroIsTrue
        || condition_memory.keys().copied().collect::<BTreeSet<_>>() != auxiliary_accesses
        || direct_substitutions.iter().any(|substitution| {
            condition_memory.get(&substitution.load_access()) != Some(&substitution.load_root())
        })
    {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidJoinedFlow(
            access,
        ));
    }

    let (load_result, load_root) = exact_load_root(flow.load().statement(), layer)?;
    let true_value = exact_store_value(join.true_arm().store(), layer)?;
    let false_value = exact_store_value(join.false_arm().store(), layer)?;
    if true_value.value().ty() != load_result.ty()
        || false_value.value().ty() != load_result.ty()
        || true_value.value().binding().width_bits() != load_result.binding().width_bits()
        || false_value.value().binding().width_bits() != load_result.binding().width_bits()
        || !matches!(
            layer.expr(condition_root).map(|expression| expression.ty()),
            Some(MachineType::Bool { storage_bits: 8 })
        )
    {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidJoinedFlow(
            access,
        ));
    }

    let semantic_return = semantic_return_from_control(join.return_control(), layer)
        .map_err(PrivateFrameConditionalJoinRewriteError::SemanticC)?;
    let return_root = match semantic_return.single_operand() {
        Some(SemanticCReturnOperand::Direct(value)) => value.expression(),
        _ => {
            return Err(PrivateFrameConditionalJoinRewriteError::InvalidJoinedFlow(
                access,
            ));
        }
    };
    let return_memory = expanded_memory_nodes(layer, output_index, [return_root])?;
    if layer.expr(return_root).is_none() || return_memory != BTreeMap::from([(access, load_root)]) {
        return Err(PrivateFrameConditionalJoinRewriteError::InvalidJoinedFlow(
            access,
        ));
    }

    Ok(CertifiedPrivateFrameJoinedSelect {
        condition: condition.clone(),
        condition_root,
        truthiness: join.condition().truthiness(),
        true_value,
        false_value,
        load_access: access,
        load_result,
        load_root,
        return_root,
    })
}

struct EntityOutputIndex {
    unique: BTreeMap<MachineValueBinding, SemanticCExprId>,
    ambiguous: BTreeSet<MachineValueBinding>,
}

impl EntityOutputIndex {
    fn new(layer: &SemanticCExpressionLayer) -> Self {
        let mut unique = BTreeMap::new();
        let mut ambiguous = BTreeSet::new();
        for entity in layer.entities() {
            if unique.insert(entity.output(), entity.root()).is_some() {
                ambiguous.insert(entity.output());
            }
        }
        Self { unique, ambiguous }
    }
}

fn expanded_memory_accesses_from_roots(
    layer: &SemanticCExpressionLayer,
    output_index: &EntityOutputIndex,
    roots: impl IntoIterator<Item = SemanticCExprId>,
) -> Result<BTreeSet<StructuredAccessId>, PrivateFrameConditionalJoinRewriteError> {
    Ok(expanded_memory_nodes(layer, output_index, roots)?
        .into_keys()
        .collect())
}

fn expanded_memory_nodes(
    layer: &SemanticCExpressionLayer,
    output_index: &EntityOutputIndex,
    roots: impl IntoIterator<Item = SemanticCExprId>,
) -> Result<BTreeMap<StructuredAccessId, SemanticCExprId>, PrivateFrameConditionalJoinRewriteError>
{
    let mut walker = ExpandedExpressionWalker {
        layer,
        output_index,
        active: BTreeSet::new(),
        visited: BTreeSet::new(),
        memory: BTreeMap::new(),
    };
    for root in roots {
        walker.visit(root)?;
    }
    Ok(walker.memory)
}

struct ExpandedExpressionWalker<'a> {
    layer: &'a SemanticCExpressionLayer,
    output_index: &'a EntityOutputIndex,
    active: BTreeSet<SemanticCExprId>,
    visited: BTreeSet<SemanticCExprId>,
    memory: BTreeMap<StructuredAccessId, SemanticCExprId>,
}

impl ExpandedExpressionWalker<'_> {
    fn visit(
        &mut self,
        expression_id: SemanticCExprId,
    ) -> Result<(), PrivateFrameConditionalJoinRewriteError> {
        if self.visited.contains(&expression_id) {
            return Ok(());
        }
        if !self.active.insert(expression_id) {
            return Err(PrivateFrameConditionalJoinRewriteError::CyclicExpression(
                expression_id,
            ));
        }
        let expression = self.layer.expr(expression_id).ok_or(
            PrivateFrameConditionalJoinRewriteError::CyclicExpression(expression_id),
        )?;
        let mut children = Vec::with_capacity(3);
        match expression.kind() {
            SemanticCExprKind::Input { binding } => {
                if self.output_index.ambiguous.contains(binding) {
                    return Err(
                        PrivateFrameConditionalJoinRewriteError::AmbiguousEntityOutput(*binding),
                    );
                }
                if let Some(root) = self.output_index.unique.get(binding) {
                    children.push(*root);
                }
            }
            SemanticCExprKind::Constant { .. } => {}
            SemanticCExprKind::MemoryRead {
                access, address, ..
            } => {
                if self
                    .memory
                    .insert(*access, expression_id)
                    .is_some_and(|previous| previous != expression_id)
                {
                    return Err(
                        PrivateFrameConditionalJoinRewriteError::AmbiguousMemoryRead(*access),
                    );
                }
                children.push(*address);
            }
            SemanticCExprKind::Copy { input }
            | SemanticCExprKind::BitwiseNot { input }
            | SemanticCExprKind::BooleanNot { input }
            | SemanticCExprKind::Cast { input, .. }
            | SemanticCExprKind::Extract { input, .. } => children.push(*input),
            SemanticCExprKind::Arithmetic { left, right, .. }
            | SemanticCExprKind::ArithmeticFlag { left, right, .. }
            | SemanticCExprKind::Bitwise { left, right, .. }
            | SemanticCExprKind::Boolean { left, right, .. }
            | SemanticCExprKind::Compare { left, right, .. } => {
                children.extend([*left, *right]);
            }
            SemanticCExprKind::Shift { value, count, .. } => {
                children.extend([*value, *count]);
            }
            SemanticCExprKind::Select {
                condition,
                if_true,
                if_false,
            } => children.extend([*condition, *if_true, *if_false]),
        }
        for child in children {
            self.visit(child)?;
        }
        self.active.remove(&expression_id);
        self.visited.insert(expression_id);
        Ok(())
    }
}
