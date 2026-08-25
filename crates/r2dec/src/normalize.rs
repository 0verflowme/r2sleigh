use crate::analysis::PredicateAnalysisView;
use crate::ast::CExpr;
use crate::control::{DecompileExecutionStop, DecompileWorkControl, DecompileWorkPhase};
use r2ssa::{
    BlockId, InstId, SSAFunction, SSAOp, SsaArtifactAuthority, SsaExecutionControl, SsaGraph,
    UseSite, ValueId,
};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// Certified role an original phi input has for one loop-carrier entity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CertifiedPhiEdgeRole {
    Entry,
    Update,
    DominatingInitializer,
}

/// Exact source definition consumed by a materialized phi edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct OriginalPhiDefinition {
    pub(crate) inst: InstId,
    pub(crate) value: ValueId,
}

/// Operand synthesized solely to preserve the old carrier off the guarded edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SyntheticPreserveOperand {
    /// Input position in the synthetic `Select` (`cond`, `if_true`, `if_false`).
    pub(crate) input_idx: usize,
    pub(crate) value: ValueId,
}

/// Extra provenance required when an edge copy is represented as a `Select`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct GuardedPhiEdgeOrigin {
    pub(crate) guard: UseSite,
    pub(crate) preserve: SyntheticPreserveOperand,
}

/// One inserted edge assignment and the exact original phi input it implements.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PhiEdgeOrigin {
    pub(crate) definition: OriginalPhiDefinition,
    pub(crate) incoming: UseSite,
    pub(crate) incoming_value: ValueId,
    pub(crate) predecessor: u64,
    pub(crate) target: u64,
    /// Operand in the normalized operation supplied by `incoming`.
    pub(crate) incoming_input_idx: usize,
    pub(crate) certified_entity: Option<r2ssa::SemanticId>,
    pub(crate) certified_roles: Box<[CertifiedPhiEdgeRole]>,
    pub(crate) guarded: Option<GuardedPhiEdgeOrigin>,
}

/// One certified initializer moved ahead of all equivalent entry edges.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RelocatedInitializerOrigin {
    pub(crate) definition: OriginalPhiDefinition,
    pub(crate) source_value: ValueId,
    pub(crate) certified_entity: r2ssa::SemanticId,
    /// Upstream post-loop phi input proving that this relocation is valid.
    ///
    /// This use remains live; it is evidence for the move, not one of the
    /// header inputs the relocated copy replaces.
    pub(crate) evidence_site: UseSite,
    /// Exact header-phi inputs replaced by this one copy, in stable order.
    pub(crate) replaced_sites: Box<[UseSite]>,
}

/// Exact origin of one operation in the normalized function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NormalizedOpOrigin {
    Original(InstId),
    PhiEdgeCopy(PhiEdgeOrigin),
    RelocatedInitializer(RelocatedInitializerOrigin),
}

/// Dense site of one operation in the normalized function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct NormalizedOpSite {
    pub(crate) block: BlockId,
    pub(crate) op_idx: usize,
}

/// One normalized operand and the exact original graph uses it represents.
///
/// A synthetic preservation operand has an empty `uses` slice. A relocated
/// initializer has several uses because one normalized expression replaces a
/// sorted set of original phi inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NormalizedInputProjection {
    pub(crate) value: ValueId,
    pub(crate) uses: Box<[UseSite]>,
}

/// Exact original output represented by one normalized definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct NormalizedOutputProjection {
    pub(crate) inst: InstId,
    pub(crate) value: ValueId,
}

/// Name-free projection from one normalized operation to original graph cells.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NormalizedOpProjection {
    pub(crate) inputs: Box<[NormalizedInputProjection]>,
    pub(crate) output: Option<NormalizedOutputProjection>,
}

/// Original phi instruction removed after all of its edges were materialized.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RemovedPhiOrigin {
    pub(crate) definition: OriginalPhiDefinition,
    /// Every original input of the removed phi, in canonical input order.
    pub(crate) incoming_sites: Box<[UseSite]>,
    /// Inputs whose value already equals the phi output and therefore require
    /// no normalized operation, in stable order.
    noop_sites: Box<[UseSite]>,
}

impl RemovedPhiOrigin {
    /// Exact self/no-op inputs certified by normalization.
    pub(crate) fn noop_sites(&self) -> &[UseSite] {
        &self.noop_sites
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NormalizationBlockOrigins {
    address: u64,
    rows: Vec<NormalizedOpOrigin>,
}

/// Validation failure for the sealed normalized-function sidecar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NormalizationOriginError {
    SourceAuthority,
    BlockTopology,
    RowCount { block: u64 },
    OriginalInstruction { block: u64, op_idx: usize },
    OriginalCoverage,
    PhiEdge { block: u64, op_idx: usize },
    RelocatedInitializer { block: u64, op_idx: usize },
    RemovedPhi,
    RemovedPhiEdge,
    InvalidCarrierCertificates,
}

impl std::fmt::Display for NormalizationOriginError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let reason = match self {
            Self::SourceAuthority => "source authority mismatch",
            Self::BlockTopology => "normalized block topology mismatch",
            Self::RowCount { .. } => "normalized origin row count mismatch",
            Self::OriginalInstruction { .. } => "invalid original instruction origin",
            Self::OriginalCoverage => "incomplete original instruction coverage",
            Self::PhiEdge { .. } => "invalid materialized phi-edge origin",
            Self::RelocatedInitializer { .. } => "invalid relocated initializer origin",
            Self::RemovedPhi => "invalid removed-phi origin",
            Self::RemovedPhiEdge => "invalid removed-phi input disposition",
            Self::InvalidCarrierCertificates => "invalid loop-carrier edge certificates",
        };
        f.write_str(reason)
    }
}

/// Typed failure from normalization construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NormalizationFailure {
    Execution(DecompileExecutionStop),
    Origins(NormalizationOriginError),
}

impl From<DecompileExecutionStop> for NormalizationFailure {
    fn from(error: DecompileExecutionStop) -> Self {
        Self::Execution(error)
    }
}

impl From<NormalizationOriginError> for NormalizationFailure {
    fn from(error: NormalizationOriginError) -> Self {
        Self::Origins(error)
    }
}

impl std::fmt::Display for NormalizationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Execution(error) => error.fmt(f),
            Self::Origins(error) => write!(f, "normalization origin refusal: {error}"),
        }
    }
}

/// Block-aligned, immutable origin rows for a normalized SSA function.
///
/// The fields are private so only normalization can mint or mutate rows. Every
/// downstream lookup is by the exact normalized `(block, op_idx)`; consumers
/// never recover a source use from variable names or operation shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NormalizationOrigins {
    authority: Option<SsaArtifactAuthority>,
    /// Indexed directly by the source graph's dense `BlockId`.
    blocks: Vec<NormalizationBlockOrigins>,
    /// Removed original phi instructions, sorted by their exact `InstId`.
    removed_phis: Vec<RemovedPhiOrigin>,
    /// Synthetic edge operations superseded by one relocated initializer.
    /// Sorted by original incoming `UseSite`.
    replaced_phi_edges: Vec<PhiEdgeOrigin>,
}

impl NormalizationOrigins {
    fn from_source(
        func: &SSAFunction,
        graph: &SsaGraph,
        authority: Option<SsaArtifactAuthority>,
    ) -> Self {
        let blocks = graph
            .block_order
            .iter()
            .map(|block_id| {
                let graph_block = graph
                    .block(*block_id)
                    .expect("source graph block order contains only valid blocks");
                let block = func
                    .get_block(graph_block.addr)
                    .expect("source graph and SSA function have identical blocks");
                let rows = (0..block.ops.len())
                    .map(|op_idx| {
                        NormalizedOpOrigin::Original(
                            graph
                                .inst_id_for_op_site(block.addr, op_idx)
                                .expect("every source SSA operation has an exact graph InstId"),
                        )
                    })
                    .collect();
                NormalizationBlockOrigins {
                    address: block.addr,
                    rows,
                }
            })
            .collect();
        Self {
            authority,
            blocks,
            removed_phis: Vec::new(),
            replaced_phi_edges: Vec::new(),
        }
    }

    pub(crate) fn for_unchanged(func: &SSAFunction, prepared: &r2ssa::SsaArtifact) -> Self {
        Self::from_source(func, prepared.graph(), Some(prepared.authority().clone()))
    }

    /// O(1) lookup from an exact normalized site to its sealed origin.
    pub(crate) fn origin(&self, site: NormalizedOpSite) -> Option<&NormalizedOpOrigin> {
        self.blocks
            .get(site.block.0 as usize)?
            .rows
            .get(site.op_idx)
    }

    /// Project one validated normalized row onto its original dense V/U/W keys.
    ///
    /// This method interprets only the sealed origin sidecar. It does not match
    /// operation shapes or recover identity from an SSA variable name.
    pub(crate) fn projection(
        &self,
        site: NormalizedOpSite,
        prepared: &r2ssa::SsaArtifact,
    ) -> Result<Option<NormalizedOpProjection>, NormalizationOriginError> {
        if self.authority.as_ref() != Some(prepared.authority()) {
            return Err(NormalizationOriginError::SourceAuthority);
        }
        Ok(self.projection_from_graph(site, prepared.graph()))
    }

    fn projection_from_graph(
        &self,
        site: NormalizedOpSite,
        graph: &SsaGraph,
    ) -> Option<NormalizedOpProjection> {
        match self.origin(site)? {
            NormalizedOpOrigin::Original(inst) => {
                let source = graph.inst(*inst)?;
                let inputs = source
                    .inputs
                    .iter()
                    .copied()
                    .enumerate()
                    .map(|(input_idx, value)| NormalizedInputProjection {
                        value,
                        uses: vec![UseSite {
                            inst: *inst,
                            input_idx,
                        }]
                        .into_boxed_slice(),
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice();
                let output = source.output.map(|value| NormalizedOutputProjection {
                    inst: *inst,
                    value,
                });
                Some(NormalizedOpProjection { inputs, output })
            }
            NormalizedOpOrigin::PhiEdgeCopy(origin) => {
                let highest_input = origin.guarded.map_or(origin.incoming_input_idx, |guarded| {
                    origin.incoming_input_idx.max(guarded.preserve.input_idx)
                });
                let mut inputs = vec![None; highest_input.checked_add(1)?];
                inputs[origin.incoming_input_idx] = Some(NormalizedInputProjection {
                    value: origin.incoming_value,
                    uses: vec![origin.incoming].into_boxed_slice(),
                });
                if let Some(guarded) = origin.guarded {
                    let guard_value = graph
                        .inst(guarded.guard.inst)?
                        .inputs
                        .get(guarded.guard.input_idx)
                        .copied()?;
                    inputs[0] = Some(NormalizedInputProjection {
                        value: guard_value,
                        uses: vec![guarded.guard].into_boxed_slice(),
                    });
                    inputs[guarded.preserve.input_idx] = Some(NormalizedInputProjection {
                        value: guarded.preserve.value,
                        uses: Box::new([]),
                    });
                }
                let inputs = inputs.into_iter().collect::<Option<Vec<_>>>()?.into_boxed_slice();
                Some(NormalizedOpProjection {
                    inputs,
                    output: Some(NormalizedOutputProjection {
                        inst: origin.definition.inst,
                        value: origin.definition.value,
                    }),
                })
            }
            NormalizedOpOrigin::RelocatedInitializer(origin) => Some(NormalizedOpProjection {
                inputs: vec![NormalizedInputProjection {
                    value: origin.source_value,
                    uses: origin.replaced_sites.clone(),
                }]
                .into_boxed_slice(),
                output: Some(NormalizedOutputProjection {
                    inst: origin.definition.inst,
                    value: origin.definition.value,
                }),
            }),
        }
    }

    /// Original phi uses deliberately represented by no normalized operation.
    pub(crate) fn noop_sites(&self) -> impl Iterator<Item = UseSite> + '_ {
        self.removed_phis
            .iter()
            .flat_map(|origin| origin.noop_sites.iter().copied())
    }

    fn rows(&self, block: BlockId) -> Option<&[NormalizedOpOrigin]> {
        Some(&self.blocks.get(block.0 as usize)?.rows)
    }

    fn rows_mut(&mut self, block: BlockId) -> Option<&mut Vec<NormalizedOpOrigin>> {
        Some(&mut self.blocks.get_mut(block.0 as usize)?.rows)
    }

    pub(crate) fn removed_phis(&self) -> &[RemovedPhiOrigin] {
        &self.removed_phis
    }

    pub(crate) fn replaced_phi_edges(&self) -> &[PhiEdgeOrigin] {
        &self.replaced_phi_edges
    }

    pub(crate) fn materialized_value_edges(&self) -> impl Iterator<Item = (ValueId, ValueId)> + '_ {
        self.blocks
            .iter()
            .flat_map(|block| block.rows.iter())
            .filter_map(|origin| match origin {
                NormalizedOpOrigin::PhiEdgeCopy(origin) => {
                    Some((origin.definition.value, origin.incoming_value))
                }
                NormalizedOpOrigin::RelocatedInitializer(origin) => {
                    Some((origin.definition.value, origin.source_value))
                }
                NormalizedOpOrigin::Original(_) => None,
            })
    }

    pub(crate) fn is_unconditional_phi_edge_copy(
        &self,
        site: NormalizedOpSite,
        successor: u64,
    ) -> bool {
        let Some(block) = self.blocks.get(site.block.0 as usize) else {
            return false;
        };
        matches!(
            self.origin(site),
            Some(NormalizedOpOrigin::PhiEdgeCopy(origin))
                if origin.predecessor == block.address
                    && origin.target == successor
                    && origin.guarded.is_none()
        )
    }

    pub(crate) fn validate(
        &self,
        normalized: &SSAFunction,
        prepared: &r2ssa::SsaArtifact,
        render_facts: Option<&r2types::FunctionRenderFacts>,
    ) -> Result<(), NormalizationOriginError> {
        if self.authority.as_ref() != Some(prepared.authority()) {
            return Err(NormalizationOriginError::SourceAuthority);
        }
        self.validate_against_graph(normalized, prepared.graph(), render_facts)
    }

    fn validate_against_graph(
        &self,
        normalized: &SSAFunction,
        graph: &SsaGraph,
        render_facts: Option<&r2types::FunctionRenderFacts>,
    ) -> Result<(), NormalizationOriginError> {
        if normalized.num_blocks() != self.blocks.len()
            || normalized.block_addrs().len() != graph.block_order.len()
        {
            return Err(NormalizationOriginError::BlockTopology);
        }
        let certificates = CarrierEdgeCertificates::build(graph, render_facts)
            .ok_or(NormalizationOriginError::InvalidCarrierCertificates)?;
        let mut seen_original = vec![false; graph.insts.len()];
        for (dense_idx, block_id) in graph.block_order.iter().copied().enumerate() {
            if block_id.0 as usize != dense_idx {
                return Err(NormalizationOriginError::BlockTopology);
            }
            let graph_block = graph
                .block(block_id)
                .ok_or(NormalizationOriginError::BlockTopology)?;
            let block_origins = self
                .blocks
                .get(dense_idx)
                .ok_or(NormalizationOriginError::BlockTopology)?;
            if block_origins.address != graph_block.addr
                || normalized.block_addrs().get(dense_idx) != Some(&graph_block.addr)
            {
                return Err(NormalizationOriginError::BlockTopology);
            }
            let block = normalized
                .get_block(graph_block.addr)
                .ok_or(NormalizationOriginError::BlockTopology)?;
            let rows = &block_origins.rows;
            if rows.len() != block.ops.len() {
                return Err(NormalizationOriginError::RowCount { block: block.addr });
            }
            for (op_idx, (op, origin)) in block.ops.iter().zip(rows).enumerate() {
                let valid = match origin {
                    NormalizedOpOrigin::Original(inst) => {
                        let Some(seen) = seen_original.get_mut(inst.0 as usize) else {
                            return Err(NormalizationOriginError::OriginalInstruction {
                                block: block.addr,
                                op_idx,
                            });
                        };
                        if *seen {
                            false
                        } else {
                            *seen = true;
                            validate_original_origin(graph, block_id, op, *inst)
                        }
                    }
                    NormalizedOpOrigin::PhiEdgeCopy(origin) => {
                        validate_phi_edge_origin(graph, &certificates, block.addr, op, origin)
                    }
                    NormalizedOpOrigin::RelocatedInitializer(origin) => {
                        validate_relocated_initializer_origin(
                            graph,
                            &certificates,
                            normalized,
                            op,
                            origin,
                        )
                    }
                };
                if !valid {
                    return Err(match origin {
                        NormalizedOpOrigin::Original(_) => {
                            NormalizationOriginError::OriginalInstruction {
                                block: block.addr,
                                op_idx,
                            }
                        }
                        NormalizedOpOrigin::PhiEdgeCopy(_) => NormalizationOriginError::PhiEdge {
                            block: block.addr,
                            op_idx,
                        },
                        NormalizedOpOrigin::RelocatedInitializer(_) => {
                            NormalizationOriginError::RelocatedInitializer {
                                block: block.addr,
                                op_idx,
                            }
                        }
                    });
                }
            }
        }
        if graph.insts.iter().any(|inst| {
            matches!(inst.payload, r2ssa::InstPayload::Op(_))
                && !seen_original
                    .get(inst.id.0 as usize)
                    .copied()
                    .unwrap_or(false)
        }) {
            return Err(NormalizationOriginError::OriginalCoverage);
        }
        if !validate_removed_phis(graph, normalized, &self.removed_phis) {
            return Err(NormalizationOriginError::RemovedPhi);
        }
        if !validate_removed_phi_input_dispositions(self, graph, &certificates) {
            return Err(NormalizationOriginError::RemovedPhiEdge);
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EdgeCertificate {
    entity: r2ssa::SemanticId,
    roles: BTreeSet<CertifiedPhiEdgeRole>,
}

/// Dense index over the already-validated upstream loop-carrier evidence.
struct CarrierEdgeCertificates {
    by_inst: Vec<Vec<Option<EdgeCertificate>>>,
    relocations_by_value: Vec<Option<RelocationCertificate>>,
}

#[derive(Clone)]
struct RelocationCertificate {
    definition: OriginalPhiDefinition,
    source_value: ValueId,
    initializer_predecessor: u64,
    initializer_site: UseSite,
    entries: Vec<r2ssa::LoopCarrierEdgeValue>,
}

impl CarrierEdgeCertificates {
    fn build(
        graph: &SsaGraph,
        render_facts: Option<&r2types::FunctionRenderFacts>,
    ) -> Option<Self> {
        let mut result = Self {
            by_inst: graph
                .insts
                .iter()
                .map(|inst| vec![None; inst.inputs.len()])
                .collect(),
            relocations_by_value: vec![None; graph.values.len()],
        };
        let Some(render_facts) = render_facts else {
            return Some(result);
        };
        let mut seen_entities = BTreeSet::new();
        for entity in render_facts.loop_carriers() {
            let r2types::CertifiedEntity::LoopCarrier {
                id,
                phi,
                identity_values,
                entries,
                updates,
                dominating_initializers,
                ..
            } = entity
            else {
                continue;
            };
            if *id != r2ssa::SemanticId::loop_carrier(*phi) || !seen_entities.insert(*id) {
                return None;
            }
            for (site, role, valid) in entries
                .iter()
                .map(|edge| (edge.site, CertifiedPhiEdgeRole::Entry, edge.validate(graph)))
                .chain(updates.iter().map(|edge| {
                    (
                        edge.site,
                        CertifiedPhiEdgeRole::Update,
                        edge.validate(graph),
                    )
                }))
                .chain(dominating_initializers.iter().map(|edge| {
                    (
                        edge.site,
                        CertifiedPhiEdgeRole::DominatingInitializer,
                        edge.validate(graph),
                    )
                }))
            {
                if !valid {
                    return None;
                }
                let slot = result
                    .by_inst
                    .get_mut(site.inst.0 as usize)?
                    .get_mut(site.input_idx)?;
                match slot {
                    Some(existing) if existing.entity != *id => return None,
                    Some(existing) => {
                        existing.roles.insert(role);
                    }
                    None => {
                        *slot = Some(EdgeCertificate {
                            entity: *id,
                            roles: BTreeSet::from([role]),
                        });
                    }
                }
            }
            if identity_values.len() >= 2 {
                if let [initializer] = dominating_initializers.as_slice() {
                    if entries.iter().any(|entry| entry.value == initializer.value) {
                        let definition = OriginalPhiDefinition {
                            inst: graph.def_inst(*phi)?,
                            value: *phi,
                        };
                        let relocation = result.relocations_by_value.get_mut(phi.0 as usize)?;
                        if relocation.is_some() {
                            return None;
                        }
                        *relocation = Some(RelocationCertificate {
                            definition,
                            source_value: initializer.value,
                            initializer_predecessor: initializer.predecessor,
                            initializer_site: initializer.site,
                            entries: entries.clone(),
                        });
                    }
                }
            }
        }
        Some(result)
    }

    fn get(&self, site: UseSite) -> Option<&EdgeCertificate> {
        self.by_inst
            .get(site.inst.0 as usize)?
            .get(site.input_idx)?
            .as_ref()
    }

    fn relocation(&self, entity: r2ssa::SemanticId) -> Option<&RelocationCertificate> {
        let r2ssa::SemanticId::LoopCarrier(value) = entity else {
            return None;
        };
        self.relocations_by_value.get(value.0 as usize)?.as_ref()
    }
}

fn original_phi_definition(
    graph: &SsaGraph,
    phi: &r2ssa::PhiNode,
) -> Option<OriginalPhiDefinition> {
    let value = graph.value_by_var.get(&phi.dst).copied()?;
    let inst = graph.def_inst(value)?;
    let definition = graph.inst(inst)?;
    matches!(definition.payload, r2ssa::InstPayload::Phi { .. })
        .then_some(OriginalPhiDefinition { inst, value })
}

fn exact_phi_edge_origin(
    graph: &SsaGraph,
    certificates: &CarrierEdgeCertificates,
    phi: &r2ssa::PhiNode,
    input_idx: usize,
    incoming_input_idx: usize,
    guarded: Option<GuardedPhiEdgeOrigin>,
) -> Option<PhiEdgeOrigin> {
    let definition = original_phi_definition(graph, phi)?;
    let (predecessor, source) = phi.sources.get(input_idx)?;
    let incoming = UseSite {
        inst: definition.inst,
        input_idx,
    };
    let incoming_value = graph
        .inst(definition.inst)?
        .inputs
        .get(input_idx)
        .copied()?;
    if graph.value(incoming_value).map(|value| &value.var) != Some(source) {
        return None;
    }
    let certificate = certificates.get(incoming);
    Some(PhiEdgeOrigin {
        definition,
        incoming,
        incoming_value,
        predecessor: *predecessor,
        target: graph
            .inst(definition.inst)
            .and_then(|inst| graph.block(inst.block))?
            .addr,
        incoming_input_idx,
        certified_entity: certificate.map(|certificate| certificate.entity),
        certified_roles: certificate
            .map(|certificate| certificate.roles.iter().copied().collect::<Vec<_>>())
            .unwrap_or_default()
            .into_boxed_slice(),
        guarded,
    })
}

fn validate_original_origin(graph: &SsaGraph, block: BlockId, op: &SSAOp, inst: InstId) -> bool {
    let Some(original) = graph.inst(inst) else {
        return false;
    };
    let r2ssa::InstPayload::Op(payload) = &original.payload else {
        return false;
    };
    if original.block != block || payload != op || original.inputs.len() != op.sources().len() {
        return false;
    }
    original
        .inputs
        .iter()
        .copied()
        .zip(op.sources())
        .all(|(value, var)| graph.value(value).map(|source| &source.var) == Some(var))
        && match (original.output, op.dst()) {
            (None, None) => true,
            (Some(value), Some(dst)) => graph.value(value).map(|value| &value.var) == Some(dst),
            _ => false,
        }
}

fn validate_phi_edge_source(
    graph: &SsaGraph,
    certificates: &CarrierEdgeCertificates,
    origin: &PhiEdgeOrigin,
) -> bool {
    let Some(definition) = graph.inst(origin.definition.inst) else {
        return false;
    };
    let r2ssa::InstPayload::Phi { predecessors } = &definition.payload else {
        return false;
    };
    if definition.output != Some(origin.definition.value)
        || origin.incoming.inst != origin.definition.inst
        || definition.inputs.get(origin.incoming.input_idx) != Some(&origin.incoming_value)
        || predecessors
            .get(origin.incoming.input_idx)
            .and_then(|block| graph.block(*block))
            .map(|block| block.addr)
            != Some(origin.predecessor)
        || graph.block(definition.block).map(|block| block.addr) != Some(origin.target)
        || !origin
            .certified_roles
            .windows(2)
            .all(|roles| roles[0] < roles[1])
    {
        return false;
    }
    match certificates.get(origin.incoming) {
        Some(certificate) => {
            origin.certified_entity == Some(certificate.entity)
                && origin.certified_roles.as_ref()
                    == certificate
                        .roles
                        .iter()
                        .copied()
                        .collect::<Vec<_>>()
                        .as_slice()
        }
        None => origin.certified_entity.is_none() && origin.certified_roles.is_empty(),
    }
}

fn validate_phi_edge_origin(
    graph: &SsaGraph,
    certificates: &CarrierEdgeCertificates,
    block: u64,
    op: &SSAOp,
    origin: &PhiEdgeOrigin,
) -> bool {
    if block != origin.predecessor || !validate_phi_edge_source(graph, certificates, origin) {
        return false;
    }
    let Some(dst) = graph.value(origin.definition.value).map(|value| &value.var) else {
        return false;
    };
    let Some(src) = graph.value(origin.incoming_value).map(|value| &value.var) else {
        return false;
    };
    match (op, origin.guarded) {
        (
            SSAOp::Copy {
                dst: copy_dst,
                src: copy_src,
            },
            None,
        ) => origin.incoming_input_idx == 0 && copy_dst == dst && copy_src == src,
        (
            SSAOp::Select {
                dst: select_dst,
                cond,
                if_true,
                if_false,
            },
            Some(guarded),
        ) => {
            let Some(guard_inst) = graph.inst(guarded.guard.inst) else {
                return false;
            };
            let r2ssa::InstPayload::Op(SSAOp::CBranch {
                cond: original_cond,
                ..
            }) = &guard_inst.payload
            else {
                return false;
            };
            let operands = [cond, if_true, if_false];
            guarded.guard.input_idx == 1
                && guard_inst.block
                    == graph
                        .block_id_for_addr(origin.predecessor)
                        .unwrap_or(BlockId(u32::MAX))
                && guard_inst
                    .inputs
                    .get(guarded.guard.input_idx)
                    .and_then(|value| graph.value(*value))
                    .map(|value| &value.var)
                    == Some(original_cond)
                && cond == original_cond
                && select_dst == dst
                && origin.incoming_input_idx < operands.len()
                && guarded.preserve.input_idx < operands.len()
                && origin.incoming_input_idx != guarded.preserve.input_idx
                && origin.incoming_input_idx != 0
                && guarded.preserve.input_idx != 0
                && operands[origin.incoming_input_idx] == src
                && graph.value(guarded.preserve.value).map(|value| &value.var) == Some(dst)
                && operands[guarded.preserve.input_idx] == dst
        }
        _ => false,
    }
}

fn validate_relocated_initializer_origin(
    graph: &SsaGraph,
    certificates: &CarrierEdgeCertificates,
    normalized: &SSAFunction,
    op: &SSAOp,
    origin: &RelocatedInitializerOrigin,
) -> bool {
    let Some(dst) = graph.value(origin.definition.value).map(|value| &value.var) else {
        return false;
    };
    let Some(src) = graph.value(origin.source_value).map(|value| &value.var) else {
        return false;
    };
    if !matches!(op, SSAOp::Copy { dst: copy_dst, src: copy_src }
        if copy_dst == dst && copy_src == src)
        || origin.replaced_sites.is_empty()
        || !origin
            .replaced_sites
            .windows(2)
            .all(|sites| sites[0] < sites[1])
    {
        return false;
    }
    let Some(certificate) = certificates.relocation(origin.certified_entity) else {
        return false;
    };
    let mut expected_replaced_sites = certificate
        .entries
        .iter()
        .filter(|entry| {
            entry.value == certificate.source_value
                && (entry.predecessor == certificate.initializer_predecessor
                    || normalized.dominates(certificate.initializer_predecessor, entry.predecessor))
        })
        .map(|entry| entry.site)
        .collect::<Vec<_>>();
    expected_replaced_sites.sort_unstable();
    expected_replaced_sites.dedup();
    if certificate.definition != origin.definition
        || certificate.source_value != origin.source_value
        || certificate.initializer_site != origin.evidence_site
        || expected_replaced_sites.as_slice() != origin.replaced_sites.as_ref()
    {
        return false;
    }
    let evidence_valid = graph
        .inst(origin.evidence_site.inst)
        .is_some_and(|inst| inst.output != Some(origin.definition.value))
        && graph
            .inst(origin.evidence_site.inst)
            .and_then(|inst| inst.inputs.get(origin.evidence_site.input_idx))
            == Some(&origin.source_value)
        && certificates.get(origin.evidence_site).is_some_and(|edge| {
            edge.entity == origin.certified_entity
                && edge
                    .roles
                    .contains(&CertifiedPhiEdgeRole::DominatingInitializer)
        });
    evidence_valid
        && origin.replaced_sites.iter().copied().all(|site| {
            graph
                .inst(site.inst)
                .is_some_and(|inst| inst.output == Some(origin.definition.value))
                && graph
                    .inst(site.inst)
                    .and_then(|inst| inst.inputs.get(site.input_idx))
                    == Some(&origin.source_value)
                && certificates.get(site).is_some_and(|edge| {
                    edge.entity == origin.certified_entity
                        && edge.roles.contains(&CertifiedPhiEdgeRole::Entry)
                })
        })
}

fn validate_removed_phis(
    graph: &SsaGraph,
    normalized: &SSAFunction,
    removed: &[RemovedPhiOrigin],
) -> bool {
    if !removed
        .windows(2)
        .all(|pair| pair[0].definition.inst < pair[1].definition.inst)
    {
        return false;
    }
    let mut accounted = vec![false; graph.insts.len()];
    let phi_inst_by_var = graph
        .insts
        .iter()
        .filter_map(|inst| {
            if !matches!(inst.payload, r2ssa::InstPayload::Phi { .. }) {
                return None;
            }
            let value = graph.value(inst.output?)?;
            Some((value.var.clone(), inst.id))
        })
        .collect::<HashMap<_, _>>();
    for removed in removed {
        let Some(inst) = graph.inst(removed.definition.inst) else {
            return false;
        };
        let expected_noop_sites = inst
            .inputs
            .iter()
            .enumerate()
            .filter_map(|(input_idx, input)| {
                (*input == removed.definition.value).then_some(UseSite {
                    inst: removed.definition.inst,
                    input_idx,
                })
            })
            .collect::<Vec<_>>();
        if inst.output != Some(removed.definition.value)
            || !matches!(inst.payload, r2ssa::InstPayload::Phi { .. })
            || removed.incoming_sites.len() != inst.inputs.len()
            || !removed
                .incoming_sites
                .iter()
                .enumerate()
                .all(|(input_idx, site)| {
                    *site
                        == UseSite {
                            inst: removed.definition.inst,
                            input_idx,
                        }
                })
            || removed.noop_sites.as_ref() != expected_noop_sites.as_slice()
            || std::mem::replace(&mut accounted[removed.definition.inst.0 as usize], true)
        {
            return false;
        }
    }
    for block in normalized.blocks() {
        for phi in &block.phis {
            let Some(inst_id) = phi_inst_by_var.get(&phi.dst).copied() else {
                return false;
            };
            let Some(inst) = graph.inst(inst_id) else {
                return false;
            };
            let Some(value) = inst.output else {
                return false;
            };
            let r2ssa::InstPayload::Phi { predecessors } = &inst.payload else {
                return false;
            };
            if inst.block
                != graph
                    .block_id_for_addr(block.addr)
                    .unwrap_or(BlockId(u32::MAX))
                || inst.output != Some(value)
                || inst.inputs.len() != phi.sources.len()
                || !inst
                    .inputs
                    .iter()
                    .copied()
                    .zip(predecessors)
                    .zip(&phi.sources)
                    .all(|((input, predecessor), (source_addr, source))| {
                        graph.value(input).map(|value| &value.var) == Some(source)
                            && graph.block(*predecessor).map(|block| block.addr)
                                == Some(*source_addr)
                    })
                || std::mem::replace(&mut accounted[inst_id.0 as usize], true)
            {
                return false;
            }
        }
    }
    graph.insts.iter().all(|inst| {
        !matches!(inst.payload, r2ssa::InstPayload::Phi { .. })
            || accounted.get(inst.id.0 as usize).copied().unwrap_or(false)
    })
}

/// Prove the inverse of the normalized phi-edge mapping.
///
/// Every input of every removed phi has exactly one disposition: a live edge
/// operation, membership in one relocated initializer, or an explicit no-op
/// because the input is already the phi output. The replaced-edge ledger is an
/// inverse certificate for the relocated memberships, not a fourth disposition.
fn validate_removed_phi_input_dispositions(
    origins: &NormalizationOrigins,
    graph: &SsaGraph,
    certificates: &CarrierEdgeCertificates,
) -> bool {
    let mut disposition_count = graph
        .insts
        .iter()
        .map(|inst| vec![None::<u8>; inst.inputs.len()])
        .collect::<Vec<_>>();
    for removed in &origins.removed_phis {
        for site in removed.incoming_sites.iter().copied() {
            let Some(slot) = disposition_count
                .get_mut(site.inst.0 as usize)
                .and_then(|counts| counts.get_mut(site.input_idx))
            else {
                return false;
            };
            if slot.replace(0).is_some() {
                return false;
            }
        }
    }

    let bump = |site: UseSite, counts: &mut [Vec<Option<u8>>]| -> bool {
        let Some(count) = counts
            .get_mut(site.inst.0 as usize)
            .and_then(|counts| counts.get_mut(site.input_idx))
            .and_then(Option::as_mut)
        else {
            return false;
        };
        let Some(next) = count.checked_add(1) else {
            return false;
        };
        *count = next;
        next == 1
    };

    for removed in &origins.removed_phis {
        for site in removed.noop_sites.iter().copied() {
            if !bump(site, &mut disposition_count) {
                return false;
            }
        }
    }

    let mut relocated_sites = graph
        .insts
        .iter()
        .map(|inst| vec![false; inst.inputs.len()])
        .collect::<Vec<_>>();
    let mark = |site: UseSite, sites: &mut [Vec<bool>]| -> bool {
        let Some(marked) = sites
            .get_mut(site.inst.0 as usize)
            .and_then(|sites| sites.get_mut(site.input_idx))
        else {
            return false;
        };
        !std::mem::replace(marked, true)
    };
    for row in origins.blocks.iter().flat_map(|block| block.rows.iter()) {
        match row {
            NormalizedOpOrigin::Original(_) => {}
            NormalizedOpOrigin::PhiEdgeCopy(origin) => {
                if !bump(origin.incoming, &mut disposition_count) {
                    return false;
                }
            }
            NormalizedOpOrigin::RelocatedInitializer(origin) => {
                for site in origin.replaced_sites.iter().copied() {
                    if !mark(site, &mut relocated_sites) || !bump(site, &mut disposition_count) {
                        return false;
                    }
                }
            }
        }
    }

    if !origins
        .replaced_phi_edges
        .windows(2)
        .all(|pair| pair[0].incoming < pair[1].incoming)
    {
        return false;
    }
    let mut replaced_sites = graph
        .insts
        .iter()
        .map(|inst| vec![false; inst.inputs.len()])
        .collect::<Vec<_>>();
    for origin in &origins.replaced_phi_edges {
        if !validate_phi_edge_source(graph, certificates, origin)
            || !mark(origin.incoming, &mut replaced_sites)
        {
            return false;
        }
    }

    relocated_sites == replaced_sites
        && disposition_count
            .iter()
            .flatten()
            .all(|count| count.is_none_or(|count| count == 1))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) enum NormalizeMode {
    General,
    Predicate,
}

pub(crate) fn normalize_expr(
    view: &(impl PredicateAnalysisView + ?Sized),
    expr: CExpr,
    mode: NormalizeMode,
) -> CExpr {
    match mode {
        NormalizeMode::General | NormalizeMode::Predicate => view.simplify_predicate_expr(expr),
    }
}

fn is_block_terminator(op: &SSAOp) -> bool {
    matches!(
        op,
        SSAOp::Branch { .. } | SSAOp::CBranch { .. } | SSAOp::Return { .. }
    )
}

/// Lower only certified loop-carrier phis into mutable edge assignments.
///
/// Other phis remain immutable semantic expressions. Lowering every machine
/// temporary or flag phi creates artificial C effects and obscures the proof
/// boundary between SSA values and mutable loop state.
#[allow(dead_code)]
pub(crate) fn materialize_certified_loop_carriers(
    func: &SSAFunction,
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
) -> Result<(SSAFunction, NormalizationOrigins), NormalizationOriginError> {
    let execution = SsaExecutionControl::default();
    let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Normalization);
    match materialize_certified_loop_carriers_with_control(func, prepared, render_facts, control) {
        Ok(result) => Ok(result),
        Err(NormalizationFailure::Origins(error)) => Err(error),
        Err(NormalizationFailure::Execution(error)) => {
            panic!("default decompiler work control cannot stop: {error}")
        }
    }
}

pub(crate) fn materialize_certified_loop_carriers_with_control(
    func: &SSAFunction,
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
    control: DecompileWorkControl<'_>,
) -> Result<(SSAFunction, NormalizationOrigins), NormalizationFailure> {
    // A merge whose destination is read has to be placed, whether or not it is
    // a certified loop carrier. Admitting carriers alone left every other merge
    // with no definition anywhere in the rendered body, and the fold cannot
    // spell a value nothing wrote: it drops the term and renders the rest, so
    // the output compiles and runs and is quietly wrong.
    //
    // `DeadPhis` already says which merges nothing observes; those stay merges
    // and cost nothing.
    let graph = prepared.graph();
    let live = prepared.live_out();
    let dead = r2ssa::deadphi::DeadPhis::find(func, graph, &live);
    materialize_phis_where_with_control(
        func,
        graph,
        Some(prepared.authority().clone()),
        Some(render_facts),
        control,
        |phi| {
            let Some(value) = graph.value_id_for_var(&phi.dst) else {
                return false;
            };
            if render_facts.loop_carrier_for_value(value).is_some() {
                return true;
            }
            // A merge nothing observes costs nothing to leave alone, and a merge at
            // a plain join -- every predecessor leading only here -- the fold can
            // render as an expression, which is what keeps ordinary merges
            // immutable.
            //
            // A merge reached from a *branching* predecessor is different: its copy
            // has to sit on one edge of a two-way branch, and the fold has no way to
            // spell that. It rendered nothing at all, and the reader never saw that
            // a value went missing -- `djb2` at x86-64 -O2 dropped the `+ rdx` its
            // remainder loop starts from and returned a plausible wrong hash.
            !dead.contains(value)
                && phi
                    .sources
                    .iter()
                    .any(|(pred, _)| func.successors(*pred).len() > 1)
        },
    )
}

fn materialize_phis_where_with_control(
    func: &SSAFunction,
    graph: &SsaGraph,
    authority: Option<SsaArtifactAuthority>,
    render_facts: Option<&r2types::FunctionRenderFacts>,
    control: DecompileWorkControl<'_>,
    mut eligible: impl FnMut(&r2ssa::PhiNode) -> bool,
) -> Result<(SSAFunction, NormalizationOrigins), NormalizationFailure> {
    control.poll()?;
    let mut normalized = func.clone();
    let mut origins = NormalizationOrigins::from_source(func, graph, authority);
    let certificates = CarrierEdgeCertificates::build(graph, render_facts)
        .ok_or(NormalizationOriginError::InvalidCarrierCertificates)?;
    let liveness = PhiEdgeLiveness::compute_with_control(func, control)?;
    let mut copies_by_pred = BTreeMap::<u64, Vec<PhiMove>>::new();
    let mut materialized_by_block = BTreeMap::<u64, BTreeSet<r2ssa::SSAVar>>::new();

    for block in func.blocks() {
        control.poll()?;
        let mut moves_by_pred = HashMap::<u64, Vec<PhiMove>>::new();
        let mut complete = true;
        let selected = widest_per_storage(
            block
                .phis
                .iter()
                .filter(|phi| eligible(phi))
                .collect::<Vec<_>>(),
        );
        if selected.is_empty() {
            continue;
        }
        // One merge that cannot be placed used to abandon every merge in its
        // block. They are independent -- each writes its own destination -- so
        // the failure belongs to the one merge, and taking its block-mates down
        // with it left them with no definition at all.
        //
        // `djb2` at x86-64 -O2 is where this showed: a Unique-space temp merge
        // in the loop-exit block could not be placed, so the counter merge
        // beside it was dropped too, and the remainder loop's `arg0 + rdx`
        // became `arg0` -- re-reading the front of the buffer instead of the
        // bytes the unrolled loop had not reached. It compiled, ran, and
        // returned a plausible wrong hash.
        let mut materialized_dsts = Vec::new();
        for phi in &selected {
            control.poll()?;
            let mut staged = Vec::new();
            let mut placed = true;
            for (input_idx, (pred, src)) in phi.sources.iter().enumerate() {
                control.poll()?;
                if src == &phi.dst {
                    continue;
                }
                let Some((op, guarded, incoming_input_idx)) = materialized_phi_edge_op(
                    func, graph, &liveness, *pred, block.addr, &phi.dst, src,
                ) else {
                    if std::env::var_os("R2SLEIGH_TRACE_MAT").is_some() {
                        eprintln!(
                            "MATFAIL block={:#x} pred={pred:#x} dst={} src={}",
                            block.addr,
                            phi.dst.display_name(),
                            src.display_name()
                        );
                    }
                    placed = false;
                    break;
                };
                staged.push((
                    *pred,
                    PhiMove {
                        dst: phi.dst.clone(),
                        src: src.clone(),
                        op,
                        origin: exact_phi_edge_origin(
                            graph,
                            &certificates,
                            phi,
                            input_idx,
                            incoming_input_idx,
                            guarded,
                        )
                        .ok_or(NormalizationOriginError::RemovedPhiEdge)?,
                    },
                ));
            }
            if !placed {
                continue;
            }
            for (pred, planned) in staged {
                moves_by_pred.entry(pred).or_default().push(planned);
            }
            materialized_dsts.push(phi.dst.clone());
        }
        if materialized_dsts.is_empty() {
            continue;
        }
        let mut scheduled = Vec::new();
        for (pred, moves) in moves_by_pred {
            control.poll()?;
            let Some(moves) = schedule_parallel_phi_moves_with_control(moves, control)? else {
                complete = false;
                break;
            };
            scheduled.push((pred, moves));
        }
        if complete {
            materialized_by_block.insert(block.addr, materialized_dsts.into_iter().collect());
            for phi in selected {
                if !materialized_by_block[&block.addr].contains(&phi.dst) {
                    continue;
                }
                let definition = original_phi_definition(graph, phi)
                    .ok_or(NormalizationOriginError::RemovedPhi)?;
                let incoming_sites = (0..phi.sources.len())
                    .map(|input_idx| UseSite {
                        inst: definition.inst,
                        input_idx,
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice();
                let noop_sites = graph
                    .inst(definition.inst)
                    .ok_or(NormalizationOriginError::RemovedPhi)?
                    .inputs
                    .iter()
                    .enumerate()
                    .filter_map(|(input_idx, input)| {
                        (*input == definition.value).then_some(UseSite {
                            inst: definition.inst,
                            input_idx,
                        })
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice();
                origins.removed_phis.push(RemovedPhiOrigin {
                    definition,
                    incoming_sites,
                    noop_sites,
                });
            }
            for (pred, moves) in scheduled {
                copies_by_pred.entry(pred).or_default().extend(moves);
            }
        }
    }

    for (addr, materialized) in materialized_by_block {
        control.poll()?;
        if let Some(block) = normalized.get_block_mut(addr) {
            block.phis.retain(|phi| !materialized.contains(&phi.dst));
        }
    }

    origins
        .removed_phis
        .sort_unstable_by_key(|removed| removed.definition.inst);
    for (pred, copies) in copies_by_pred {
        control.poll()?;
        if copies.is_empty() {
            continue;
        }
        if let Some(block) = normalized.get_block_mut(pred) {
            let insert_at = block
                .ops
                .iter()
                .rposition(is_block_terminator)
                .unwrap_or(block.ops.len());
            let block_id = graph
                .block_id_for_addr(pred)
                .expect("normalized predecessor belongs to the source graph");
            let (ops, inserted_origins): (Vec<_>, Vec<_>) = copies
                .into_iter()
                .map(|planned| (planned.op, NormalizedOpOrigin::PhiEdgeCopy(planned.origin)))
                .unzip();
            block.ops.splice(insert_at..insert_at, ops);
            origins
                .rows_mut(block_id)
                .expect("origin rows exist for every normalized block")
                .splice(insert_at..insert_at, inserted_origins);
        }
    }

    control.poll()?;
    origins.validate_against_graph(&normalized, graph, render_facts)?;
    Ok((normalized, origins))
}

#[cfg(test)]
fn materialize_all_phis(func: &SSAFunction) -> SSAFunction {
    materialize_all_phis_with_origins(func).0
}

#[cfg(test)]
fn materialize_all_phis_with_origins(
    func: &SSAFunction,
) -> (SSAFunction, NormalizationOrigins, SsaGraph) {
    let execution = SsaExecutionControl::default();
    let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Normalization);
    let graph = SsaGraph::from_function(func);
    let (normalized, origins) =
        materialize_phis_where_with_control(func, &graph, None, None, control, |_| true)
            .expect("default decompiler work control cannot stop");
    (normalized, origins, graph)
}

struct PhiMove {
    dst: r2ssa::SSAVar,
    src: r2ssa::SSAVar,
    op: SSAOp,
    origin: PhiEdgeOrigin,
}

/// Keep one merge per register, not one per width the machine wrote it at.
///
/// A header that merges both `RAX` and `EAX` is merging one register twice, and
/// materialising both gives the rendering two mutable variables for one value.
/// They then share a name and the body reads `x = x` beside the update that
/// already wrote it. The widest slice contains the others, so it is the one that
/// carries the value; anything at a different offset is a different place and is
/// kept.
fn widest_per_storage<'a>(phis: Vec<&'a r2ssa::PhiNode>) -> Vec<&'a r2ssa::PhiNode> {
    use r2ssa::CanonicalStorageSpace;
    // Ordered, because what the fold emits has to be the same on every run and
    // a hash map hands its values back in whatever order it likes.
    let mut widest_by_slot: std::collections::BTreeMap<
        (CanonicalStorageSpace, u64),
        &r2ssa::PhiNode,
    > = std::collections::BTreeMap::new();
    let mut kept = Vec::with_capacity(phis.len());
    for phi in phis {
        let Some(storage) = phi.canonical_storage else {
            kept.push(phi);
            continue;
        };
        if !matches!(storage.space, CanonicalStorageSpace::Register) {
            kept.push(phi);
            continue;
        }
        match widest_by_slot.entry((storage.space, storage.offset)) {
            std::collections::btree_map::Entry::Vacant(slot) => {
                slot.insert(phi);
            }
            std::collections::btree_map::Entry::Occupied(mut slot) => {
                let held = slot.get().canonical_storage.map_or(0, |held| held.size);
                if storage.size > held {
                    slot.insert(phi);
                }
            }
        }
    }
    kept.extend(widest_by_slot.into_values());
    kept
}

fn materialized_phi_edge_op(
    func: &SSAFunction,
    graph: &SsaGraph,
    liveness: &PhiEdgeLiveness,
    pred: u64,
    target: u64,
    dst: &r2ssa::SSAVar,
    src: &r2ssa::SSAVar,
) -> Option<(SSAOp, Option<GuardedPhiEdgeOrigin>, usize)> {
    let successors = func.successors(pred);
    if successors.as_slice() == [target] {
        return Some((
            SSAOp::Copy {
                dst: dst.clone(),
                src: src.clone(),
            },
            None,
            0,
        ));
    }
    if can_materialize_on_branch_edge(func, liveness, pred, target, dst) {
        return Some((
            SSAOp::Copy {
                dst: dst.clone(),
                src: src.clone(),
            },
            None,
            0,
        ));
    }
    guarded_loop_backedge_phi_op(func, graph, pred, target, dst, src)
}

fn guarded_loop_backedge_phi_op(
    func: &SSAFunction,
    graph: &SsaGraph,
    pred: u64,
    target: u64,
    dst: &r2ssa::SSAVar,
    src: &r2ssa::SSAVar,
) -> Option<(SSAOp, Option<GuardedPhiEdgeOrigin>, usize)> {
    let successors = func.successors(pred);
    if successors.len() != 2 || !successors.contains(&target) || !func.dominates(target, pred) {
        return None;
    }
    let source_block = func.get_block(pred)?;
    let terminator_idx = source_block.ops.len().checked_sub(1)?;
    let cond = match source_block.ops.get(terminator_idx)? {
        SSAOp::CBranch { cond, .. } if cond != dst => cond.clone(),
        _ => return None,
    };
    let guard_inst = graph.inst_id_for_op_site(pred, terminator_idx)?;
    let guard = UseSite {
        inst: guard_inst,
        input_idx: 1,
    };
    let preserve_value = graph.value_id_for_var(dst)?;
    let (if_true, if_false, incoming_input_idx, preserve_input_idx) =
        match func.edge_type(pred, target)? {
            r2ssa::CFGEdge::True => (src.clone(), dst.clone(), 1, 2),
            r2ssa::CFGEdge::False => (dst.clone(), src.clone(), 2, 1),
            r2ssa::CFGEdge::Normal | r2ssa::CFGEdge::Back => return None,
        };
    Some((
        SSAOp::Select {
            dst: dst.clone(),
            cond,
            if_true,
            if_false,
        },
        Some(GuardedPhiEdgeOrigin {
            guard,
            preserve: SyntheticPreserveOperand {
                input_idx: preserve_input_idx,
                value: preserve_value,
            },
        }),
        incoming_input_idx,
    ))
}

/// Order out-of-SSA moves without changing the simultaneous semantics of a
/// phi bundle. Cyclic bundles stay in SSA until a temporary-backed lowering
/// can represent them exactly.
fn schedule_parallel_phi_moves_with_control(
    mut moves: Vec<PhiMove>,
    control: DecompileWorkControl<'_>,
) -> Result<Option<Vec<PhiMove>>, DecompileExecutionStop> {
    let mut scheduled = Vec::with_capacity(moves.len());
    while !moves.is_empty() {
        control.poll()?;
        let ready = moves.iter().position(|candidate| {
            !moves
                .iter()
                .any(|other| other.dst != candidate.dst && other.src == candidate.dst)
        });
        let Some(ready) = ready else {
            return Ok(None);
        };
        scheduled.push(moves.remove(ready));
    }
    Ok(Some(scheduled))
}

pub(crate) struct PhiEdgeLiveness {
    live_in: HashMap<u64, HashSet<r2ssa::SSAVar>>,
    phi_defs: HashMap<u64, HashSet<r2ssa::SSAVar>>,
    edge_phi_uses: HashMap<(u64, u64), HashSet<r2ssa::SSAVar>>,
}

impl PhiEdgeLiveness {
    pub(crate) fn compute_with_control(
        func: &SSAFunction,
        control: DecompileWorkControl<'_>,
    ) -> Result<Self, DecompileExecutionStop> {
        control.poll()?;
        let mut defs_by_block = HashMap::<u64, HashSet<r2ssa::SSAVar>>::new();
        let mut uses_by_block = HashMap::<u64, HashSet<r2ssa::SSAVar>>::new();
        let mut phi_defs = HashMap::<u64, HashSet<r2ssa::SSAVar>>::new();
        let mut edge_phi_uses = HashMap::<(u64, u64), HashSet<r2ssa::SSAVar>>::new();

        for block in func.blocks() {
            control.poll()?;
            let mut defs = HashSet::new();
            let mut uses = HashSet::new();
            let mut defined = HashSet::new();
            for phi in &block.phis {
                control.poll()?;
                defs.insert(phi.dst.clone());
                defined.insert(phi.dst.clone());
                phi_defs
                    .entry(block.addr)
                    .or_default()
                    .insert(phi.dst.clone());
                for (pred, src) in &phi.sources {
                    edge_phi_uses
                        .entry((*pred, block.addr))
                        .or_default()
                        .insert(src.clone());
                }
            }
            for op in &block.ops {
                control.poll()?;
                for src in op.sources() {
                    if !defined.contains(src) {
                        uses.insert(src.clone());
                    }
                }
                if let Some(dst) = op.dst() {
                    defs.insert(dst.clone());
                    defined.insert(dst.clone());
                }
            }
            defs_by_block.insert(block.addr, defs);
            uses_by_block.insert(block.addr, uses);
        }

        let mut live_in = func
            .block_addrs()
            .iter()
            .copied()
            .map(|addr| (addr, HashSet::new()))
            .collect::<HashMap<_, _>>();
        let mut live_out = live_in.clone();
        let mut changed = true;
        while changed {
            control.poll()?;
            changed = false;
            for &addr in func.block_addrs().iter().rev() {
                control.poll()?;
                let mut next_out = HashSet::new();
                for successor in func.successors(addr) {
                    control.poll()?;
                    next_out.extend(edge_live_in(
                        live_in.get(&successor),
                        phi_defs.get(&successor),
                        edge_phi_uses.get(&(addr, successor)),
                    ));
                }
                let mut next_in = uses_by_block.get(&addr).cloned().unwrap_or_default();
                let defs = defs_by_block.get(&addr).cloned().unwrap_or_default();
                next_in.extend(
                    next_out
                        .iter()
                        .filter(|value| !defs.contains(*value))
                        .cloned(),
                );
                if live_out.get(&addr) != Some(&next_out) {
                    live_out.insert(addr, next_out);
                    changed = true;
                }
                if live_in.get(&addr) != Some(&next_in) {
                    live_in.insert(addr, next_in);
                    changed = true;
                }
            }
        }
        control.poll()?;
        Ok(Self {
            live_in,
            phi_defs,
            edge_phi_uses,
        })
    }

    fn live_on_edge(&self, pred: u64, successor: u64) -> HashSet<r2ssa::SSAVar> {
        edge_live_in(
            self.live_in.get(&successor),
            self.phi_defs.get(&successor),
            self.edge_phi_uses.get(&(pred, successor)),
        )
    }
}

fn edge_live_in(
    successor_live_in: Option<&HashSet<r2ssa::SSAVar>>,
    successor_phi_defs: Option<&HashSet<r2ssa::SSAVar>>,
    edge_phi_uses: Option<&HashSet<r2ssa::SSAVar>>,
) -> HashSet<r2ssa::SSAVar> {
    let mut live = HashSet::new();
    if let Some(successor_live_in) = successor_live_in {
        live.extend(
            successor_live_in
                .iter()
                .filter(|value| successor_phi_defs.is_none_or(|defs| !defs.contains(*value)))
                .cloned(),
        );
    }
    if let Some(edge_phi_uses) = edge_phi_uses {
        live.extend(edge_phi_uses.iter().cloned());
    }
    live
}

/// Whether a merge's copy can sit at the end of a two-way predecessor.
///
/// The copy runs on every edge out of the block, not only the one the merge
/// came in on, so it is sound exactly when nothing on the other edges can tell:
/// the terminator must not read the destination, and the destination must not
/// be live along any other successor.
///
/// This once also required the target to dominate the predecessor, which
/// confined it to loop backedges. Soundness never depended on that, and the
/// restriction refused every merge on a loop *exit* edge -- leaving those
/// destinations with no definition at all, which is how `djb2` at x86-64 -O2
/// lost the counter its remainder loop starts from.
fn can_materialize_on_branch_edge(
    func: &SSAFunction,
    liveness: &PhiEdgeLiveness,
    pred: u64,
    target: u64,
    dst: &r2ssa::SSAVar,
) -> bool {
    let successors = func.successors(pred);
    successors.len() > 1
        && successors.contains(&target)
        && !func
            .get_block(pred)
            .and_then(|block| block.ops.last())
            .is_some_and(|op| op.sources().contains(&dst))
        && successors
            .into_iter()
            .filter(|successor| *successor != target)
            .all(|successor| !liveness.live_on_edge(pred, successor).contains(dst))
}

fn remove_phi_edge_operation(
    ops: &mut Vec<SSAOp>,
    rows: &mut Vec<NormalizedOpOrigin>,
    definition: OriginalPhiDefinition,
    entity: r2ssa::SemanticId,
    site: UseSite,
) -> Option<PhiEdgeOrigin> {
    if ops.len() != rows.len() {
        return None;
    }
    let row_idx = rows.iter().position(|origin| {
        matches!(origin, NormalizedOpOrigin::PhiEdgeCopy(edge)
            if edge.incoming == site
                && edge.definition == definition
                && edge.certified_entity == Some(entity))
    })?;
    ops.remove(row_idx);
    match rows.remove(row_idx) {
        NormalizedOpOrigin::PhiEdgeCopy(origin) => Some(origin),
        NormalizedOpOrigin::Original(_) | NormalizedOpOrigin::RelocatedInitializer(_) => {
            unreachable!("selected row was sealed as a phi-edge operation")
        }
    }
}

/// Coalesce certified loop carriers across zero-iteration exits.
///
/// Prepared SSA proves the carrier identity and a dominating entry-valued
/// edge. The renderer only performs the corresponding SSA destruction: one
/// initialization before the loop decision replaces redundant copies on the
/// loop-entry edges, while latch updates remain at their original program
/// point.
#[allow(dead_code)]
pub(crate) fn materialize_certified_loop_carrier_initializers(
    func: &mut SSAFunction,
    origins: &mut NormalizationOrigins,
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
) -> Result<(), NormalizationOriginError> {
    let execution = SsaExecutionControl::default();
    let control = DecompileWorkControl::new(&execution, DecompileWorkPhase::Normalization);
    match materialize_certified_loop_carrier_initializers_with_control(
        func,
        origins,
        prepared,
        render_facts,
        control,
    ) {
        Ok(()) => Ok(()),
        Err(NormalizationFailure::Origins(error)) => Err(error),
        Err(NormalizationFailure::Execution(error)) => {
            panic!("default decompiler work control cannot stop: {error}")
        }
    }
}

pub(crate) fn materialize_certified_loop_carrier_initializers_with_control(
    func: &mut SSAFunction,
    origins: &mut NormalizationOrigins,
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
    control: DecompileWorkControl<'_>,
) -> Result<(), NormalizationFailure> {
    control.poll()?;
    CarrierEdgeCertificates::build(prepared.graph(), Some(render_facts))
        .ok_or(NormalizationOriginError::InvalidCarrierCertificates)?;
    origins.validate(func, prepared, Some(render_facts))?;
    for entity in render_facts.loop_carriers() {
        control.poll()?;
        let r2types::CertifiedEntity::LoopCarrier {
            id,
            phi,
            identity_values,
            entries,
            dominating_initializers,
            ..
        } = entity
        else {
            continue;
        };
        if identity_values.len() < 2 {
            continue;
        }
        let [initializer] = dominating_initializers.as_slice() else {
            continue;
        };
        if !entries.iter().any(|entry| entry.value == initializer.value) {
            continue;
        }
        let dst = prepared
            .value_var(*phi)
            .cloned()
            .ok_or(NormalizationOriginError::InvalidCarrierCertificates)?;
        let src = prepared
            .value_var(initializer.value)
            .cloned()
            .ok_or(NormalizationOriginError::InvalidCarrierCertificates)?;
        if dst.size != src.size {
            return Err(NormalizationOriginError::InvalidCarrierCertificates.into());
        }

        let mut relocated_entry_sites = entries
            .iter()
            .filter(|entry| {
                entry.value == initializer.value
                    && (entry.predecessor == initializer.predecessor
                        || prepared
                            .function()
                            .dominates(initializer.predecessor, entry.predecessor))
            })
            .map(|entry| entry.site)
            .collect::<Vec<_>>();
        relocated_entry_sites.sort_unstable();
        relocated_entry_sites.dedup();
        if relocated_entry_sites.is_empty() {
            continue;
        }
        let definition = OriginalPhiDefinition {
            inst: prepared
                .graph()
                .def_inst(*phi)
                .ok_or(NormalizationOriginError::InvalidCarrierCertificates)?,
            value: *phi,
        };
        let mut initializer_entry_site = None;
        let mut fully_located = true;
        let mut located = Vec::new();
        for site in &relocated_entry_sites {
            control.poll()?;
            let predecessor = prepared
                .graph()
                .inst(site.inst)
                .and_then(|inst| match &inst.payload {
                    r2ssa::InstPayload::Phi { predecessors } => {
                        predecessors.get(site.input_idx).copied()
                    }
                    r2ssa::InstPayload::Op(_) => None,
                })
                .and_then(|block| prepared.graph().block(block))
                .map(|block| block.addr)
                .ok_or(NormalizationOriginError::InvalidCarrierCertificates)?;
            let block_id = prepared
                .graph()
                .block_id_for_addr(predecessor)
                .ok_or(NormalizationOriginError::InvalidCarrierCertificates)?;
            let Some(_row_idx) = origins.rows(block_id).and_then(|rows| {
                rows.iter().position(|origin| {
                    matches!(origin, NormalizedOpOrigin::PhiEdgeCopy(edge)
                        if edge.incoming == *site
                            && edge.definition == definition
                            && edge.certified_entity == Some(*id))
                })
            }) else {
                fully_located = false;
                break;
            };
            if predecessor == initializer.predecessor {
                initializer_entry_site = Some(*site);
            }
            located.push((block_id, predecessor, *site));
        }
        if !fully_located {
            continue;
        }

        // Remove by sealed origin rather than operation shape. An unrelated
        // byte-identical copy is a different normalized operation and remains.
        located.sort_unstable_by_key(|(block, _, site)| (*block, *site));
        for (block_id, predecessor, site) in &located {
            if Some(*site) == initializer_entry_site {
                continue;
            }
            let removed_edge = remove_phi_edge_operation(
                &mut func
                    .get_block_mut(*predecessor)
                    .ok_or(NormalizationOriginError::BlockTopology)?
                    .ops,
                origins
                    .rows_mut(*block_id)
                    .ok_or(NormalizationOriginError::BlockTopology)?,
                definition,
                *id,
                *site,
            )
            .ok_or(NormalizationOriginError::RemovedPhiEdge)?;
            origins.replaced_phi_edges.push(removed_edge);
        }

        let relocated = NormalizedOpOrigin::RelocatedInitializer(RelocatedInitializerOrigin {
            definition,
            source_value: initializer.value,
            certified_entity: *id,
            evidence_site: initializer.site,
            replaced_sites: relocated_entry_sites.into_boxed_slice(),
        });
        let initializer_block_id = prepared
            .graph()
            .block_id_for_addr(initializer.predecessor)
            .ok_or(NormalizationOriginError::InvalidCarrierCertificates)?;
        let initializer_row = initializer_entry_site
            .map(|initializer_entry_site| {
                origins
                    .rows(initializer_block_id)
                    .and_then(|rows| {
                        rows.iter().position(|origin| {
                            matches!(origin, NormalizedOpOrigin::PhiEdgeCopy(edge)
                            if edge.incoming == initializer_entry_site
                                && edge.definition == definition)
                        })
                    })
                    .ok_or(NormalizationOriginError::RemovedPhiEdge)
            })
            .transpose()?;
        if let Some(row_idx) = initializer_row {
            let replaced = std::mem::replace(
                &mut origins
                    .rows_mut(initializer_block_id)
                    .ok_or(NormalizationOriginError::BlockTopology)?[row_idx],
                relocated,
            );
            let NormalizedOpOrigin::PhiEdgeCopy(replaced) = replaced else {
                unreachable!("initializer row was sealed as a phi-edge operation")
            };
            origins.replaced_phi_edges.push(replaced);
        } else {
            let block = func
                .get_block_mut(initializer.predecessor)
                .ok_or(NormalizationOriginError::BlockTopology)?;
            let insert_at = block
                .ops
                .iter()
                .rposition(is_block_terminator)
                .unwrap_or(block.ops.len());
            block.ops.insert(insert_at, SSAOp::Copy { dst, src });
            origins
                .rows_mut(initializer_block_id)
                .ok_or(NormalizationOriginError::BlockTopology)?
                .insert(insert_at, relocated);
        }
    }
    origins
        .replaced_phi_edges
        .sort_unstable_by_key(|edge| edge.incoming);
    control.poll()?;
    origins.validate(func, prepared, Some(render_facts))?;
    Ok(())
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::ast::{BinaryOp, UnaryOp};
    use crate::fold::FoldingContext;
    use r2il::{ArchSpec, R2ILBlock, R2ILOp, RegisterDef, Varnode};
    use r2ssa::{PhiNode, SSAFunction, SSAVar};

    /// The names a fixture in this module declares.
    fn test_table() -> std::cell::RefCell<crate::symbol::SymbolTable> {
        std::cell::RefCell::new(crate::symbol::SymbolTable::new())
    }

    #[test]
    fn normalization_is_idempotent_for_predicates() {
        let ctx = FoldingContext::new(64);
        let expr = CExpr::unary(
            UnaryOp::Not,
            CExpr::binary(
                BinaryOp::Eq,
                CExpr::binary(BinaryOp::Sub, ctx.name_ref("x"), CExpr::IntLit(0)),
                CExpr::IntLit(0),
            ),
        );

        let once = normalize_expr(&ctx, expr.clone(), NormalizeMode::Predicate);
        let twice = normalize_expr(&ctx, once.clone(), NormalizeMode::Predicate);
        assert_eq!(once, twice, "Predicate normalization must be idempotent");
    }

    #[test]
    fn initializer_removal_uses_exact_origin_not_duplicate_copy_shape() {
        let dst = SSAVar::new("RAX", 2, 8);
        let src = SSAVar::new("RAX", 1, 8);
        let op = SSAOp::Copy {
            dst: dst.clone(),
            src: src.clone(),
        };
        let definition = OriginalPhiDefinition {
            inst: InstId(10),
            value: ValueId(2),
        };
        let entity = r2ssa::SemanticId::loop_carrier(ValueId(2));
        let edge = |input_idx| {
            NormalizedOpOrigin::PhiEdgeCopy(PhiEdgeOrigin {
                definition,
                incoming: UseSite {
                    inst: definition.inst,
                    input_idx,
                },
                incoming_value: ValueId(1),
                predecessor: 0x1000 + input_idx as u64 * 4,
                target: 0x1010,
                incoming_input_idx: 0,
                certified_entity: Some(entity),
                certified_roles: vec![CertifiedPhiEdgeRole::Entry].into_boxed_slice(),
                guarded: None,
            })
        };
        let mut ops = vec![op.clone(), op];
        let mut rows = vec![edge(0), edge(1)];

        let removed = remove_phi_edge_operation(
            &mut ops,
            &mut rows,
            definition,
            entity,
            UseSite {
                inst: definition.inst,
                input_idx: 0,
            },
        )
        .expect("certified occurrence");

        assert_eq!(removed.incoming.input_idx, 0);
        assert_eq!(ops.len(), 1, "one byte-identical copy must remain");
        assert!(matches!(
            rows.as_slice(),
            [NormalizedOpOrigin::PhiEdgeCopy(origin)] if origin.incoming.input_idx == 1
        ));
    }

    #[test]
    fn materialize_phis_on_single_successor_pred() {
        // 0x1000: cbranch to 0x1008 else 0x1004
        // 0x1004: define reg0 = 1, branch 0x100c
        // 0x1008: define reg0 = 2, branch 0x100c
        // 0x100c: return reg0 (forces phi at join)
        let mut b0 = R2ILBlock::new(0x1000, 4);
        b0.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1008, 8),
        });

        let mut b1 = R2ILBlock::new(0x1004, 4);
        b1.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(1, 8),
        });
        b1.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });

        let mut b2 = R2ILBlock::new(0x1008, 4);
        b2.push(R2ILOp::Copy {
            dst: Varnode::register(0, 8),
            src: Varnode::constant(2, 8),
        });
        b2.push(R2ILOp::Branch {
            target: Varnode::constant(0x100c, 8),
        });

        let mut b3 = R2ILBlock::new(0x100c, 4);
        b3.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });

        let func = SSAFunction::from_blocks_raw_no_arch(&[b0, b1, b2, b3]).expect("ssa function");
        let with_phis = func.blocks().any(|b| !b.phis.is_empty());
        assert!(with_phis, "fixture should include phi nodes");

        let (normalized, origins, graph) = materialize_all_phis_with_origins(&func);
        origins
            .validate_against_graph(&normalized, &graph, None)
            .expect("materialized joins have exact dense origins");
        let materialized_sites = origins
            .blocks
            .iter()
            .enumerate()
            .flat_map(|(block_idx, block)| {
                block
                    .rows
                    .iter()
                    .enumerate()
                    .filter_map(move |(op_idx, origin)| {
                        matches!(origin, NormalizedOpOrigin::PhiEdgeCopy(_)).then_some((
                            BlockId(block_idx as u32),
                            block.address,
                            op_idx,
                        ))
                    })
            })
            .collect::<Vec<_>>();
        let &(block_id, block_addr, op_idx) = materialized_sites
            .first()
            .expect("fixture materializes phi inputs");

        let mut duplicate_function = normalized.clone();
        let duplicate_op = duplicate_function
            .get_block(block_addr)
            .expect("materialized predecessor")
            .ops[op_idx]
            .clone();
        duplicate_function
            .get_block_mut(block_addr)
            .expect("materialized predecessor")
            .ops
            .insert(op_idx, duplicate_op.clone());
        let mut duplicate_origins = origins.clone();
        let duplicate_origin = duplicate_origins
            .rows(block_id)
            .expect("materialized predecessor origins")[op_idx]
            .clone();
        duplicate_origins
            .rows_mut(block_id)
            .expect("materialized predecessor origins")
            .insert(op_idx, duplicate_origin.clone());
        assert_eq!(
            duplicate_origins.validate_against_graph(&duplicate_function, &graph, None),
            Err(NormalizationOriginError::RemovedPhiEdge),
            "two individually valid rows cannot claim one original input"
        );

        let mut omitted_function = normalized.clone();
        omitted_function
            .get_block_mut(block_addr)
            .expect("materialized predecessor")
            .ops
            .remove(op_idx);
        let mut omitted_origins = origins.clone();
        omitted_origins
            .rows_mut(block_id)
            .expect("materialized predecessor origins")
            .remove(op_idx);
        assert_eq!(
            omitted_origins.validate_against_graph(&omitted_function, &graph, None),
            Err(NormalizationOriginError::RemovedPhiEdge),
            "every removed phi input needs one explicit disposition"
        );

        let &(omitted_block_id, omitted_block_addr, omitted_op_idx) = materialized_sites
            .get(1)
            .expect("join fixture has a second incoming edge");
        assert_ne!(block_id, omitted_block_id);
        let mut duplicate_and_omitted_function = normalized.clone();
        duplicate_and_omitted_function
            .get_block_mut(block_addr)
            .expect("duplicated predecessor")
            .ops
            .insert(op_idx, duplicate_op);
        duplicate_and_omitted_function
            .get_block_mut(omitted_block_addr)
            .expect("omitted predecessor")
            .ops
            .remove(omitted_op_idx);
        let mut duplicate_and_omitted_origins = origins.clone();
        duplicate_and_omitted_origins
            .rows_mut(block_id)
            .expect("duplicated predecessor origins")
            .insert(op_idx, duplicate_origin);
        duplicate_and_omitted_origins
            .rows_mut(omitted_block_id)
            .expect("omitted predecessor origins")
            .remove(omitted_op_idx);
        assert_eq!(
            duplicate_and_omitted_origins.validate_against_graph(
                &duplicate_and_omitted_function,
                &graph,
                None,
            ),
            Err(NormalizationOriginError::RemovedPhiEdge),
            "equal row counts cannot hide one duplicated and one omitted input"
        );
        let any_phi = normalized.blocks().any(|b| !b.phis.is_empty());
        assert!(
            !any_phi,
            "phis should be removed when all edges materialize"
        );
    }

    #[test]
    fn lower_loop_backedge_unconditionally_when_dst_is_dead_on_exit_edge() {
        let hash_1 = SSAVar::new("RAX", 1, 8);
        let hash_2 = SSAVar::new("RAX", 2, 8);
        let hash_4 = SSAVar::new("RAX", 4, 8);
        let cond = SSAVar::new("tmp:cond", 1, 1);

        let mut func = loop_backedge_phi_fixture();
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: hash_1.clone(),
                src: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::Branch {
                target: SSAVar::new("ram:1004", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("header").phis = vec![PhiNode {
            dst: hash_2.clone(),
            sources: vec![(0x1000, hash_1), (0x1008, hash_4.clone())],
            canonical_storage: None,
        }];
        func.get_block_mut(0x1004).expect("header").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("latch").ops = vec![
            SSAOp::IntAdd {
                dst: hash_4.clone(),
                a: hash_2.clone(),
                b: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::IntNotEqual {
                dst: cond.clone(),
                a: SSAVar::new("RSI", 0, 8),
                b: SSAVar::new("const:0", 0, 8),
            },
            SSAOp::CBranch {
                target: SSAVar::new("ram:1004", 0, 8),
                cond: cond.clone(),
            },
        ];
        func.get_block_mut(0x100c).expect("exit").ops = vec![SSAOp::Return {
            target: SSAVar::new("RIP", 1, 8),
        }];

        let normalized = materialize_all_phis(&func);
        assert!(
            normalized
                .get_block(0x1004)
                .is_some_and(|block| block.phis.is_empty()),
            "loop header phi should be eliminated when all edge moves are exact"
        );
        let latch = normalized.get_block(0x1008).expect("latch");
        assert!(
            latch.ops.iter().any(|op| matches!(
                op,
                SSAOp::Copy { dst, src } if dst == &hash_2 && src == &hash_4
            )),
            "a value dead on every exit edge may be updated before the branch"
        );
    }

    #[test]
    fn self_phi_input_is_projected_as_an_explicit_noop_use() {
        let entry_value = SSAVar::new("RAX", 1, 8);
        let phi_value = SSAVar::new("RAX", 2, 8);
        let mut func = loop_backedge_phi_fixture();
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: entry_value.clone(),
                src: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::Branch {
                target: SSAVar::new("ram:1004", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("header").phis = vec![PhiNode {
            dst: phi_value.clone(),
            sources: vec![(0x1000, entry_value), (0x1008, phi_value.clone())],
            canonical_storage: None,
        }];
        func.get_block_mut(0x1004).expect("header").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("latch").ops = vec![SSAOp::CBranch {
            target: SSAVar::new("ram:1004", 0, 8),
            cond: SSAVar::new("const:1", 0, 1),
        }];

        let (normalized, origins, graph) = materialize_all_phis_with_origins(&func);
        origins
            .validate_against_graph(&normalized, &graph, None)
            .expect("self input has one explicit noop disposition");
        let phi_inst = graph
            .insts
            .iter()
            .find(|inst| inst.output.is_some_and(|output| {
                graph
                    .value(output)
                    .is_some_and(|value| value.var == phi_value)
            }))
            .expect("phi instruction");
        assert_eq!(
            origins.noop_sites().collect::<Vec<_>>(),
            vec![UseSite {
                inst: phi_inst.id,
                input_idx: 1,
            }]
        );
    }

    #[test]
    fn guard_loop_backedge_phi_when_dst_live_on_exit_edge() {
        let hash_1 = SSAVar::new("RAX", 1, 8);
        let hash_2 = SSAVar::new("RAX", 2, 8);
        let hash_4 = SSAVar::new("RAX", 4, 8);
        let cond = SSAVar::new("tmp:cond", 1, 1);

        let mut func = loop_backedge_phi_fixture();
        func.get_block_mut(0x1000).expect("entry").ops = vec![
            SSAOp::Copy {
                dst: hash_1.clone(),
                src: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::Branch {
                target: SSAVar::new("ram:1004", 0, 8),
            },
        ];
        func.get_block_mut(0x1004).expect("header").phis = vec![PhiNode {
            dst: hash_2.clone(),
            sources: vec![(0x1000, hash_1), (0x1008, hash_4.clone())],
            canonical_storage: None,
        }];
        func.get_block_mut(0x1004).expect("header").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("latch").ops = vec![
            SSAOp::IntAdd {
                dst: hash_4.clone(),
                a: hash_2.clone(),
                b: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::IntNotEqual {
                dst: cond.clone(),
                a: SSAVar::new("RSI", 0, 8),
                b: SSAVar::new("const:0", 0, 8),
            },
            SSAOp::CBranch {
                target: SSAVar::new("ram:1004", 0, 8),
                cond: cond.clone(),
            },
        ];
        func.get_block_mut(0x100c).expect("exit").ops = vec![
            SSAOp::Copy {
                dst: SSAVar::new("RBX", 1, 8),
                src: hash_2.clone(),
            },
            SSAOp::Return {
                target: SSAVar::new("RIP", 1, 8),
            },
        ];

        let (normalized, origins, graph) = materialize_all_phis_with_origins(&func);
        origins
            .validate_against_graph(&normalized, &graph, None)
            .expect("guarded normalization has exact dense origins");
        assert!(
            normalized
                .get_block(0x1004)
                .is_some_and(|block| block.phis.is_empty()),
            "an exact guarded backedge move should eliminate the loop-header phi"
        );
        let latch = normalized.get_block(0x1008).expect("latch");
        let latch_id = graph.block_id_for_addr(0x1008).expect("latch graph id");
        let select_idx = latch
            .ops
            .iter()
            .position(|op| matches!(op, SSAOp::Select { dst, .. } if dst == &hash_2))
            .expect("guarded edge select");
        let NormalizedOpOrigin::PhiEdgeCopy(edge) = origins
            .origin(NormalizedOpSite {
                block: latch_id,
                op_idx: select_idx,
            })
            .expect("dense select origin")
        else {
            panic!("guarded select must stay typed synthetic")
        };
        assert_eq!(
            edge.incoming.input_idx, 1,
            "backedge is the second phi input"
        );
        assert_eq!(edge.incoming_input_idx, 1, "true arm carries the update");
        let guarded = edge.guarded.expect("guard use and preserve operand");
        assert_eq!(guarded.guard.input_idx, 1, "CBranch condition use");
        assert_eq!(guarded.preserve.input_idx, 2, "false arm preserves carrier");
        let original_terminator = graph
            .inst_id_for_op_site(0x1008, 2)
            .expect("source branch InstId");
        assert!(matches!(
            origins.origin(NormalizedOpSite {
                block: latch_id,
                op_idx: latch.ops.len() - 1,
            }),
            Some(NormalizedOpOrigin::Original(inst)) if *inst == original_terminator
        ));
        let mut forged = origins.clone();
        forged.rows_mut(latch_id).expect("latch origin rows").pop();
        assert_eq!(
            forged.validate_against_graph(&normalized, &graph, None),
            Err(NormalizationOriginError::RowCount { block: 0x1008 })
        );
        let mut forged_site = origins.clone();
        let NormalizedOpOrigin::PhiEdgeCopy(forged_edge) =
            &mut forged_site.rows_mut(latch_id).expect("latch origin rows")[select_idx]
        else {
            panic!("select origin")
        };
        forged_edge.incoming.input_idx = 0;
        assert_eq!(
            forged_site.validate_against_graph(&normalized, &graph, None),
            Err(NormalizationOriginError::PhiEdge {
                block: 0x1008,
                op_idx: select_idx,
            })
        );
        assert!(
            latch.ops.iter().any(|op| matches!(
                op,
                SSAOp::Select {
                    dst,
                    cond: select_cond,
                    if_true,
                    if_false,
                } if dst == &hash_2
                    && select_cond == &cond
                    && if_true == &hash_4
                    && if_false == &hash_2
            )),
            "the backedge update must execute only when its branch edge is taken"
        );

        let (normalized_again, origins_again, graph_again) =
            materialize_all_phis_with_origins(&func);
        assert_eq!(origins, origins_again, "origin allocation is deterministic");
        origins_again
            .validate_against_graph(&normalized_again, &graph_again, None)
            .expect("repeated normalization validates identically");
    }

    #[test]
    fn keep_loop_phi_when_edge_guard_reads_its_destination() {
        let value_1 = SSAVar::new("RAX", 1, 8);
        let value_2 = SSAVar::new("RAX", 2, 8);
        let value_4 = SSAVar::new("RAX", 4, 8);
        let mut func = loop_backedge_phi_fixture();
        func.get_block_mut(0x1000).expect("entry").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1004", 0, 8),
        }];
        func.get_block_mut(0x1004).expect("header").phis = vec![PhiNode {
            dst: value_2.clone(),
            sources: vec![(0x1000, value_1), (0x1008, value_4.clone())],
            canonical_storage: None,
        }];
        func.get_block_mut(0x1004).expect("header").ops = vec![SSAOp::Branch {
            target: SSAVar::new("ram:1008", 0, 8),
        }];
        func.get_block_mut(0x1008).expect("latch").ops = vec![
            SSAOp::IntAdd {
                dst: value_4,
                a: value_2.clone(),
                b: SSAVar::new("const:1", 0, 8),
            },
            SSAOp::CBranch {
                target: SSAVar::new("ram:1004", 0, 8),
                cond: value_2.clone(),
            },
        ];

        let normalized = materialize_all_phis(&func);

        assert_eq!(
            normalized.get_block(0x1004).expect("header").phis.len(),
            1,
            "lowering before the branch would overwrite its condition"
        );
        assert!(
            !normalized
                .get_block(0x1000)
                .expect("entry")
                .ops
                .iter()
                .any(|op| matches!(op, SSAOp::Copy { dst, .. } if dst == &value_2)),
            "a rejected phi bundle must not leak its entry-edge copy"
        );
    }

    #[test]
    fn keep_parallel_phi_bundle_when_moves_are_cyclic() {
        let a = SSAVar::new("RAX", 2, 8);
        let b = SSAVar::new("RBX", 2, 8);
        let mut func = loop_backedge_phi_fixture();
        func.get_block_mut(0x1004).expect("header").phis = vec![
            PhiNode {
                dst: a.clone(),
                sources: vec![(0x1000, SSAVar::new("RAX", 1, 8)), (0x1008, b.clone())],
                canonical_storage: None,
            },
            PhiNode {
                dst: b.clone(),
                sources: vec![(0x1000, SSAVar::new("RBX", 1, 8)), (0x1008, a.clone())],
                canonical_storage: None,
            },
        ];

        let normalized = materialize_all_phis(&func);

        assert_eq!(
            normalized.get_block(0x1004).expect("header").phis.len(),
            2,
            "cyclic parallel moves must remain as phis until temporaries are certified"
        );
        assert!(
            !normalized
                .get_block(0x1000)
                .expect("entry")
                .ops
                .iter()
                .any(|op| matches!(op, SSAOp::Copy { dst, .. } if dst == &a || dst == &b)),
            "an incomplete phi bundle must not leak partial edge copies"
        );
    }

    #[test]
    fn certified_carrier_initializer_moves_before_zero_iteration_branch() {
        let mut entry = R2ILBlock::new(0x2000, 4);
        entry.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x200c, 8),
        });
        let mut preheader = R2ILBlock::new(0x2004, 4);
        preheader.push(R2ILOp::Branch {
            target: Varnode::constant(0x2008, 8),
        });
        let mut loop_block = R2ILBlock::new(0x2008, 4);
        loop_block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(1, 8),
        });
        loop_block.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x2008, 8),
        });
        let mut exit = R2ILBlock::new(0x200c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::register(0, 8),
        });
        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RAX", 0, 8));
        arch.add_register(RegisterDef::new("RSP", 8, 8));
        arch.add_register(RegisterDef::new("RIP", 16, 8));
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2dec-normalize-loop-owner".to_vec(),
            "sysv64",
            std::iter::empty::<r2ssa::SourceAbiParameterSpec>(),
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(0),
            },
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| interface.with_stack_pointer_storage(storage(8)))
        .and_then(|interface| interface.with_return_address_storage(storage(16)))
        .expect("exact zero-iteration loop interface");
        let prepared = std::sync::Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(
                &[entry, preheader, loop_block, exit],
                Some(&arch),
                interface,
            )
            .expect("zero-iteration loop fixture"),
        );
        let carrier = prepared
            .structured()
            .loops
            .values()
            .flat_map(|loop_fact| loop_fact.carriers.iter())
            .find(|carrier| !carrier.dominating_initializers.is_empty())
            .expect("certified loop carrier");
        let phi = prepared
            .value_var(carrier.phi)
            .expect("carrier phi")
            .clone();
        let init = prepared
            .value_var(carrier.dominating_initializers[0].value)
            .expect("carrier initializer")
            .clone();
        let analysis = r2types::build_source_owned_type_writeback_analysis(
            r2types::TypeWritebackAnalysisRequest::new(
                std::sync::Arc::clone(&prepared),
                r2types::ParsedExternalContext::default(),
            )
            .expect("matching source assumptions"),
        )
        .expect("source-owned loop analysis");
        let render_facts = analysis.function_facts().render_facts();
        let mut invalid_render_facts = render_facts.clone();
        let r2types::CertifiedEntity::LoopCarrier { entries, .. } = invalid_render_facts
            .certified_entities
            .get_mut(&carrier.id)
            .expect("render facts retain the upstream carrier")
        else {
            panic!("carrier identity must resolve to a loop carrier")
        };
        entries
            .first_mut()
            .expect("certified carrier has an entry")
            .site
            .input_idx = usize::MAX;
        assert!(matches!(
            materialize_certified_loop_carriers(
                prepared.function(),
                prepared.as_ref(),
                &invalid_render_facts,
            ),
            Err(NormalizationOriginError::InvalidCarrierCertificates)
        ));

        let (mut normalized, mut origins) = materialize_certified_loop_carriers(
            prepared.function(),
            prepared.as_ref(),
            render_facts,
        )
        .expect("certified carrier geometry has valid exact origins");
        materialize_certified_loop_carrier_initializers(
            &mut normalized,
            &mut origins,
            prepared.as_ref(),
            render_facts,
        )
        .expect("certified initializer has valid exact origins");
        origins
            .validate(&normalized, prepared.as_ref(), Some(render_facts))
            .expect("normalization origins remain sealed after relocation");
        let (relocated_site, relocated) = origins
            .blocks
            .iter()
            .enumerate()
            .flat_map(|(block_idx, block)| {
                block.rows.iter().enumerate().map(move |(op_idx, origin)| {
                    (
                        NormalizedOpSite {
                            block: BlockId(block_idx as u32),
                            op_idx,
                        },
                        origin,
                    )
                })
            })
            .find_map(|(site, origin)| match origin {
                NormalizedOpOrigin::RelocatedInitializer(origin)
                    if origin.definition.value == carrier.phi =>
                {
                    Some((site, origin))
                }
                _ => None,
            })
            .expect("certified initializer has a typed relocated origin");
        let replaced_sites = origins
            .replaced_phi_edges()
            .iter()
            .filter(|edge| edge.definition.value == carrier.phi)
            .map(|edge| edge.incoming)
            .collect::<Vec<_>>();
        assert_eq!(
            relocated.evidence_site,
            carrier.dominating_initializers[0].site
        );
        assert_eq!(relocated.replaced_sites.as_ref(), replaced_sites.as_slice());
        assert!(
            relocated
                .replaced_sites
                .windows(2)
                .all(|sites| sites[0] < sites[1])
        );
        assert!(!relocated.replaced_sites.contains(&relocated.evidence_site));
        let projection = origins
            .projection(relocated_site, prepared.as_ref())
            .expect("source authority matches")
            .expect("relocated row projects");
        assert_eq!(projection.inputs.len(), 1);
        assert_eq!(projection.inputs[0].value, relocated.source_value);
        assert_eq!(
            projection.inputs[0].uses.as_ref(),
            relocated.replaced_sites.as_ref(),
            "one relocated input fans out to every replaced original use"
        );
        assert!(!projection.inputs[0].uses.contains(&relocated.evidence_site));
        assert_eq!(
            projection.output,
            Some(NormalizedOutputProjection {
                inst: relocated.definition.inst,
                value: relocated.definition.value,
            })
        );
        let mut foreign_block = R2ILBlock::new(0x3000, 4);
        foreign_block.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });
        let foreign = r2ssa::SsaArtifact::for_decompile(&[foreign_block], None)
            .expect("independent artifact");
        assert_eq!(
            origins.projection(relocated_site, &foreign),
            Err(NormalizationOriginError::SourceAuthority),
            "projection lookup is sealed to the exact source authority"
        );
        assert!(
            origins
                .replaced_phi_edges()
                .iter()
                .all(|edge| edge.incoming != relocated.evidence_site),
            "the upstream initializer use is retained as evidence, not claimed as replaced"
        );
        assert!(
            origins
                .blocks
                .iter()
                .flat_map(|block| block.rows.iter())
                .any(|origin| matches!(origin,
                    NormalizedOpOrigin::PhiEdgeCopy(edge)
                        if edge.incoming == relocated.evidence_site)),
            "the genuine post-loop evidence use remains a live exact-origin edge"
        );

        let entry = normalized.get_block(0x2000).expect("entry");
        assert!(entry.ops.iter().any(|op| matches!(
            op,
            SSAOp::Copy { dst, src } if dst == &phi && src == &init
        )));
        let preheader = normalized.get_block(0x2004).expect("preheader");
        assert!(!preheader.ops.iter().any(|op| matches!(
            op,
            SSAOp::Copy { dst, src } if dst == &phi && src == &init
        )));
    }

    #[test]
    fn post_loop_carrier_edges_stay_before_destructive_register_reuse() {
        let mut entry = R2ILBlock::new(0x3000, 4);
        entry.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x3010, 8),
        });
        let mut preheader = R2ILBlock::new(0x3004, 4);
        preheader.push(R2ILOp::Branch {
            target: Varnode::constant(0x3008, 8),
        });
        let mut loop_block = R2ILBlock::new(0x3008, 8);
        loop_block.push(R2ILOp::IntAdd {
            dst: Varnode::register(0, 8),
            a: Varnode::register(0, 8),
            b: Varnode::constant(4, 8),
        });
        loop_block.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x3008, 8),
        });
        let mut exit = R2ILBlock::new(0x3010, 8);
        exit.push(R2ILOp::Copy {
            dst: Varnode::register(16, 8),
            src: Varnode::register(0, 8),
        });
        exit.push(R2ILOp::IntSub {
            dst: Varnode::register(0, 8),
            a: Varnode::register(8, 8),
            b: Varnode::register(0, 8),
        });
        exit.push(R2ILOp::Load {
            dst: Varnode::register(24, 8),
            space: r2il::SpaceId::Ram,
            addr: Varnode::register(16, 8),
        });
        exit.push(R2ILOp::Return {
            target: Varnode::register(24, 8),
        });

        let mut arch = ArchSpec::new("x86-64");
        arch.addr_size = 8;
        arch.add_register(RegisterDef::new("RDI", 0, 8));
        arch.add_register(RegisterDef::new("RSI", 8, 8));
        arch.add_register(RegisterDef::new("RCX", 16, 8));
        arch.add_register(RegisterDef::new("RAX", 24, 8));
        arch.add_register(RegisterDef::new("RSP", 32, 8));
        arch.add_register(RegisterDef::new("RIP", 40, 8));
        let storage = |offset| r2ssa::CanonicalStorageId {
            space: r2ssa::CanonicalStorageSpace::Register,
            offset,
            size: 8,
        };
        let interface = r2ssa::SourceFunctionInterface::new_exact(
            b"r2dec-normalize-post-loop-reuse".to_vec(),
            "sysv64",
            std::iter::empty::<r2ssa::SourceAbiParameterSpec>(),
            r2ssa::SourceFunctionReturn::Register {
                storage: storage(24),
            },
            std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
        )
        .and_then(|interface| interface.with_stack_pointer_storage(storage(32)))
        .and_then(|interface| interface.with_return_address_storage(storage(40)))
        .expect("exact post-loop reuse interface");
        let prepared = std::sync::Arc::new(
            r2ssa::SsaArtifact::for_decompile_with_interface(
                &[entry, preheader, loop_block, exit],
                Some(&arch),
                interface,
            )
            .expect("post-loop register-reuse fixture"),
        );
        let post_loop_phi = prepared
            .function()
            .get_block(0x3010)
            .and_then(|block| block.phis.iter().find(|phi| phi.dst.name == "RDI"))
            .expect("exit merges the skipped-loop and loop-carried pointers");
        let loop_phi = prepared
            .function()
            .get_block(0x3008)
            .and_then(|block| block.phis.iter().find(|phi| phi.dst.name == "RDI"))
            .expect("loop header owns the pointer carrier");
        let post_loop_value = prepared
            .graph()
            .value_id_for_var(&post_loop_phi.dst)
            .expect("post-loop phi has a stable value identity");
        let loop_value = prepared
            .graph()
            .value_id_for_var(&loop_phi.dst)
            .expect("loop header phi has a stable value identity");
        let analysis = r2types::build_source_owned_type_writeback_analysis(
            r2types::TypeWritebackAnalysisRequest::new(
                std::sync::Arc::clone(&prepared),
                r2types::ParsedExternalContext::default(),
            )
            .expect("matching source assumptions"),
        )
        .expect("source-owned post-loop analysis");
        let render_facts = analysis.function_facts().render_facts();
        assert!(
            render_facts
                .loop_carrier_for_value(post_loop_value)
                .is_some(),
            "the upstream certificate must own the post-loop identity value"
        );
        assert!(render_facts.loop_carrier_for_value(loop_value).is_some());

        let (mut normalized, mut origins) = materialize_certified_loop_carriers(
            prepared.function(),
            prepared.as_ref(),
            render_facts,
        )
        .expect("certified carriers have exact origins");
        materialize_certified_loop_carrier_initializers(
            &mut normalized,
            &mut origins,
            prepared.as_ref(),
            render_facts,
        )
        .expect("initializer relocation remains source-sealed");
        origins
            .validate(&normalized, prepared.as_ref(), Some(render_facts))
            .expect("post-loop edge dispositions remain complete");

        let (relocated_block, relocated_op) = origins
            .blocks
            .iter()
            .enumerate()
            .find_map(|(block_idx, block)| {
                block.rows.iter().enumerate().find_map(|(op_idx, origin)| {
                    matches!(origin,
                        NormalizedOpOrigin::RelocatedInitializer(relocated)
                            if relocated.definition.value == loop_value)
                    .then_some((block_idx, op_idx))
                })
            })
            .expect("the certified loop initializer relocates ahead of the zero-iteration split");
        assert_eq!(origins.blocks[relocated_block].address, 0x3000);
        assert!(matches!(
            normalized
                .get_block(0x3000)
                .and_then(|block| block.ops.get(relocated_op)),
            Some(SSAOp::Copy { dst, .. }) if dst == &loop_phi.dst
        ));

        let mut edge_predecessors = origins
            .blocks
            .iter()
            .flat_map(|block| block.rows.iter())
            .filter_map(|origin| match origin {
                NormalizedOpOrigin::PhiEdgeCopy(edge)
                    if edge.definition.value == post_loop_value =>
                {
                    Some(edge.predecessor)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        edge_predecessors.sort_unstable();
        assert_eq!(edge_predecessors, vec![0x3000, 0x3008]);
        assert!(origins.blocks.iter().flat_map(|block| &block.rows).all(
            |origin| !matches!(origin,
                NormalizedOpOrigin::RelocatedInitializer(relocated)
                    if relocated.definition.value == post_loop_value)
        ));
        assert!(
            normalized
                .get_block(0x3010)
                .expect("exit block")
                .ops
                .iter()
                .all(|op| op.dst() != Some(&post_loop_phi.dst)),
            "the saved pointer must be selected on its exact incoming edges, before RDI is reused"
        );
        let exit_ops = &normalized.get_block(0x3010).expect("exit block").ops;
        let preserve = exit_ops
            .iter()
            .position(|op| matches!(op,
                SSAOp::Copy { dst, src }
                    if dst.name == "RCX" && src == &post_loop_phi.dst))
            .expect("the exact post-loop pointer is preserved");
        let reuse = exit_ops
            .iter()
            .position(|op| matches!(op, SSAOp::IntSub { dst, .. } if dst.name == "RDI"))
            .expect("RDI is reused for the byte-count computation");
        let dereference = exit_ops
            .iter()
            .position(|op| matches!(op, SSAOp::Load { addr, .. } if addr.name == "RCX"))
            .expect("the tail load uses the preserved pointer carrier");
        assert!(preserve < reuse && reuse < dereference);
    }

    fn loop_backedge_phi_fixture() -> SSAFunction {
        let mut entry = R2ILBlock::new(0x1000, 4);
        entry.push(R2ILOp::Branch {
            target: Varnode::constant(0x1004, 8),
        });

        let mut header = R2ILBlock::new(0x1004, 4);
        header.push(R2ILOp::Branch {
            target: Varnode::constant(0x1008, 8),
        });

        let mut latch = R2ILBlock::new(0x1008, 4);
        latch.push(R2ILOp::CBranch {
            cond: Varnode::constant(1, 1),
            target: Varnode::constant(0x1004, 8),
        });

        let mut exit = R2ILBlock::new(0x100c, 4);
        exit.push(R2ILOp::Return {
            target: Varnode::constant(0, 8),
        });

        SSAFunction::from_blocks_raw_no_arch(&[entry, header, latch, exit]).expect("loop fixture")
    }
}

/// One name for every value a certified loop carrier passes through.
///
/// A carrier is one mutable variable the machine spells differently on each
/// edge: an entry value, a phi, a latch update and a post-loop merge are four
/// SSA values and one C local. Naming is per-version, so the same variable
/// reached the page as `rax_1`, `rax_2` and `rax_3`, with the loop assigning two
/// of them and the return reading a fourth that still held the entry value.
///
/// Two kinds of carrier are left alone, and both were found by rendering rather
/// than reasoning. One the loop reloads from a frame slot is a copy of that
/// slot, so naming it puts a second variable on the page for one value. One
/// whose values are not all the same storage holding one value is a register the
/// machine reused, and naming it would say two different values are one.
///
/// Constants are skipped. An entry edge arriving as a literal is the
/// initializer, not another spelling of the variable.
/// A carrier read at a width other than the one it is carried at.
///
/// `eax` and `rax` are one place at two widths, and a loop that carries the
/// place at one of them is still the source of a read at the other. The name is
/// the carrier's; the width is the width of *this* view of it, which is what
/// makes the difference between the two expressible at all -- an alias maps a
/// name to a name and cannot say "the low four bytes of".
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CarrierMemberView {
    /// The carrier this value is a view of.
    pub(crate) carrier: String,
    /// Width of this view, in bytes.
    pub(crate) width: u32,
    /// Width the carrier itself is held at, in bytes.
    pub(crate) carrier_width: u32,
}

/// Values that are one of a carrier's other widths.
///
/// A loop header carries a place once, but Sleigh gives each width its own phi:
/// adler32 at x86-64 -O1 has `RAX_2` certified as the carrier and `EAX_2`
/// beside it in the same block, over `{ Register, offset 0 }` at four bytes
/// instead of eight. Without the pairing the narrow phi belongs to no carrier,
/// so the tail that reads it after the loop is dropped and the return is left
/// quoting a name nothing defines.
///
/// Only a phi in the carrier's own header block counts. Every value at the place
/// is *not* the carrier -- that is the whole-function renaming that was measured
/// at 34 correct down to 13 -- and a phi in the header is the narrow point where
/// the two widths are provably the same run of the same storage.
pub(crate) fn carrier_member_views(
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
    aliases: &HashMap<String, String>,
) -> HashMap<String, CarrierMemberView> {
    use r2types::CertifiedEntity;

    // The pairing is only sound where the machine guarantees it: after a narrow
    // write the wide value is the narrow one zero-extended, so one answers for
    // the other. Where it does not hold, the upper bytes are whatever they were.
    if !prepared.narrow_write_clears_register() {
        return HashMap::new();
    }

    let graph = prepared.graph();
    let mut views = HashMap::new();
    for carrier in render_facts.loop_carriers() {
        let CertifiedEntity::LoopCarrier { phi, .. } = carrier else {
            continue;
        };
        let Some(carrier_var) = graph.value(*phi).map(|value| value.var.clone()) else {
            continue;
        };
        let Some(name) = aliases.get(&carrier_var.display_name()).cloned() else {
            continue;
        };
        let Some(storage) = graph.canonical_storage_for_var(&carrier_var) else {
            continue;
        };
        for block in prepared.function().blocks() {
            if !block.phis.iter().any(|phi| phi.dst == carrier_var) {
                continue;
            }
            for peer in &block.phis {
                if peer.dst == carrier_var || peer.dst.size == carrier_var.size {
                    continue;
                }
                // A peer that is a carrier in its own right keeps its own name.
                if aliases.contains_key(&peer.dst.display_name()) {
                    continue;
                }
                let Some(peer_storage) = graph.canonical_storage_for_var(&peer.dst) else {
                    continue;
                };
                if peer_storage.space != storage.space || peer_storage.offset != storage.offset {
                    continue;
                }
                views.insert(
                    peer.dst.display_name(),
                    CarrierMemberView {
                        carrier: name.clone(),
                        width: peer.dst.size,
                        carrier_width: carrier_var.size,
                    },
                );
            }
        }
        // The loop's exit value at another width is the same read one block
        // later: adler32's tail consumes the accumulator as `ecx` where the
        // carrier is `rcx`, and without this the return quotes `ecx_9`, a name
        // nothing declares.
        let CertifiedEntity::LoopCarrier { updates, .. } = carrier else {
            continue;
        };
        let update_values: HashSet<_> = updates.iter().map(|update| update.value).collect();
        for (merge, width) in exit_merges_for_carrier(prepared, *phi, &update_values) {
            if width == carrier_var.size || aliases.contains_key(&merge) {
                continue;
            }
            views.insert(
                merge,
                CarrierMemberView {
                    carrier: name.clone(),
                    width,
                    carrier_width: carrier_var.size,
                },
            );
        }
    }
    views
}

pub(crate) fn carrier_name_aliases(
    prepared: &r2ssa::SsaArtifact,
    render_facts: &r2types::FunctionRenderFacts,
) -> HashMap<String, String> {
    use r2types::CertifiedEntity;

    let graph = prepared.graph();
    let mirrored = prepared.memory_mirrored_carriers();
    let reused = prepared.carriers_spanning_a_reuse();
    let mut aliases = HashMap::new();
    let mut taken = HashSet::new();
    let spans = prepared.storage_spans();
    let mut names_by_span: HashMap<r2ssa::span::SpanId, String> = HashMap::new();
    for carrier in render_facts.loop_carriers() {
        let CertifiedEntity::LoopCarrier {
            id,
            header,
            phi,
            identity_values,
            entries,
            updates,
            ..
        } = carrier
        else {
            continue;
        };
        if mirrored.contains(id) || reused.contains(id) {
            continue;
        }
        let Some(base) = graph
            .value(*phi)
            .map(|value| crate::analysis::utils::ssa_render_base_name(&value.var))
        else {
            continue;
        };
        // Two loops carrying the same register are two variables *unless the
        // register holds one value across both*, which is what a storage span
        // says. A four-way unrolled loop followed by a remainder loop carries one
        // accumulator through both, and naming them apart left the remainder
        // starting from nothing: `fnv1a32` at x86-64 -O2 ran its tail over
        // `rax_1000005f0`, which no statement ever gave the value `rax` reached.
        //
        // `StorageSpans` computes where a storage stops holding one value, so it
        // answers this directly and the header suffix is kept for the case it was
        // written for: two carriers over one register in genuinely separate runs.
        let span = spans.span_of(*phi);
        let name = match span.and_then(|span| names_by_span.get(&span).cloned()) {
            Some(existing) => existing,
            None => {
                let name = if taken.insert(base.clone()) {
                    base
                } else {
                    format!("{base}_{header:x}")
                };
                if let Some(span) = span {
                    names_by_span.insert(span, name.clone());
                }
                name
            }
        };
        let members = identity_values
            .iter()
            .copied()
            .chain(entries.iter().map(|edge| edge.value))
            .chain(updates.iter().flat_map(|update| {
                std::iter::once(update.value).chain(update.identity_values.iter().copied())
            }));
        let update_values: HashSet<_> = updates.iter().map(|update| update.value).collect();
        for member in members {
            let Some(var) = graph.value(member).map(|value| &value.var) else {
                continue;
            };
            if var.is_const() {
                continue;
            }
            aliases.insert(var.display_name(), name.clone());
        }
        let carrier_width = graph.value(*phi).map_or(0, |value| value.var.size);
        for (merge, width) in exit_merges_for_carrier(prepared, *phi, &update_values) {
            // A merge at the carrier's own width *is* the carrier and takes its
            // name. One at another width is the carrier read at that width,
            // which a name cannot express -- `carrier_member_views` renders
            // those as a cast instead.
            if width == carrier_width {
                aliases.insert(merge, name.clone());
            }
        }
    }
    aliases
}

/// Merges that join a carrier's entry value with its update value.
///
/// A loop with a bypass has a second merge after it, joining "the loop never
/// ran", which carries the entry value, with "the loop ran", which carries the
/// update. That merge is the carrier: materialising places the carrier's
/// initialiser where it dominates both edges, so the variable already holds the
/// right value whichever way control arrived.
///
/// The carrier is a third name rather than either source, so this cannot be
/// found by looking at the merge's sources; the certified entries and updates
/// are what identify it.
fn exit_merges_for_carrier(
    prepared: &r2ssa::SsaArtifact,
    phi: r2ssa::ValueId,
    update_values: &HashSet<r2ssa::ValueId>,
) -> Vec<(String, u32)> {
    let graph = prepared.graph();
    let Some(carrier) = graph.value(phi).map(|value| value.var.clone()) else {
        return Vec::new();
    };
    let mut merges = Vec::new();
    for block in prepared.function().blocks() {
        for merge in &block.phis {
            if merge.dst == carrier {
                continue;
            }
            // A merge at another width over the same place is this carrier read
            // at that width -- adler32 leaves its loop through `ecx` where the
            // carrier is `rcx`. Sound only where a narrow write clears the rest
            // of the register, which is what makes the two one location.
            if merge.dst.size != carrier.size {
                let same_place = match (
                    graph.canonical_storage_for_var(&carrier),
                    graph.canonical_storage_for_var(&merge.dst),
                ) {
                    (Some(carrier_place), Some(merge_place)) => {
                        carrier_place.space == merge_place.space
                            && carrier_place.offset == merge_place.offset
                    }
                    _ => false,
                };
                if !same_place || !prepared.narrow_write_clears_register() {
                    continue;
                }
            }
            let Some(values) = merge
                .sources
                .iter()
                .map(|(_, src)| graph.value_id_for_var(src))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            // Every edge must carry a value this carrier holds, and both sides
            // must be present: a merge of two entry values is a different merge
            // that happens to be over the same storage.
            // The bypass edge carries "the loop never ran", and that is not
            // always the header phi's own entry value: in pearson the merge is
            // `phi(RCX_4 = update, RCX_5)` where `RCX_5` is the value the
            // carrier was initialised with before the loop, a different
            // `ValueId` from the certified entry. Requiring a certified entry
            // there left the exit merge unaliased and pearson returned `rcx_6`,
            // a name nothing declares. The carrier's own dominating
            // initialisers are the same variable by construction, so they
            // count.
            // A phi over this storage that takes one of the carrier's updates
            // on one edge is the carrier leaving the loop, whatever the other
            // edge carries: the bypass value is "the loop never ran", and it is
            // not required to be a value the carrier certified. Requiring that
            // left pearson's exit merge unaliased and its return printed
            // `rcx_6`, a name nothing declares.
            if values.iter().any(|value| update_values.contains(value))
                && values.iter().any(|value| !update_values.contains(value))
            {
                merges.push((merge.dst.display_name(), merge.dst.size));
            }
        }
    }
    merges
}
