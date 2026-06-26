use serde::{Deserialize, Serialize};

use crate::facts::{
    FunctionSignatureProjection, FunctionTypeFacts, OutParamCertificateEvidence,
    OutParamCertificateSource, SignatureProjectionResult,
};

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnalysisPlans {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact_build: Option<r2sym::ArtifactBuildPlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub query: Option<r2sym::QueryPlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_plan: Option<r2sym::TypePlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub decompile: Option<r2sym::DecompilePlan>,
}

impl AnalysisPlans {
    pub fn from_semantics(semantics: Option<&r2sym::SemanticArtifact>) -> Self {
        let Some(semantics) = semantics else {
            return Self::default();
        };
        Self {
            artifact_build: Some(semantics.build_plan()),
            query: Some(semantics.query_plan()),
            type_plan: Some(semantics.type_plan()),
            decompile: Some(semantics.decompile_plan()),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterprocSummaryView {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub set: Option<r2ssa::InterprocSummarySet>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rollup: Option<SummaryEffectRollup>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub helpers: Vec<SummaryHelperView>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SummaryEffectRollup {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub root_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub root_return_relation: Option<r2ssa::SummaryReturnRelation>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub out_param_facts: Vec<SummaryOutParamFact>,
    #[serde(default)]
    pub pointer_param_indices: Vec<usize>,
    #[serde(default)]
    pub transfer_count: usize,
    #[serde(default)]
    pub allocation_count: usize,
    #[serde(default)]
    pub lifetime_count: usize,
    #[serde(default)]
    pub sync_count: usize,
    #[serde(default)]
    pub atomic_count: usize,
    pub helper_summary_count: usize,
    pub has_unknown_calls: bool,
    pub touches_unknown_memory: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SummaryHelperView {
    pub function_id: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub arg_count_hint: Option<usize>,
    pub return_relation: r2ssa::SummaryReturnRelation,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub out_param_facts: Vec<SummaryOutParamFact>,
    #[serde(default)]
    pub pointer_param_indices: Vec<usize>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub transfer_effects: Vec<r2ssa::SummaryTransferEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub allocation_effects: Vec<r2ssa::SummaryAllocationEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub lifetime_effects: Vec<r2ssa::SummaryLifetimeEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub sync_effects: Vec<r2ssa::SummarySyncEffect>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub atomic_effects: Vec<r2ssa::SummaryAtomicEffect>,
    pub has_unknown_calls: bool,
    pub touches_unknown_memory: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SummaryOutParamFact {
    pub param_index: usize,
    pub evidence: OutParamCertificateEvidence,
    pub source: OutParamCertificateSource,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecompileCapabilityView {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub plan: Option<r2sym::DecompilePlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub slice_class: Option<r2sym::SliceClass>,
    pub skipped_large_cfg: bool,
    pub has_native_regions: bool,
    pub has_summary_islands: bool,
    pub has_primary_summary_islands: bool,
    pub summary_island_count: usize,
    pub primary_summary_island_count: usize,
    pub generic_memory_summary_count: usize,
    pub has_memory_read_write_summary_pair: bool,
    pub actionable_region_count: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub ambiguous_targets: Vec<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub residual_reasons: Vec<r2sym::ResidualReason>,
    pub assumption_conflicted: bool,
    pub summary_conflicted: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DecompileRouteKind {
    Standard,
    StructuredWorker,
    SummaryIslands,
    LinearWorker,
    VmSummary,
    FallbackComment,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecompileRouteFacts {
    pub kind: DecompileRouteKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fallback_comment: Option<String>,
    pub skip_runtime_type_inference: bool,
    pub use_prepared_semantic_view: bool,
    pub proof_coverage: r2sym::ProofCoverage,
    pub render_permission: r2sym::RenderPermission,
}

impl InterprocSummaryView {
    pub fn new(set: Option<r2ssa::InterprocSummarySet>) -> Self {
        let rollup = summary_rollup(set.as_ref());
        let helpers = helper_views(set.as_ref());
        Self {
            set,
            rollup,
            helpers,
        }
    }

    pub fn as_set(&self) -> Option<&r2ssa::InterprocSummarySet> {
        self.set.as_ref()
    }

    pub fn root_summary(&self) -> Option<&r2ssa::FunctionSemanticSummary> {
        let set = self.set.as_ref()?;
        let root = set.root?;
        set.summaries.get(&root)
    }

    pub fn diagnostics(&self) -> Option<&r2ssa::InterprocSummaryDiagnostics> {
        self.set.as_ref().map(|set| &set.diagnostics)
    }

    pub fn helper_summary_for_name(&self, name: &str) -> Option<&r2ssa::FunctionSemanticSummary> {
        let normalized = name.trim().to_ascii_lowercase();
        self.set.as_ref()?.summaries.values().find(|summary| {
            summary
                .name
                .as_deref()
                .is_some_and(|summary_name| summary_name.trim().to_ascii_lowercase() == normalized)
        })
    }

    pub fn helper_view_for_name(&self, name: &str) -> Option<&SummaryHelperView> {
        let normalized = name.trim().to_ascii_lowercase();
        self.helpers.iter().find(|summary| {
            summary
                .name
                .as_deref()
                .is_some_and(|summary_name| summary_name.trim().to_ascii_lowercase() == normalized)
        })
    }

    pub fn out_param_indices(&self) -> Vec<usize> {
        out_param_indices_from_facts(
            self.rollup
                .as_ref()
                .map(|rollup| rollup.out_param_facts.as_slice())
                .unwrap_or(&[]),
        )
    }

    pub fn pointer_param_indices(&self) -> &[usize] {
        self.rollup
            .as_ref()
            .map(|rollup| rollup.pointer_param_indices.as_slice())
            .unwrap_or(&[])
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunctionFacts {
    pub types: FunctionTypeFacts,
    pub semantics: Option<r2sym::SemanticArtifact>,
    pub proof: r2sym::ProofCoverage,
    pub decompile_route: Option<DecompileRouteFacts>,
    pub assumptions: r2ssa::AssumptionSet,
    pub plans: AnalysisPlans,
    pub summary_view: InterprocSummaryView,
    pub diagnostics: Vec<String>,
    pub assumption_usage: r2ssa::AssumptionUsageReport,
}

impl FunctionFacts {
    pub fn new(types: FunctionTypeFacts, semantics: Option<r2sym::SemanticArtifact>) -> Self {
        let plans = AnalysisPlans::from_semantics(semantics.as_ref());
        let proof = semantics
            .as_ref()
            .map(r2sym::SemanticArtifact::semantic_claim_summary)
            .map(|claims| r2sym::ProofCoverage::from_semantic_claims(&claims))
            .unwrap_or_default();
        Self {
            types,
            semantics,
            proof,
            decompile_route: None,
            assumptions: r2ssa::AssumptionSet::default(),
            plans,
            summary_view: InterprocSummaryView::default(),
            diagnostics: Vec::new(),
            assumption_usage: r2ssa::AssumptionUsageReport::default(),
        }
    }

    pub fn with_assumptions(mut self, assumptions: r2ssa::AssumptionSet) -> Self {
        self.assumptions = assumptions;
        self
    }

    pub fn with_summary_set(mut self, set: Option<r2ssa::InterprocSummarySet>) -> Self {
        self.summary_view = InterprocSummaryView::new(set);
        self
    }

    pub fn with_summary_view(mut self, summary_view: InterprocSummaryView) -> Self {
        self.summary_view = summary_view;
        self
    }

    pub fn with_diagnostics<I>(mut self, diagnostics: I) -> Self
    where
        I: IntoIterator<Item = String>,
    {
        self.diagnostics = diagnostics.into_iter().collect();
        self
    }

    pub fn with_assumption_usage(mut self, usage: r2ssa::AssumptionUsageReport) -> Self {
        self.assumption_usage = usage;
        self
    }

    pub fn with_proof_coverage(mut self, proof: r2sym::ProofCoverage) -> Self {
        self.proof = proof;
        self
    }

    pub fn with_decompile_route(mut self, route: DecompileRouteFacts) -> Self {
        self.decompile_route = Some(route);
        self
    }

    pub fn set_decompile_route(&mut self, route: Option<DecompileRouteFacts>) {
        self.decompile_route = route;
    }

    pub fn decompile_route(&self) -> Option<&DecompileRouteFacts> {
        self.decompile_route.as_ref()
    }

    pub fn merge_proof_coverage(&mut self, proof: r2sym::ProofCoverage) {
        self.proof = std::mem::take(&mut self.proof).merge(proof);
    }

    pub fn set_semantics(&mut self, semantics: Option<r2sym::SemanticArtifact>) {
        self.semantics = semantics;
        self.refresh_plans();
        if let Some(semantics) = self.semantics.as_ref() {
            self.merge_proof_coverage(r2sym::ProofCoverage::from_semantic_claims(
                &semantics.semantic_claim_summary(),
            ));
        }
    }

    pub fn refresh_plans(&mut self) {
        self.plans = AnalysisPlans::from_semantics(self.semantics.as_ref());
    }

    pub fn type_plan(&self) -> Option<r2sym::TypePlan> {
        self.plans.type_plan.clone()
    }

    pub fn decompile_plan(&self) -> Option<r2sym::DecompilePlan> {
        self.plans.decompile.clone()
    }

    pub fn query_plan(&self) -> Option<r2sym::QueryPlan> {
        self.plans.query.clone()
    }

    pub fn artifact_build_plan(&self) -> Option<r2sym::ArtifactBuildPlan> {
        self.plans.artifact_build.clone()
    }

    pub fn apply_signature_projection(
        &mut self,
        function_name: &str,
        projection: FunctionSignatureProjection,
        ptr_bits: u32,
    ) -> SignatureProjectionResult {
        self.types
            .apply_signature_projection(function_name, projection, ptr_bits)
    }

    pub fn interproc_summary_set(&self) -> Option<&r2ssa::InterprocSummarySet> {
        self.summary_view.as_set()
    }

    pub fn semantic_artifact(&self) -> Option<&r2sym::SemanticArtifact> {
        self.semantics.as_ref()
    }

    pub fn summary_rollup(&self) -> Option<&SummaryEffectRollup> {
        self.summary_view.rollup.as_ref()
    }

    pub fn has_assumption_conflicts(&self) -> bool {
        !self.assumption_usage.conflicts.is_empty()
    }

    pub fn has_applied_assumptions(&self) -> bool {
        !self.assumption_usage.applied.is_empty()
    }

    pub fn has_summary_conflicts(&self) -> bool {
        self.summary_view
            .diagnostics()
            .is_some_and(|diagnostics| !diagnostics.converged)
    }

    pub fn decompile_capability(&self) -> DecompileCapabilityView {
        let mut capability = DecompileCapabilityView {
            plan: self.decompile_plan(),
            assumption_conflicted: self.has_assumption_conflicts(),
            summary_conflicted: self.has_summary_conflicts(),
            ..DecompileCapabilityView::default()
        };
        let Some(semantics) = self.semantic_artifact() else {
            return capability;
        };
        capability.slice_class = semantics.slice_class();
        capability.skipped_large_cfg = semantics.diagnostics.skipped_large_cfg;
        capability.has_native_regions = semantics
            .native_body()
            .is_some_and(|body| !body.regions.is_empty());
        capability.has_summary_islands = semantics
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_summary_islands);
        capability.has_primary_summary_islands = semantics
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_primary_summary_islands);
        capability.summary_island_count = semantics
            .native_body()
            .map(r2sym::NativeArtifactBody::summary_island_count)
            .unwrap_or(0);
        capability.primary_summary_island_count = semantics
            .native_body()
            .map(r2sym::NativeArtifactBody::primary_summary_island_count)
            .unwrap_or(0);
        capability.generic_memory_summary_count = semantics
            .native_body()
            .map(r2sym::NativeArtifactBody::generic_memory_summary_count)
            .unwrap_or(0);
        capability.has_memory_read_write_summary_pair = semantics
            .native_body()
            .is_some_and(r2sym::NativeArtifactBody::has_memory_read_write_summary_pair);
        capability.actionable_region_count = semantics.actionable_regions().len();
        capability.ambiguous_targets = semantics.ambiguous_targets();
        capability.residual_reasons = semantics.diagnostics.residual_reasons.clone();
        capability
    }
}

fn summary_rollup(set: Option<&r2ssa::InterprocSummarySet>) -> Option<SummaryEffectRollup> {
    let set = set?;
    let root_summary = set.root.and_then(|root| set.summaries.get(&root));
    let out_param_facts = root_summary
        .map(summary_out_param_facts)
        .unwrap_or_default();

    let mut pointer_param_indices = root_summary
        .map(|summary| {
            let mut indices = summary
                .arg_effects
                .iter()
                .filter_map(|(idx, effect)| {
                    (effect.read || effect.write || effect.escape || effect.free).then_some(*idx)
                })
                .collect::<Vec<_>>();
            for effect in &summary.memory_effects {
                if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.location.region {
                    indices.push(index);
                }
            }
            push_structured_summary_pointer_indices(summary, &mut indices);
            indices
        })
        .unwrap_or_default();
    pointer_param_indices.sort_unstable();
    pointer_param_indices.dedup();

    Some(SummaryEffectRollup {
        root_name: root_summary.and_then(|summary| summary.name.clone()),
        root_return_relation: root_summary.map(|summary| summary.return_relation.clone()),
        out_param_facts,
        pointer_param_indices,
        transfer_count: root_summary.map_or(0, |summary| summary.transfer_effects.len()),
        allocation_count: root_summary.map_or(0, |summary| summary.allocation_effects.len()),
        lifetime_count: root_summary.map_or(0, |summary| summary.lifetime_effects.len()),
        sync_count: root_summary.map_or(0, |summary| summary.sync_effects.len()),
        atomic_count: root_summary.map_or(0, |summary| summary.atomic_effects.len()),
        helper_summary_count: set
            .summaries
            .len()
            .saturating_sub(usize::from(set.root.is_some())),
        has_unknown_calls: root_summary.is_some_and(|summary| summary.has_unknown_calls),
        touches_unknown_memory: root_summary.is_some_and(|summary| summary.touches_unknown_memory),
    })
}

fn helper_views(set: Option<&r2ssa::InterprocSummarySet>) -> Vec<SummaryHelperView> {
    let Some(set) = set else {
        return Vec::new();
    };
    let mut helpers = set
        .summaries
        .iter()
        .filter(|(id, _)| Some(**id) != set.root)
        .map(|(id, summary)| {
            let out_param_facts = summary_out_param_facts(summary);

            let mut pointer_param_indices = summary
                .arg_effects
                .iter()
                .filter_map(|(idx, effect)| {
                    (effect.read || effect.write || effect.escape || effect.free).then_some(*idx)
                })
                .collect::<Vec<_>>();
            for effect in &summary.memory_effects {
                if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.location.region {
                    pointer_param_indices.push(index);
                }
            }
            push_structured_summary_pointer_indices(summary, &mut pointer_param_indices);
            pointer_param_indices.sort_unstable();
            pointer_param_indices.dedup();

            SummaryHelperView {
                function_id: id.0,
                name: summary.name.clone(),
                arg_count_hint: summary.arg_count_hint,
                return_relation: summary.return_relation.clone(),
                out_param_facts,
                pointer_param_indices,
                transfer_effects: summary.transfer_effects.clone(),
                allocation_effects: summary.allocation_effects.clone(),
                lifetime_effects: summary.lifetime_effects.clone(),
                sync_effects: summary.sync_effects.clone(),
                atomic_effects: summary.atomic_effects.clone(),
                has_unknown_calls: summary.has_unknown_calls,
                touches_unknown_memory: summary.touches_unknown_memory,
            }
        })
        .collect::<Vec<_>>();
    helpers.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then(left.function_id.cmp(&right.function_id))
    });
    helpers
}

fn summary_out_param_facts(summary: &r2ssa::FunctionSemanticSummary) -> Vec<SummaryOutParamFact> {
    let mut facts = summary
        .arg_effects
        .iter()
        .enumerate()
        .filter(|(_, (_, effect))| effect.write)
        .map(|(effect_index, (idx, _))| SummaryOutParamFact {
            param_index: *idx,
            evidence: OutParamCertificateEvidence::InterprocArgWrite,
            source: OutParamCertificateSource::InterprocSummaryEffect {
                function_id: summary.id.0,
                evidence: OutParamCertificateEvidence::InterprocArgWrite,
                param_index: *idx,
                effect_index,
            },
        })
        .collect::<Vec<_>>();
    for (effect_index, effect) in summary.memory_effects.iter().enumerate() {
        if effect.kind == r2ssa::SummaryMemoryEffectKind::Write
            && let r2ssa::SummaryMemoryRegion::Arg { index } = effect.location.region
        {
            facts.push(SummaryOutParamFact {
                param_index: index,
                evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                source: OutParamCertificateSource::InterprocSummaryEffect {
                    function_id: summary.id.0,
                    evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                    param_index: index,
                    effect_index,
                },
            });
        }
    }
    for (effect_index, effect) in summary.transfer_effects.iter().enumerate() {
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.dst.region {
            facts.push(SummaryOutParamFact {
                param_index: index,
                evidence: OutParamCertificateEvidence::InterprocTransferDst,
                source: OutParamCertificateSource::InterprocSummaryEffect {
                    function_id: summary.id.0,
                    evidence: OutParamCertificateEvidence::InterprocTransferDst,
                    param_index: index,
                    effect_index,
                },
            });
        }
    }
    facts.sort();
    facts.dedup();
    facts
}

fn out_param_indices_from_facts(facts: &[SummaryOutParamFact]) -> Vec<usize> {
    let mut indices = facts
        .iter()
        .map(|fact| fact.param_index)
        .collect::<Vec<_>>();
    indices.sort_unstable();
    indices.dedup();
    indices
}

fn push_structured_summary_pointer_indices(
    summary: &r2ssa::FunctionSemanticSummary,
    indices: &mut Vec<usize>,
) {
    for effect in &summary.transfer_effects {
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.dst.region {
            indices.push(index);
        }
        if let r2ssa::SummaryMemoryRegion::Arg { index } = effect.src.region {
            indices.push(index);
        }
    }
    for effect in &summary.lifetime_effects {
        indices.push(effect.arg);
    }
    for effect in &summary.sync_effects {
        indices.push(effect.arg);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn summary_with_effects(id: r2ssa::InterprocFunctionId) -> r2ssa::FunctionSemanticSummary {
        let mut summary = r2ssa::FunctionSemanticSummary::unknown(id, Some("sym.effect".into()));
        summary.arg_effects.insert(
            0,
            r2ssa::SummaryArgEffect {
                escape: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );
        summary.arg_effects.insert(
            1,
            r2ssa::SummaryArgEffect {
                write: true,
                ..r2ssa::SummaryArgEffect::default()
            },
        );
        summary.memory_effects.push(r2ssa::SummaryMemoryEffect {
            kind: r2ssa::SummaryMemoryEffectKind::Write,
            location: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 2 },
                range: None,
            },
        });
        summary.memory_effects.push(r2ssa::SummaryMemoryEffect {
            kind: r2ssa::SummaryMemoryEffectKind::Escape,
            location: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 5 },
                range: None,
            },
        });
        summary.transfer_effects.push(r2ssa::SummaryTransferEffect {
            dst: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 3 },
                range: None,
            },
            src: r2ssa::SummaryMemoryLocation {
                region: r2ssa::SummaryMemoryRegion::Arg { index: 4 },
                range: None,
            },
            len: r2ssa::SummaryTransferLength::Unknown,
        });
        summary
    }

    #[test]
    fn summary_rollup_out_params_require_writeback_evidence() {
        let root = r2ssa::InterprocFunctionId(0x401000);
        let helper = r2ssa::InterprocFunctionId(0x402000);
        let set = r2ssa::InterprocSummarySet {
            root: Some(root),
            summaries: BTreeMap::from([
                (root, summary_with_effects(root)),
                (helper, summary_with_effects(helper)),
            ]),
            diagnostics: Default::default(),
        };

        let view = InterprocSummaryView::new(Some(set));

        assert_eq!(view.out_param_indices(), vec![1, 2, 3]);
        assert_eq!(
            view.rollup
                .as_ref()
                .expect("rollup")
                .out_param_facts
                .iter()
                .map(|fact| (&fact.evidence, &fact.source))
                .collect::<Vec<_>>(),
            vec![
                (
                    &OutParamCertificateEvidence::InterprocArgWrite,
                    &OutParamCertificateSource::InterprocSummaryEffect {
                        function_id: root.0,
                        evidence: OutParamCertificateEvidence::InterprocArgWrite,
                        param_index: 1,
                        effect_index: 1,
                    },
                ),
                (
                    &OutParamCertificateEvidence::InterprocMemoryWrite,
                    &OutParamCertificateSource::InterprocSummaryEffect {
                        function_id: root.0,
                        evidence: OutParamCertificateEvidence::InterprocMemoryWrite,
                        param_index: 2,
                        effect_index: 0,
                    },
                ),
                (
                    &OutParamCertificateEvidence::InterprocTransferDst,
                    &OutParamCertificateSource::InterprocSummaryEffect {
                        function_id: root.0,
                        evidence: OutParamCertificateEvidence::InterprocTransferDst,
                        param_index: 3,
                        effect_index: 0,
                    },
                ),
            ]
        );
        assert_eq!(view.pointer_param_indices(), &[0, 1, 2, 3, 4, 5]);
        let helper_view = view
            .helper_view_for_name("sym.effect")
            .expect("helper view");
        assert_eq!(
            out_param_indices_from_facts(&helper_view.out_param_facts),
            vec![1, 2, 3]
        );
        assert_eq!(helper_view.pointer_param_indices, vec![0, 1, 2, 3, 4, 5]);
    }
}
