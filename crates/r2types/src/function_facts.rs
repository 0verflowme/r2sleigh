use serde::{Deserialize, Serialize};

use crate::facts::FunctionTypeFacts;

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
    #[serde(default)]
    pub out_param_indices: Vec<usize>,
    #[serde(default)]
    pub pointer_param_indices: Vec<usize>,
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
    #[serde(default)]
    pub out_param_indices: Vec<usize>,
    #[serde(default)]
    pub pointer_param_indices: Vec<usize>,
    pub has_unknown_calls: bool,
    pub touches_unknown_memory: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecompileCapabilityView {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub plan: Option<r2sym::DecompilePlan>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub slice_class: Option<r2sym::SliceClass>,
    pub skipped_large_cfg: bool,
    pub has_native_regions: bool,
    pub actionable_region_count: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub ambiguous_targets: Vec<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub residual_reasons: Vec<r2sym::ResidualReason>,
    pub assumption_conflicted: bool,
    pub summary_conflicted: bool,
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

    pub fn out_param_indices(&self) -> &[usize] {
        self.rollup
            .as_ref()
            .map(|rollup| rollup.out_param_indices.as_slice())
            .unwrap_or(&[])
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
    pub assumptions: r2ssa::AssumptionSet,
    pub plans: AnalysisPlans,
    pub summary_view: InterprocSummaryView,
    pub diagnostics: Vec<String>,
    pub assumption_usage: r2ssa::AssumptionUsageReport,
}

impl FunctionFacts {
    pub fn new(types: FunctionTypeFacts, semantics: Option<r2sym::SemanticArtifact>) -> Self {
        let plans = AnalysisPlans::from_semantics(semantics.as_ref());
        Self {
            types,
            semantics,
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

    pub fn set_semantics(&mut self, semantics: Option<r2sym::SemanticArtifact>) {
        self.semantics = semantics;
        self.refresh_plans();
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
        capability.actionable_region_count = semantics.actionable_regions().len();
        capability.ambiguous_targets = semantics.ambiguous_targets();
        capability.residual_reasons = semantics.diagnostics.residual_reasons.clone();
        capability
    }
}

fn summary_rollup(set: Option<&r2ssa::InterprocSummarySet>) -> Option<SummaryEffectRollup> {
    let set = set?;
    let root_summary = set.root.and_then(|root| set.summaries.get(&root));
    let mut out_param_indices = root_summary
        .map(|summary| {
            summary
                .arg_effects
                .iter()
                .filter_map(|(idx, effect)| (effect.write || effect.escape).then_some(*idx))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    out_param_indices.sort_unstable();
    out_param_indices.dedup();

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
            indices
        })
        .unwrap_or_default();
    pointer_param_indices.sort_unstable();
    pointer_param_indices.dedup();

    Some(SummaryEffectRollup {
        root_name: root_summary.and_then(|summary| summary.name.clone()),
        root_return_relation: root_summary.map(|summary| summary.return_relation.clone()),
        out_param_indices,
        pointer_param_indices,
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
            let mut out_param_indices = summary
                .arg_effects
                .iter()
                .filter_map(|(idx, effect)| (effect.write || effect.escape).then_some(*idx))
                .collect::<Vec<_>>();
            out_param_indices.sort_unstable();
            out_param_indices.dedup();

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
            pointer_param_indices.sort_unstable();
            pointer_param_indices.dedup();

            SummaryHelperView {
                function_id: id.0,
                name: summary.name.clone(),
                arg_count_hint: summary.arg_count_hint,
                return_relation: summary.return_relation.clone(),
                out_param_indices,
                pointer_param_indices,
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
