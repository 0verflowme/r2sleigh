use serde::{Deserialize, Serialize};

use super::artifact::ResidualReason;
use super::region::{ExecutionModel, RefinementStage, SemanticArtifactDiagnostics};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ArtifactBuildPlan {
    Ready,
    Fallback { reason: String },
    Residual { reasons: Vec<String> },
    Refuse { reason: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum QueryPlan {
    Ready,
    Fallback { reason: String },
    Residual { reasons: Vec<String> },
    Refuse { reason: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypePlan {
    NativeAugmentation,
    VmSummaryOnly { reason: String },
    Fallback { reason: String },
    Residual { reasons: Vec<String> },
    Refuse { reason: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum DecompilePlan {
    NativeStructured,
    NativeSummaryIslands { reason: String },
    NativeLinear { reason: String },
    VmSummaryOnly { reason: String },
    Fallback { reason: String },
    Residual { reasons: Vec<String> },
    Refuse { reason: String },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum QueryGuidanceMode {
    Necessary,
    NarrowOnly,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TargetQueryPlan {
    Ready { mode: QueryGuidanceMode },
    Fallback { reason: String },
    Residual { reasons: Vec<String> },
    Refuse { reason: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TargetQueryExecutionRoute {
    ContinuationSeeded {
        bridge_target: u64,
        route: Box<TargetQueryExecutionRoute>,
    },
    ArtifactCondition {
        mode: QueryGuidanceMode,
    },
    ArtifactMemoryOnly,
    DynamicTargetCompile {
        reason: String,
        mode: QueryGuidanceMode,
    },
    VmTargetCompile {
        reason: String,
    },
    ResidualOnly {
        reasons: Vec<String>,
    },
    Refuse {
        reason: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TargetQueryRoutePlan {
    pub target_plan: TargetQueryPlan,
    pub execution: TargetQueryExecutionRoute,
}

impl TargetQueryRoutePlan {
    pub fn dynamic_fallback() -> Self {
        Self {
            target_plan: TargetQueryPlan::Fallback {
                reason: "semantic artifact unavailable".to_string(),
            },
            execution: TargetQueryExecutionRoute::DynamicTargetCompile {
                reason: "semantic artifact unavailable".to_string(),
                mode: QueryGuidanceMode::NarrowOnly,
            },
        }
    }
}

impl TypePlan {
    pub fn allows_native_augmentation(&self) -> bool {
        matches!(self, Self::NativeAugmentation)
    }

    pub fn is_vm_summary_only(&self) -> bool {
        matches!(self, Self::VmSummaryOnly { .. })
    }
}

impl DecompilePlan {
    pub fn allows_native_linearization(&self) -> bool {
        matches!(
            self,
            Self::NativeStructured | Self::NativeSummaryIslands { .. } | Self::NativeLinear { .. }
        )
    }

    pub fn allows_native_structuring(&self) -> bool {
        matches!(self, Self::NativeStructured)
    }

    pub fn is_vm_summary_only(&self) -> bool {
        matches!(self, Self::VmSummaryOnly { .. })
    }
}

fn residual_reason_strings(diagnostics: &SemanticArtifactDiagnostics) -> Vec<String> {
    diagnostics
        .residual_reasons
        .iter()
        .map(|reason| format!("{reason:?}"))
        .collect()
}

fn joined_residual_reason(reasons: &[String]) -> String {
    if reasons.is_empty() {
        "residual semantic guidance required".to_string()
    } else {
        reasons.join(", ")
    }
}

fn has_large_cfg_only_residual(diagnostics: &SemanticArtifactDiagnostics) -> bool {
    !diagnostics.residual_reasons.is_empty()
        && diagnostics
            .residual_reasons
            .iter()
            .all(|reason| matches!(reason, ResidualReason::LargeCfg))
}

pub fn derive_artifact_build_plan(
    stage: RefinementStage,
    diagnostics: &SemanticArtifactDiagnostics,
) -> ArtifactBuildPlan {
    if diagnostics.skipped_missing_arch {
        return ArtifactBuildPlan::Refuse {
            reason: "missing architecture".to_string(),
        };
    }
    match stage {
        RefinementStage::Residual => ArtifactBuildPlan::Residual {
            reasons: residual_reason_strings(diagnostics),
        },
        RefinementStage::Raw | RefinementStage::Compiled => ArtifactBuildPlan::Ready,
    }
}

pub fn derive_query_plan(
    stage: RefinementStage,
    execution: ExecutionModel,
    diagnostics: &SemanticArtifactDiagnostics,
    has_query_support: bool,
) -> QueryPlan {
    if matches!(execution, ExecutionModel::Vm) || has_query_support {
        QueryPlan::Ready
    } else if matches!(stage, RefinementStage::Residual) {
        QueryPlan::Residual {
            reasons: residual_reason_strings(diagnostics),
        }
    } else {
        QueryPlan::Refuse {
            reason: "query capability unavailable".to_string(),
        }
    }
}

pub fn derive_type_plan(
    stage: RefinementStage,
    execution: ExecutionModel,
    diagnostics: &SemanticArtifactDiagnostics,
    has_native_semantics: bool,
) -> TypePlan {
    if matches!(execution, ExecutionModel::Vm) {
        TypePlan::VmSummaryOnly {
            reason: "vm artifacts expose summary-only type hints".to_string(),
        }
    } else if !diagnostics.skipped_large_cfg || has_native_semantics {
        TypePlan::NativeAugmentation
    } else if matches!(stage, RefinementStage::Residual) {
        TypePlan::Residual {
            reasons: residual_reason_strings(diagnostics),
        }
    } else {
        TypePlan::Fallback {
            reason: "type capability unavailable".to_string(),
        }
    }
}

pub fn derive_decompile_plan(
    stage: RefinementStage,
    execution: ExecutionModel,
    diagnostics: &SemanticArtifactDiagnostics,
    has_native_semantics: bool,
    has_summary_islands: bool,
    supports_guarded_structuring: bool,
) -> DecompilePlan {
    if matches!(execution, ExecutionModel::Vm) {
        DecompilePlan::VmSummaryOnly {
            reason: "vm artifacts currently support summary rendering only".to_string(),
        }
    } else if matches!(execution, ExecutionModel::Native)
        && has_native_semantics
        && supports_guarded_structuring
    {
        DecompilePlan::NativeStructured
    } else if matches!(execution, ExecutionModel::Native)
        && diagnostics.skipped_large_cfg
        && has_native_semantics
        && has_summary_islands
    {
        DecompilePlan::NativeSummaryIslands {
            reason: "large native worker summarized as typed islands".to_string(),
        }
    } else if matches!(execution, ExecutionModel::Native) && has_native_semantics {
        DecompilePlan::NativeLinear {
            reason: "guarded structuring unavailable".to_string(),
        }
    } else if matches!(stage, RefinementStage::Residual)
        && !has_large_cfg_only_residual(diagnostics)
    {
        DecompilePlan::Residual {
            reasons: residual_reason_strings(diagnostics),
        }
    } else {
        DecompilePlan::Fallback {
            reason: "decompile capability unavailable".to_string(),
        }
    }
}

pub fn derive_target_query_plan(
    query_plan: &QueryPlan,
    has_guidance: bool,
    has_source_conflict: bool,
    necessary_for_target: bool,
) -> TargetQueryPlan {
    match query_plan {
        QueryPlan::Refuse { reason } => TargetQueryPlan::Refuse {
            reason: reason.clone(),
        },
        QueryPlan::Residual { reasons } => TargetQueryPlan::Residual {
            reasons: reasons.clone(),
        },
        QueryPlan::Fallback { reason } => TargetQueryPlan::Fallback {
            reason: reason.clone(),
        },
        QueryPlan::Ready if has_source_conflict => TargetQueryPlan::Residual {
            reasons: vec!["conflicting target guidance sources".to_string()],
        },
        QueryPlan::Ready if has_guidance => TargetQueryPlan::Ready {
            mode: if necessary_for_target {
                QueryGuidanceMode::Necessary
            } else {
                QueryGuidanceMode::NarrowOnly
            },
        },
        QueryPlan::Ready => TargetQueryPlan::Fallback {
            reason: "target guidance unavailable".to_string(),
        },
    }
}

pub fn derive_target_query_route_plan(
    query_plan: &QueryPlan,
    target_plan: &TargetQueryPlan,
    execution: ExecutionModel,
    has_authoritative_source: bool,
    has_memory_guidance: bool,
) -> TargetQueryRoutePlan {
    let execution = match query_plan {
        QueryPlan::Ready => match target_plan {
            TargetQueryPlan::Ready { mode } => match execution {
                ExecutionModel::Vm => TargetQueryExecutionRoute::VmTargetCompile {
                    reason: "vm target compilation selected".to_string(),
                },
                ExecutionModel::Native if has_authoritative_source => {
                    TargetQueryExecutionRoute::ArtifactCondition { mode: *mode }
                }
                ExecutionModel::Native if has_memory_guidance => {
                    TargetQueryExecutionRoute::ArtifactMemoryOnly
                }
                ExecutionModel::Native => TargetQueryExecutionRoute::DynamicTargetCompile {
                    reason: "target guidance unavailable".to_string(),
                    mode: *mode,
                },
            },
            TargetQueryPlan::Fallback { reason } => match execution {
                ExecutionModel::Vm => TargetQueryExecutionRoute::VmTargetCompile {
                    reason: reason.clone(),
                },
                ExecutionModel::Native => TargetQueryExecutionRoute::DynamicTargetCompile {
                    reason: reason.clone(),
                    mode: QueryGuidanceMode::NarrowOnly,
                },
            },
            TargetQueryPlan::Residual { reasons } => TargetQueryExecutionRoute::ResidualOnly {
                reasons: reasons.clone(),
            },
            TargetQueryPlan::Refuse { reason } => TargetQueryExecutionRoute::Refuse {
                reason: reason.clone(),
            },
        },
        QueryPlan::Fallback { reason } => match execution {
            ExecutionModel::Vm => TargetQueryExecutionRoute::VmTargetCompile {
                reason: reason.clone(),
            },
            ExecutionModel::Native => TargetQueryExecutionRoute::DynamicTargetCompile {
                reason: reason.clone(),
                mode: QueryGuidanceMode::NarrowOnly,
            },
        },
        QueryPlan::Residual { reasons } => match execution {
            ExecutionModel::Vm => TargetQueryExecutionRoute::ResidualOnly {
                reasons: reasons.clone(),
            },
            ExecutionModel::Native => TargetQueryExecutionRoute::DynamicTargetCompile {
                reason: joined_residual_reason(reasons),
                mode: QueryGuidanceMode::NarrowOnly,
            },
        },
        QueryPlan::Refuse { reason } => TargetQueryExecutionRoute::Refuse {
            reason: reason.clone(),
        },
    };
    TargetQueryRoutePlan {
        target_plan: target_plan.clone(),
        execution,
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::{
        DecompilePlan, QueryPlan, TargetQueryExecutionRoute, TargetQueryPlan, TargetQueryRoutePlan,
        TypePlan, derive_decompile_plan, derive_query_plan, derive_target_query_plan,
        derive_target_query_route_plan, derive_type_plan,
    };
    use crate::{ExecutionModel, RefinementStage, SemanticArtifactDiagnostics};

    fn diagnostics(skipped_large_cfg: bool) -> SemanticArtifactDiagnostics {
        SemanticArtifactDiagnostics {
            branches_evaluated: 0,
            branches_pruned: 0,
            branches_unknown: 0,
            skipped_missing_arch: false,
            skipped_large_cfg,
            residual_reasons: Vec::new(),
            interpreter: None,
            ambiguous_targets: Vec::new(),
        }
    }

    proptest! {
        #[test]
        fn query_plan_derivation_is_total(
            is_vm in any::<bool>(),
            is_residual in any::<bool>(),
            skipped_large_cfg in any::<bool>(),
            has_query_support in any::<bool>(),
        ) {
            let plan = derive_query_plan(
                if is_residual { RefinementStage::Residual } else { RefinementStage::Compiled },
                if is_vm { ExecutionModel::Vm } else { ExecutionModel::Native },
                &diagnostics(skipped_large_cfg),
                has_query_support,
            );
            let is_valid = match plan {
                QueryPlan::Ready
                | QueryPlan::Fallback { .. }
                | QueryPlan::Residual { .. }
                | QueryPlan::Refuse { .. } => true,
            };
            prop_assert!(is_valid);
        }

        #[test]
        fn type_plan_derivation_is_total(
            is_vm in any::<bool>(),
            is_residual in any::<bool>(),
            skipped_large_cfg in any::<bool>(),
            has_native_semantics in any::<bool>(),
        ) {
            let plan = derive_type_plan(
                if is_residual { RefinementStage::Residual } else { RefinementStage::Compiled },
                if is_vm { ExecutionModel::Vm } else { ExecutionModel::Native },
                &diagnostics(skipped_large_cfg),
                has_native_semantics,
            );
            let is_valid = match plan {
                TypePlan::NativeAugmentation
                | TypePlan::VmSummaryOnly { .. }
                | TypePlan::Fallback { .. }
                | TypePlan::Residual { .. }
                | TypePlan::Refuse { .. } => true,
            };
            prop_assert!(is_valid);
        }

        #[test]
        fn decompile_plan_derivation_is_total(
            is_vm in any::<bool>(),
            is_residual in any::<bool>(),
            skipped_large_cfg in any::<bool>(),
            has_native_semantics in any::<bool>(),
            supports_guarded_structuring in any::<bool>(),
        ) {
            let plan = derive_decompile_plan(
                if is_residual { RefinementStage::Residual } else { RefinementStage::Compiled },
                if is_vm { ExecutionModel::Vm } else { ExecutionModel::Native },
                &diagnostics(skipped_large_cfg),
                has_native_semantics,
                has_native_semantics && skipped_large_cfg,
                supports_guarded_structuring,
            );
            let is_valid = match plan {
                DecompilePlan::NativeStructured
                | DecompilePlan::NativeSummaryIslands { .. }
                | DecompilePlan::NativeLinear { .. }
                | DecompilePlan::VmSummaryOnly { .. }
                | DecompilePlan::Fallback { .. }
                | DecompilePlan::Residual { .. }
                | DecompilePlan::Refuse { .. } => true,
            };
            prop_assert!(is_valid);
        }
    }

    #[test]
    fn target_query_plan_refuses_conflicting_guidance() {
        let plan = derive_target_query_plan(&QueryPlan::Ready, true, true, true);
        assert!(matches!(plan, TargetQueryPlan::Residual { .. }));
    }

    #[test]
    fn target_query_route_plan_blocks_conflicting_guidance() {
        let target_plan = derive_target_query_plan(&QueryPlan::Ready, true, true, true);
        let route = derive_target_query_route_plan(
            &QueryPlan::Ready,
            &target_plan,
            ExecutionModel::Native,
            true,
            true,
        );
        assert!(matches!(
            route.target_plan,
            TargetQueryPlan::Residual { .. }
        ));
        assert!(matches!(
            route.execution,
            TargetQueryExecutionRoute::ResidualOnly { .. }
        ));
    }

    #[test]
    fn target_query_route_plan_keeps_ready_paths_artifact_authoritative() {
        let target_plan = derive_target_query_plan(&QueryPlan::Ready, false, false, false);
        let route = derive_target_query_route_plan(
            &QueryPlan::Ready,
            &target_plan,
            ExecutionModel::Native,
            false,
            false,
        );
        assert!(matches!(
            route.target_plan,
            TargetQueryPlan::Fallback { .. }
        ));
        assert!(matches!(
            route.execution,
            TargetQueryExecutionRoute::DynamicTargetCompile { .. }
        ));
    }

    #[test]
    fn target_query_route_plan_allows_dynamic_fallback_on_residual_routes() {
        let query_plan = QueryPlan::Residual {
            reasons: vec!["budget".to_string()],
        };
        let target_plan = derive_target_query_plan(&query_plan, false, false, false);
        let route = derive_target_query_route_plan(
            &query_plan,
            &target_plan,
            ExecutionModel::Native,
            false,
            false,
        );
        assert!(matches!(
            route.execution,
            TargetQueryExecutionRoute::DynamicTargetCompile { .. }
        ));
    }

    proptest! {
        #[test]
        fn target_query_route_plan_is_total(
            is_vm in any::<bool>(),
            ready in any::<bool>(),
            conflict in any::<bool>(),
            has_guidance in any::<bool>(),
            necessary in any::<bool>(),
            has_authoritative_source in any::<bool>(),
            has_memory_guidance in any::<bool>(),
        ) {
            let query_plan = if ready {
                QueryPlan::Ready
            } else {
                QueryPlan::Residual { reasons: vec!["budget".to_string()] }
            };
            let target_plan = derive_target_query_plan(&query_plan, has_guidance, conflict, necessary);
            let route = derive_target_query_route_plan(
                &query_plan,
                &target_plan,
                if is_vm {
                    ExecutionModel::Vm
                } else {
                    ExecutionModel::Native
                },
                has_authoritative_source,
                has_memory_guidance,
            );
            let TargetQueryRoutePlan { .. } = route;
            match route.execution {
                TargetQueryExecutionRoute::ContinuationSeeded { .. }
                | TargetQueryExecutionRoute::ArtifactCondition { .. }
                | TargetQueryExecutionRoute::ArtifactMemoryOnly
                | TargetQueryExecutionRoute::DynamicTargetCompile { .. }
                | TargetQueryExecutionRoute::VmTargetCompile { .. }
                | TargetQueryExecutionRoute::ResidualOnly { .. }
                | TargetQueryExecutionRoute::Refuse { .. } => {}
            }
        }
    }
}
