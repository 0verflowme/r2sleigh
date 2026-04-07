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
pub struct TargetQueryRoutePlan {
    pub target_plan: TargetQueryPlan,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub branch_guidance: Option<QueryGuidanceMode>,
    pub allow_memory_term_narrowing: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dynamic_target_compile_reason: Option<String>,
    pub allow_dynamic_target_compile: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub vm_target_compile_reason: Option<String>,
    pub allow_vm_target_compile: bool,
}

impl TargetQueryRoutePlan {
    pub fn dynamic_fallback() -> Self {
        Self {
            target_plan: TargetQueryPlan::Fallback {
                reason: "semantic artifact unavailable".to_string(),
            },
            branch_guidance: None,
            allow_memory_term_narrowing: false,
            dynamic_target_compile_reason: Some("semantic artifact unavailable".to_string()),
            allow_dynamic_target_compile: true,
            vm_target_compile_reason: Some("semantic artifact unavailable".to_string()),
            allow_vm_target_compile: true,
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
        matches!(self, Self::NativeStructured | Self::NativeLinear { .. })
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
    has_authoritative_source: bool,
    has_memory_guidance: bool,
) -> TargetQueryRoutePlan {
    match query_plan {
        QueryPlan::Ready => match target_plan {
            TargetQueryPlan::Ready { mode } => TargetQueryRoutePlan {
                target_plan: target_plan.clone(),
                branch_guidance: Some(*mode),
                allow_memory_term_narrowing: has_authoritative_source && has_memory_guidance,
                dynamic_target_compile_reason: None,
                allow_dynamic_target_compile: false,
                vm_target_compile_reason: None,
                allow_vm_target_compile: false,
            },
            TargetQueryPlan::Fallback { .. } => TargetQueryRoutePlan {
                target_plan: target_plan.clone(),
                branch_guidance: None,
                allow_memory_term_narrowing: has_authoritative_source && has_memory_guidance,
                dynamic_target_compile_reason: None,
                allow_dynamic_target_compile: false,
                vm_target_compile_reason: None,
                allow_vm_target_compile: false,
            },
            TargetQueryPlan::Residual { .. } | TargetQueryPlan::Refuse { .. } => {
                TargetQueryRoutePlan {
                    target_plan: target_plan.clone(),
                    branch_guidance: None,
                    allow_memory_term_narrowing: false,
                    dynamic_target_compile_reason: None,
                    allow_dynamic_target_compile: false,
                    vm_target_compile_reason: None,
                    allow_vm_target_compile: false,
                }
            }
        },
        QueryPlan::Fallback { reason } => TargetQueryRoutePlan {
            target_plan: target_plan.clone(),
            branch_guidance: None,
            allow_memory_term_narrowing: false,
            dynamic_target_compile_reason: Some(reason.clone()),
            allow_dynamic_target_compile: true,
            vm_target_compile_reason: Some(reason.clone()),
            allow_vm_target_compile: true,
        },
        QueryPlan::Residual { reasons } => {
            let reason = reasons.join(", ");
            TargetQueryRoutePlan {
                target_plan: target_plan.clone(),
                branch_guidance: None,
                allow_memory_term_narrowing: false,
                dynamic_target_compile_reason: Some(reason.clone()),
                allow_dynamic_target_compile: true,
                vm_target_compile_reason: Some(reason),
                allow_vm_target_compile: true,
            }
        }
        QueryPlan::Refuse { .. } => TargetQueryRoutePlan {
            target_plan: target_plan.clone(),
            branch_guidance: None,
            allow_memory_term_narrowing: false,
            dynamic_target_compile_reason: None,
            allow_dynamic_target_compile: false,
            vm_target_compile_reason: None,
            allow_vm_target_compile: false,
        },
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::{
        DecompilePlan, QueryPlan, TargetQueryPlan, TargetQueryRoutePlan, TypePlan,
        derive_decompile_plan, derive_query_plan, derive_target_query_plan,
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
            ambiguous_targets: Vec::new(),
            cache_hit: false,
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
                supports_guarded_structuring,
            );
            let is_valid = match plan {
                DecompilePlan::NativeStructured
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
        let route = derive_target_query_route_plan(&QueryPlan::Ready, &target_plan, true, true);
        assert!(matches!(
            route.target_plan,
            TargetQueryPlan::Residual { .. }
        ));
        assert!(route.branch_guidance.is_none());
        assert!(!route.allow_memory_term_narrowing);
        assert!(!route.allow_dynamic_target_compile);
        assert!(!route.allow_vm_target_compile);
    }

    #[test]
    fn target_query_route_plan_keeps_ready_paths_artifact_authoritative() {
        let target_plan = derive_target_query_plan(&QueryPlan::Ready, false, false, false);
        let route = derive_target_query_route_plan(&QueryPlan::Ready, &target_plan, false, false);
        assert!(matches!(
            route.target_plan,
            TargetQueryPlan::Fallback { .. }
        ));
        assert!(route.branch_guidance.is_none());
        assert!(!route.allow_memory_term_narrowing);
        assert!(!route.allow_dynamic_target_compile);
        assert!(!route.allow_vm_target_compile);
    }

    #[test]
    fn target_query_route_plan_allows_dynamic_fallback_on_residual_routes() {
        let query_plan = QueryPlan::Residual {
            reasons: vec!["budget".to_string()],
        };
        let target_plan = derive_target_query_plan(&query_plan, false, false, false);
        let route = derive_target_query_route_plan(&query_plan, &target_plan, false, false);
        assert!(route.branch_guidance.is_none());
        assert!(route.dynamic_target_compile_reason.is_some());
        assert!(route.allow_dynamic_target_compile);
        assert!(route.vm_target_compile_reason.is_some());
        assert!(route.allow_vm_target_compile);
    }

    proptest! {
        #[test]
        fn target_query_route_plan_is_total(
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
                has_authoritative_source,
                has_memory_guidance,
            );
            let TargetQueryRoutePlan { .. } = route;
            let valid = true;
            prop_assert!(valid);
            if matches!(target_plan, TargetQueryPlan::Ready { .. }) {
                prop_assert_eq!(
                    route.allow_memory_term_narrowing,
                    has_authoritative_source && has_memory_guidance
                );
            }
            if matches!(target_plan, TargetQueryPlan::Fallback { .. }) && ready {
                prop_assert_eq!(
                    route.allow_memory_term_narrowing,
                    has_authoritative_source && has_memory_guidance
                );
            }
            if ready {
                prop_assert!(!route.allow_dynamic_target_compile);
                prop_assert!(!route.allow_vm_target_compile);
            }
            if matches!(target_plan, TargetQueryPlan::Residual { .. } | TargetQueryPlan::Refuse { .. }) || !ready {
                prop_assert!(route.branch_guidance.is_none());
            }
        }
    }
}
