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
    Ready,
    Fallback { reason: String },
    Residual { reasons: Vec<String> },
    Refuse { reason: String },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum DecompilePlan {
    Ready,
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
    pub allow_dynamic_target_compile: bool,
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
            allow_dynamic_target_compile: true,
            allow_vm_target_compile: true,
        }
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
    if matches!(execution, ExecutionModel::Vm)
        || !diagnostics.skipped_large_cfg
        || has_native_semantics
    {
        TypePlan::Ready
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
) -> DecompilePlan {
    if matches!(execution, ExecutionModel::Native)
        && (!diagnostics.skipped_large_cfg || has_native_semantics)
    {
        DecompilePlan::Ready
    } else if matches!(stage, RefinementStage::Residual)
        && !has_large_cfg_only_residual(diagnostics)
    {
        DecompilePlan::Residual {
            reasons: residual_reason_strings(diagnostics),
        }
    } else if matches!(execution, ExecutionModel::Vm) {
        DecompilePlan::Fallback {
            reason: "vm consumer required".to_string(),
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
                allow_dynamic_target_compile: true,
                allow_vm_target_compile: true,
            },
            TargetQueryPlan::Fallback { .. } => TargetQueryRoutePlan {
                target_plan: target_plan.clone(),
                branch_guidance: None,
                allow_memory_term_narrowing: has_authoritative_source && has_memory_guidance,
                allow_dynamic_target_compile: true,
                allow_vm_target_compile: true,
            },
            TargetQueryPlan::Residual { .. } | TargetQueryPlan::Refuse { .. } => {
                TargetQueryRoutePlan {
                    target_plan: target_plan.clone(),
                    branch_guidance: None,
                    allow_memory_term_narrowing: false,
                    allow_dynamic_target_compile: false,
                    allow_vm_target_compile: false,
                }
            }
        },
        QueryPlan::Fallback { .. } | QueryPlan::Residual { .. } | QueryPlan::Refuse { .. } => {
            TargetQueryRoutePlan {
                target_plan: target_plan.clone(),
                branch_guidance: None,
                allow_memory_term_narrowing: false,
                allow_dynamic_target_compile: false,
                allow_vm_target_compile: false,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::{
        DecompilePlan, QueryPlan, TargetQueryPlan, TargetQueryRoutePlan, derive_decompile_plan,
        derive_query_plan, derive_target_query_plan, derive_target_query_route_plan,
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
        fn decompile_plan_derivation_is_total(
            is_vm in any::<bool>(),
            is_residual in any::<bool>(),
            skipped_large_cfg in any::<bool>(),
            has_native_semantics in any::<bool>(),
        ) {
            let plan = derive_decompile_plan(
                if is_residual { RefinementStage::Residual } else { RefinementStage::Compiled },
                if is_vm { ExecutionModel::Vm } else { ExecutionModel::Native },
                &diagnostics(skipped_large_cfg),
                has_native_semantics,
            );
            let is_valid = match plan {
                DecompilePlan::Ready
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
    fn target_query_route_plan_allows_dynamic_fallback_without_branch_guidance() {
        let target_plan = derive_target_query_plan(&QueryPlan::Ready, false, false, false);
        let route = derive_target_query_route_plan(&QueryPlan::Ready, &target_plan, false, false);
        assert!(matches!(
            route.target_plan,
            TargetQueryPlan::Fallback { .. }
        ));
        assert!(route.branch_guidance.is_none());
        assert!(!route.allow_memory_term_narrowing);
        assert!(route.allow_dynamic_target_compile);
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
            if matches!(target_plan, TargetQueryPlan::Residual { .. } | TargetQueryPlan::Refuse { .. }) || !ready {
                prop_assert!(route.branch_guidance.is_none());
            }
        }
    }
}
