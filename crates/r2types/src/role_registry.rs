use std::collections::{BTreeMap, BTreeSet};

use crate::convert::CTypeLike;
use crate::facts::{FunctionParamSpec, FunctionSignatureSpec};
use crate::model::Signedness;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RoleTypeProjection {
    pub ret_type: Option<CTypeLike>,
    pub pointer_param_indices: BTreeSet<usize>,
    pub param_type_hints: BTreeMap<usize, CTypeLike>,
    pub param_name_hints: BTreeMap<usize, String>,
}

fn signed_int_type(bits: u32) -> CTypeLike {
    CTypeLike::Int {
        bits,
        signedness: Signedness::Signed,
    }
}

fn c_int_type() -> CTypeLike {
    typedef_type("int")
}

fn signed_byte_pointer_type() -> CTypeLike {
    CTypeLike::Pointer(Box::new(signed_int_type(8)))
}

fn void_pointer_type() -> CTypeLike {
    CTypeLike::Pointer(Box::new(CTypeLike::Void))
}

fn typedef_type(name: &str) -> CTypeLike {
    CTypeLike::Typedef(name.to_string())
}

fn typedef_pointer_type(name: &str) -> CTypeLike {
    CTypeLike::Pointer(Box::new(typedef_type(name)))
}

fn p(name: &str, ty: CTypeLike) -> FunctionParamSpec {
    FunctionParamSpec {
        name: name.to_string(),
        ty: Some(ty),
    }
}

fn sig(ret_type: CTypeLike, params: Vec<FunctionParamSpec>) -> FunctionSignatureSpec {
    FunctionSignatureSpec {
        ret_type: Some(ret_type),
        params,
    }
}

fn param_only_sig(params: Vec<FunctionParamSpec>) -> FunctionSignatureSpec {
    FunctionSignatureSpec {
        ret_type: None,
        params,
    }
}

fn extend_params_to_count(
    mut params: Vec<FunctionParamSpec>,
    current_param_count: usize,
    fallback_prefix: &str,
    fallback_type: CTypeLike,
) -> Vec<FunctionParamSpec> {
    let fixed_count = params.len();
    let count = current_param_count.max(fixed_count);
    for idx in fixed_count..count {
        params.push(p(
            &format!("{fallback_prefix}{}", idx - fixed_count + 1),
            fallback_type.clone(),
        ));
    }
    params
}

fn diagnostic_signature(current_param_count: usize) -> FunctionSignatureSpec {
    let count = current_param_count.max(2);
    let mut params = Vec::with_capacity(count);
    params.push(p("errnum", typedef_type("errno_t")));
    params.push(p("fmt", signed_byte_pointer_type()));
    for idx in 2..count {
        params.push(p(
            &format!("diag_value{}", idx - 1),
            typedef_type("uintptr_t"),
        ));
    }
    sig(CTypeLike::Void, params)
}

fn format_argument_fetch_signature() -> FunctionSignatureSpec {
    sig(
        c_int_type(),
        vec![
            p("args", typedef_pointer_type("__va_list_tag")),
            p("arguments_out", void_pointer_type()),
        ],
    )
}

fn string_scan_signature(current_param_count: usize) -> FunctionSignatureSpec {
    param_only_sig(extend_params_to_count(
        vec![
            p("string", signed_byte_pointer_type()),
            p("len", typedef_type("size_t")),
            p("flags", c_int_type()),
        ],
        current_param_count,
        "scan_arg",
        typedef_type("uintptr_t"),
    ))
}

fn field_selection_signature(current_param_count: usize) -> FunctionSignatureSpec {
    param_only_sig(extend_params_to_count(
        vec![
            p("record", void_pointer_type()),
            p("key", void_pointer_type()),
            p("offset", typedef_type("size_t")),
        ],
        current_param_count,
        "field_arg",
        typedef_type("uintptr_t"),
    ))
}

fn directory_traversal_signature(current_param_count: usize) -> FunctionSignatureSpec {
    param_only_sig(extend_params_to_count(
        vec![
            p("fts", typedef_pointer_type("FTS")),
            p("entry", typedef_pointer_type("FTSENT")),
            p("parent", typedef_pointer_type("FTSENT")),
        ],
        current_param_count,
        "dir_arg",
        typedef_type("uintptr_t"),
    ))
}

fn record_stream_signature(current_param_count: usize) -> FunctionSignatureSpec {
    param_only_sig(extend_params_to_count(
        vec![
            p("stream", typedef_pointer_type("FILE")),
            p("linebuffer", void_pointer_type()),
        ],
        current_param_count,
        "record_arg",
        typedef_type("uintptr_t"),
    ))
}

fn sort_merge_signature(current_param_count: usize) -> FunctionSignatureSpec {
    param_only_sig(extend_params_to_count(
        vec![
            p("files", void_pointer_type()),
            p("nfiles", typedef_type("size_t")),
            p("output", typedef_pointer_type("FILE")),
        ],
        current_param_count,
        "merge_arg",
        typedef_type("uintptr_t"),
    ))
}

fn memory_transfer_signature(current_param_count: usize) -> FunctionSignatureSpec {
    param_only_sig(extend_params_to_count(
        vec![
            p("dst", signed_byte_pointer_type()),
            p("src", signed_byte_pointer_type()),
            p("len", typedef_type("size_t")),
        ],
        current_param_count,
        "transfer_arg",
        typedef_type("uintptr_t"),
    ))
}

fn file_transfer_signature(current_param_count: usize) -> FunctionSignatureSpec {
    param_only_sig(extend_params_to_count(
        vec![
            p("src_fd", c_int_type()),
            p("dst_fd", c_int_type()),
            p("len", typedef_type("size_t")),
        ],
        current_param_count,
        "file_arg",
        typedef_type("uintptr_t"),
    ))
}

pub fn signature_hint_for_role_identity(
    role: &r2sym::NativeWorkerRoleIdentity,
    current_param_count: usize,
) -> Option<FunctionSignatureSpec> {
    if matches!(role.source, r2sym::NativeWorkerRoleSource::NameHint)
        || !role.evidence.allows_narrowing()
    {
        return None;
    }
    signature_hint_for_summary_kinds(&role.summary_kinds, current_param_count)
}

pub fn type_projection_for_role_identity(
    role: &r2sym::NativeWorkerRoleIdentity,
    current_param_count: usize,
) -> Option<RoleTypeProjection> {
    signature_hint_for_role_identity(role, current_param_count)
        .map(|signature| type_projection_for_signature(&signature))
}

pub fn type_projection_for_signature(signature: &FunctionSignatureSpec) -> RoleTypeProjection {
    let mut projection = RoleTypeProjection {
        ret_type: signature.ret_type.clone(),
        ..RoleTypeProjection::default()
    };
    for (idx, param) in signature.params.iter().enumerate() {
        if !param.name.is_empty() {
            projection.param_name_hints.insert(idx, param.name.clone());
        }
        let Some(ty) = param.ty.clone() else {
            continue;
        };
        if matches!(ty, CTypeLike::Pointer(_)) {
            projection.pointer_param_indices.insert(idx);
        }
        projection.param_type_hints.insert(idx, ty);
    }
    projection
}

pub fn signature_hint_for_summary_kinds(
    worker_kinds: &BTreeSet<r2sym::NativeWorkerSummaryKind>,
    current_param_count: usize,
) -> Option<FunctionSignatureSpec> {
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::DiagnosticWrapper) {
        return Some(diagnostic_signature(current_param_count));
    }
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::FormatArgumentFetch) {
        return Some(format_argument_fetch_signature());
    }
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::DirectoryTraversal) {
        return Some(directory_traversal_signature(current_param_count));
    }
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::FieldSelection) {
        return Some(field_selection_signature(current_param_count));
    }
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::StringScan) {
        return Some(string_scan_signature(current_param_count));
    }
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::RecordStream) {
        return Some(record_stream_signature(current_param_count));
    }
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::SortMerge) {
        return Some(sort_merge_signature(current_param_count));
    }
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::MemoryTransfer) {
        return Some(memory_transfer_signature(current_param_count));
    }
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::FileTransfer) {
        return Some(file_transfer_signature(current_param_count));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn role_identity_signature_requires_non_name_evidence() {
        let name_hint = r2sym::NativeWorkerRoleIdentity {
            role_name: r2sym::NativeWorkerSummaryKind::FormatArgumentFetch
                .canonical_role_name()
                .to_string(),
            source: r2sym::NativeWorkerRoleSource::NameHint,
            linkage: r2ssa::FunctionSemanticLinkage::Unknown,
            confidence: r2sym::SemanticConfidence::Heuristic,
            source_names: vec!["sym.printf_fetchargs".to_string()],
            summary_kinds: BTreeSet::from([r2sym::NativeWorkerSummaryKind::FormatArgumentFetch]),
            evidence: r2sym::SemanticEvidence::heuristic(r2sym::SemanticEvidenceReason::NameHint),
        };
        assert!(signature_hint_for_role_identity(&name_hint, 0).is_none());
        assert!(type_projection_for_role_identity(&name_hint, 0).is_none());

        let structural = r2sym::NativeWorkerRoleIdentity {
            source: r2sym::NativeWorkerRoleSource::Structural,
            confidence: r2sym::SemanticConfidence::Likely,
            evidence: r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::SummaryBudget),
            ..name_hint
        };
        let signature = signature_hint_for_role_identity(&structural, 0)
            .expect("structural role identity should project signature");
        assert_eq!(signature.ret_type, Some(c_int_type()));
        assert!(type_projection_for_role_identity(&structural, 0).is_some());
    }

    #[test]
    fn structural_role_source_names_are_presentation_only() {
        let base = r2sym::NativeWorkerRoleIdentity {
            role_name: r2sym::NativeWorkerSummaryKind::FileTransfer
                .canonical_role_name()
                .to_string(),
            source: r2sym::NativeWorkerRoleSource::Structural,
            linkage: r2ssa::FunctionSemanticLinkage::Internal,
            confidence: r2sym::SemanticConfidence::Likely,
            source_names: Vec::new(),
            summary_kinds: BTreeSet::from([r2sym::NativeWorkerSummaryKind::FileTransfer]),
            evidence: r2sym::SemanticEvidence::likely(r2sym::SemanticEvidenceReason::SummaryBudget),
        };
        let expected_signature = signature_hint_for_role_identity(&base, 3);
        let expected_projection = type_projection_for_role_identity(&base, 3);
        assert!(expected_signature.is_some());
        assert!(expected_projection.is_some());

        for source_names in [
            vec!["xnmalloc".to_string()],
            vec!["malloc".to_string()],
            vec!["table_walk".to_string()],
            vec!["renamed_worker".to_string()],
            Vec::new(),
        ] {
            let role = r2sym::NativeWorkerRoleIdentity {
                source_names,
                ..base.clone()
            };
            assert_eq!(
                signature_hint_for_role_identity(&role, 3),
                expected_signature
            );
            assert_eq!(
                type_projection_for_role_identity(&role, 3),
                expected_projection
            );
        }
    }

    #[test]
    fn registry_projects_summary_only_worker_roles() {
        let diagnostic = BTreeSet::from([r2sym::NativeWorkerSummaryKind::DiagnosticWrapper]);
        let signature = signature_hint_for_summary_kinds(&diagnostic, 4)
            .expect("expected diagnostic signature");
        assert_eq!(signature.params.len(), 4);
        assert_eq!(signature.params[0].name, "errnum");
        assert_eq!(signature.params[3].name, "diag_value2");

        let fetch = BTreeSet::from([r2sym::NativeWorkerSummaryKind::FormatArgumentFetch]);
        let signature =
            signature_hint_for_summary_kinds(&fetch, 0).expect("expected fetchargs signature");
        assert_eq!(signature.ret_type, Some(c_int_type()));
        assert_eq!(signature.params[1].ty, Some(void_pointer_type()));

        let numeric = BTreeSet::from([r2sym::NativeWorkerSummaryKind::NumericTransform]);
        assert!(
            signature_hint_for_summary_kinds(&numeric, 2).is_none(),
            "a generic numeric summary does not prove concrete parameter roles"
        );
    }
}
