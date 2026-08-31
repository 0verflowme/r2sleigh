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
        typedef_type("printf_status_t"),
        vec![
            p("args", typedef_pointer_type("__va_list_tag")),
            p("arguments_out", typedef_pointer_type("arguments")),
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
            p("line", typedef_pointer_type("line")),
            p("key", typedef_pointer_type("keyfield")),
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
            p("linebuffer", typedef_pointer_type("linebuffer")),
        ],
        current_param_count,
        "record_arg",
        typedef_type("uintptr_t"),
    ))
}

fn sort_merge_signature(current_param_count: usize) -> FunctionSignatureSpec {
    param_only_sig(extend_params_to_count(
        vec![
            p("files", typedef_pointer_type("sortfile")),
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

pub fn semantic_typedef_is_authoritative(name: &str) -> bool {
    matches!(
        name.trim().to_ascii_lowercase().as_str(),
        "_bool"
            | "__va_list_tag"
            | "_getopt_data"
            | "aclinfo"
            | "allocation_ptr"
            | "argmatch_value"
            | "arguments"
            | "backup_type"
            | "base32_decode_context"
            | "base64_decode_context"
            | "base_encode_context"
            | "bin_tree_t"
            | "bitset_word_t"
            | "blake2b_state"
            | "calendar_date"
            | "char32_t"
            | "count_t"
            | "copy_debug"
            | "cp_options"
            | "crc32_t"
            | "cycle_check_state"
            | "dir_attr"
            | "dir_list"
            | "dir"
            | "double"
            | "errno_t"
            | "fadvice_t"
            | "fcntl_arg"
            | "file"
            | "fileinfo"
            | "filetype"
            | "float"
            | "fsword"
            | "fs_usage"
            | "fstatus"
            | "fts"
            | "ftsent"
            | "fts_compar_fn"
            | "gid_t"
            | "hash_table"
            | "idx_t"
            | "int"
            | "intmax_t"
            | "ino_t"
            | "keyfield"
            | "line"
            | "linebuffer"
            | "long"
            | "long double"
            | "mcel_t"
            | "mbbuf_t"
            | "mbstate_t"
            | "memory_ptr"
            | "mbfield_parser"
            | "md5_ctx"
            | "merge_node"
            | "merge_node_queue"
            | "mode_t"
            | "mp_limb_t"
            | "mp_size_t"
            | "mkdir_ancestor_fn"
            | "mkdir_announce_fn"
            | "nproc_query"
            | "obstack"
            | "off_t"
            | "option"
            | "parser_control"
            | "pid_t"
            | "ptrdiff_t"
            | "printf_directive"
            | "printf_status_t"
            | "re_dfa_t"
            | "re_dfastate_t"
            | "re_match_context_t"
            | "re_node_set"
            | "re_pattern_buffer"
            | "re_registers"
            | "re_charset_t"
            | "re_string_t"
            | "re_token_t"
            | "reg_errcode_t"
            | "regex_t"
            | "regmatch_t"
            | "reg_syntax_t"
            | "quoting_options"
            | "quoting_style"
            | "randint_source"
            | "randread_source"
            | "retval_t"
            | "rm_status"
            | "rm_options"
            | "savedir_option"
            | "sbyte_count_t"
            | "selabel_handle"
            | "sha256_ctx"
            | "sha512_ctx"
            | "short"
            | "size_t"
            | "sm3_ctx"
            | "sortfile"
            | "speed_t"
            | "state_array_t"
            | "stat"
            | "stat_print_data_ref"
            | "stat_print_data"
            | "stat_print_fn"
            | "strtol_error"
            | "struct_utmp"
            | "ssize_t"
            | "tempname_args"
            | "tempname_tryfunc"
            | "time_t"
            | "timespec"
            | "tm"
            | "timezone_t"
            | "token_buffer"
            | "tokens"
            | "uid_t"
            | "utmp_alloc"
            | "utmp_session"
            | "unicode_callback_context"
            | "unicode_failure_callback"
            | "unicode_success_callback"
            | "unsigned int"
            | "unsigned long"
            | "unsigned short"
            | "uintmax_t"
            | "uintptr_t"
            | "value"
            | "va_list"
            | "wchar_t"
            | "wc_lines"
            | "wint_transform"
            | "xtime_t"
    )
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
        assert_eq!(signature.ret_type, Some(typedef_type("printf_status_t")));
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
        assert_eq!(signature.ret_type, Some(typedef_type("printf_status_t")));
        assert_eq!(
            signature.params[1].ty,
            Some(typedef_pointer_type("arguments"))
        );

        let numeric = BTreeSet::from([r2sym::NativeWorkerSummaryKind::NumericTransform]);
        assert!(
            signature_hint_for_summary_kinds(&numeric, 2).is_none(),
            "a generic numeric summary does not prove concrete parameter roles"
        );
    }

    #[test]
    fn registry_owns_authoritative_typedef_policy() {
        assert!(semantic_typedef_is_authoritative("allocation_ptr"));
        assert!(semantic_typedef_is_authoritative("argmatch_value"));
        assert!(semantic_typedef_is_authoritative("bin_tree_t"));
        assert!(semantic_typedef_is_authoritative("bitset_word_t"));
        assert!(semantic_typedef_is_authoritative("calendar_date"));
        assert!(semantic_typedef_is_authoritative("blake2b_state"));
        assert!(semantic_typedef_is_authoritative("cycle_check_state"));
        assert!(semantic_typedef_is_authoritative("DIR"));
        assert!(semantic_typedef_is_authoritative("FTS"));
        assert!(semantic_typedef_is_authoritative("_Bool"));
        assert!(semantic_typedef_is_authoritative("fcntl_arg"));
        assert!(semantic_typedef_is_authoritative("gid_t"));
        assert!(semantic_typedef_is_authoritative("long"));
        assert!(semantic_typedef_is_authoritative("memory_ptr"));
        assert!(semantic_typedef_is_authoritative("mode_t"));
        assert!(semantic_typedef_is_authoritative("mkdir_ancestor_fn"));
        assert!(semantic_typedef_is_authoritative("mkdir_announce_fn"));
        assert!(semantic_typedef_is_authoritative("md5_ctx"));
        assert!(semantic_typedef_is_authoritative("mp_limb_t"));
        assert!(semantic_typedef_is_authoritative("parser_control"));
        assert!(semantic_typedef_is_authoritative("ptrdiff_t"));
        assert!(semantic_typedef_is_authoritative("re_dfa_t"));
        assert!(semantic_typedef_is_authoritative("re_dfastate_t"));
        assert!(semantic_typedef_is_authoritative("re_match_context_t"));
        assert!(semantic_typedef_is_authoritative("re_node_set"));
        assert!(semantic_typedef_is_authoritative("re_pattern_buffer"));
        assert!(semantic_typedef_is_authoritative("re_registers"));
        assert!(semantic_typedef_is_authoritative("re_charset_t"));
        assert!(semantic_typedef_is_authoritative("reg_errcode_t"));
        assert!(semantic_typedef_is_authoritative("regex_t"));
        assert!(semantic_typedef_is_authoritative("regmatch_t"));
        assert!(semantic_typedef_is_authoritative("re_string_t"));
        assert!(semantic_typedef_is_authoritative("re_token_t"));
        assert!(semantic_typedef_is_authoritative("reg_syntax_t"));
        assert!(semantic_typedef_is_authoritative("state_array_t"));
        assert!(semantic_typedef_is_authoritative("stat_print_data_ref"));
        assert!(semantic_typedef_is_authoritative("stat_print_fn"));
        assert!(semantic_typedef_is_authoritative("wchar_t"));
        assert!(semantic_typedef_is_authoritative("wint_transform"));
        assert!(semantic_typedef_is_authoritative("quoting_options"));
        assert!(semantic_typedef_is_authoritative("selabel_handle"));
        assert!(semantic_typedef_is_authoritative("printf_directive"));
        assert!(semantic_typedef_is_authoritative("hash_table"));
        assert!(semantic_typedef_is_authoritative("fsword"));
        assert!(semantic_typedef_is_authoritative("mcel_t"));
        assert!(semantic_typedef_is_authoritative("nproc_query"));
        assert!(semantic_typedef_is_authoritative("randread_source"));
        assert!(semantic_typedef_is_authoritative("sha256_ctx"));
        assert!(semantic_typedef_is_authoritative("sha512_ctx"));
        assert!(semantic_typedef_is_authoritative("sm3_ctx"));
        assert!(semantic_typedef_is_authoritative("speed_t"));
        assert!(semantic_typedef_is_authoritative("timezone_t"));
        assert!(semantic_typedef_is_authoritative("uid_t"));
        assert!(semantic_typedef_is_authoritative("utmp_alloc"));
        assert!(semantic_typedef_is_authoritative("utmp_session"));
        assert!(semantic_typedef_is_authoritative(
            "unicode_success_callback"
        ));
        assert!(semantic_typedef_is_authoritative("wc_lines"));
        assert!(semantic_typedef_is_authoritative("unsigned int"));
        assert!(semantic_typedef_is_authoritative("unsigned long"));
        assert!(semantic_typedef_is_authoritative("unsigned short"));
        assert!(semantic_typedef_is_authoritative("xtime_t"));
        assert!(semantic_typedef_is_authoritative("tempname_args"));
        assert!(semantic_typedef_is_authoritative("tempname_tryfunc"));
        assert!(semantic_typedef_is_authoritative("timespec"));
        assert!(semantic_typedef_is_authoritative("va_list"));
        assert!(!semantic_typedef_is_authoritative("sla_struct_deadbeef"));
    }
}
