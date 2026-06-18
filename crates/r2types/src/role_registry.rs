use std::collections::{BTreeMap, BTreeSet};

use crate::convert::CTypeLike;
use crate::facts::{FunctionParamSpec, FunctionSignatureSpec};
use crate::model::Signedness;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RoleTypeProjection {
    pub ret_type: Option<CTypeLike>,
    pub pointer_param_indices: BTreeSet<usize>,
    pub out_param_indices: BTreeSet<usize>,
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

fn c_uint_type() -> CTypeLike {
    typedef_type("unsigned int")
}

fn c_ulong_type() -> CTypeLike {
    typedef_type("unsigned long")
}

fn signed_byte_pointer_type() -> CTypeLike {
    CTypeLike::Pointer(Box::new(signed_int_type(8)))
}

fn unsigned_byte_pointer_type() -> CTypeLike {
    CTypeLike::Pointer(Box::new(CTypeLike::Int {
        bits: 8,
        signedness: Signedness::Unsigned,
    }))
}

fn signed_byte_pointer_pointer_type() -> CTypeLike {
    CTypeLike::Pointer(Box::new(signed_byte_pointer_type()))
}

fn typedef_type(name: &str) -> CTypeLike {
    CTypeLike::Typedef(name.to_string())
}

fn typedef_pointer_type(name: &str) -> CTypeLike {
    CTypeLike::Pointer(Box::new(typedef_type(name)))
}

fn struct_pointer_type(name: &str) -> CTypeLike {
    CTypeLike::Pointer(Box::new(CTypeLike::Struct(name.to_string())))
}

fn void_pointer_type() -> CTypeLike {
    CTypeLike::Pointer(Box::new(CTypeLike::Void))
}

fn allocation_ptr_type() -> CTypeLike {
    typedef_type("allocation_ptr")
}

fn memory_ptr_type() -> CTypeLike {
    typedef_type("memory_ptr")
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

fn numeric_transform_signature(current_param_count: usize) -> FunctionSignatureSpec {
    param_only_sig(extend_params_to_count(
        vec![
            p("result", void_pointer_type()),
            p("input", typedef_type("intmax_t")),
        ],
        current_param_count,
        "numeric_arg",
        typedef_type("intmax_t"),
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

fn version_etc_signature(current_param_count: usize) -> FunctionSignatureSpec {
    let count = current_param_count.max(5);
    let mut params = vec![
        p("stream", typedef_pointer_type("FILE")),
        p("command_name", signed_byte_pointer_type()),
        p("package", signed_byte_pointer_type()),
        p("version", signed_byte_pointer_type()),
    ];
    for idx in 4..count {
        params.push(p(&format!("author{}", idx - 3), signed_byte_pointer_type()));
    }
    sig(CTypeLike::Void, params)
}

fn format_output_signature(current_param_count: usize) -> FunctionSignatureSpec {
    sig(
        CTypeLike::Void,
        extend_params_to_count(
            vec![
                p("program", signed_byte_pointer_type()),
                p("message", signed_byte_pointer_type()),
            ],
            current_param_count,
            "format_arg",
            typedef_type("uintptr_t"),
        ),
    )
}

fn openat_safer_signature(current_param_count: usize) -> FunctionSignatureSpec {
    sig(
        c_int_type(),
        extend_params_to_count(
            vec![
                p("fd", c_int_type()),
                p("file", signed_byte_pointer_type()),
                p("flags", c_int_type()),
            ],
            current_param_count,
            "mode_arg",
            typedef_type("mode_t"),
        ),
    )
}

fn error_signature(current_param_count: usize) -> FunctionSignatureSpec {
    let count = current_param_count.max(3);
    let mut params = vec![
        p("status", c_int_type()),
        p("errnum", c_int_type()),
        p("message", signed_byte_pointer_type()),
    ];
    for idx in 3..count {
        params.push(p(
            &format!("diag_value{}", idx - 2),
            typedef_type("uintptr_t"),
        ));
    }
    sig(CTypeLike::Void, params)
}

fn error_at_line_signature(current_param_count: usize) -> FunctionSignatureSpec {
    let count = current_param_count.max(5);
    let mut params = vec![
        p("status", c_int_type()),
        p("errnum", c_int_type()),
        p("file_name", signed_byte_pointer_type()),
        p("line_number", c_uint_type()),
        p("message", signed_byte_pointer_type()),
    ];
    for idx in 5..count {
        params.push(p(
            &format!("diag_value{}", idx - 4),
            typedef_type("uintptr_t"),
        ));
    }
    sig(CTypeLike::Void, params)
}

fn verror_signature(current_param_count: usize) -> FunctionSignatureSpec {
    let count = current_param_count.max(4);
    let mut params = vec![
        p("status", c_int_type()),
        p("errnum", c_int_type()),
        p("message", signed_byte_pointer_type()),
        p("args", typedef_pointer_type("__va_list_tag")),
    ];
    for idx in 4..count {
        params.push(p(
            &format!("diag_value{}", idx - 3),
            typedef_type("uintptr_t"),
        ));
    }
    sig(CTypeLike::Void, params)
}

fn long_options_signature(current_param_count: usize, scan_all: bool) -> FunctionSignatureSpec {
    let mut params = vec![
        p("argc", c_int_type()),
        p("argv", signed_byte_pointer_pointer_type()),
        p("command_name", signed_byte_pointer_type()),
        p("package", signed_byte_pointer_type()),
        p("version", signed_byte_pointer_type()),
    ];
    if scan_all {
        params.push(p("scan_all", CTypeLike::Bool));
    }
    params.push(p("usage_func", CTypeLike::Function));
    let fixed_count = params.len();
    let count = current_param_count.max(fixed_count + 1);
    for idx in fixed_count..count {
        params.push(p(
            &format!("author{}", idx - fixed_count + 1),
            signed_byte_pointer_type(),
        ));
    }
    sig(CTypeLike::Void, params)
}

pub fn normalize_role_name(name: &str) -> String {
    name.trim()
        .trim_start_matches("sym.")
        .trim_start_matches("dbg.")
        .trim_start_matches("fcn.")
        .trim_start_matches("sub.")
        .to_ascii_lowercase()
}

fn is_fileinfo_sort_comparator_role(name: &str) -> bool {
    name.starts_with("xstrcoll_df_")
        || name.starts_with("rev_xstrcoll_df_")
        || name.starts_with("strcmp_df_")
        || name.starts_with("rev_strcmp_df_")
}

pub(crate) fn signature_hint_for_name_candidates<'a>(
    candidates: impl IntoIterator<Item = &'a str>,
    current_param_count: usize,
) -> Option<FunctionSignatureSpec> {
    for candidate in candidates {
        if let Some(signature) =
            signature_hint_for_role_name(&normalize_role_name(candidate), current_param_count)
        {
            return Some(signature);
        }
    }
    None
}

#[cfg(test)]
pub(crate) fn type_projection_for_name_candidates<'a>(
    candidates: impl IntoIterator<Item = &'a str>,
    current_param_count: usize,
) -> Option<RoleTypeProjection> {
    signature_hint_for_name_candidates(candidates, current_param_count)
        .map(|signature| type_projection_for_signature(&signature))
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
    signature_hint_for_name_candidates(
        std::iter::once(role.role_name.as_str())
            .chain(role.source_names.iter().map(String::as_str)),
        current_param_count,
    )
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
            if role_param_name_is_out_param(&param.name) {
                projection.out_param_indices.insert(idx);
            }
        }
        projection.param_type_hints.insert(idx, ty);
    }
    projection
}

fn role_param_name_is_out_param(name: &str) -> bool {
    let normalized = name.trim().to_ascii_lowercase();
    normalized.ends_with("_out")
        || matches!(
            normalized.as_str(),
            "base_in_result"
                | "block_size"
                | "bytes"
                | "copy_into_self"
                | "count_out"
                | "dir_status"
                | "endptr"
                | "have_pending_line"
                | "hole_size"
                | "invalid"
                | "lengthp"
                | "limited"
                | "longind"
                | "longindex"
                | "matched_ent"
                | "n"
                | "n_bytes"
                | "new_dst"
                | "period"
                | "pfps"
                | "pid"
                | "pipefds"
                | "pwc"
                | "quota"
                | "rename_succeeded"
                | "result"
                | "resultbuf"
                | "size"
                | "tokens_out"
                | "total_out"
                | "available_out"
                | "val"
        )
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
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::NumericTransform) {
        return Some(numeric_transform_signature(current_param_count));
    }
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::MemoryTransfer) {
        return Some(memory_transfer_signature(current_param_count));
    }
    if worker_kinds.contains(&r2sym::NativeWorkerSummaryKind::FileTransfer) {
        return Some(file_transfer_signature(current_param_count));
    }
    None
}

pub(crate) fn signature_hint_for_role_name(
    role_name: &str,
    current_param_count: usize,
) -> Option<FunctionSignatureSpec> {
    Some(match role_name {
        "main" | "wmain" => sig(
            c_int_type(),
            vec![
                p("argc", c_int_type()),
                p("argv", signed_byte_pointer_pointer_type()),
                p("envp", signed_byte_pointer_pointer_type()),
            ],
        ),
        "entry.init0" | "entry0" | "_start" => sig(CTypeLike::Void, Vec::new()),
        "entry.fini0"
        | "__do_global_dtors_aux"
        | "register_tm_clones"
        | "deregister_tm_clones"
        | "_init" => sig(CTypeLike::Void, Vec::new()),
        "diagnose" => diagnostic_signature(current_param_count),
        "usage" => sig(CTypeLike::Void, vec![p("status", c_int_type())]),
        "printf_fetchargs" => format_argument_fetch_signature(),
        "oprintf_" | "oprintf_.constprop.0" => format_output_signature(current_param_count),
        "_internal_fnwmatch" | "internal_fnwmatch" => sig(
            c_int_type(),
            vec![
                p("pattern", typedef_pointer_type("wchar_t")),
                p("string", typedef_pointer_type("wchar_t")),
                p("string_end", typedef_pointer_type("wchar_t")),
                p("no_leading_period", CTypeLike::Bool),
                p("flags", c_int_type()),
                p("ends", void_pointer_type()),
                p("alloca_used", typedef_type("size_t")),
            ],
        ),
        "fnmatch" | "rpl_fnmatch" => sig(
            c_int_type(),
            vec![
                p("pattern", signed_byte_pointer_type()),
                p("string", signed_byte_pointer_type()),
                p("flags", c_int_type()),
            ],
        ),
        "canonicalize_filename_mode" => sig(
            signed_byte_pointer_type(),
            vec![
                p("name", signed_byte_pointer_type()),
                p("can_mode", typedef_type("canonicalize_mode_t")),
            ],
        ),
        "file_prefixlen" => sig(
            typedef_type("idx_t"),
            vec![
                p("s", signed_byte_pointer_type()),
                p("len", typedef_pointer_type("ptrdiff_t")),
            ],
        ),
        "getmonth" => sig(
            c_int_type(),
            vec![
                p("month", signed_byte_pointer_type()),
                p("ea", signed_byte_pointer_pointer_type()),
            ],
        ),
        "operand_matches" => sig(
            CTypeLike::Bool,
            vec![
                p("str", signed_byte_pointer_type()),
                p("pattern", signed_byte_pointer_type()),
                p("delim", signed_int_type(8)),
            ],
        ),
        "xstrxfrm" => sig(
            typedef_type("size_t"),
            vec![
                p("dest", signed_byte_pointer_type()),
                p("src", signed_byte_pointer_type()),
                p("destsize", typedef_type("size_t")),
            ],
        ),
        "set_file_security_ctx" => sig(
            CTypeLike::Bool,
            vec![
                p("dst_name", signed_byte_pointer_type()),
                p("recurse", CTypeLike::Bool),
                p("x", typedef_pointer_type("cp_options")),
            ],
        ),
        "localtime_rz" => sig(
            struct_pointer_type("tm"),
            vec![
                p("tz", typedef_type("timezone_t")),
                p("t", typedef_pointer_type("time_t")),
                p("tm", struct_pointer_type("tm")),
            ],
        ),
        "locale_charset" => sig(signed_byte_pointer_type(), Vec::new()),
        "current_timespec" => sig(CTypeLike::Struct("timespec".to_string()), Vec::new()),
        "parse_datetime_body" => sig(
            CTypeLike::Bool,
            vec![
                p("result", struct_pointer_type("timespec")),
                p("input", signed_byte_pointer_type()),
                p("now", struct_pointer_type("timespec")),
                p("flags", c_uint_type()),
                p("tzdefault", typedef_type("timezone_t")),
                p("tzstring", signed_byte_pointer_type()),
            ],
        ),
        "posixtime" => sig(
            CTypeLike::Bool,
            vec![
                p("p", typedef_pointer_type("time_t")),
                p("s", signed_byte_pointer_type()),
                p("syntax_bits", c_uint_type()),
            ],
        ),
        "rpl_obstack_memory_used" => sig(
            typedef_type("size_t"),
            vec![p("h", struct_pointer_type("obstack"))],
        ),
        "alloc_ibuf" | "alloc_obuf" => sig(CTypeLike::Void, Vec::new()),
        "save_token" => sig(CTypeLike::Void, vec![p("t", struct_pointer_type("Tokens"))]),
        "filename_unescape" => sig(
            signed_byte_pointer_type(),
            vec![
                p("s", signed_byte_pointer_type()),
                p("s_len", typedef_type("idx_t")),
            ],
        ),
        "compare" => sig(
            c_int_type(),
            vec![
                p("a", struct_pointer_type("line")),
                p("b", struct_pointer_type("line")),
            ],
        ),
        "memcoll" | "xmemcoll" => sig(
            c_int_type(),
            vec![
                p("s1", signed_byte_pointer_type()),
                p("s1len", typedef_type("size_t")),
                p("s2", signed_byte_pointer_type()),
                p("s2len", typedef_type("size_t")),
            ],
        ),
        "strcoll_loop" => sig(
            c_int_type(),
            vec![
                p("s1", signed_byte_pointer_type()),
                p("s1size", typedef_type("size_t")),
                p("s2", signed_byte_pointer_type()),
                p("s2size", typedef_type("size_t")),
            ],
        ),
        "print_stats" | "maybe_close_stdout" => sig(CTypeLike::Void, Vec::new()),
        "create_hard_link" => sig(
            CTypeLike::Bool,
            vec![
                p("src_name", signed_byte_pointer_type()),
                p("src_dirfd", c_int_type()),
                p("src_relname", signed_byte_pointer_type()),
                p("dst_name", signed_byte_pointer_type()),
                p("dst_dirfd", c_int_type()),
                p("dst_relname", signed_byte_pointer_type()),
                p("replace", CTypeLike::Bool),
                p("verbose", CTypeLike::Bool),
                p("dereference", CTypeLike::Bool),
            ],
        ),
        "close_stream" => sig(
            c_int_type(),
            vec![p("stream", typedef_pointer_type("FILE"))],
        ),
        "rpl_fseeko" => sig(
            c_int_type(),
            vec![
                p("fp", typedef_pointer_type("FILE")),
                p("offset", typedef_type("off_t")),
                p("whence", c_int_type()),
            ],
        ),
        "fopen_safer" => sig(
            typedef_pointer_type("FILE"),
            vec![
                p("file", signed_byte_pointer_type()),
                p("mode", signed_byte_pointer_type()),
            ],
        ),
        "open_safer" => sig(
            c_int_type(),
            vec![
                p("file", signed_byte_pointer_type()),
                p("flags", c_int_type()),
                p("mode", c_int_type()),
            ],
        ),
        "tzalloc" => sig(
            typedef_type("timezone_t"),
            vec![p("name", signed_byte_pointer_type())],
        ),
        "xget_version" => sig(
            CTypeLike::Enum("backup_type".to_string()),
            vec![
                p("context", signed_byte_pointer_type()),
                p("version", signed_byte_pointer_type()),
            ],
        ),
        "reap" => sig(typedef_type("pid_t"), vec![p("pid", typedef_type("pid_t"))]),
        "record_file" => sig(
            CTypeLike::Void,
            vec![
                p("ht", typedef_pointer_type("hash_table")),
                p("file", signed_byte_pointer_type()),
                p("stats", typedef_pointer_type("stat")),
            ],
        ),
        "num_processors_via_affinity_mask" => sig(c_ulong_type(), Vec::new()),
        "process_signals" | "exit_cleanup" | "clear_files" | "flush_stdout" => {
            sig(CTypeLike::Void, Vec::new())
        }
        "indent" => sig(
            CTypeLike::Void,
            vec![
                p("from", typedef_type("size_t")),
                p("to", typedef_type("size_t")),
            ],
        ),
        "dired_dump_obstack" => sig(
            CTypeLike::Void,
            vec![
                p("prefix", signed_byte_pointer_type()),
                p("os", struct_pointer_type("obstack")),
            ],
        ),
        "calc_req_mask" => sig(c_uint_type(), Vec::new()),
        "getuser" => sig(
            signed_byte_pointer_type(),
            vec![p("uid", typedef_type("uid_t"))],
        ),
        "getgroup" => sig(
            signed_byte_pointer_type(),
            vec![p("gid", typedef_type("gid_t"))],
        ),
        "format_user_or_group" => sig(
            CTypeLike::Void,
            vec![
                p("name", signed_byte_pointer_type()),
                p("id", typedef_type("uintmax_t")),
                p("width", c_int_type()),
            ],
        ),
        "xstrtol_fatal" => sig(
            CTypeLike::Void,
            vec![
                p("err", typedef_type("strtol_error")),
                p("opt_idx", c_int_type()),
                p("c", signed_int_type(8)),
                p("long_options", typedef_pointer_type("option")),
                p("arg", signed_byte_pointer_type()),
            ],
        ),
        "rpl_obstack_free" => sig(
            CTypeLike::Void,
            vec![
                p("h", struct_pointer_type("obstack")),
                p("obj", void_pointer_type()),
            ],
        ),
        "rpl_obstack_allocated_p" => sig(
            c_int_type(),
            vec![
                p("h", struct_pointer_type("obstack")),
                p("obj", void_pointer_type()),
            ],
        ),
        "_obstack_begin_worker" => sig(
            c_int_type(),
            vec![
                p("h", struct_pointer_type("obstack")),
                p("chunk_size", typedef_type("idx_t")),
                p("alignment", typedef_type("idx_t")),
            ],
        ),
        "has_xattr" => sig(
            CTypeLike::Bool,
            vec![
                p("xattr", signed_byte_pointer_type()),
                p("ai", typedef_pointer_type("aclinfo")),
                p("fd", c_int_type()),
                p("name", signed_byte_pointer_type()),
                p("flags", c_int_type()),
            ],
        ),
        "check_tuning" => sig(
            CTypeLike::Bool,
            vec![p("table", typedef_pointer_type("hash_table"))],
        ),
        "rpl_fflush" => sig(
            c_int_type(),
            vec![p("stream", typedef_pointer_type("FILE"))],
        ),
        "imaxtostr" => sig(
            signed_byte_pointer_type(),
            vec![
                p("value", typedef_type("intmax_t")),
                p("buf", signed_byte_pointer_type()),
            ],
        ),
        "umaxtostr" => sig(
            signed_byte_pointer_type(),
            vec![
                p("value", typedef_type("uintmax_t")),
                p("buf", signed_byte_pointer_type()),
            ],
        ),
        "hwcap_allowed" => sig(
            CTypeLike::Bool,
            vec![p("glibc_hwcap", signed_byte_pointer_type())],
        ),
        "base32_encode" | "base64_encode" => sig(
            CTypeLike::Void,
            vec![
                p("in", signed_byte_pointer_type()),
                p("inlen", typedef_type("idx_t")),
                p("out", signed_byte_pointer_type()),
                p("outlen", typedef_type("idx_t")),
            ],
        ),
        "base32_decode_ctx" => sig(
            CTypeLike::Bool,
            vec![
                p("ctx", struct_pointer_type("base32_decode_context")),
                p("in", signed_byte_pointer_type()),
                p("inlen", typedef_type("idx_t")),
                p("out", signed_byte_pointer_type()),
                p("outlen", typedef_pointer_type("idx_t")),
            ],
        ),
        "base64_decode_ctx" => sig(
            CTypeLike::Bool,
            vec![
                p("ctx", struct_pointer_type("base64_decode_context")),
                p("in", signed_byte_pointer_type()),
                p("inlen", typedef_type("idx_t")),
                p("out", signed_byte_pointer_type()),
                p("outlen", typedef_pointer_type("idx_t")),
            ],
        ),
        "base58_encode_ctx_finalize" => sig(
            CTypeLike::Bool,
            vec![
                p("ctx", struct_pointer_type("base_encode_context")),
                p("out", signed_byte_pointer_pointer_type()),
                p("outlen", typedef_pointer_type("idx_t")),
            ],
        ),
        "re_string_reconstruct" => sig(
            typedef_type("reg_errcode_t"),
            vec![
                p("pstr", typedef_pointer_type("re_string_t")),
                p("idx", typedef_type("idx_t")),
                p("eflags", c_int_type()),
            ],
        ),
        "re_search_internal" => sig(
            typedef_type("reg_errcode_t"),
            vec![
                p("preg", typedef_pointer_type("regex_t")),
                p("string", signed_byte_pointer_type()),
                p("length", typedef_type("idx_t")),
                p("start", typedef_type("idx_t")),
                p("last_start", typedef_type("idx_t")),
                p("stop", typedef_type("idx_t")),
                p("nmatch", typedef_pointer_type("re_registers")),
                p("pmatch", typedef_pointer_type("regmatch_t")),
                p("eflags", c_int_type()),
            ],
        ),
        "re_compile_internal" => sig(
            typedef_type("reg_errcode_t"),
            vec![
                p("preg", typedef_pointer_type("re_pattern_buffer")),
                p("pattern", signed_byte_pointer_type()),
                p("length", typedef_type("idx_t")),
                p("syntax", typedef_type("reg_syntax_t")),
            ],
        ),
        "parse_expression" => sig(
            typedef_pointer_type("bin_tree_t"),
            vec![
                p("regexp", typedef_pointer_type("re_string_t")),
                p("preg", typedef_pointer_type("regex_t")),
                p("token", typedef_pointer_type("re_token_t")),
                p("syntax", typedef_type("reg_syntax_t")),
                p("nest", typedef_type("idx_t")),
                p("err", typedef_pointer_type("reg_errcode_t")),
            ],
        ),
        "build_trtable" => sig(
            CTypeLike::Bool,
            vec![
                p("dfa", typedef_pointer_type("re_dfa_t")),
                p("state", typedef_pointer_type("re_dfastate_t")),
            ],
        ),
        "update_cur_sifted_state" => sig(
            typedef_type("reg_errcode_t"),
            vec![
                p("mctx", typedef_pointer_type("re_match_context_t")),
                p("dest_nodes", typedef_pointer_type("re_node_set")),
                p("str_idx", typedef_type("idx_t")),
                p("candidates", typedef_pointer_type("re_node_set")),
            ],
        ),
        "transit_state_bkref" => sig(
            typedef_type("reg_errcode_t"),
            vec![
                p("mctx", typedef_pointer_type("re_match_context_t")),
                p("nodes", typedef_pointer_type("re_node_set")),
            ],
        ),
        "build_charclass" => sig(
            typedef_type("reg_errcode_t"),
            vec![
                p("trans", typedef_pointer_type("re_dfa_t")),
                p("sbcset", typedef_pointer_type("bitset_word_t")),
                p("mbcset", typedef_pointer_type("re_charset_t")),
                p("char_class_alloc", typedef_pointer_type("idx_t")),
                p("class_name", signed_byte_pointer_type()),
                p("syntax", typedef_type("reg_syntax_t")),
            ],
        ),
        "check_arrival" => sig(
            typedef_type("reg_errcode_t"),
            vec![
                p("mctx", typedef_pointer_type("re_match_context_t")),
                p("path", typedef_pointer_type("state_array_t")),
                p("top_node", typedef_type("idx_t")),
                p("top_str", typedef_type("idx_t")),
                p("last_node", typedef_type("idx_t")),
                p("last_str", typedef_type("idx_t")),
                p("type", c_int_type()),
            ],
        ),
        "peek_token" => sig(
            c_int_type(),
            vec![
                p("token", typedef_pointer_type("re_token_t")),
                p("input", typedef_pointer_type("re_string_t")),
                p("syntax", typedef_type("reg_syntax_t")),
            ],
        ),
        "build_wcs_upper_buffer" => sig(
            typedef_type("reg_errcode_t"),
            vec![p("pstr", typedef_pointer_type("re_string_t"))],
        ),
        "yyparse" => sig(
            c_int_type(),
            vec![p("pc", typedef_pointer_type("parser_control"))],
        ),
        "install_file_in_file" => sig(
            CTypeLike::Bool,
            vec![
                p("from", signed_byte_pointer_type()),
                p("to", signed_byte_pointer_type()),
                p("to_dirfd", c_int_type()),
                p("to_relname", signed_byte_pointer_type()),
                p("x", typedef_pointer_type("cp_options")),
            ],
        ),
        "chown_files" => sig(
            CTypeLike::Bool,
            vec![
                p("files", signed_byte_pointer_pointer_type()),
                p("bit_flags", c_int_type()),
                p("uid", typedef_type("uid_t")),
                p("gid", typedef_type("gid_t")),
                p("required_uid", typedef_type("uid_t")),
                p("required_gid", typedef_type("gid_t")),
                p("chopt", struct_pointer_type("Chown_option")),
            ],
        ),
        "who" => sig(
            CTypeLike::Void,
            vec![
                p("filename", signed_byte_pointer_type()),
                p("options", c_int_type()),
            ],
        ),
        "read_utmp" => sig(
            c_int_type(),
            vec![
                p("file", signed_byte_pointer_type()),
                p("n_entries", typedef_pointer_type("idx_t")),
                p(
                    "utmp_buf",
                    CTypeLike::Pointer(Box::new(typedef_pointer_type("STRUCT_UTMP"))),
                ),
                p("options", c_int_type()),
            ],
        ),
        "dopass" => sig(
            c_int_type(),
            vec![
                p("fd", c_int_type()),
                p("st", typedef_pointer_type("stat")),
                p("qname", signed_byte_pointer_type()),
                p("sizep", typedef_pointer_type("off_t")),
                p("type", c_int_type()),
                p("s", typedef_pointer_type("randread_source")),
                p("k", c_ulong_type()),
                p("n", c_ulong_type()),
            ],
        ),
        "process_field" => sig(
            CTypeLike::Bool,
            vec![
                p("text", signed_byte_pointer_type()),
                p("field", typedef_type("uintmax_t")),
            ],
        ),
        "debug_print_current_time"
        | "debug_print_current_time.part.0"
        | "debug_print_relative_time"
        | "debug_print_relative_time.part.0" => sig(
            CTypeLike::Void,
            vec![
                p("item", signed_byte_pointer_type()),
                p("pc", typedef_pointer_type("parser_control")),
            ],
        ),
        "factor_using_pollard_rho" => sig(
            CTypeLike::Void,
            vec![
                p("factors", struct_pointer_type("factors")),
                p("n", typedef_type("mp_limb_t")),
                p("a", typedef_type("mp_limb_t")),
            ],
        ),
        "factor_using_pollard_rho2" => sig(
            CTypeLike::Void,
            vec![
                p("factors", struct_pointer_type("factors")),
                p("n1", typedef_type("mp_limb_t")),
                p("n0", typedef_type("mp_limb_t")),
                p("a", typedef_type("mp_limb_t")),
            ],
        ),
        "factor_up" | "factor_up.part.0" | "factor_up.part.0.constprop.0" => sig(
            CTypeLike::Void,
            vec![
                p("factors", struct_pointer_type("factors")),
                p("t1", typedef_type("mp_limb_t")),
                p("t0", typedef_type("mp_limb_t")),
                p("prime_idx", typedef_type("idx_t")),
            ],
        ),
        "mp_factor_using_pollard_rho" => sig(
            CTypeLike::Void,
            vec![
                p("factors", struct_pointer_type("mp_factors")),
                p("mp", typedef_pointer_type("mp_limb_t")),
                p("n", typedef_type("mp_size_t")),
                p("a", typedef_type("mp_limb_t")),
            ],
        ),
        "seq_fast" => sig(
            CTypeLike::Void,
            vec![
                p("a", signed_byte_pointer_type()),
                p("b", signed_byte_pointer_type()),
                p("step", typedef_type("uintmax_t")),
            ],
        ),
        "tsort" => sig(CTypeLike::Void, vec![p("file", signed_byte_pointer_type())]),
        "splice_cat" => sig(c_int_type(), Vec::new()),
        "mgetgroups" => sig(
            c_int_type(),
            vec![
                p("username", signed_byte_pointer_type()),
                p("gid", typedef_type("gid_t")),
                p(
                    "groups",
                    CTypeLike::Pointer(Box::new(typedef_pointer_type("gid_t"))),
                ),
            ],
        ),
        "parse_additional_groups" => sig(
            c_int_type(),
            vec![
                p("groups", signed_byte_pointer_type()),
                p(
                    "pgids",
                    CTypeLike::Pointer(Box::new(typedef_pointer_type("gid_t"))),
                ),
                p("pn_gids", typedef_pointer_type("idx_t")),
                p("show_errors", CTypeLike::Bool),
            ],
        ),
        "parse_tab_stops" => sig(
            CTypeLike::Void,
            vec![p("stops", signed_byte_pointer_type())],
        ),
        "finalize_tab_stops" | "list_signal_handling" => sig(CTypeLike::Void, Vec::new()),
        "parse_block_signal_params" => sig(
            CTypeLike::Void,
            vec![
                p("arg", signed_byte_pointer_type()),
                p("block", CTypeLike::Bool),
            ],
        ),
        "operand2sig" => sig(c_int_type(), vec![p("operand", signed_byte_pointer_type())]),
        "str2sig" => sig(
            c_int_type(),
            vec![
                p("signame", signed_byte_pointer_type()),
                p("signum", CTypeLike::Pointer(Box::new(c_int_type()))),
            ],
        ),
        "get_dev" => sig(
            CTypeLike::Void,
            vec![
                p("device", signed_byte_pointer_type()),
                p("mount_point", signed_byte_pointer_type()),
                p("file", signed_byte_pointer_type()),
                p("stat_file", signed_byte_pointer_type()),
                p("fstype", signed_byte_pointer_type()),
                p("me_dummy", CTypeLike::Bool),
                p("me_remote", CTypeLike::Bool),
                p("force_fsu", struct_pointer_type("fs_usage")),
                p("process_all", CTypeLike::Bool),
            ],
        ),
        "chdir_long" => sig(c_int_type(), vec![p("dir", signed_byte_pointer_type())]),
        "append_quoted" => sig(CTypeLike::Void, vec![p("str", signed_byte_pointer_type())]),
        "append_entry" => sig(
            CTypeLike::Void,
            vec![
                p("prefix", signed_int_type(8)),
                p("item", signed_byte_pointer_type()),
                p("arg", signed_byte_pointer_type()),
            ],
        ),
        "writeline" => {
            let mut params = vec![
                p("line", typedef_pointer_type("linebuffer")),
                p("class", c_int_type()),
            ];
            if current_param_count > 2 {
                params[1] = p("match", CTypeLike::Bool);
                params.push(p("linecount", typedef_type("intmax_t")));
            }
            sig(CTypeLike::Void, params)
        }
        name if is_fileinfo_sort_comparator_role(name) => sig(
            c_int_type(),
            vec![
                p("a", typedef_pointer_type("fileinfo")),
                p("b", typedef_pointer_type("fileinfo")),
            ],
        ),
        "getopt" | "rpl_getopt" => sig(
            c_int_type(),
            vec![
                p("argc", c_int_type()),
                p("argv", signed_byte_pointer_pointer_type()),
                p("optstring", signed_byte_pointer_type()),
            ],
        ),
        "getopt_long" | "getopt_long_only" | "rpl_getopt_long" | "rpl_getopt_long_only" => sig(
            c_int_type(),
            vec![
                p("argc", c_int_type()),
                p("argv", signed_byte_pointer_pointer_type()),
                p("optstring", signed_byte_pointer_type()),
                p("longopts", typedef_pointer_type("option")),
                p("longindex", CTypeLike::Pointer(Box::new(c_int_type()))),
            ],
        ),
        "_getopt_internal" => sig(
            c_int_type(),
            vec![
                p("argc", c_int_type()),
                p("argv", signed_byte_pointer_pointer_type()),
                p("optstring", signed_byte_pointer_type()),
                p("longopts", typedef_pointer_type("option")),
                p("longind", CTypeLike::Pointer(Box::new(c_int_type()))),
                p("long_only", c_int_type()),
                p("posixly_correct", c_int_type()),
            ],
        ),
        "_getopt_internal_r" => sig(
            c_int_type(),
            vec![
                p("argc", c_int_type()),
                p("argv", signed_byte_pointer_pointer_type()),
                p("optstring", signed_byte_pointer_type()),
                p("longopts", typedef_pointer_type("option")),
                p("longind", CTypeLike::Pointer(Box::new(c_int_type()))),
                p("long_only", c_int_type()),
                p("d", typedef_pointer_type("_getopt_data")),
                p("posixly_correct", c_int_type()),
            ],
        ),
        "parse_long_options" => long_options_signature(current_param_count, false),
        "parse_gnu_standard_options_only" => long_options_signature(current_param_count, true),
        "human_options" => sig(
            typedef_type("strtol_error"),
            vec![
                p("spec", signed_byte_pointer_type()),
                p("opts", CTypeLike::Pointer(Box::new(c_int_type()))),
                p("block_size", typedef_pointer_type("uintmax_t")),
            ],
        ),
        "parse_integer" => sig(
            typedef_type("intmax_t"),
            vec![
                p("str", signed_byte_pointer_type()),
                p("invalid", typedef_pointer_type("strtol_error")),
            ],
        ),
        "parse_number" => sig(c_int_type(), vec![p("str", signed_byte_pointer_type())]),
        "traverse_raw_number" => sig(
            signed_int_type(8),
            vec![p("number", signed_byte_pointer_pointer_type())],
        ),
        "argv_iter_init_argv" => sig(
            struct_pointer_type("argv_iterator"),
            vec![p("argv", signed_byte_pointer_pointer_type())],
        ),
        "argv_iter_init_stream" => sig(
            struct_pointer_type("argv_iterator"),
            vec![p("stream", typedef_pointer_type("FILE"))],
        ),
        "argv_iter" => sig(
            signed_byte_pointer_type(),
            vec![
                p("iter", struct_pointer_type("argv_iterator")),
                p(
                    "err",
                    CTypeLike::Pointer(Box::new(CTypeLike::Enum("argv_iter_err".to_string()))),
                ),
            ],
        ),
        "argv_iter_n_args" => sig(
            typedef_type("idx_t"),
            vec![p("iter", struct_pointer_type("argv_iterator"))],
        ),
        "argv_iter_free" => sig(
            CTypeLike::Void,
            vec![p("iter", struct_pointer_type("argv_iterator"))],
        ),
        "check_secret" => sig(c_int_type(), vec![p("x", c_int_type())]),
        "process_string" => sig(c_int_type(), vec![p("s", signed_byte_pointer_type())]),
        "test_boolxor" => sig(
            c_int_type(),
            vec![p("a", c_int_type()), p("b", c_int_type())],
        ),
        "alloc_wrapper2" => sig(allocation_ptr_type(), vec![p("n", typedef_type("size_t"))]),
        "large_basic_block_guard" => sig(c_int_type(), vec![p("x", c_int_type())]),
        "tiny_vm_dispatch" => sig(
            c_int_type(),
            vec![
                p("code", unsigned_byte_pointer_type()),
                p("len", c_int_type()),
            ],
        ),
        "xnumtoumax" => sig(
            typedef_type("uintmax_t"),
            vec![
                p("n_str", signed_byte_pointer_type()),
                p("base", c_int_type()),
                p("min", typedef_type("uintmax_t")),
                p("max", typedef_type("uintmax_t")),
                p("suffixes", signed_byte_pointer_type()),
                p("err", signed_byte_pointer_type()),
                p("err_exit", c_int_type()),
                p("flags", c_int_type()),
            ],
        ),
        "xnumtoimax" => sig(
            typedef_type("intmax_t"),
            vec![
                p("n_str", signed_byte_pointer_type()),
                p("base", c_int_type()),
                p("min", typedef_type("intmax_t")),
                p("max", typedef_type("intmax_t")),
                p("suffixes", signed_byte_pointer_type()),
                p("err", signed_byte_pointer_type()),
                p("err_exit", c_int_type()),
                p("flags", c_int_type()),
            ],
        ),
        "xstrtol" => sig(
            typedef_type("strtol_error"),
            vec![
                p("nptr", signed_byte_pointer_type()),
                p("endptr", signed_byte_pointer_pointer_type()),
                p("base", c_int_type()),
                p("val", typedef_pointer_type("long")),
                p("valid_suffixes", signed_byte_pointer_type()),
            ],
        ),
        "xstrtoul" => sig(
            typedef_type("strtol_error"),
            vec![
                p("nptr", signed_byte_pointer_type()),
                p("endptr", signed_byte_pointer_pointer_type()),
                p("base", c_int_type()),
                p("val", typedef_pointer_type("unsigned long")),
                p("valid_suffixes", signed_byte_pointer_type()),
            ],
        ),
        "print_files" => sig(
            CTypeLike::Void,
            vec![
                p("number_of_files", c_int_type()),
                p("av", signed_byte_pointer_pointer_type()),
            ],
        ),
        "squeeze_filter.constprop.0" => sig(
            CTypeLike::Void,
            vec![
                p("buf", signed_byte_pointer_type()),
                p("size", typedef_type("size_t")),
            ],
        ),
        "squeeze_filter" => sig(
            CTypeLike::Void,
            vec![
                p("buf", signed_byte_pointer_type()),
                p("size", typedef_type("size_t")),
                p("reader", CTypeLike::Function),
            ],
        ),
        "bytes_split" => sig(
            CTypeLike::Void,
            vec![
                p("n_bytes", typedef_type("intmax_t")),
                p("rem_bytes", typedef_type("intmax_t")),
                p("buf", signed_byte_pointer_type()),
                p("bufsize", typedef_type("idx_t")),
                p("initial_read", typedef_type("ssize_t")),
                p("max_files", typedef_type("intmax_t")),
            ],
        ),
        "ftoastr" => sig(
            c_int_type(),
            vec![
                p("buf", signed_byte_pointer_type()),
                p("bufsize", typedef_type("size_t")),
                p("flags", c_int_type()),
                p("width", c_int_type()),
                p("x", typedef_type("float")),
            ],
        ),
        "dtoastr" => sig(
            c_int_type(),
            vec![
                p("buf", signed_byte_pointer_type()),
                p("bufsize", typedef_type("size_t")),
                p("flags", c_int_type()),
                p("width", c_int_type()),
                p("x", typedef_type("double")),
            ],
        ),
        "ldtoastr" => sig(
            c_int_type(),
            vec![
                p("buf", signed_byte_pointer_type()),
                p("bufsize", typedef_type("size_t")),
                p("flags", c_int_type()),
                p("width", c_int_type()),
                p("x", typedef_type("long double")),
            ],
        ),
        "eval6" => sig(
            typedef_pointer_type("VALUE"),
            vec![p("evaluate", CTypeLike::Bool)],
        ),
        "settimeout" => sig(
            CTypeLike::Void,
            vec![
                p("duration", typedef_type("double")),
                p("warn", CTypeLike::Bool),
            ],
        ),
        "output_file" => sig(
            CTypeLike::Void,
            vec![
                p("file", signed_byte_pointer_type()),
                p("binary_file", c_int_type()),
                p("digest", unsigned_byte_pointer_type()),
                p("raw", CTypeLike::Bool),
                p("tagged", CTypeLike::Bool),
                p(
                    "delim",
                    CTypeLike::Int {
                        bits: 8,
                        signedness: Signedness::Unsigned,
                    },
                ),
                p("args", CTypeLike::Bool),
                p("length", typedef_type("intmax_t")),
            ],
        ),
        "add_utmp" => sig(
            CTypeLike::Struct("utmp_alloc".to_string()),
            vec![
                p("a", CTypeLike::Struct("utmp_alloc".to_string())),
                p("options", c_int_type()),
                p("user", signed_byte_pointer_type()),
                p("user_len", typedef_type("idx_t")),
                p("id", signed_byte_pointer_type()),
                p("id_len", typedef_type("idx_t")),
                p("line", signed_byte_pointer_type()),
                p("line_len", typedef_type("idx_t")),
                p("host", signed_byte_pointer_type()),
                p("host_len", typedef_type("idx_t")),
                p("pid", typedef_type("pid_t")),
                p("type", typedef_type("short")),
                p("ts", CTypeLike::Struct("timespec".to_string())),
                p("session", typedef_type("utmp_session")),
                p("termination", c_int_type()),
                p("exit", c_int_type()),
            ],
        ),
        "iopoll_internal" => sig(
            c_int_type(),
            vec![
                p("fdin", c_int_type()),
                p("fdout", c_int_type()),
                p("block", CTypeLike::Bool),
                p("broken_output", CTypeLike::Bool),
            ],
        ),
        "make_dir_parents" => sig(
            CTypeLike::Bool,
            vec![
                p("dir", signed_byte_pointer_type()),
                p("wd", struct_pointer_type("savewd")),
                p("make_ancestor", typedef_type("mkdir_ancestor_fn")),
                p("options", memory_ptr_type()),
                p("mode", typedef_type("mode_t")),
                p("announce", typedef_type("mkdir_announce_fn")),
                p("mode_bits", typedef_type("mode_t")),
                p("owner", typedef_type("uid_t")),
                p("group", typedef_type("gid_t")),
                p("preserve_existing", CTypeLike::Bool),
            ],
        ),
        "savewd_chdir" => sig(
            c_int_type(),
            vec![
                p("wd", struct_pointer_type("savewd")),
                p("dir", signed_byte_pointer_type()),
                p("options", c_int_type()),
                p("open_result", CTypeLike::Pointer(Box::new(c_int_type()))),
            ],
        ),
        "fmt_paragraph" | "next_file_name" | "stdbuf" => sig(CTypeLike::Void, Vec::new()),
        "get_line" if current_param_count >= 3 => sig(
            CTypeLike::Bool,
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p(
                    "linep",
                    CTypeLike::Pointer(Box::new(struct_pointer_type("line"))),
                ),
                p("which", c_int_type()),
            ],
        ),
        "get_line" => sig(
            c_int_type(),
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("c", c_int_type()),
            ],
        ),
        "fremote" => sig(
            CTypeLike::Bool,
            vec![
                p("fd", c_int_type()),
                p("file", struct_pointer_type("File_spec")),
            ],
        ),
        "tail_bytes" | "tail_lines" => sig(
            typedef_type("off_t"),
            vec![
                p("prettyname", signed_byte_pointer_type()),
                p("fd", c_int_type()),
                p("st", struct_pointer_type("stat")),
                p("count", typedef_type("count_t")),
            ],
        ),
        "head_lines" => sig(
            CTypeLike::Bool,
            vec![
                p("filename", signed_byte_pointer_type()),
                p("fd", c_int_type()),
                p("lines_to_write", typedef_type("uintmax_t")),
            ],
        ),
        "elide_tail_lines_seekable" => sig(
            CTypeLike::Bool,
            vec![
                p("pretty_filename", signed_byte_pointer_type()),
                p("fd", c_int_type()),
                p("n_lines", typedef_type("uintmax_t")),
                p("start_pos", typedef_type("off_t")),
                p("size", typedef_type("off_t")),
            ],
        ),
        "recheck" => sig(
            CTypeLike::Void,
            vec![
                p("file", struct_pointer_type("File_spec")),
                p("blocking", CTypeLike::Bool),
            ],
        ),
        "do_link" => sig(
            CTypeLike::Bool,
            vec![
                p("source", signed_byte_pointer_type()),
                p("destdir_fd", c_int_type()),
                p("dest_base", signed_byte_pointer_type()),
                p("dest", signed_byte_pointer_type()),
                p("link_errno", c_int_type()),
            ],
        ),
        "create" => sig(c_int_type(), vec![p("name", signed_byte_pointer_type())]),
        "fread_file" => sig(
            signed_byte_pointer_type(),
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("flags", c_int_type()),
                p("length", typedef_pointer_type("size_t")),
            ],
        ),
        "do_wipefd" => sig(
            CTypeLike::Bool,
            vec![
                p("fd", c_int_type()),
                p("qname", signed_byte_pointer_type()),
                p("source", struct_pointer_type("randint_source")),
                p("flags", struct_pointer_type("Options")),
            ],
        ),
        "print_entry" => sig(
            CTypeLike::Void,
            vec![p("utmp_ent", typedef_pointer_type("struct_utmp"))],
        ),
        "print_stuff" => sig(
            CTypeLike::Void,
            vec![p("pw_name", signed_byte_pointer_type())],
        ),
        "print_stat" | "print_statfs" => sig(
            CTypeLike::Bool,
            vec![
                p("pformat", signed_byte_pointer_type()),
                p("prefix_len", typedef_type("size_t")),
                p("mod", signed_int_type(8)),
                p("m", signed_int_type(8)),
                p("fd", c_int_type()),
                p("filename", signed_byte_pointer_type()),
                p("data", typedef_pointer_type("stat_print_data")),
            ],
        ),
        "print_it" => sig(
            CTypeLike::Bool,
            vec![
                p("format", signed_byte_pointer_type()),
                p("fd", c_int_type()),
                p("filename", signed_byte_pointer_type()),
                p("print_func", typedef_type("stat_print_fn")),
                p("data", typedef_type("stat_print_data_ref")),
            ],
        ),
        "apply_settings" => sig(
            CTypeLike::Void,
            vec![
                p("checking", CTypeLike::Bool),
                p("device_name", signed_byte_pointer_type()),
                p("settings", signed_byte_pointer_pointer_type()),
                p("n_settings", c_int_type()),
                p("mode", struct_pointer_type("termios")),
                p(
                    "require_set_attr",
                    CTypeLike::Pointer(Box::new(CTypeLike::Bool)),
                ),
            ],
        ),
        "apply_mode" => sig(
            CTypeLike::Void,
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("stream_name", signed_byte_pointer_type()),
                p("envvar", signed_byte_pointer_type()),
            ],
        ),
        "baud_to_value" => sig(c_ulong_type(), vec![p("speed", typedef_type("speed_t"))]),
        "add_field_list" => sig(CTypeLike::Void, vec![p("str", signed_byte_pointer_type())]),
        "users" => sig(
            CTypeLike::Void,
            vec![
                p("filename", signed_byte_pointer_type()),
                p("options", c_int_type()),
            ],
        ),
        "cleanup" => {
            let params = if current_param_count == 0 {
                Vec::new()
            } else {
                vec![p("sig", c_int_type())]
            };
            sig(CTypeLike::Void, params)
        }
        "prog_fprintf" => sig(
            CTypeLike::Void,
            extend_params_to_count(
                vec![
                    p("fp", typedef_pointer_type("FILE")),
                    p("fmt", signed_byte_pointer_type()),
                ],
                current_param_count,
                "value",
                typedef_type("uintptr_t"),
            ),
        ),
        "write_block" => sig(
            CTypeLike::Void,
            vec![
                p("current_offset", typedef_type("intmax_t")),
                p("n_bytes", typedef_type("idx_t")),
                p("prev_block", signed_byte_pointer_type()),
                p("curr_block", signed_byte_pointer_type()),
            ],
        ),
        "get_next" => sig(
            c_int_type(),
            vec![
                p("spec", struct_pointer_type("Spec_list")),
                p(
                    "class",
                    CTypeLike::Pointer(Box::new(CTypeLike::Enum("Upper_Lower_class".to_string()))),
                ),
            ],
        ),
        "get_spec_stats" => sig(
            CTypeLike::Void,
            vec![p("spec", struct_pointer_type("Spec_list"))],
        ),
        "process_line" => sig(
            c_int_type(),
            vec![
                p("line", signed_byte_pointer_type()),
                p("newline", CTypeLike::Bool),
            ],
        ),
        "ignorable_failure" => sig(
            CTypeLike::Bool,
            vec![
                p("error_number", c_int_type()),
                p("dir", signed_byte_pointer_type()),
            ],
        ),
        "tee_files" => sig(
            CTypeLike::Bool,
            vec![
                p("nfiles", c_int_type()),
                p("files", signed_byte_pointer_pointer_type()),
                p("pipe_check", CTypeLike::Bool),
            ],
        ),
        "errno_iterate" => sig(
            CTypeLike::Void,
            vec![
                p("callback", CTypeLike::Function),
                p("data", memory_ptr_type()),
            ],
        ),
        "careadlinkat" => sig(
            signed_byte_pointer_type(),
            vec![
                p("fd", c_int_type()),
                p("filename", signed_byte_pointer_type()),
                p("buffer", signed_byte_pointer_type()),
                p("buffer_size", typedef_type("size_t")),
                p("alloc", struct_pointer_type("allocator")),
                p("preadlinkat", CTypeLike::Function),
            ],
        ),
        "crc32_update_no_xor_pclmul" => sig(
            typedef_type("crc32_t"),
            vec![
                p("crc", typedef_type("crc32_t")),
                p("buf", memory_ptr_type()),
                p("len", typedef_type("size_t")),
            ],
        ),
        "synchronize_output" => sig(c_int_type(), Vec::new()),
        "copy_file_data" => sig(
            typedef_type("intmax_t"),
            vec![
                p("ifd", c_int_type()),
                p("ist", typedef_pointer_type("stat")),
                p("ipos", typedef_type("off_t")),
                p("iname", signed_byte_pointer_type()),
                p("ofd", c_int_type()),
                p("ost", typedef_pointer_type("stat")),
                p("opos", typedef_type("off_t")),
                p("oname", signed_byte_pointer_type()),
                p("ibytes", typedef_type("count_t")),
                p("x", typedef_pointer_type("cp_options")),
                p("debug", typedef_pointer_type("copy_debug")),
            ],
        ),
        "create_hole" => sig(
            typedef_type("off_t"),
            vec![
                p("fd", c_int_type()),
                p("name", signed_byte_pointer_type()),
                p("size", typedef_type("off_t")),
            ],
        ),
        "full_write" => sig(
            typedef_type("idx_t"),
            vec![
                p("fd", c_int_type()),
                p("buf", memory_ptr_type()),
                p("count", typedef_type("idx_t")),
            ],
        ),
        "write_zeros" => sig(
            CTypeLike::Bool,
            vec![
                p("fd", c_int_type()),
                p("n_bytes", typedef_type("off_t")),
                p("abuf", signed_byte_pointer_pointer_type()),
                p("buf_size", typedef_type("idx_t")),
            ],
        ),
        "sparse_copy" => sig(
            typedef_type("intmax_t"),
            vec![
                p("src_fd", c_int_type()),
                p("dest_fd", c_int_type()),
                p("abuf", signed_byte_pointer_pointer_type()),
                p("buf_size", typedef_type("idx_t")),
                p("allow_reflink", CTypeLike::Bool),
                p("src_name", signed_byte_pointer_type()),
                p("dst_name", signed_byte_pointer_type()),
                p("max_n_read", typedef_type("count_t")),
                p("hole_size", typedef_pointer_type("off_t")),
                p("debug", typedef_pointer_type("copy_debug")),
            ],
        ),
        "copy_with_unblock" => sig(
            CTypeLike::Void,
            vec![
                p("buf", signed_byte_pointer_type()),
                p("nread", typedef_type("idx_t")),
            ],
        ),
        "copy_bytes" => sig(
            CTypeLike::Void,
            vec![
                p("dst", signed_byte_pointer_type()),
                p("src", signed_byte_pointer_type()),
                p("n_bytes", typedef_type("size_t")),
            ],
        ),
        "iwrite" | "iwrite.constprop.0" => sig(
            typedef_type("idx_t"),
            vec![
                p("fd", c_int_type()),
                p("buf", signed_byte_pointer_type()),
                p("size", typedef_type("idx_t")),
            ],
        ),
        "translate_charset" => sig(
            CTypeLike::Void,
            vec![p("new_trans", signed_byte_pointer_type())],
        ),
        "invalidate_cache" => sig(
            CTypeLike::Bool,
            vec![p("fd", c_int_type()), p("len", typedef_type("off_t"))],
        ),
        "copy_internal" => sig(
            CTypeLike::Bool,
            vec![
                p("src_name", signed_byte_pointer_type()),
                p("dst_name", signed_byte_pointer_type()),
                p("dst_dirfd", c_int_type()),
                p("dst_relname", signed_byte_pointer_type()),
                p("nonexistent_dst", c_int_type()),
                p("parent", typedef_pointer_type("stat")),
                p("ancestors", typedef_pointer_type("dir_list")),
                p("x", typedef_pointer_type("cp_options")),
                p("command_line_arg", CTypeLike::Bool),
                p(
                    "first_dir_created_per_command_line_arg",
                    CTypeLike::Pointer(Box::new(CTypeLike::Bool)),
                ),
                p(
                    "copy_into_self",
                    CTypeLike::Pointer(Box::new(CTypeLike::Bool)),
                ),
                p(
                    "rename_succeeded",
                    CTypeLike::Pointer(Box::new(CTypeLike::Bool)),
                ),
            ],
        ),
        "do_copy" => sig(
            CTypeLike::Bool,
            vec![
                p("n_files", c_int_type()),
                p("file", signed_byte_pointer_pointer_type()),
                p("target_directory", signed_byte_pointer_type()),
                p("no_target_directory", CTypeLike::Bool),
                p("x", typedef_pointer_type("cp_options")),
            ],
        ),
        "make_dir_parents_private" => sig(
            CTypeLike::Bool,
            vec![
                p("const_dir", signed_byte_pointer_type()),
                p("src_offset", typedef_type("size_t")),
                p("dst_dirfd", c_int_type()),
                p("verbose_fmt_string", signed_byte_pointer_type()),
                p("attr_list", typedef_pointer_type("dir_attr")),
                p("new_dst", CTypeLike::Pointer(Box::new(CTypeLike::Bool))),
                p("x", typedef_pointer_type("cp_options")),
            ],
        ),
        "backupfile_internal" => sig(
            signed_byte_pointer_type(),
            vec![
                p("dir_fd", c_int_type()),
                p("file", signed_byte_pointer_type()),
                p("backup_type", typedef_type("backup_type")),
                p("rename", CTypeLike::Bool),
            ],
        ),
        "utimecmpat" => sig(
            c_int_type(),
            vec![
                p("dfd", c_int_type()),
                p("dst_name", signed_byte_pointer_type()),
                p("dst_stat", typedef_pointer_type("stat")),
                p("src_stat", typedef_pointer_type("stat")),
                p("options", c_int_type()),
            ],
        ),
        "fdutimensat" => sig(
            c_int_type(),
            vec![
                p("fd", c_int_type()),
                p("dir", c_int_type()),
                p("file", signed_byte_pointer_type()),
                p("times", typedef_pointer_type("timespec")),
                p("atflag", c_int_type()),
            ],
        ),
        "rpl_nanosleep" => sig(
            c_int_type(),
            vec![
                p("requested_delay", struct_pointer_type("timespec")),
                p("remaining_delay", struct_pointer_type("timespec")),
            ],
        ),
        "xnanosleep" => sig(c_int_type(), vec![p("seconds", CTypeLike::Float(64))]),
        "fts_build" => sig(
            typedef_pointer_type("FTSENT"),
            vec![
                p("sp", typedef_pointer_type("FTS")),
                p("type", c_int_type()),
            ],
        ),
        "rpl_fts_read" => sig(
            typedef_pointer_type("FTSENT"),
            vec![p("sp", typedef_pointer_type("FTS"))],
        ),
        "rpl_fts_open" => sig(
            typedef_pointer_type("FTS"),
            vec![
                p("argv", signed_byte_pointer_pointer_type()),
                p("options", c_int_type()),
                p("compar", typedef_pointer_type("fts_compar_fn")),
            ],
        ),
        "rpl_fts_close" | "fts_close" => {
            sig(c_int_type(), vec![p("sp", typedef_pointer_type("FTS"))])
        }
        "fts_safe_changedir" => sig(
            c_int_type(),
            vec![
                p("sp", typedef_pointer_type("FTS")),
                p("p", typedef_pointer_type("FTSENT")),
                p("fd", c_int_type()),
                p("dir", signed_byte_pointer_type()),
            ],
        ),
        "defaultcon" => sig(
            c_int_type(),
            vec![
                p("selabel_handle", typedef_pointer_type("selabel_handle")),
                p("path", signed_byte_pointer_type()),
                p("mode", typedef_type("mode_t")),
            ],
        ),
        "restorecon_private" => sig(
            c_int_type(),
            vec![
                p("selabel_handle", typedef_pointer_type("selabel_handle")),
                p("path", signed_byte_pointer_type()),
            ],
        ),
        "restorecon" => sig(
            CTypeLike::Bool,
            vec![
                p("selabel_handle", typedef_pointer_type("selabel_handle")),
                p("path", signed_byte_pointer_type()),
                p("recurse", CTypeLike::Bool),
            ],
        ),
        "re_protect" => sig(
            CTypeLike::Bool,
            vec![
                p("const_dst_name", signed_byte_pointer_type()),
                p("dst_src_name", signed_byte_pointer_type()),
                p("dst_dirfd", c_int_type()),
                p("dst_relname", signed_byte_pointer_type()),
                p("attr_list", typedef_pointer_type("dir_attr")),
                p("x", typedef_pointer_type("cp_options")),
            ],
        ),
        "renameatu" => sig(
            c_int_type(),
            vec![
                p("fd1", c_int_type()),
                p("src", signed_byte_pointer_type()),
                p("fd2", c_int_type()),
                p("dst", signed_byte_pointer_type()),
                p("flags", c_uint_type()),
            ],
        ),
        "streamsavedir" => sig(
            signed_byte_pointer_type(),
            vec![
                p("dirp", typedef_pointer_type("DIR")),
                p("option", CTypeLike::Enum("savedir_option".to_string())),
            ],
        ),
        "version_etc_arn" => sig(
            CTypeLike::Void,
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("command_name", signed_byte_pointer_type()),
                p("package", signed_byte_pointer_type()),
                p("version", signed_byte_pointer_type()),
                p("authors", signed_byte_pointer_pointer_type()),
                p("n_authors", typedef_type("size_t")),
            ],
        ),
        "version_etc_ar" => sig(
            CTypeLike::Void,
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("command_name", signed_byte_pointer_type()),
                p("package", signed_byte_pointer_type()),
                p("version", signed_byte_pointer_type()),
                p("authors", signed_byte_pointer_pointer_type()),
            ],
        ),
        "version_etc_va" => sig(
            CTypeLike::Void,
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("command_name", signed_byte_pointer_type()),
                p("package", signed_byte_pointer_type()),
                p("version", signed_byte_pointer_type()),
                p("authors", typedef_type("va_list")),
                p("author_probe", typedef_type("uintptr_t")),
            ],
        ),
        "version_etc" => version_etc_signature(current_param_count),
        "emit_bug_reporting_address" => sig(CTypeLike::Void, Vec::new()),
        "last_component" => sig(
            signed_byte_pointer_type(),
            vec![p("filename", signed_byte_pointer_type())],
        ),
        "mdir_name" | "dir_name" => sig(
            signed_byte_pointer_type(),
            vec![p("file", signed_byte_pointer_type())],
        ),
        "oputs_" | "oputs_.constprop.0" => {
            sig(CTypeLike::Void, vec![p("text", signed_byte_pointer_type())])
        }
        "prompt.constprop.0" => sig(
            typedef_type("RM_status"),
            vec![
                p("fts", typedef_pointer_type("FTS")),
                p("ent", typedef_pointer_type("FTSENT")),
                p("is_dir", CTypeLike::Bool),
                p("dir_status", CTypeLike::Pointer(Box::new(c_int_type()))),
            ],
        ),
        "skip_whitespace_run" => sig(
            CTypeLike::Enum("field_terminator".to_string()),
            vec![
                p("mbuf", typedef_pointer_type("mbbuf_t")),
                p("parser", typedef_pointer_type("mbfield_parser")),
                p(
                    "have_pending_line",
                    CTypeLike::Pointer(Box::new(CTypeLike::Bool)),
                ),
                p("have_initial_whitespace", CTypeLike::Bool),
            ],
        ),
        "scan_mb_blank_field" => sig(
            CTypeLike::Enum("field_terminator".to_string()),
            vec![
                p("mbuf", typedef_pointer_type("mbbuf_t")),
                p("parser", typedef_pointer_type("mbfield_parser")),
                p(
                    "have_pending_line",
                    CTypeLike::Pointer(Box::new(CTypeLike::Bool)),
                ),
                p("write_field", CTypeLike::Bool),
                p("n_bytes", typedef_pointer_type("idx_t")),
            ],
        ),
        "scan_mb_delim_field" => sig(
            CTypeLike::Enum("field_terminator".to_string()),
            vec![
                p("mbuf", typedef_pointer_type("mbbuf_t")),
                p(
                    "have_pending_line",
                    CTypeLike::Pointer(Box::new(CTypeLike::Bool)),
                ),
                p("write_field", CTypeLike::Bool),
                p("n_bytes", typedef_pointer_type("idx_t")),
            ],
        ),
        "cut_characters_mode" => sig(
            CTypeLike::Void,
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("byte_mode", CTypeLike::Bool),
            ],
        ),
        "cut_fields_mb_any" => sig(
            CTypeLike::Void,
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("whitespace_mode", CTypeLike::Bool),
            ],
        ),
        "cut_fields_bytesearch" => sig(
            CTypeLike::Void,
            vec![p("stream", typedef_pointer_type("FILE"))],
        ),
        "cut_file" => sig(
            CTypeLike::Void,
            vec![
                p("file", typedef_pointer_type("FILE")),
                p("cut_stream", memory_ptr_type()),
            ],
        ),
        "cut_bytes" => sig(
            CTypeLike::Void,
            vec![
                p("line", signed_byte_pointer_type()),
                p("n_bytes", typedef_type("idx_t")),
            ],
        ),
        "memchr2" => sig(
            memory_ptr_type(),
            vec![
                p("s", memory_ptr_type()),
                p("c1", c_int_type()),
                p("c2", c_int_type()),
                p("n", typedef_type("size_t")),
            ],
        ),
        "set_fields" => sig(
            CTypeLike::Void,
            vec![
                p("fieldstr", signed_byte_pointer_type()),
                p("options", c_uint_type()),
            ],
        ),
        "print_name_with_quoting" => sig(
            typedef_type("size_t"),
            vec![
                p("f", typedef_pointer_type("fileinfo")),
                p("symlink_target", CTypeLike::Bool),
                p("stack", typedef_pointer_type("obstack")),
                p("start_col", typedef_type("size_t")),
            ],
        ),
        "print_long_format" => sig(
            CTypeLike::Void,
            vec![p("f", typedef_pointer_type("fileinfo"))],
        ),
        "print_filename.part.0" => sig(
            CTypeLike::Void,
            vec![
                p("filename", signed_byte_pointer_type()),
                p("stream", typedef_pointer_type("FILE")),
            ],
        ),
        "get_funky_string" => sig(
            typedef_type("size_t"),
            vec![
                p("buffer", signed_byte_pointer_type()),
                p("filename", signed_byte_pointer_type()),
                p("buffersize", typedef_type("size_t")),
                p("options", typedef_pointer_type("quoting_options")),
            ],
        ),
        "abformat_init" => sig(
            CTypeLike::Void,
            vec![p("f", typedef_pointer_type("fileinfo"))],
        ),
        "signal_setup" => sig(CTypeLike::Void, vec![p("init", CTypeLike::Bool)]),
        "quote_name_buf.constprop.0" => sig(
            typedef_type("size_t"),
            vec![
                p("buffer", signed_byte_pointer_type()),
                p("f", typedef_pointer_type("fileinfo")),
                p("symlink_target", CTypeLike::Bool),
                p("stack", typedef_pointer_type("obstack")),
                p("start_col", typedef_type("size_t")),
            ],
        ),
        "print_file_name_and_frills.isra.0" | "print_file_name_and_frills" => sig(
            typedef_type("size_t"),
            vec![
                p("f", typedef_pointer_type("fileinfo")),
                p("start_col", typedef_type("size_t")),
            ],
        ),
        "print_with_separator" => sig(CTypeLike::Void, vec![p("sep", signed_int_type(8))]),
        "quote_name" => sig(
            typedef_type("size_t"),
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("f", typedef_pointer_type("fileinfo")),
                p("symlink_target", CTypeLike::Bool),
                p("stack", typedef_pointer_type("obstack")),
                p("start_col", typedef_type("size_t")),
                p("name", signed_byte_pointer_type()),
                p("width", typedef_type("size_t")),
            ],
        ),
        "calculate_columns" => sig(CTypeLike::Void, Vec::new()),
        "print_current_files" => sig(CTypeLike::Void, Vec::new()),
        "verrevcmp" => sig(
            c_int_type(),
            vec![
                p("s1", signed_byte_pointer_type()),
                p("s1_len", typedef_type("size_t")),
                p("s2", signed_byte_pointer_type()),
                p("s2_len", typedef_type("size_t")),
            ],
        ),
        "filenvercmp" => sig(
            c_int_type(),
            vec![
                p("a", signed_byte_pointer_type()),
                p("alen", typedef_type("ptrdiff_t")),
                p("b", signed_byte_pointer_type()),
                p("blen", typedef_type("ptrdiff_t")),
            ],
        ),
        "mpsort_with_tmp.part.0" => sig(
            CTypeLike::Void,
            vec![
                p("files", typedef_pointer_type("sortfile")),
                p("nfiles", typedef_type("size_t")),
                p("tmp", typedef_pointer_type("sortfile")),
                p("output", typedef_pointer_type("FILE")),
                p("lines", typedef_pointer_type("line")),
            ],
        ),
        "gobble_file.constprop.0" => sig(
            typedef_type("uintmax_t"),
            vec![
                p("name", signed_byte_pointer_type()),
                p("type", typedef_type("filetype")),
                p("inode", typedef_type("ino_t")),
                p("command_line_arg", CTypeLike::Bool),
                p("dirname", signed_byte_pointer_type()),
            ],
        ),
        "print_dir" => sig(
            CTypeLike::Void,
            vec![
                p("name", signed_byte_pointer_type()),
                p("realname", signed_byte_pointer_type()),
                p("command_line_arg", CTypeLike::Bool),
            ],
        ),
        "extract_dirs_from_files" => sig(
            CTypeLike::Void,
            vec![
                p("dirname", signed_byte_pointer_type()),
                p("command_line_arg", CTypeLike::Bool),
            ],
        ),
        "fdfile_has_aclinfo" => sig(
            CTypeLike::Bool,
            vec![
                p("fd", c_int_type()),
                p("name", signed_byte_pointer_type()),
                p("ai", typedef_pointer_type("aclinfo")),
                p("flags", c_int_type()),
            ],
        ),
        "human_readable" => sig(
            signed_byte_pointer_type(),
            vec![
                p("n", typedef_type("uintmax_t")),
                p("buf", signed_byte_pointer_type()),
                p("opts", c_int_type()),
                p("from_block_size", typedef_type("uintmax_t")),
                p("to_block_size", typedef_type("uintmax_t")),
            ],
        ),
        "quotearg_buffer_restyled" => sig(
            typedef_type("size_t"),
            vec![
                p("buffer", signed_byte_pointer_type()),
                p("buffersize", typedef_type("size_t")),
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
                p(
                    "quoting_style",
                    CTypeLike::Enum("quoting_style".to_string()),
                ),
                p("flags", c_int_type()),
                p(
                    "quote_these_too",
                    CTypeLike::Pointer(Box::new(c_uint_type())),
                ),
                p("left_quote", signed_byte_pointer_type()),
                p("right_quote", signed_byte_pointer_type()),
            ],
        ),
        "clone_quoting_options" => sig(
            typedef_pointer_type("quoting_options"),
            vec![p("options", typedef_pointer_type("quoting_options"))],
        ),
        "get_quoting_style" => sig(
            CTypeLike::Enum("quoting_style".to_string()),
            vec![p("options", typedef_pointer_type("quoting_options"))],
        ),
        "set_quoting_style" => sig(
            CTypeLike::Void,
            vec![
                p("options", typedef_pointer_type("quoting_options")),
                p("style", CTypeLike::Enum("quoting_style".to_string())),
            ],
        ),
        "set_char_quoting" => sig(
            c_int_type(),
            vec![
                p("options", typedef_pointer_type("quoting_options")),
                p("ch", signed_int_type(8)),
                p("value", c_int_type()),
            ],
        ),
        "set_quoting_flags" => sig(
            c_int_type(),
            vec![
                p("options", typedef_pointer_type("quoting_options")),
                p("flags", c_int_type()),
            ],
        ),
        "set_custom_quoting" => sig(
            CTypeLike::Void,
            vec![
                p("options", typedef_pointer_type("quoting_options")),
                p("left_quote", signed_byte_pointer_type()),
                p("right_quote", signed_byte_pointer_type()),
            ],
        ),
        "quotearg_buffer" => sig(
            typedef_type("size_t"),
            vec![
                p("buffer", signed_byte_pointer_type()),
                p("buffersize", typedef_type("size_t")),
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
                p("options", typedef_pointer_type("quoting_options")),
            ],
        ),
        "quotearg_alloc" => sig(
            signed_byte_pointer_type(),
            vec![
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
                p("options", typedef_pointer_type("quoting_options")),
            ],
        ),
        "quotearg_alloc_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
                p("size", typedef_pointer_type("size_t")),
                p("options", typedef_pointer_type("quoting_options")),
            ],
        ),
        "quotearg_n_options" => sig(
            signed_byte_pointer_type(),
            vec![
                p("n", c_int_type()),
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
                p("options", typedef_pointer_type("quoting_options")),
            ],
        ),
        "quotearg_n" => sig(
            signed_byte_pointer_type(),
            vec![p("n", c_int_type()), p("arg", signed_byte_pointer_type())],
        ),
        "quotearg" => sig(
            signed_byte_pointer_type(),
            vec![p("arg", signed_byte_pointer_type())],
        ),
        "quotearg_n_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("n", c_int_type()),
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
            ],
        ),
        "quotearg_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
            ],
        ),
        "quotearg_n_style" => sig(
            signed_byte_pointer_type(),
            vec![
                p("n", c_int_type()),
                p("style", CTypeLike::Enum("quoting_style".to_string())),
                p("arg", signed_byte_pointer_type()),
            ],
        ),
        "quotearg_n_style_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("n", c_int_type()),
                p("style", CTypeLike::Enum("quoting_style".to_string())),
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
            ],
        ),
        "quotearg_style" => sig(
            signed_byte_pointer_type(),
            vec![
                p("style", CTypeLike::Enum("quoting_style".to_string())),
                p("arg", signed_byte_pointer_type()),
            ],
        ),
        "quotearg_style_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("style", CTypeLike::Enum("quoting_style".to_string())),
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
            ],
        ),
        "quotearg_char" => sig(
            signed_byte_pointer_type(),
            vec![
                p("arg", signed_byte_pointer_type()),
                p("ch", signed_int_type(8)),
            ],
        ),
        "quotearg_char_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
                p("ch", signed_int_type(8)),
            ],
        ),
        "quotearg_colon" => sig(
            signed_byte_pointer_type(),
            vec![p("arg", signed_byte_pointer_type())],
        ),
        "quotearg_colon_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
            ],
        ),
        "quotearg_n_style_colon" => sig(
            signed_byte_pointer_type(),
            vec![
                p("n", c_int_type()),
                p("style", CTypeLike::Enum("quoting_style".to_string())),
                p("arg", signed_byte_pointer_type()),
            ],
        ),
        "quotearg_n_custom" => sig(
            signed_byte_pointer_type(),
            vec![
                p("n", c_int_type()),
                p("left_quote", signed_byte_pointer_type()),
                p("right_quote", signed_byte_pointer_type()),
                p("arg", signed_byte_pointer_type()),
            ],
        ),
        "quotearg_n_custom_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("n", c_int_type()),
                p("left_quote", signed_byte_pointer_type()),
                p("right_quote", signed_byte_pointer_type()),
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
            ],
        ),
        "quotearg_custom" => sig(
            signed_byte_pointer_type(),
            vec![
                p("left_quote", signed_byte_pointer_type()),
                p("right_quote", signed_byte_pointer_type()),
                p("arg", signed_byte_pointer_type()),
            ],
        ),
        "quotearg_custom_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("left_quote", signed_byte_pointer_type()),
                p("right_quote", signed_byte_pointer_type()),
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
            ],
        ),
        "quote_n_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("n", c_int_type()),
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
            ],
        ),
        "quote_mem" => sig(
            signed_byte_pointer_type(),
            vec![
                p("arg", signed_byte_pointer_type()),
                p("argsize", typedef_type("size_t")),
            ],
        ),
        "quote_n" => sig(
            signed_byte_pointer_type(),
            vec![p("n", c_int_type()), p("arg", signed_byte_pointer_type())],
        ),
        "quote" => sig(
            signed_byte_pointer_type(),
            vec![p("arg", signed_byte_pointer_type())],
        ),
        "quotearg_free" => sig(CTypeLike::Void, Vec::new()),
        "rpl_mbrtoc32" | "mbrtoc32" => sig(
            typedef_type("size_t"),
            vec![
                p("pwc", typedef_pointer_type("char32_t")),
                p("s", signed_byte_pointer_type()),
                p("n", typedef_type("size_t")),
                p("ps", typedef_pointer_type("mbstate_t")),
            ],
        ),
        "rpl_mbrtowc" | "mbrtowc" => sig(
            typedef_type("size_t"),
            vec![
                p("pwc", typedef_pointer_type("wchar_t")),
                p("s", signed_byte_pointer_type()),
                p("n", typedef_type("size_t")),
                p("ps", typedef_pointer_type("mbstate_t")),
            ],
        ),
        "mbsnwidth" => sig(
            c_int_type(),
            vec![
                p("string", signed_byte_pointer_type()),
                p("nbytes", typedef_type("size_t")),
                p("flags", c_int_type()),
            ],
        ),
        "strnumcmp" => sig(
            c_int_type(),
            vec![
                p("a", signed_byte_pointer_type()),
                p("b", signed_byte_pointer_type()),
                p("decimal_point", c_int_type()),
                p("thousands_sep", c_int_type()),
            ],
        ),
        "strintcmp" => sig(
            c_int_type(),
            vec![
                p("a", signed_byte_pointer_type()),
                p("b", signed_byte_pointer_type()),
            ],
        ),
        "xstrtoumax" => sig(
            typedef_type("strtol_error"),
            vec![
                p("nptr", signed_byte_pointer_type()),
                p("endptr", signed_byte_pointer_pointer_type()),
                p("base", c_int_type()),
                p("val", typedef_pointer_type("uintmax_t")),
                p("valid_suffixes", signed_byte_pointer_type()),
            ],
        ),
        "xstrtoimax" => sig(
            typedef_type("strtol_error"),
            vec![
                p("nptr", signed_byte_pointer_type()),
                p("endptr", signed_byte_pointer_pointer_type()),
                p("base", c_int_type()),
                p("val", typedef_pointer_type("intmax_t")),
                p("valid_suffixes", signed_byte_pointer_type()),
            ],
        ),
        "vstrtoimax" => sig(
            typedef_type("intmax_t"),
            vec![p("s", signed_byte_pointer_type())],
        ),
        "digest_file" | "digest_file.isra.0" => sig(
            CTypeLike::Bool,
            vec![
                p("filename", signed_byte_pointer_type()),
                p("digest", unsigned_byte_pointer_type()),
                p("digest_len", typedef_type("size_t")),
            ],
        ),
        "write_counts" => sig(
            CTypeLike::Void,
            vec![
                p("lines", typedef_type("uintmax_t")),
                p("words", typedef_type("uintmax_t")),
                p("chars", typedef_type("uintmax_t")),
                p("bytes", typedef_type("uintmax_t")),
                p("linelength", typedef_type("intmax_t")),
                p("file", signed_byte_pointer_type()),
            ],
        ),
        "shaxxx_stream" | "shaxxx_stream.isra.0" => sig(
            CTypeLike::Bool,
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("digest", unsigned_byte_pointer_type()),
                p("filename", signed_byte_pointer_type()),
            ],
        ),
        "binop" => sig(c_int_type(), vec![p("op", signed_byte_pointer_type())]),
        "binary_operator" => sig(
            CTypeLike::Bool,
            vec![
                p("lhs_is_length", CTypeLike::Bool),
                p("op", CTypeLike::Enum("binop".to_string())),
            ],
        ),
        "unary_operator" => sig(CTypeLike::Bool, Vec::new()),
        "or" | "three_arguments" => sig(CTypeLike::Bool, Vec::new()),
        "argmatch" => sig(
            typedef_type("ptrdiff_t"),
            vec![
                p("arg", signed_byte_pointer_type()),
                p("arglist", signed_byte_pointer_pointer_type()),
                p("vallist", typedef_pointer_type("argmatch_value")),
                p("valsize", typedef_type("size_t")),
            ],
        ),
        "__xargmatch_internal" => sig(
            typedef_type("ptrdiff_t"),
            vec![
                p("context", signed_byte_pointer_type()),
                p("arg", signed_byte_pointer_type()),
                p("arglist", signed_byte_pointer_pointer_type()),
                p("vallist", typedef_pointer_type("argmatch_value")),
                p("valsize", typedef_type("size_t")),
                p("usage_func", CTypeLike::Function),
                p("allow_abbrev", CTypeLike::Bool),
            ],
        ),
        "argmatch_exact" => sig(
            typedef_type("ptrdiff_t"),
            vec![
                p("arg", signed_byte_pointer_type()),
                p("arglist", signed_byte_pointer_pointer_type()),
            ],
        ),
        "argmatch_invalid" => sig(
            CTypeLike::Void,
            vec![
                p("context", signed_byte_pointer_type()),
                p("value", signed_byte_pointer_type()),
                p("problem", typedef_type("ptrdiff_t")),
            ],
        ),
        "argmatch_valid" => sig(
            CTypeLike::Void,
            vec![
                p("arglist", signed_byte_pointer_pointer_type()),
                p("vallist", typedef_pointer_type("argmatch_value")),
                p("valsize", typedef_type("size_t")),
            ],
        ),
        "argmatch_to_argument" => sig(
            signed_byte_pointer_type(),
            vec![
                p("value", typedef_pointer_type("argmatch_value")),
                p("arglist", signed_byte_pointer_pointer_type()),
                p("vallist", typedef_pointer_type("argmatch_value")),
                p("valsize", typedef_type("size_t")),
            ],
        ),
        "error" => error_signature(current_param_count),
        "error_at_line" => error_at_line_signature(current_param_count),
        "error_tail" | "verror" => verror_signature(current_param_count),
        "print_errno_message" => sig(CTypeLike::Void, vec![p("errnum", c_int_type())]),
        "verror_at_line" => sig(
            CTypeLike::Void,
            vec![
                p("status", c_int_type()),
                p("errnum", c_int_type()),
                p("file_name", signed_byte_pointer_type()),
                p("line_number", c_uint_type()),
                p("message", signed_byte_pointer_type()),
                p("args", typedef_pointer_type("__va_list_tag")),
            ],
        ),
        "printf_parse" => sig(
            c_int_type(),
            vec![
                p("format", signed_byte_pointer_type()),
                p("directives", typedef_pointer_type("printf_directive")),
                p("arguments", typedef_pointer_type("arguments")),
            ],
        ),
        "print_formatted" => sig(
            c_int_type(),
            vec![
                p("format", signed_byte_pointer_type()),
                p("argc", c_int_type()),
                p("argv", signed_byte_pointer_pointer_type()),
            ],
        ),
        "print_esc" => sig(
            c_int_type(),
            vec![
                p("escstart", signed_byte_pointer_type()),
                p("octal_0", CTypeLike::Bool),
            ],
        ),
        "print_xfer_stats" => sig(
            CTypeLike::Void,
            vec![p("progress_time", typedef_type("xtime_t"))],
        ),
        "unicode_to_mb" => sig(
            typedef_type("long"),
            vec![
                p("code", c_uint_type()),
                p("success", typedef_pointer_type("unicode_success_callback")),
                p("failure", typedef_pointer_type("unicode_failure_callback")),
                p(
                    "callback_arg",
                    typedef_pointer_type("unicode_callback_context"),
                ),
            ],
        ),
        "vasnprintf" => sig(
            signed_byte_pointer_type(),
            vec![
                p("resultbuf", signed_byte_pointer_type()),
                p("lengthp", typedef_pointer_type("size_t")),
                p("format", signed_byte_pointer_type()),
                p("args", typedef_pointer_type("__va_list_tag")),
            ],
        ),
        "rpl_fopen" => sig(
            typedef_pointer_type("FILE"),
            vec![
                p("filename", signed_byte_pointer_type()),
                p("mode", signed_byte_pointer_type()),
            ],
        ),
        "fd_safer" => sig(c_int_type(), vec![p("fd", c_int_type())]),
        "fadvise" => sig(
            CTypeLike::Void,
            vec![
                p("fp", typedef_pointer_type("FILE")),
                p("advice", typedef_type("fadvice_t")),
            ],
        ),
        "opendirat" => sig(
            typedef_pointer_type("DIR"),
            vec![
                p("dir_fd", c_int_type()),
                p("dir", signed_byte_pointer_type()),
                p("extra_flags", c_int_type()),
                p("pnew_fd", CTypeLike::Pointer(Box::new(c_int_type()))),
            ],
        ),
        "stream_open" => sig(
            typedef_pointer_type("FILE"),
            vec![
                p("file", signed_byte_pointer_type()),
                p("how", signed_byte_pointer_type()),
            ],
        ),
        "openat_safer" => openat_safer_signature(current_param_count),
        "rpl_fcntl" => sig(
            c_int_type(),
            vec![
                p("fd", c_int_type()),
                p("action", c_int_type()),
                p("arg", typedef_type("fcntl_arg")),
            ],
        ),
        "freopen_safer" => sig(
            typedef_pointer_type("FILE"),
            vec![
                p("filename", signed_byte_pointer_type()),
                p("mode", signed_byte_pointer_type()),
                p("stream", typedef_pointer_type("FILE")),
            ],
        ),
        "find_field" | "find_field.isra.0" => sig(
            signed_byte_pointer_type(),
            vec![
                p("line", signed_byte_pointer_type()),
                p("field", typedef_type("size_t")),
            ],
        ),
        "begfield" | "limfield" => sig(
            signed_byte_pointer_type(),
            vec![
                p("line", typedef_pointer_type("line")),
                p("key", typedef_pointer_type("keyfield")),
            ],
        ),
        "begfield.isra.0" | "limfield.isra.0" => sig(
            signed_byte_pointer_type(),
            vec![
                p("line", typedef_pointer_type("line")),
                p("field", typedef_type("size_t")),
                p("offset", typedef_type("size_t")),
            ],
        ),
        "key_to_opts" => sig(
            CTypeLike::Void,
            vec![
                p("key", typedef_pointer_type("keyfield")),
                p("opts", signed_byte_pointer_type()),
            ],
        ),
        "sequential_sort" => sig(
            CTypeLike::Void,
            vec![
                p("lines", typedef_pointer_type("line")),
                p("nlines", typedef_type("size_t")),
                p("temp", typedef_pointer_type("line")),
                p("to_temp", CTypeLike::Bool),
            ],
        ),
        "skip" => sig(
            typedef_type("intmax_t"),
            vec![
                p("fdesc", c_int_type()),
                p("file", signed_byte_pointer_type()),
                p("records", typedef_type("intmax_t")),
                p("blocksize", typedef_type("idx_t")),
                p("bytes", typedef_pointer_type("idx_t")),
            ],
        ),
        "wc" => sig(
            CTypeLike::Bool,
            vec![
                p("fd", c_int_type()),
                p("file_x", signed_byte_pointer_type()),
                p("fstatus", typedef_pointer_type("fstatus")),
            ],
        ),
        "is_utf8_charset" => sig(CTypeLike::Bool, Vec::new()),
        "mcel_scan" => sig(
            typedef_type("mcel_t"),
            vec![
                p("p", signed_byte_pointer_type()),
                p("lim", signed_byte_pointer_type()),
            ],
        ),
        "mcel_cmp" => sig(
            c_int_type(),
            vec![
                p("left", typedef_type("mcel_t")),
                p("right", typedef_type("mcel_t")),
            ],
        ),
        "mcel_tocmp" => sig(
            c_int_type(),
            vec![
                p("to", typedef_type("wint_transform")),
                p("c1", typedef_type("mcel_t")),
                p("c2", typedef_type("mcel_t")),
            ],
        ),
        "mcel_scant" => sig(
            typedef_type("mcel_t"),
            vec![
                p("p", signed_byte_pointer_type()),
                p("terminator", signed_int_type(8)),
            ],
        ),
        "copy" => sig(
            CTypeLike::Bool,
            vec![
                p("src_name", signed_byte_pointer_type()),
                p("dst_name", signed_byte_pointer_type()),
                p("dst_dirfd", c_int_type()),
                p("dst_relname", signed_byte_pointer_type()),
                p("nonexistent_dst", c_int_type()),
                p("options", typedef_pointer_type("cp_options")),
                p(
                    "copy_into_self",
                    CTypeLike::Pointer(Box::new(CTypeLike::Bool)),
                ),
                p(
                    "rename_succeeded",
                    CTypeLike::Pointer(Box::new(CTypeLike::Bool)),
                ),
            ],
        ),
        "emit_verbose" => sig(
            CTypeLike::Void,
            vec![
                p("format", signed_byte_pointer_type()),
                p("src", signed_byte_pointer_type()),
                p("dst", signed_byte_pointer_type()),
                p("backup_dst_name", signed_byte_pointer_type()),
            ],
        ),
        "do_move" => sig(
            CTypeLike::Bool,
            vec![
                p("source", signed_byte_pointer_type()),
                p("dest", signed_byte_pointer_type()),
                p("dest_dirfd", c_int_type()),
                p("dest_relname", signed_byte_pointer_type()),
                p("x", typedef_pointer_type("cp_options")),
            ],
        ),
        "overwrite_ok" => sig(
            CTypeLike::Bool,
            vec![
                p("x", typedef_pointer_type("cp_options")),
                p("dst_name", signed_byte_pointer_type()),
                p("dst_dirfd", c_int_type()),
                p("dst_relname", signed_byte_pointer_type()),
                p("dst_sb", typedef_pointer_type("stat")),
            ],
        ),
        "areadlinkat_with_size" => sig(
            signed_byte_pointer_type(),
            vec![
                p("fd", c_int_type()),
                p("file", signed_byte_pointer_type()),
                p("size", typedef_type("size_t")),
            ],
        ),
        "areadlink_with_size" => sig(
            signed_byte_pointer_type(),
            vec![
                p("filename", signed_byte_pointer_type()),
                p("size_hint", typedef_type("size_t")),
            ],
        ),
        "mfile_name_concat" => sig(
            signed_byte_pointer_type(),
            vec![
                p("dir", signed_byte_pointer_type()),
                p("base", signed_byte_pointer_type()),
                p("base_in_result", signed_byte_pointer_pointer_type()),
            ],
        ),
        "set_owner.isra.0" | "set_owner" => sig(
            c_int_type(),
            vec![
                p("x", typedef_pointer_type("cp_options")),
                p("dst_name", signed_byte_pointer_type()),
                p("dst_dirfd", c_int_type()),
                p("dst_relname", signed_byte_pointer_type()),
                p("dest_desc", c_int_type()),
                p("src_sb", typedef_pointer_type("stat")),
                p("new_dst", CTypeLike::Bool),
                p("dst_sb", typedef_pointer_type("stat")),
            ],
        ),
        "set_process_security_ctx" => sig(
            CTypeLike::Bool,
            vec![
                p("src_name", signed_byte_pointer_type()),
                p("dst_name", signed_byte_pointer_type()),
                p("mode", typedef_type("mode_t")),
                p("new_dst", CTypeLike::Bool),
                p("x", typedef_pointer_type("cp_options")),
            ],
        ),
        "rpl_getfilecon" | "rpl_getfilecon_raw" | "rpl_lgetfilecon" | "rpl_lgetfilecon_raw" => sig(
            c_int_type(),
            vec![
                p("file", signed_byte_pointer_type()),
                p("con", signed_byte_pointer_pointer_type()),
            ],
        ),
        "same_nameat" => sig(
            CTypeLike::Bool,
            vec![
                p("source_dfd", c_int_type()),
                p("source", signed_byte_pointer_type()),
                p("dest_dfd", c_int_type()),
                p("dest", signed_byte_pointer_type()),
            ],
        ),
        "force_linkat" => sig(
            c_int_type(),
            vec![
                p("srcdir", c_int_type()),
                p("srcname", signed_byte_pointer_type()),
                p("dstdir", c_int_type()),
                p("dstname", signed_byte_pointer_type()),
                p("flags", c_int_type()),
                p("force", CTypeLike::Bool),
                p("linkat_errno", c_int_type()),
            ],
        ),
        "force_symlinkat" => sig(
            c_int_type(),
            vec![
                p("srcname", signed_byte_pointer_type()),
                p("dstdir", c_int_type()),
                p("dstname", signed_byte_pointer_type()),
                p("force", CTypeLike::Bool),
                p("symlinkat_errno", c_int_type()),
            ],
        ),
        "strmode" => sig(
            CTypeLike::Void,
            vec![
                p("mode", typedef_type("mode_t")),
                p("str", signed_byte_pointer_type()),
            ],
        ),
        "do_statx" => sig(
            c_int_type(),
            vec![
                p("fd", c_int_type()),
                p("name", signed_byte_pointer_type()),
                p("st", typedef_pointer_type("stat")),
                p("flags", c_int_type()),
                p("mask", c_uint_type()),
            ],
        ),
        "getuidbyname" => sig(
            typedef_pointer_type("uid_t"),
            vec![p("user", signed_byte_pointer_type())],
        ),
        "setlocale_null_r_unlocked" => sig(
            c_int_type(),
            vec![
                p("category", c_int_type()),
                p("buf", signed_byte_pointer_type()),
                p("bufsize", typedef_type("size_t")),
            ],
        ),
        "hard_locale" => sig(CTypeLike::Bool, vec![p("category", c_int_type())]),
        "set_program_name" => sig(
            CTypeLike::Void,
            vec![p("argv0", signed_byte_pointer_type())],
        ),
        "keycompare" => sig(
            c_int_type(),
            vec![
                p("a", typedef_pointer_type("line")),
                p("b", typedef_pointer_type("line")),
            ],
        ),
        "__strftime_internal.isra.0" => sig(
            typedef_type("retval_t"),
            vec![
                p("s", typedef_pointer_type("FILE")),
                p("maxsize", typedef_type("size_t")),
                p("format", signed_byte_pointer_type()),
                p("tp", typedef_pointer_type("tm")),
                p("upcase", CTypeLike::Bool),
                p("yr_spec", CTypeLike::Enum("pad_style".to_string())),
            ],
        ),
        "nstrftime" | "c_nstrftime" => sig(
            typedef_type("ptrdiff_t"),
            vec![
                p("s", signed_byte_pointer_type()),
                p("maxsize", typedef_type("size_t")),
                p("format", signed_byte_pointer_type()),
                p("tp", typedef_pointer_type("tm")),
                p("tz", typedef_type("timezone_t")),
                p("ns", c_int_type()),
            ],
        ),
        "rm" => sig(
            typedef_type("RM_status"),
            vec![
                p("file", signed_byte_pointer_pointer_type()),
                p("x", typedef_pointer_type("rm_options")),
            ],
        ),
        "close_stdin" => sig(CTypeLike::Void, Vec::new()),
        "write_line" => sig(
            CTypeLike::Void,
            vec![
                p("line", typedef_pointer_type("line")),
                p("fp", typedef_pointer_type("FILE")),
                p("output_file", signed_byte_pointer_type()),
            ],
        ),
        "readlinebuffer_delim" => sig(
            typedef_pointer_type("linebuffer"),
            vec![
                p("linebuffer", typedef_pointer_type("linebuffer")),
                p("stream", typedef_pointer_type("FILE")),
                p("delimiter", signed_int_type(8)),
            ],
        ),
        "mergefps" => sig(
            CTypeLike::Void,
            vec![
                p("files", typedef_pointer_type("sortfile")),
                p("ntemps", typedef_type("size_t")),
                p("nfiles", typedef_type("size_t")),
                p("ofp", typedef_pointer_type("FILE")),
                p("output_file", signed_byte_pointer_type()),
                p(
                    "fps",
                    CTypeLike::Pointer(Box::new(typedef_pointer_type("FILE"))),
                ),
            ],
        ),
        "open_input_files" => sig(
            typedef_type("size_t"),
            vec![
                p("files", typedef_pointer_type("sortfile")),
                p("nfiles", typedef_type("size_t")),
                p(
                    "pfps",
                    CTypeLike::Pointer(Box::new(CTypeLike::Pointer(Box::new(
                        typedef_pointer_type("FILE"),
                    )))),
                ),
            ],
        ),
        "sortlines" => sig(
            CTypeLike::Void,
            vec![
                p("lines", typedef_pointer_type("line")),
                p("nthreads", typedef_type("size_t")),
                p("total_lines", typedef_type("size_t")),
                p("node", typedef_pointer_type("merge_node")),
                p("queue", typedef_pointer_type("merge_node_queue")),
                p("tfp", typedef_pointer_type("FILE")),
                p("temp_output", signed_byte_pointer_type()),
            ],
        ),
        "pipe_child" => sig(
            c_int_type(),
            vec![
                p("pid", typedef_pointer_type("pid_t")),
                p("pipefds", CTypeLike::Pointer(Box::new(c_int_type()))),
                p("tempfd", c_int_type()),
                p("decompress", CTypeLike::Bool),
                p("tries", typedef_type("size_t")),
            ],
        ),
        "rpl_pipe2" | "pipe2" => sig(
            c_int_type(),
            vec![
                p("pipefds", CTypeLike::Pointer(Box::new(c_int_type()))),
                p("flags", c_int_type()),
            ],
        ),
        "merge" => sig(
            CTypeLike::Void,
            vec![
                p("files", typedef_pointer_type("sortfile")),
                p("ntemps", typedef_type("size_t")),
                p("nfiles", typedef_type("size_t")),
                p("output_file", signed_byte_pointer_type()),
            ],
        ),
        "mergefiles" => sig(
            typedef_type("size_t"),
            vec![
                p("files", struct_pointer_type("sortfile")),
                p("ntemps", typedef_type("size_t")),
                p("nfiles", typedef_type("size_t")),
                p("ofp", typedef_pointer_type("FILE")),
                p("output_file", signed_byte_pointer_type()),
            ],
        ),
        "init_node" => sig(
            struct_pointer_type("merge_node"),
            vec![
                p("parent", struct_pointer_type("merge_node")),
                p("node_pool", struct_pointer_type("merge_node")),
                p("dest", struct_pointer_type("line")),
                p("nthreads", typedef_type("size_t")),
                p("nlines", typedef_type("size_t")),
                p("is_lo_child", CTypeLike::Bool),
            ],
        ),
        "sort_files" => sig(CTypeLike::Void, Vec::new()),
        "fts_stat" => sig(
            c_int_type(),
            vec![
                p("sp", typedef_pointer_type("FTS")),
                p("p", typedef_pointer_type("FTSENT")),
                p("follow", CTypeLike::Bool),
            ],
        ),
        "leave_dir" => sig(
            CTypeLike::Void,
            vec![
                p("fts", typedef_pointer_type("FTS")),
                p("entry", typedef_pointer_type("FTSENT")),
            ],
        ),
        "find_entry" => param_only_sig(vec![
            p("fts", typedef_pointer_type("FTS")),
            p("entry", typedef_pointer_type("FTSENT")),
            p("parent", typedef_pointer_type("FTSENT")),
        ]),
        "rpl_fts_children" => sig(
            typedef_pointer_type("FTSENT"),
            vec![
                p("sp", typedef_pointer_type("FTS")),
                p("instr", c_int_type()),
            ],
        ),
        "transfer_entries" => sig(
            CTypeLike::Void,
            vec![
                p("dst", typedef_pointer_type("FTS")),
                p("src", typedef_pointer_type("FTS")),
            ],
        ),
        "excise" => sig(
            CTypeLike::Bool,
            vec![
                p("fts", typedef_pointer_type("FTS")),
                p("ent", typedef_pointer_type("FTSENT")),
                p("x", typedef_pointer_type("rm_options")),
            ],
        ),
        "get_dir_status" => sig(
            c_int_type(),
            vec![
                p("fts", typedef_pointer_type("FTS")),
                p("ent", typedef_pointer_type("FTSENT")),
                p("dir_status", CTypeLike::Pointer(Box::new(c_int_type()))),
            ],
        ),
        "filesystem_type" => sig(
            typedef_type("fsword"),
            vec![
                p("p", typedef_pointer_type("FTSENT")),
                p("fd", c_int_type()),
            ],
        ),
        "hash_print_statistics" => sig(
            CTypeLike::Void,
            vec![
                p("table", typedef_pointer_type("hash_table")),
                p("stream", typedef_pointer_type("FILE")),
            ],
        ),
        "hash_free" | "hash_clear" => sig(
            CTypeLike::Void,
            vec![p("table", typedef_pointer_type("hash_table"))],
        ),
        "hash_lookup" | "hash_insert" => sig(
            memory_ptr_type(),
            vec![
                p("table", typedef_pointer_type("hash_table")),
                p("entry", memory_ptr_type()),
            ],
        ),
        "heap_insert" => sig(
            c_int_type(),
            vec![
                p("heap", typedef_pointer_type("heap")),
                p("item", memory_ptr_type()),
            ],
        ),
        "heap_remove_top" => sig(
            memory_ptr_type(),
            vec![p("heap", typedef_pointer_type("heap"))],
        ),
        "hash_get_first" => sig(
            memory_ptr_type(),
            vec![p("table", typedef_pointer_type("hash_table"))],
        ),
        "hash_get_next" => sig(
            memory_ptr_type(),
            vec![
                p("table", typedef_pointer_type("hash_table")),
                p("entry", memory_ptr_type()),
            ],
        ),
        "hash_get_n_buckets"
        | "hash_get_n_buckets_used"
        | "hash_get_n_entries"
        | "hash_get_max_bucket_length" => sig(
            typedef_type("size_t"),
            vec![p("table", typedef_pointer_type("hash_table"))],
        ),
        "hash_insert_if_absent" => sig(
            c_int_type(),
            vec![
                p("table", typedef_pointer_type("hash_table")),
                p("entry", memory_ptr_type()),
                p(
                    "matched_ent",
                    CTypeLike::Pointer(Box::new(memory_ptr_type())),
                ),
            ],
        ),
        "hash_get_entries" => sig(
            typedef_type("size_t"),
            vec![
                p("table", typedef_pointer_type("hash_table")),
                p("buffer", CTypeLike::Pointer(Box::new(memory_ptr_type()))),
                p("buffer_size", typedef_type("size_t")),
            ],
        ),
        "hash_do_for_each" => sig(
            c_int_type(),
            vec![
                p("table", typedef_pointer_type("hash_table")),
                p("processor", CTypeLike::Function),
                p("processor_data", memory_ptr_type()),
            ],
        ),
        "hash_reset_tuning" => sig(
            CTypeLike::Void,
            vec![p("table", typedef_pointer_type("hash_table"))],
        ),
        "hash_table_ok" => sig(
            CTypeLike::Bool,
            vec![p("table", typedef_pointer_type("hash_table"))],
        ),
        "hash_rehash" => sig(
            CTypeLike::Bool,
            vec![
                p("table", typedef_pointer_type("hash_table")),
                p("candidate", typedef_type("size_t")),
            ],
        ),
        "hash_remove" => sig(
            memory_ptr_type(),
            vec![
                p("table", typedef_pointer_type("hash_table")),
                p("entry", memory_ptr_type()),
            ],
        ),
        "fillbuf" => sig(
            CTypeLike::Bool,
            vec![
                p("file", typedef_pointer_type("sortfile")),
                p("buf", signed_byte_pointer_type()),
                p("buf_size", typedef_type("size_t")),
            ],
        ),
        "maybe_create_temp" => sig(
            typedef_pointer_type("sortfile"),
            vec![
                p("file", typedef_pointer_type("sortfile")),
                p("small", CTypeLike::Bool),
            ],
        ),
        "find_in_given_path" => sig(
            signed_byte_pointer_type(),
            vec![
                p("progname", signed_byte_pointer_type()),
                p("path", signed_byte_pointer_type()),
            ],
        ),
        "get_cgroup2_cpu_quota" => sig(
            CTypeLike::Bool,
            vec![
                p("path", signed_byte_pointer_type()),
                p("quota", typedef_pointer_type("uintmax_t")),
                p("period", typedef_pointer_type("uintmax_t")),
                p("limited", CTypeLike::Pointer(Box::new(CTypeLike::Bool))),
            ],
        ),
        "gregorian_to_persian" => sig(
            c_int_type(),
            vec![
                p("result", typedef_pointer_type("calendar_date")),
                p("greg_year", c_int_type()),
                p("greg_month", c_int_type()),
                p("greg_day", c_int_type()),
            ],
        ),
        "gregorian_to_ethiopian" => sig(
            c_int_type(),
            vec![
                p("result", typedef_pointer_type("calendar_date")),
                p("greg_year", c_int_type()),
                p("greg_month", c_int_type()),
                p("greg_day", c_int_type()),
            ],
        ),
        "cycle_check_init" => sig(
            CTypeLike::Void,
            vec![p("state", typedef_pointer_type("cycle_check_state"))],
        ),
        "cycle_check" => sig(
            CTypeLike::Bool,
            vec![
                p("state", typedef_pointer_type("cycle_check_state")),
                p("sb", typedef_pointer_type("stat")),
            ],
        ),
        "next_prime" => sig(
            typedef_type("size_t"),
            vec![p("candidate", typedef_type("size_t"))],
        ),
        "isaac_refill" | "isaac_seed" => sig(
            CTypeLike::Void,
            vec![p("source", typedef_pointer_type("randread_source"))],
        ),
        "randread" => param_only_sig(vec![
            p("source", typedef_pointer_type("randread_source")),
            p("buf", signed_byte_pointer_type()),
            p("size", typedef_type("size_t")),
        ]),
        "randread_new" => sig(
            typedef_pointer_type("randread_source"),
            vec![
                p("name", signed_byte_pointer_type()),
                p("bytes_bound", typedef_type("size_t")),
            ],
        ),
        "randperm_new" => sig(
            typedef_pointer_type("size_t"),
            vec![
                p("r", struct_pointer_type("randint_source")),
                p("h", typedef_type("size_t")),
                p("n", typedef_type("size_t")),
            ],
        ),
        "wc_lines_avx2" | "wc_lines_avx512" => sig(
            typedef_type("wc_lines"),
            vec![
                p("buf", signed_byte_pointer_type()),
                p("len", typedef_type("size_t")),
            ],
        ),
        "readtoken" => sig(
            typedef_type("size_t"),
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("delim", signed_byte_pointer_type()),
                p("n_delim", typedef_type("size_t")),
                p("tokenbuffer", typedef_pointer_type("token_buffer")),
            ],
        ),
        "readtokens" => sig(
            typedef_type("size_t"),
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p("projected_n_tokens", typedef_type("size_t")),
                p("delim", signed_byte_pointer_type()),
                p("n_delim", typedef_type("size_t")),
                p(
                    "tokens_out",
                    CTypeLike::Pointer(Box::new(signed_byte_pointer_pointer_type())),
                ),
                p(
                    "token_lengths",
                    CTypeLike::Pointer(Box::new(typedef_pointer_type("size_t"))),
                ),
            ],
        ),
        "readtokens0" => sig(
            CTypeLike::Bool,
            vec![
                p("stream", typedef_pointer_type("FILE")),
                p(
                    "tokens_out",
                    CTypeLike::Pointer(Box::new(signed_byte_pointer_pointer_type())),
                ),
                p("count_out", typedef_pointer_type("size_t")),
            ],
        ),
        "add_range_pair" => sig(
            CTypeLike::Void,
            vec![
                p("lo", typedef_type("uintmax_t")),
                p("hi", typedef_type("uintmax_t")),
            ],
        ),
        "try_tempname_len" => sig(
            c_int_type(),
            vec![
                p("tmpl", signed_byte_pointer_type()),
                p("suffixlen", c_int_type()),
                p("args", typedef_pointer_type("tempname_args")),
                p("tryfunc", typedef_type("tempname_tryfunc")),
                p("x_suffix_len", typedef_type("size_t")),
            ],
        ),
        "close_stdout" => sig(CTypeLike::Void, Vec::new()),
        "rpl_fclose" => sig(c_int_type(), vec![p("fp", typedef_pointer_type("FILE"))]),
        "write_bytes" => sig(
            CTypeLike::Void,
            vec![
                p("buf", signed_byte_pointer_type()),
                p("n_bytes", typedef_type("size_t")),
            ],
        ),
        "yesno" => sig(CTypeLike::Bool, Vec::new()),
        "posix2_version" => sig(c_int_type(), Vec::new()),
        "parse_field_count" => sig(
            signed_byte_pointer_type(),
            vec![
                p("string", signed_byte_pointer_type()),
                p("val", typedef_pointer_type("size_t")),
                p("msgid", signed_byte_pointer_type()),
            ],
        ),
        "cwd_advance_fd" => sig(
            CTypeLike::Void,
            vec![
                p("sp", typedef_pointer_type("FTS")),
                p("fd", c_int_type()),
                p("chdir_down_one", CTypeLike::Bool),
            ],
        ),
        "restore_initial_cwd" => sig(c_int_type(), vec![p("sp", typedef_pointer_type("FTS"))]),
        "fts_sort" => sig(
            typedef_pointer_type("FTSENT"),
            vec![
                p("sp", typedef_pointer_type("FTS")),
                p("head", typedef_pointer_type("FTSENT")),
                p("nitems", typedef_type("size_t")),
            ],
        ),
        "get_root_dev_ino" => sig(
            struct_pointer_type("dev_ino"),
            vec![p("root_d_i", struct_pointer_type("dev_ino"))],
        ),
        "get_meminfo" => sig(
            CTypeLike::Bool,
            vec![
                p("total_out", typedef_pointer_type("uintmax_t")),
                p("available_out", typedef_pointer_type("uintmax_t")),
            ],
        ),
        "physmem_total" => sig(typedef_type("uintmax_t"), Vec::new()),
        "physmem_claimable" => sig(
            CTypeLike::Float(64),
            vec![p("aggressivity", CTypeLike::Float(64))],
        ),
        "num_processors" => sig(
            c_ulong_type(),
            vec![p("query", CTypeLike::Enum("nproc_query".to_string()))],
        ),
        "rpl_obstack_newchunk" => sig(
            CTypeLike::Void,
            vec![
                p("h", typedef_pointer_type("obstack")),
                p("length", typedef_type("size_t")),
            ],
        ),
        "_gl_scratch_buffer_grow" | "_gl_scratch_buffer_grow_preserve" => sig(
            CTypeLike::Bool,
            vec![p("buffer", struct_pointer_type("scratch_buffer"))],
        ),
        "xmalloc" => sig(
            allocation_ptr_type(),
            vec![p("size", typedef_type("size_t"))],
        ),
        "ximalloc" => sig(
            allocation_ptr_type(),
            vec![p("size", typedef_type("idx_t"))],
        ),
        "xcharalloc" => sig(
            signed_byte_pointer_type(),
            vec![p("n", typedef_type("size_t"))],
        ),
        "xzalloc" => sig(
            allocation_ptr_type(),
            vec![p("size", typedef_type("size_t"))],
        ),
        "xizalloc" => sig(
            allocation_ptr_type(),
            vec![p("size", typedef_type("idx_t"))],
        ),
        "xcalloc" => sig(
            allocation_ptr_type(),
            vec![
                p("n", typedef_type("size_t")),
                p("size", typedef_type("size_t")),
            ],
        ),
        "xicalloc" => sig(
            allocation_ptr_type(),
            vec![
                p("n", typedef_type("idx_t")),
                p("size", typedef_type("idx_t")),
            ],
        ),
        "xrealloc" => sig(
            allocation_ptr_type(),
            vec![
                p("ptr", allocation_ptr_type()),
                p("size", typedef_type("size_t")),
            ],
        ),
        "xirealloc" => sig(
            allocation_ptr_type(),
            vec![
                p("ptr", allocation_ptr_type()),
                p("size", typedef_type("idx_t")),
            ],
        ),
        "xreallocarray" => sig(
            allocation_ptr_type(),
            vec![
                p("ptr", allocation_ptr_type()),
                p("n", typedef_type("size_t")),
                p("size", typedef_type("size_t")),
            ],
        ),
        "rpl_reallocarray" => sig(
            allocation_ptr_type(),
            vec![
                p("ptr", allocation_ptr_type()),
                p("n", typedef_type("size_t")),
                p("size", typedef_type("size_t")),
            ],
        ),
        "xnrealloc" => sig(
            allocation_ptr_type(),
            vec![
                p("ptr", allocation_ptr_type()),
                p("n", typedef_type("size_t")),
                p("size", typedef_type("size_t")),
            ],
        ),
        "xireallocarray" => sig(
            allocation_ptr_type(),
            vec![
                p("ptr", allocation_ptr_type()),
                p("n", typedef_type("idx_t")),
                p("size", typedef_type("idx_t")),
            ],
        ),
        "x2realloc" => sig(
            allocation_ptr_type(),
            vec![
                p("ptr", allocation_ptr_type()),
                p("size", typedef_pointer_type("size_t")),
            ],
        ),
        "x2nrealloc" => sig(
            allocation_ptr_type(),
            vec![
                p("ptr", allocation_ptr_type()),
                p("n", typedef_pointer_type("size_t")),
                p("size", typedef_type("size_t")),
            ],
        ),
        "xpalloc" => sig(
            allocation_ptr_type(),
            vec![
                p("ptr", allocation_ptr_type()),
                p("n", typedef_pointer_type("idx_t")),
                p("n_incr_min", typedef_type("idx_t")),
                p("n_max", typedef_type("ptrdiff_t")),
                p("size", typedef_type("idx_t")),
            ],
        ),
        "xnmalloc" => sig(
            allocation_ptr_type(),
            vec![
                p("n", typedef_type("size_t")),
                p("size", typedef_type("size_t")),
            ],
        ),
        "xinmalloc" => sig(
            allocation_ptr_type(),
            vec![
                p("n", typedef_type("idx_t")),
                p("size", typedef_type("idx_t")),
            ],
        ),
        "xmemdup" => sig(
            allocation_ptr_type(),
            vec![
                p("src", memory_ptr_type()),
                p("size", typedef_type("size_t")),
            ],
        ),
        "ximemdup" => sig(
            allocation_ptr_type(),
            vec![
                p("src", memory_ptr_type()),
                p("size", typedef_type("idx_t")),
            ],
        ),
        "ximemdup0" => sig(
            signed_byte_pointer_type(),
            vec![
                p("src", memory_ptr_type()),
                p("size", typedef_type("idx_t")),
            ],
        ),
        "xstrdup" => sig(
            signed_byte_pointer_type(),
            vec![p("str", signed_byte_pointer_type())],
        ),
        "xalloc_die" => sig(CTypeLike::Void, Vec::new()),
        _ => return None,
    })
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
    fn registry_normalizes_common_symbol_prefixes() {
        let signature = signature_hint_for_name_candidates(["sym.rpl_fts_read"], 0)
            .expect("expected FTS read signature");
        assert_eq!(signature.ret_type, Some(typedef_pointer_type("FTSENT")));
        assert_eq!(signature.params[0].name, "sp");
        assert_eq!(signature.params[0].ty, Some(typedef_pointer_type("FTS")));
    }

    #[test]
    fn role_identity_signature_requires_non_name_evidence() {
        let name_hint = r2sym::NativeWorkerRoleIdentity {
            role_name: r2sym::NativeWorkerSummaryKind::FormatArgumentFetch
                .canonical_role_name()
                .to_string(),
            source: r2sym::NativeWorkerRoleSource::NameHint,
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
    fn registry_covers_current_coreutils_worker_roles() {
        for name in [
            "copy_file_data",
            "sparse_copy",
            "make_dir_parents_private",
            "fts_build",
            "rpl_fts_read",
            "rpl_fts_open",
            "rpl_fts_close",
            "prompt.constprop.0",
            "skip_whitespace_run",
            "scan_mb_blank_field",
            "scan_mb_delim_field",
            "cut_fields_bytesearch",
            "fdfile_has_aclinfo",
            "__strftime_internal.isra.0",
            "_internal_fnwmatch",
            "_getopt_internal_r",
            "getopt_long",
            "digest_file.isra.0",
            "shaxxx_stream.isra.0",
            "entry0",
            "entry.fini0",
            "register_tm_clones",
            "deregister_tm_clones",
            "_init",
            "entry.init0",
            "usage",
            "binop",
            "binary_operator",
            "unary_operator",
            "argmatch",
            "argmatch_exact",
            "__xargmatch_internal",
            "verror_at_line",
            "write_counts",
            "defaultcon",
            "restorecon_private",
            "restorecon",
            "re_protect",
            "renameatu",
            "streamsavedir",
            "clone_quoting_options",
            "get_quoting_style",
            "set_quoting_style",
            "set_char_quoting",
            "set_quoting_flags",
            "set_custom_quoting",
            "quotearg_alloc_mem",
            "quotearg_n_options",
            "quotearg_n_custom_mem",
            "quote_n_mem",
            "quotearg_free",
            "version_etc_arn",
            "version_etc_ar",
            "version_etc_va",
            "version_etc",
            "emit_bug_reporting_address",
            "xpalloc",
            "xmalloc",
            "xrealloc",
            "xnrealloc",
            "xnmalloc",
            "xmemdup",
            "xstrdup",
            "xalloc_die",
            "rpl_mbrtowc",
            "printf_parse",
            "oprintf_.constprop.0",
            "print_xfer_stats",
            "unicode_to_mb",
            "rpl_fopen",
            "rpl_nanosleep",
            "xnanosleep",
            "rpl_fcntl",
            "vstrtoimax",
            "find_field.isra.0",
            "readlinebuffer_delim",
            "sortlines",
            "mergefiles",
            "pipe_child",
            "cut_file",
            "cut_bytes",
            "memchr2",
            "print_filename.part.0",
            "get_funky_string",
            "abformat_init",
            "signal_setup",
            "quote_name_buf.constprop.0",
            "quote_name",
            "calculate_columns",
            "print_current_files",
            "verrevcmp",
            "mpsort_with_tmp.part.0",
            "fts_stat",
            "rpl_fts_children",
            "transfer_entries",
            "hash_print_statistics",
            "hash_get_max_bucket_length",
            "hash_get_next",
            "hash_insert_if_absent",
            "hash_rehash",
            "hash_remove",
            "excise",
            "fillbuf",
            "maybe_create_temp",
            "find_in_given_path",
            "get_cgroup2_cpu_quota",
            "isaac_refill",
            "isaac_seed",
            "wc_lines_avx2",
            "wc_lines_avx512",
            "readtokens0",
            "get_meminfo",
            "physmem_total",
            "rpl_obstack_newchunk",
            "_gl_scratch_buffer_grow_preserve",
            "copy_with_unblock",
            "copy_bytes",
            "iwrite.constprop.0",
            "translate_charset",
            "invalidate_cache",
            "parse_long_options",
            "parse_gnu_standard_options_only",
            "human_options",
            "parse_integer",
            "parse_number",
            "traverse_raw_number",
            "argv_iter_init_argv",
            "argv_iter_init_stream",
            "argv_iter",
            "argv_iter_n_args",
            "argv_iter_free",
            "check_secret",
            "process_string",
            "test_boolxor",
            "alloc_wrapper2",
            "large_basic_block_guard",
            "tiny_vm_dispatch",
            "xnumtoumax",
            "synchronize_output",
            "stream_open",
            "close_stream",
            "rpl_fseeko",
            "fopen_safer",
            "rpl_fflush",
            "maybe_close_stdout",
            "open_safer",
            "openat_safer",
            "is_utf8_charset",
            "mcel_scan",
            "mcel_cmp",
            "mcel_tocmp",
            "mcel_scant",
            "copy",
            "do_move",
            "overwrite_ok",
            "areadlink_with_size",
            "areadlinkat_with_size",
            "mfile_name_concat",
            "set_owner.isra.0",
            "set_process_security_ctx",
            "same_nameat",
            "force_linkat",
            "force_symlinkat",
            "strmode",
            "do_statx",
            "getuidbyname",
            "setlocale_null_r_unlocked",
            "hard_locale",
            "set_program_name",
            "nstrftime",
            "sort_files",
            "get_dir_status",
            "filesystem_type",
            "add_range_pair",
            "try_tempname_len",
            "close_stdin",
            "close_stdout",
            "rpl_fclose",
            "rpl_reallocarray",
            "write_bytes",
            "yesno",
            "parse_field_count",
            "cwd_advance_fd",
            "restore_initial_cwd",
            "fts_sort",
            "get_root_dev_ino",
            "init_node",
            "open_input_files",
            "filenvercmp",
            "print_file_name_and_frills.isra.0",
            "print_with_separator",
            "extract_dirs_from_files",
            "error",
            "error_at_line",
            "hash_free",
            "randread_new",
            "randperm_new",
            "num_processors",
            "physmem_claimable",
            "fdutimensat",
            "gregorian_to_ethiopian",
            "cycle_check_init",
            "cycle_check",
            "canonicalize_filename_mode",
            "save_token",
            "filename_unescape",
            "compare",
            "memcoll",
            "xmemcoll",
            "print_stats",
            "create_hard_link",
            "record_file",
            "calc_req_mask",
            "reap",
            "num_processors_via_affinity_mask",
            "process_signals",
            "exit_cleanup",
            "clear_files",
            "flush_stdout",
            "getuser",
            "getgroup",
            "format_user_or_group",
            "xstrtol_fatal",
            "tzalloc",
            "xget_version",
            "rpl_obstack_free",
            "rpl_obstack_allocated_p",
            "has_xattr",
            "check_tuning",
            "imaxtostr",
            "umaxtostr",
            "hwcap_allowed",
            "file_prefixlen",
            "last_component",
            "mdir_name",
            "getmonth",
            "operand_matches",
            "xstrxfrm",
            "set_file_security_ctx",
            "localtime_rz",
            "locale_charset",
            "current_timespec",
            "rpl_obstack_memory_used",
            "alloc_ibuf",
            "alloc_obuf",
            "parse_datetime_body",
            "posixtime",
            "readtoken",
            "readtokens",
            "re_search_internal",
            "re_compile_internal",
            "parse_expression",
            "build_trtable",
            "update_cur_sifted_state",
            "transit_state_bkref",
            "build_charclass",
            "check_arrival",
            "peek_token",
            "build_wcs_upper_buffer",
            "xstrcoll_df_version",
            "rev_strcmp_df_mtime",
        ] {
            assert!(
                signature_hint_for_role_name(name, 0).is_some(),
                "missing registry role for {name}"
            );
        }
    }

    #[test]
    fn registry_keeps_canonicalize_filename_mode_exact() {
        let signature = signature_hint_for_name_candidates(["dbg.canonicalize_filename_mode"], 3)
            .expect("expected canonicalize filename signature");

        assert_eq!(signature.ret_type, Some(signed_byte_pointer_type()));
        assert_eq!(signature.params.len(), 2);
        assert_eq!(signature.params[0].name, "name");
        assert_eq!(signature.params[1].name, "can_mode");
        assert_eq!(
            signature.params[1].ty,
            Some(typedef_type("canonicalize_mode_t"))
        );
    }

    #[test]
    fn registry_projects_coreutils_tail_quality_roles() {
        let print_files =
            signature_hint_for_role_name("print_files", 0).expect("expected print_files signature");
        assert_eq!(print_files.ret_type, Some(CTypeLike::Void));
        assert_eq!(print_files.params[0].ty, Some(c_int_type()));
        assert_eq!(
            print_files.params[1].ty,
            Some(signed_byte_pointer_pointer_type())
        );

        let squeeze = signature_hint_for_role_name("squeeze_filter.constprop.0", 0)
            .expect("expected squeeze_filter constprop signature");
        assert_eq!(squeeze.ret_type, Some(CTypeLike::Void));
        assert_eq!(squeeze.params.len(), 2);
        assert_eq!(squeeze.params[1].ty, Some(typedef_type("size_t")));

        let xnum =
            signature_hint_for_role_name("xnumtoimax", 0).expect("expected xnumtoimax signature");
        assert_eq!(xnum.ret_type, Some(typedef_type("intmax_t")));
        assert_eq!(xnum.params[1].ty, Some(c_int_type()));

        let dtoa = signature_hint_for_role_name("ldtoastr", 0).expect("expected ldtoastr");
        assert_eq!(dtoa.ret_type, Some(c_int_type()));
        assert_eq!(dtoa.params[4].ty, Some(typedef_type("long double")));

        let output = signature_hint_for_role_name("output_file", 0).expect("expected output_file");
        assert_eq!(output.ret_type, Some(CTypeLike::Void));
        assert_eq!(output.params[2].ty, Some(unsigned_byte_pointer_type()));
        assert_eq!(output.params[7].ty, Some(typedef_type("intmax_t")));

        let join_get_line =
            signature_hint_for_role_name("get_line", 3).expect("expected join get_line");
        assert_eq!(join_get_line.ret_type, Some(CTypeLike::Bool));
        assert_eq!(
            join_get_line.params[1].ty,
            Some(CTypeLike::Pointer(Box::new(struct_pointer_type("line"))))
        );

        let baud = signature_hint_for_role_name("baud_to_value", 0).expect("expected baud");
        assert_eq!(baud.ret_type, Some(c_ulong_type()));
        assert_eq!(baud.params[0].ty, Some(typedef_type("speed_t")));

        let mkdir =
            signature_hint_for_role_name("make_dir_parents", 0).expect("expected mkdir parents");
        assert_eq!(mkdir.params[2].ty, Some(typedef_type("mkdir_ancestor_fn")));
        assert_eq!(mkdir.params[5].ty, Some(typedef_type("mkdir_announce_fn")));

        let add_utmp = signature_hint_for_role_name("add_utmp", 0).expect("expected add_utmp");
        assert_eq!(add_utmp.params[13].ty, Some(typedef_type("utmp_session")));

        let print_it = signature_hint_for_role_name("print_it", 0).expect("expected print_it");
        assert_eq!(print_it.ret_type, Some(CTypeLike::Bool));
        assert_eq!(print_it.params[3].ty, Some(typedef_type("stat_print_fn")));
        assert_eq!(
            print_it.params[4].ty,
            Some(typedef_type("stat_print_data_ref"))
        );
    }

    #[test]
    fn registry_covers_coreutils_mf100_gap_signatures() {
        for name in [
            "sym.sha256_process_block",
            "sym.sm3_process_block",
            "sym.blake2b_compress",
            "dbg.sha384_read_ctx",
        ] {
            assert!(
                signature_hint_for_name_candidates([name], 0).is_none(),
                "hash/crypto names alone must not create authoritative signatures for {name}"
            );
        }

        let datetime = signature_hint_for_name_candidates(["dbg.parse_datetime_body"], 0)
            .expect("parse_datetime_body signature");
        assert_eq!(datetime.ret_type, Some(CTypeLike::Bool));
        assert_eq!(datetime.params[0].ty, Some(struct_pointer_type("timespec")));
        assert_eq!(datetime.params[3].ty, Some(c_uint_type()));
        assert_eq!(datetime.params[4].ty, Some(typedef_type("timezone_t")));

        let posixtime =
            signature_hint_for_name_candidates(["dbg.posixtime"], 0).expect("posixtime signature");
        assert_eq!(posixtime.ret_type, Some(CTypeLike::Bool));
        assert_eq!(posixtime.params[0].ty, Some(typedef_pointer_type("time_t")));
        assert_eq!(posixtime.params[2].ty, Some(c_uint_type()));

        let randperm = signature_hint_for_name_candidates(["dbg.randperm_new"], 0)
            .expect("randperm_new signature");
        assert_eq!(randperm.ret_type, Some(typedef_pointer_type("size_t")));
        assert_eq!(
            randperm.params[0].ty,
            Some(struct_pointer_type("randint_source"))
        );
        assert_eq!(randperm.params[1].ty, Some(typedef_type("size_t")));

        let readtoken =
            signature_hint_for_name_candidates(["dbg.readtoken"], 0).expect("readtoken signature");
        assert_eq!(readtoken.ret_type, Some(typedef_type("size_t")));
        assert_eq!(readtoken.params[0].ty, Some(typedef_pointer_type("FILE")));
        assert_eq!(
            readtoken.params[3].ty,
            Some(typedef_pointer_type("token_buffer"))
        );

        let readtokens = signature_hint_for_name_candidates(["dbg.readtokens"], 0)
            .expect("readtokens signature");
        assert_eq!(readtokens.ret_type, Some(typedef_type("size_t")));
        assert_eq!(readtokens.params[1].ty, Some(typedef_type("size_t")));
        assert_eq!(
            readtokens.params[4].ty,
            Some(CTypeLike::Pointer(Box::new(
                signed_byte_pointer_pointer_type()
            )))
        );

        let reconstruct = signature_hint_for_name_candidates(["dbg.re_string_reconstruct"], 0)
            .expect("regex reconstruct signature");
        assert_eq!(reconstruct.ret_type, Some(typedef_type("reg_errcode_t")));
        assert_eq!(
            reconstruct.params[0].ty,
            Some(typedef_pointer_type("re_string_t"))
        );

        let search = signature_hint_for_name_candidates(["dbg.re_search_internal"], 0)
            .expect("regex search signature");
        assert_eq!(search.ret_type, Some(typedef_type("reg_errcode_t")));
        assert_eq!(search.params[0].ty, Some(typedef_pointer_type("regex_t")));
        assert_eq!(search.params[2].ty, Some(typedef_type("idx_t")));
        assert_eq!(search.params.len(), 9);

        let compile = signature_hint_for_name_candidates(["dbg.re_compile_internal"], 0)
            .expect("regex compile signature");
        assert_eq!(compile.ret_type, Some(typedef_type("reg_errcode_t")));
        assert_eq!(compile.params[3].ty, Some(typedef_type("reg_syntax_t")));

        let expr = signature_hint_for_name_candidates(["dbg.parse_expression"], 0)
            .expect("regex expression parser signature");
        assert_eq!(expr.ret_type, Some(typedef_pointer_type("bin_tree_t")));
        assert_eq!(expr.params[1].ty, Some(typedef_pointer_type("regex_t")));

        let trtable = signature_hint_for_name_candidates(["dbg.build_trtable"], 0)
            .expect("regex transition table signature");
        assert_eq!(trtable.ret_type, Some(CTypeLike::Bool));
        assert_eq!(
            trtable.params[1].ty,
            Some(typedef_pointer_type("re_dfastate_t"))
        );

        let charclass = signature_hint_for_name_candidates(["dbg.build_charclass"], 0)
            .expect("regex charclass signature");
        assert_eq!(charclass.params.len(), 6);
        assert_eq!(
            charclass.params[2].ty,
            Some(typedef_pointer_type("re_charset_t"))
        );

        let sift = signature_hint_for_name_candidates(["dbg.update_cur_sifted_state"], 0)
            .expect("regex sift signature");
        assert_eq!(sift.ret_type, Some(typedef_type("reg_errcode_t")));
        assert_eq!(
            sift.params[0].ty,
            Some(typedef_pointer_type("re_match_context_t"))
        );
        assert_eq!(sift.params[2].ty, Some(typedef_type("idx_t")));

        let arrival = signature_hint_for_name_candidates(["dbg.check_arrival"], 0)
            .expect("regex arrival signature");
        assert_eq!(
            arrival.params[1].ty,
            Some(typedef_pointer_type("state_array_t"))
        );
        assert_eq!(arrival.params[2].ty, Some(typedef_type("idx_t")));
        assert_eq!(arrival.params.len(), 7);

        let parser =
            signature_hint_for_name_candidates(["dbg.yyparse"], 0).expect("yyparse signature");
        assert_eq!(parser.ret_type, Some(c_int_type()));
        assert_eq!(
            parser.params[0].ty,
            Some(typedef_pointer_type("parser_control"))
        );

        let install = signature_hint_for_name_candidates(["dbg.install_file_in_file"], 0)
            .expect("install_file_in_file signature");
        assert_eq!(install.ret_type, Some(CTypeLike::Bool));
        assert_eq!(
            install.params[4].ty,
            Some(typedef_pointer_type("cp_options"))
        );

        let chown =
            signature_hint_for_name_candidates(["dbg.chown_files"], 0).expect("chown_files");
        assert_eq!(chown.ret_type, Some(CTypeLike::Bool));
        assert_eq!(chown.params[3].ty, Some(typedef_type("gid_t")));

        let read_utmp =
            signature_hint_for_name_candidates(["dbg.read_utmp"], 0).expect("read_utmp");
        assert_eq!(read_utmp.ret_type, Some(c_int_type()));
        assert_eq!(read_utmp.params[1].ty, Some(typedef_pointer_type("idx_t")));

        let dopass = signature_hint_for_name_candidates(["dbg.dopass"], 0).expect("dopass");
        assert_eq!(dopass.ret_type, Some(c_int_type()));
        assert_eq!(dopass.params[3].ty, Some(typedef_pointer_type("off_t")));

        let factor = signature_hint_for_name_candidates(["sym.factor_up.part.0.constprop.0"], 0)
            .expect("factor_up signature");
        assert_eq!(factor.ret_type, Some(CTypeLike::Void));
        assert_eq!(factor.params[1].ty, Some(typedef_type("mp_limb_t")));

        let seq = signature_hint_for_name_candidates(["dbg.seq_fast"], 0).expect("seq_fast");
        assert_eq!(seq.ret_type, Some(CTypeLike::Void));
        assert_eq!(seq.params[2].ty, Some(typedef_type("uintmax_t")));

        let base32 =
            signature_hint_for_name_candidates(["dbg.base32_encode"], 0).expect("base32_encode");
        assert_eq!(base32.ret_type, Some(CTypeLike::Void));
        assert_eq!(base32.params[1].ty, Some(typedef_type("idx_t")));

        let base64 = signature_hint_for_name_candidates(["dbg.base64_decode_ctx"], 0)
            .expect("base64_decode_ctx");
        assert_eq!(base64.ret_type, Some(CTypeLike::Bool));
        assert_eq!(base64.params[4].ty, Some(typedef_pointer_type("idx_t")));

        let signals =
            signature_hint_for_name_candidates(["dbg.str2sig"], 0).expect("str2sig signature");
        assert_eq!(signals.ret_type, Some(c_int_type()));
        assert_eq!(
            signals.params[1].ty,
            Some(CTypeLike::Pointer(Box::new(c_int_type())))
        );

        let lines =
            signature_hint_for_name_candidates(["dbg.writeline"], 3).expect("writeline signature");
        assert_eq!(lines.ret_type, Some(CTypeLike::Void));
        assert_eq!(lines.params[2].ty, Some(typedef_type("intmax_t")));

        let prefix = signature_hint_for_name_candidates(["dbg.file_prefixlen"], 0)
            .expect("file_prefixlen signature");
        assert_eq!(prefix.ret_type, Some(typedef_type("idx_t")));
        assert_eq!(prefix.params[1].name, "len");

        let comparator = signature_hint_for_name_candidates(["dbg.rev_xstrcoll_df_version"], 0)
            .expect("fileinfo comparator signature");
        assert_eq!(comparator.ret_type, Some(c_int_type()));
        assert_eq!(
            comparator.params[0].ty,
            Some(typedef_pointer_type("fileinfo"))
        );

        let obstack = signature_hint_for_name_candidates(["dbg.rpl_obstack_memory_used"], 0)
            .expect("obstack signature");
        assert_eq!(obstack.ret_type, Some(typedef_type("size_t")));
        assert_eq!(obstack.params[0].ty, Some(struct_pointer_type("obstack")));

        let save_token =
            signature_hint_for_name_candidates(["dbg.save_token"], 0).expect("save_token");
        assert_eq!(save_token.ret_type, Some(CTypeLike::Void));
        assert_eq!(save_token.params[0].ty, Some(struct_pointer_type("Tokens")));

        let compare = signature_hint_for_name_candidates(["sym.compare"], 0).expect("compare");
        assert_eq!(compare.ret_type, Some(c_int_type()));
        assert_eq!(compare.params[0].ty, Some(struct_pointer_type("line")));

        let fseeko = signature_hint_for_name_candidates(["dbg.rpl_fseeko"], 0).expect("rpl_fseeko");
        assert_eq!(fseeko.ret_type, Some(c_int_type()));
        assert_eq!(fseeko.params[1].ty, Some(typedef_type("off_t")));

        let start = signature_hint_for_name_candidates(["entry0"], 1).expect("entry0");
        assert_eq!(start.ret_type, Some(CTypeLike::Void));
        assert!(start.params.is_empty());

        let record =
            signature_hint_for_name_candidates(["dbg.record_file"], 0).expect("record_file");
        assert_eq!(record.ret_type, Some(CTypeLike::Void));
        assert_eq!(
            record.params[0].ty,
            Some(typedef_pointer_type("hash_table"))
        );

        let xstrtol =
            signature_hint_for_name_candidates(["sym.xstrtol_fatal"], 0).expect("xstrtol_fatal");
        assert_eq!(xstrtol.params.len(), 5);
        assert_eq!(xstrtol.params[3].ty, Some(typedef_pointer_type("option")));

        let formatter = signature_hint_for_name_candidates(["sym.format_user_or_group"], 0)
            .expect("format_user_or_group");
        assert_eq!(formatter.ret_type, Some(CTypeLike::Void));
        assert_eq!(formatter.params[1].ty, Some(typedef_type("uintmax_t")));

        let error_tail = signature_hint_for_name_candidates(["dbg.error_tail"], 4)
            .expect("error_tail signature");
        assert_eq!(error_tail.ret_type, Some(CTypeLike::Void));
        assert_eq!(error_tail.params[0].ty, Some(c_int_type()));
        assert_eq!(error_tail.params[1].ty, Some(c_int_type()));
        assert_eq!(
            error_tail.params[3].ty,
            Some(typedef_pointer_type("__va_list_tag"))
        );

        let argmatch_to_argument =
            signature_hint_for_name_candidates(["dbg.argmatch_to_argument"], 4)
                .expect("argmatch_to_argument signature");
        assert_eq!(
            argmatch_to_argument.params[0].ty,
            Some(typedef_pointer_type("argmatch_value"))
        );
        assert_eq!(
            argmatch_to_argument.params[1].ty,
            Some(signed_byte_pointer_pointer_type())
        );
        assert_eq!(
            argmatch_to_argument.params[3].ty,
            Some(typedef_type("size_t"))
        );

        let indent =
            signature_hint_for_name_candidates(["dbg.indent"], 2).expect("indent signature");
        assert_eq!(indent.ret_type, Some(CTypeLike::Void));
        assert_eq!(indent.params[0].ty, Some(typedef_type("size_t")));
        assert_eq!(indent.params[1].ty, Some(typedef_type("size_t")));

        let dired = signature_hint_for_name_candidates(["dbg.dired_dump_obstack"], 2)
            .expect("dired_dump_obstack signature");
        assert_eq!(dired.ret_type, Some(CTypeLike::Void));
        assert_eq!(dired.params[0].ty, Some(signed_byte_pointer_type()));
        assert_eq!(dired.params[1].ty, Some(struct_pointer_type("obstack")));

        let obstack_begin = signature_hint_for_name_candidates(["dbg._obstack_begin_worker"], 3)
            .expect("obstack begin worker signature");
        assert_eq!(obstack_begin.ret_type, Some(c_int_type()));
        assert_eq!(
            obstack_begin.params[0].ty,
            Some(struct_pointer_type("obstack"))
        );
        assert_eq!(obstack_begin.params[1].ty, Some(typedef_type("idx_t")));
        assert_eq!(obstack_begin.params[2].ty, Some(typedef_type("idx_t")));
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
    }

    #[test]
    fn registry_projects_role_type_algebra_for_coreutils_out_params() {
        let readtokens =
            type_projection_for_name_candidates(["readtokens0"], 0).expect("readtokens role");
        assert_eq!(readtokens.ret_type, Some(CTypeLike::Bool));
        assert_eq!(readtokens.pointer_param_indices, BTreeSet::from([0, 1, 2]));
        assert_eq!(readtokens.out_param_indices, BTreeSet::from([1, 2]));
        assert_eq!(
            readtokens.param_type_hints.get(&1),
            Some(&CTypeLike::Pointer(Box::new(
                signed_byte_pointer_pointer_type()
            )))
        );
        assert_eq!(
            readtokens.param_type_hints.get(&2),
            Some(&typedef_pointer_type("size_t"))
        );

        let sort_open =
            type_projection_for_name_candidates(["open_input_files"], 0).expect("sort opener");
        assert_eq!(sort_open.ret_type, Some(typedef_type("size_t")));
        assert_eq!(sort_open.out_param_indices, BTreeSet::from([2]));
        assert_eq!(
            sort_open.param_type_hints.get(&2),
            Some(&CTypeLike::Pointer(Box::new(CTypeLike::Pointer(Box::new(
                typedef_pointer_type("FILE"),
            )))))
        );

        let meminfo = type_projection_for_name_candidates(["get_meminfo"], 0).expect("meminfo");
        assert_eq!(meminfo.ret_type, Some(CTypeLike::Bool));
        assert_eq!(meminfo.out_param_indices, BTreeSet::from([0, 1]));
        assert_eq!(
            meminfo.param_type_hints.get(&0),
            Some(&typedef_pointer_type("uintmax_t"))
        );

        let numeric =
            type_projection_for_name_candidates(["xstrtoumax"], 0).expect("numeric parser");
        assert_eq!(numeric.ret_type, Some(typedef_type("strtol_error")));
        assert_eq!(numeric.out_param_indices, BTreeSet::from([1, 3]));
        assert_eq!(
            numeric.param_type_hints.get(&3),
            Some(&typedef_pointer_type("uintmax_t"))
        );
    }

    #[test]
    fn registry_projects_getopt_roles_without_name_only_hash_signatures() {
        assert!(
            signature_hint_for_role_name("_md5_process_block", 0).is_none(),
            "hash names alone must not create authoritative signatures"
        );
        let fnwmatch = signature_hint_for_role_name("_internal_fnwmatch", 0)
            .expect("expected fnwmatch signature");
        assert_eq!(fnwmatch.params[0].name, "pattern");
        assert_eq!(fnwmatch.params[0].ty, Some(typedef_pointer_type("wchar_t")));
        assert_eq!(fnwmatch.params[3].ty, Some(CTypeLike::Bool));

        let getopt = signature_hint_for_role_name("_getopt_internal_r", 0)
            .expect("expected getopt signature");
        assert_eq!(
            getopt.params[1].ty,
            Some(signed_byte_pointer_pointer_type())
        );
        assert_eq!(getopt.params[3].ty, Some(typedef_pointer_type("option")));
        assert_eq!(
            getopt.params[6].ty,
            Some(typedef_pointer_type("_getopt_data"))
        );

        let parse_long = signature_hint_for_role_name("parse_long_options", 0)
            .expect("expected long options signature");
        assert_eq!(parse_long.ret_type, Some(CTypeLike::Void));
        assert_eq!(
            parse_long.params[1].ty,
            Some(signed_byte_pointer_pointer_type())
        );
        assert_eq!(parse_long.params[5].ty, Some(CTypeLike::Function));
        assert_eq!(parse_long.params[6].name, "author1");
        assert_eq!(parse_long.params[6].ty, Some(signed_byte_pointer_type()));

        let parse_gnu = signature_hint_for_role_name("parse_gnu_standard_options_only", 0)
            .expect("expected GNU options signature");
        assert_eq!(parse_gnu.ret_type, Some(CTypeLike::Void));
        assert_eq!(parse_gnu.params[5].ty, Some(CTypeLike::Bool));
        assert_eq!(parse_gnu.params[6].ty, Some(CTypeLike::Function));
        assert_eq!(parse_gnu.params[7].name, "author1");
        assert_eq!(parse_gnu.params[7].ty, Some(signed_byte_pointer_type()));

        let strcoll = signature_hint_for_role_name("strcoll_loop", 0)
            .expect("expected strcoll_loop signature");
        assert_eq!(strcoll.ret_type, Some(c_int_type()));
        assert_eq!(strcoll.params[0].ty, Some(signed_byte_pointer_type()));
        assert_eq!(strcoll.params[1].ty, Some(typedef_type("size_t")));
        assert_eq!(strcoll.params[2].ty, Some(signed_byte_pointer_type()));
        assert_eq!(strcoll.params[3].ty, Some(typedef_type("size_t")));
    }

    #[test]
    fn registry_projects_broad_coreutils_blocker_roles() {
        let digest = signature_hint_for_role_name("digest_file.isra.0", 0)
            .expect("expected digest_file signature");
        assert_eq!(digest.ret_type, Some(CTypeLike::Bool));
        assert_eq!(digest.params[0].name, "filename");
        assert_eq!(digest.params[1].ty, Some(unsigned_byte_pointer_type()));
        assert_eq!(digest.params[2].ty, Some(typedef_type("size_t")));

        let sha_stream = signature_hint_for_role_name("shaxxx_stream.isra.0", 0)
            .expect("expected shaxxx_stream signature");
        assert_eq!(sha_stream.ret_type, Some(CTypeLike::Bool));
        assert_eq!(sha_stream.params[0].ty, Some(typedef_pointer_type("FILE")));
        assert_eq!(sha_stream.params[1].ty, Some(unsigned_byte_pointer_type()));

        let quote = signature_hint_for_role_name("quotearg_n_options", 0)
            .expect("expected quotearg_n_options signature");
        assert_eq!(quote.ret_type, Some(signed_byte_pointer_type()));
        assert_eq!(
            quote.params[3].ty,
            Some(typedef_pointer_type("quoting_options"))
        );

        let mbrtowc =
            signature_hint_for_role_name("rpl_mbrtowc", 0).expect("expected mbrtowc signature");
        assert_eq!(mbrtowc.params[0].ty, Some(typedef_pointer_type("wchar_t")));
        assert_eq!(
            mbrtowc.params[3].ty,
            Some(typedef_pointer_type("mbstate_t"))
        );

        let binop = signature_hint_for_role_name("binop", 0).expect("expected binop signature");
        assert_eq!(binop.ret_type, Some(c_int_type()));
        assert_eq!(binop.params[0].name, "op");

        let fopen =
            signature_hint_for_role_name("rpl_fopen", 0).expect("expected rpl_fopen signature");
        assert_eq!(fopen.ret_type, Some(typedef_pointer_type("FILE")));
        assert_eq!(fopen.params[1].name, "mode");

        let write_counts =
            signature_hint_for_role_name("write_counts", 0).expect("expected write_counts");
        assert_eq!(write_counts.ret_type, Some(CTypeLike::Void));
        assert_eq!(write_counts.params[0].ty, Some(typedef_type("uintmax_t")));
        assert_eq!(write_counts.params[4].ty, Some(typedef_type("intmax_t")));

        let verror = signature_hint_for_role_name("verror_at_line", 0).expect("expected verror");
        assert_eq!(verror.ret_type, Some(CTypeLike::Void));
        assert_eq!(verror.params[3].ty, Some(c_uint_type()));
        assert_eq!(
            verror.params[5].ty,
            Some(typedef_pointer_type("__va_list_tag"))
        );

        let plain_verror = signature_hint_for_role_name("verror", 0).expect("expected verror");
        assert_eq!(plain_verror.ret_type, Some(CTypeLike::Void));
        assert_eq!(plain_verror.params[0].ty, Some(c_int_type()));
        assert_eq!(plain_verror.params[1].ty, Some(c_int_type()));

        let argmatch = signature_hint_for_role_name("argmatch", 0).expect("expected argmatch");
        assert_eq!(
            argmatch.params[1].ty,
            Some(signed_byte_pointer_pointer_type())
        );
        assert_eq!(
            argmatch.params[2].ty,
            Some(typedef_pointer_type("argmatch_value"))
        );

        let binary =
            signature_hint_for_role_name("binary_operator", 0).expect("expected binary operator");
        assert_eq!(binary.params[0].ty, Some(CTypeLike::Bool));
        assert_eq!(
            binary.params[1].ty,
            Some(CTypeLike::Enum("binop".to_string()))
        );

        let renameatu = signature_hint_for_role_name("renameatu", 0).expect("expected renameatu");
        assert_eq!(renameatu.ret_type, Some(c_int_type()));
        assert_eq!(renameatu.params[1].ty, Some(signed_byte_pointer_type()));
        assert_eq!(renameatu.params[4].ty, Some(c_uint_type()));

        let streamsavedir =
            signature_hint_for_role_name("streamsavedir", 0).expect("expected streamsavedir");
        assert_eq!(streamsavedir.ret_type, Some(signed_byte_pointer_type()));
        assert_eq!(
            streamsavedir.params[0].ty,
            Some(typedef_pointer_type("DIR"))
        );

        let key_to_opts =
            signature_hint_for_role_name("key_to_opts", 0).expect("expected key_to_opts");
        assert_eq!(key_to_opts.ret_type, Some(CTypeLike::Void));
        assert_eq!(
            key_to_opts.params[0].ty,
            Some(typedef_pointer_type("keyfield"))
        );
        assert_eq!(key_to_opts.params[1].ty, Some(signed_byte_pointer_type()));

        let heap_remove_top =
            signature_hint_for_role_name("heap_remove_top", 0).expect("expected heap_remove_top");
        assert_eq!(heap_remove_top.ret_type, Some(memory_ptr_type()));
        assert_eq!(
            heap_remove_top.params[0].ty,
            Some(typedef_pointer_type("heap"))
        );

        let skip = signature_hint_for_role_name("skip", 0).expect("expected dd skip");
        assert_eq!(skip.ret_type, Some(typedef_type("intmax_t")));
        assert_eq!(skip.params[0].name, "fdesc");
        assert_eq!(skip.params[0].ty, Some(c_int_type()));
        assert_eq!(skip.params[2].ty, Some(typedef_type("intmax_t")));
        assert_eq!(skip.params[4].ty, Some(typedef_pointer_type("idx_t")));

        let unblock =
            signature_hint_for_role_name("copy_with_unblock", 0).expect("expected dd unblock");
        assert_eq!(unblock.ret_type, Some(CTypeLike::Void));
        assert_eq!(unblock.params[0].name, "buf");
        assert_eq!(unblock.params[0].ty, Some(signed_byte_pointer_type()));
        assert_eq!(unblock.params[1].ty, Some(typedef_type("idx_t")));

        let iwrite =
            signature_hint_for_role_name("iwrite.constprop.0", 0).expect("expected dd iwrite");
        assert_eq!(iwrite.ret_type, Some(typedef_type("idx_t")));
        assert_eq!(iwrite.params[0].ty, Some(c_int_type()));
        assert_eq!(iwrite.params[1].ty, Some(signed_byte_pointer_type()));
        assert_eq!(iwrite.params[2].ty, Some(typedef_type("idx_t")));

        let translate =
            signature_hint_for_role_name("translate_charset", 0).expect("expected charset hint");
        assert_eq!(translate.ret_type, Some(CTypeLike::Void));
        assert_eq!(translate.params[0].ty, Some(signed_byte_pointer_type()));

        let invalidate =
            signature_hint_for_role_name("invalidate_cache", 0).expect("expected cache hint");
        assert_eq!(invalidate.ret_type, Some(CTypeLike::Bool));
        assert_eq!(invalidate.params[0].ty, Some(c_int_type()));
        assert_eq!(invalidate.params[1].ty, Some(typedef_type("off_t")));

        let human = signature_hint_for_role_name("human_options", 0).expect("expected human opts");
        assert_eq!(human.ret_type, Some(typedef_type("strtol_error")));
        assert_eq!(human.params[0].ty, Some(signed_byte_pointer_type()));
        assert_eq!(
            human.params[1].ty,
            Some(CTypeLike::Pointer(Box::new(c_int_type())))
        );
        assert_eq!(human.params[2].ty, Some(typedef_pointer_type("uintmax_t")));

        let parse_integer =
            signature_hint_for_role_name("parse_integer", 0).expect("expected parse integer");
        assert_eq!(parse_integer.ret_type, Some(typedef_type("intmax_t")));
        assert_eq!(
            parse_integer.params[1].ty,
            Some(typedef_pointer_type("strtol_error"))
        );
        let parse_number =
            signature_hint_for_role_name("parse_number", 0).expect("expected parse number");
        assert_eq!(parse_number.ret_type, Some(c_int_type()));
        assert_eq!(parse_number.params[0].ty, Some(signed_byte_pointer_type()));
        let argv_iter =
            signature_hint_for_role_name("argv_iter", 0).expect("expected argv iterator");
        assert_eq!(argv_iter.ret_type, Some(signed_byte_pointer_type()));
        assert_eq!(
            argv_iter.params[0].ty,
            Some(struct_pointer_type("argv_iterator"))
        );
        let argv_init =
            signature_hint_for_role_name("argv_iter_init_argv", 0).expect("expected argv init");
        assert_eq!(
            argv_init.ret_type,
            Some(struct_pointer_type("argv_iterator"))
        );

        let usage = signature_hint_for_role_name("usage", 0).expect("expected usage");
        assert_eq!(usage.ret_type, Some(CTypeLike::Void));
        assert_eq!(usage.params[0].ty, Some(c_int_type()));

        let boolxor = signature_hint_for_role_name("test_boolxor", 0).expect("expected boolxor");
        assert_eq!(boolxor.ret_type, Some(c_int_type()));
        assert_eq!(boolxor.params[0].ty, Some(c_int_type()));
        assert_eq!(boolxor.params[1].ty, Some(c_int_type()));

        let alloc =
            signature_hint_for_role_name("alloc_wrapper2", 0).expect("expected alloc wrapper");
        assert_eq!(alloc.ret_type, Some(allocation_ptr_type()));
        assert_eq!(alloc.params[0].ty, Some(typedef_type("size_t")));

        let vm =
            signature_hint_for_role_name("tiny_vm_dispatch", 0).expect("expected tiny vm role");
        assert_eq!(vm.ret_type, Some(c_int_type()));
        assert_eq!(vm.params[0].ty, Some(unsigned_byte_pointer_type()));
        assert_eq!(vm.params[1].ty, Some(c_int_type()));

        let sync =
            signature_hint_for_role_name("synchronize_output", 0).expect("expected output sync");
        assert_eq!(sync.ret_type, Some(c_int_type()));
        assert!(sync.params.is_empty());

        let wc = signature_hint_for_role_name("wc", 0).expect("expected wc");
        assert_eq!(wc.ret_type, Some(CTypeLike::Bool));
        assert_eq!(wc.params[0].name, "fd");
        assert_eq!(wc.params[0].ty, Some(c_int_type()));
        assert_eq!(wc.params[2].ty, Some(typedef_pointer_type("fstatus")));

        let vstrtoimax =
            signature_hint_for_role_name("vstrtoimax", 0).expect("expected vstrtoimax");
        assert_eq!(vstrtoimax.ret_type, Some(typedef_type("intmax_t")));
        assert_eq!(vstrtoimax.params[0].ty, Some(signed_byte_pointer_type()));

        let fts_close =
            signature_hint_for_role_name("rpl_fts_close", 0).expect("expected fts close");
        assert_eq!(fts_close.ret_type, Some(c_int_type()));
        assert_eq!(fts_close.params[0].ty, Some(typedef_pointer_type("FTS")));

        let quote_alloc = signature_hint_for_role_name("quotearg_alloc_mem", 0)
            .expect("expected quotearg_alloc_mem");
        assert_eq!(
            quote_alloc.params[2].ty,
            Some(typedef_pointer_type("size_t"))
        );
        assert_eq!(
            quote_alloc.params[3].ty,
            Some(typedef_pointer_type("quoting_options"))
        );

        let version =
            signature_hint_for_role_name("version_etc_va", 0).expect("expected version_etc_va");
        assert_eq!(version.ret_type, Some(CTypeLike::Void));
        assert_eq!(version.params.len(), 6);
        assert_eq!(version.params[4].ty, Some(typedef_type("va_list")));
        assert_eq!(version.params[5].ty, Some(typedef_type("uintptr_t")));

        let xpalloc = signature_hint_for_role_name("xpalloc", 0).expect("expected xpalloc");
        assert_eq!(xpalloc.ret_type, Some(allocation_ptr_type()));
        assert_eq!(xpalloc.params[0].ty, Some(allocation_ptr_type()));
        assert_eq!(xpalloc.params[1].ty, Some(typedef_pointer_type("idx_t")));
        let xnrealloc = signature_hint_for_role_name("xnrealloc", 0).expect("expected xnrealloc");
        assert_eq!(xnrealloc.ret_type, Some(allocation_ptr_type()));
        assert_eq!(xnrealloc.params[1].ty, Some(typedef_type("size_t")));

        let xargmatch =
            signature_hint_for_role_name("__xargmatch_internal", 0).expect("expected xargmatch");
        assert_eq!(xargmatch.ret_type, Some(typedef_type("ptrdiff_t")));
        assert_eq!(
            xargmatch.params[2].ty,
            Some(signed_byte_pointer_pointer_type())
        );
        assert_eq!(
            xargmatch.params[3].ty,
            Some(typedef_pointer_type("argmatch_value"))
        );

        let memchr2 = signature_hint_for_role_name("memchr2", 0).expect("expected memchr2");
        assert_eq!(memchr2.ret_type, Some(memory_ptr_type()));
        assert_eq!(memchr2.params[3].ty, Some(typedef_type("size_t")));

        let hash_insert =
            signature_hint_for_role_name("hash_insert_if_absent", 0).expect("expected hash insert");
        assert_eq!(hash_insert.ret_type, Some(c_int_type()));
        assert_eq!(
            hash_insert.params[0].ty,
            Some(typedef_pointer_type("hash_table"))
        );
        assert_eq!(
            hash_insert.params[2].ty,
            Some(CTypeLike::Pointer(Box::new(memory_ptr_type())))
        );
        let hash_lookup =
            signature_hint_for_role_name("hash_lookup", 0).expect("expected hash lookup");
        assert_eq!(hash_lookup.ret_type, Some(memory_ptr_type()));
        assert_eq!(hash_lookup.params[1].ty, Some(memory_ptr_type()));
        let heap_insert =
            signature_hint_for_role_name("heap_insert", 0).expect("expected heap insert");
        assert_eq!(heap_insert.ret_type, Some(c_int_type()));
        assert_eq!(heap_insert.params[0].ty, Some(typedef_pointer_type("heap")));
        assert_eq!(heap_insert.params[1].ty, Some(memory_ptr_type()));
        let hash_entries =
            signature_hint_for_role_name("hash_get_entries", 0).expect("expected hash entries");
        assert_eq!(hash_entries.ret_type, Some(typedef_type("size_t")));
        assert_eq!(
            hash_entries.params[1].ty,
            Some(CTypeLike::Pointer(Box::new(memory_ptr_type())))
        );
        let parse_field =
            signature_hint_for_role_name("parse_field_count", 0).expect("expected field parser");
        assert_eq!(parse_field.ret_type, Some(signed_byte_pointer_type()));
        assert_eq!(
            parse_field.params[1].ty,
            Some(typedef_pointer_type("size_t"))
        );
        let fts_sort = signature_hint_for_role_name("fts_sort", 0).expect("expected fts_sort");
        assert_eq!(fts_sort.ret_type, Some(typedef_pointer_type("FTSENT")));
        assert_eq!(fts_sort.params[0].ty, Some(typedef_pointer_type("FTS")));
        let root_dev =
            signature_hint_for_role_name("get_root_dev_ino", 0).expect("expected root dev ino");
        assert_eq!(root_dev.ret_type, Some(struct_pointer_type("dev_ino")));
        assert_eq!(root_dev.params[0].ty, Some(struct_pointer_type("dev_ino")));
        let last_component =
            signature_hint_for_role_name("last_component", 0).expect("expected last_component");
        assert_eq!(last_component.ret_type, Some(signed_byte_pointer_type()));

        let quote_name = signature_hint_for_role_name("quote_name_buf.constprop.0", 0)
            .expect("expected quote_name_buf");
        assert_eq!(quote_name.ret_type, Some(typedef_type("size_t")));
        assert_eq!(
            quote_name.params[1].ty,
            Some(typedef_pointer_type("fileinfo"))
        );

        let wc_lines = signature_hint_for_role_name("wc_lines_avx512", 0)
            .expect("expected vector line counter");
        assert_eq!(wc_lines.ret_type, Some(typedef_type("wc_lines")));
        assert_eq!(wc_lines.params[1].ty, Some(typedef_type("size_t")));

        let same_name =
            signature_hint_for_role_name("same_nameat", 0).expect("expected same_nameat signature");
        assert_eq!(same_name.ret_type, Some(CTypeLike::Bool));
        assert_eq!(same_name.params[1].ty, Some(signed_byte_pointer_type()));
        assert_eq!(same_name.params[3].ty, Some(signed_byte_pointer_type()));

        let statx = signature_hint_for_role_name("do_statx", 0).expect("expected do_statx");
        assert_eq!(statx.ret_type, Some(c_int_type()));
        assert_eq!(statx.params[2].ty, Some(typedef_pointer_type("stat")));
        assert_eq!(statx.params[4].ty, Some(c_uint_type()));

        let strmode = signature_hint_for_role_name("strmode", 0).expect("expected strmode");
        assert_eq!(strmode.ret_type, Some(CTypeLike::Void));
        assert_eq!(strmode.params[0].ty, Some(typedef_type("mode_t")));

        let mcel = signature_hint_for_role_name("mcel_scan", 0).expect("expected mcel_scan");
        assert_eq!(mcel.ret_type, Some(typedef_type("mcel_t")));
        assert_eq!(mcel.params[1].ty, Some(signed_byte_pointer_type()));
        let mcel_tocmp =
            signature_hint_for_role_name("mcel_tocmp", 0).expect("expected mcel_tocmp");
        assert_eq!(mcel_tocmp.ret_type, Some(c_int_type()));
        assert_eq!(
            mcel_tocmp.params[0].ty,
            Some(typedef_type("wint_transform"))
        );
        assert_eq!(mcel_tocmp.params[1].ty, Some(typedef_type("mcel_t")));

        let xnanosleep =
            signature_hint_for_role_name("xnanosleep", 0).expect("expected xnanosleep");
        assert_eq!(xnanosleep.ret_type, Some(c_int_type()));
        assert_eq!(xnanosleep.params[0].ty, Some(CTypeLike::Float(64)));

        let mfile = signature_hint_for_role_name("mfile_name_concat", 0)
            .expect("expected mfile_name_concat");
        assert_eq!(mfile.ret_type, Some(signed_byte_pointer_type()));
        assert_eq!(mfile.params[2].ty, Some(signed_byte_pointer_pointer_type()));

        let uid_lookup =
            signature_hint_for_role_name("getuidbyname", 0).expect("expected getuidbyname");
        assert_eq!(uid_lookup.ret_type, Some(typedef_pointer_type("uid_t")));

        let init_node = signature_hint_for_role_name("init_node", 0).expect("expected init_node");
        assert_eq!(init_node.ret_type, Some(struct_pointer_type("merge_node")));
        assert_eq!(
            init_node.params[0].ty,
            Some(struct_pointer_type("merge_node"))
        );
        assert_eq!(init_node.params[2].ty, Some(struct_pointer_type("line")));
        let mergefiles =
            signature_hint_for_role_name("mergefiles", 0).expect("expected mergefiles");
        assert_eq!(mergefiles.ret_type, Some(typedef_type("size_t")));
        assert_eq!(
            mergefiles.params[0].ty,
            Some(struct_pointer_type("sortfile"))
        );
        assert_eq!(mergefiles.params[3].ty, Some(typedef_pointer_type("FILE")));
        let scratch = signature_hint_for_role_name("_gl_scratch_buffer_grow_preserve", 0)
            .expect("expected scratch buffer grow");
        assert_eq!(scratch.ret_type, Some(CTypeLike::Bool));
        assert_eq!(
            scratch.params[0].ty,
            Some(struct_pointer_type("scratch_buffer"))
        );

        let try_temp =
            signature_hint_for_role_name("try_tempname_len", 0).expect("expected tempname");
        assert_eq!(try_temp.ret_type, Some(c_int_type()));
        assert_eq!(
            try_temp.params[2].ty,
            Some(typedef_pointer_type("tempname_args"))
        );
        assert_eq!(
            try_temp.params[3].ty,
            Some(typedef_type("tempname_tryfunc"))
        );

        let filenver =
            signature_hint_for_role_name("filenvercmp", 0).expect("expected filenvercmp");
        assert_eq!(filenver.params[1].ty, Some(typedef_type("ptrdiff_t")));
        assert_eq!(filenver.params[3].ty, Some(typedef_type("ptrdiff_t")));

        let frills = signature_hint_for_role_name("print_file_name_and_frills.isra.0", 0)
            .expect("expected frills");
        assert_eq!(frills.ret_type, Some(typedef_type("size_t")));
        assert_eq!(frills.params[0].ty, Some(typedef_pointer_type("fileinfo")));

        let write_bytes =
            signature_hint_for_role_name("write_bytes", 0).expect("expected write_bytes");
        assert_eq!(write_bytes.ret_type, Some(CTypeLike::Void));
        assert_eq!(write_bytes.params[1].ty, Some(typedef_type("size_t")));

        let opendirat = signature_hint_for_role_name("opendirat", 0).expect("expected opendirat");
        assert_eq!(opendirat.ret_type, Some(typedef_pointer_type("DIR")));
        assert_eq!(opendirat.params[0].ty, Some(c_int_type()));
        assert_eq!(opendirat.params[2].ty, Some(c_int_type()));

        let emit_verbose =
            signature_hint_for_role_name("emit_verbose", 0).expect("expected emit_verbose");
        assert_eq!(emit_verbose.ret_type, Some(CTypeLike::Void));
        assert_eq!(emit_verbose.params[0].ty, Some(signed_byte_pointer_type()));
    }

    #[test]
    fn registry_projects_accepted_type_quality_tranche_roles() {
        let xnum = signature_hint_for_role_name("xnumtoumax", 0).expect("expected xnumtoumax");
        assert_eq!(xnum.ret_type, Some(typedef_type("uintmax_t")));
        assert_eq!(xnum.params.len(), 8);
        assert_eq!(xnum.params[0].ty, Some(signed_byte_pointer_type()));
        assert_eq!(xnum.params[2].ty, Some(typedef_type("uintmax_t")));
        assert_eq!(xnum.params[6].ty, Some(c_int_type()));
        assert_eq!(xnum.params[7].name, "flags");
        assert_eq!(xnum.params[7].ty, Some(c_int_type()));

        let limfield =
            signature_hint_for_role_name("limfield.isra.0", 0).expect("expected limfield");
        assert_eq!(limfield.ret_type, Some(signed_byte_pointer_type()));
        assert_eq!(limfield.params[0].ty, Some(typedef_pointer_type("line")));
        assert_eq!(limfield.params[1].ty, Some(typedef_type("size_t")));

        let sequential =
            signature_hint_for_role_name("sequential_sort", 0).expect("expected sequential_sort");
        assert_eq!(sequential.ret_type, Some(CTypeLike::Void));
        assert_eq!(sequential.params[0].ty, Some(typedef_pointer_type("line")));
        assert_eq!(sequential.params[1].ty, Some(typedef_type("size_t")));
        assert_eq!(sequential.params[3].ty, Some(CTypeLike::Bool));

        let oprintf =
            signature_hint_for_role_name("oprintf_.constprop.0", 5).expect("expected oprintf");
        assert_eq!(oprintf.ret_type, Some(CTypeLike::Void));
        assert_eq!(oprintf.params[0].ty, Some(signed_byte_pointer_type()));
        assert_eq!(oprintf.params[2].name, "format_arg1");
        assert_eq!(oprintf.params[2].ty, Some(typedef_type("uintptr_t")));

        let cycle = signature_hint_for_role_name("cycle_check", 0).expect("expected cycle_check");
        assert_eq!(cycle.ret_type, Some(CTypeLike::Bool));
        assert_eq!(
            cycle.params[0].ty,
            Some(typedef_pointer_type("cycle_check_state"))
        );
        assert_eq!(cycle.params[1].ty, Some(typedef_pointer_type("stat")));

        let copy_bytes = signature_hint_for_role_name("copy_bytes", 0).expect("copy_bytes");
        assert_eq!(copy_bytes.ret_type, Some(CTypeLike::Void));
        assert_eq!(copy_bytes.params[2].ty, Some(typedef_type("size_t")));

        let create_hole = signature_hint_for_role_name("create_hole", 0).expect("create_hole");
        assert_eq!(create_hole.ret_type, Some(typedef_type("off_t")));
        assert_eq!(create_hole.params[0].ty, Some(c_int_type()));

        let full_write = signature_hint_for_role_name("full_write", 0).expect("full_write");
        assert_eq!(full_write.ret_type, Some(typedef_type("idx_t")));
        assert_eq!(full_write.params[0].ty, Some(c_int_type()));
        assert_eq!(full_write.params[1].ty, Some(memory_ptr_type()));

        let filecon =
            signature_hint_for_role_name("rpl_getfilecon_raw", 0).expect("getfilecon wrapper");
        assert_eq!(filecon.ret_type, Some(c_int_type()));
        assert_eq!(
            filecon.params[1].ty,
            Some(signed_byte_pointer_pointer_type())
        );

        let locale = signature_hint_for_role_name("setlocale_null_r_unlocked", 0)
            .expect("expected locale helper");
        assert_eq!(locale.ret_type, Some(c_int_type()));
        assert_eq!(locale.params[1].ty, Some(signed_byte_pointer_type()));
        assert_eq!(locale.params[2].ty, Some(typedef_type("size_t")));

        let readlink = signature_hint_for_role_name("areadlink_with_size", 0)
            .expect("expected readlink helper");
        assert_eq!(readlink.ret_type, Some(signed_byte_pointer_type()));
        assert_eq!(readlink.params[1].ty, Some(typedef_type("size_t")));

        let hard_locale =
            signature_hint_for_role_name("hard_locale", 0).expect("expected hard_locale");
        assert_eq!(hard_locale.ret_type, Some(CTypeLike::Bool));
        assert_eq!(hard_locale.params[0].ty, Some(c_int_type()));

        let progname =
            signature_hint_for_role_name("set_program_name", 0).expect("expected progname");
        assert_eq!(progname.ret_type, Some(CTypeLike::Void));
        assert_eq!(progname.params[0].ty, Some(signed_byte_pointer_type()));

        let nstrftime = signature_hint_for_role_name("nstrftime", 0).expect("expected nstrftime");
        assert_eq!(nstrftime.ret_type, Some(typedef_type("ptrdiff_t")));
        assert_eq!(nstrftime.params[3].ty, Some(typedef_pointer_type("tm")));
        assert_eq!(nstrftime.params[4].ty, Some(typedef_type("timezone_t")));

        let hash_free = signature_hint_for_role_name("hash_free", 0).expect("expected hash_free");
        assert_eq!(hash_free.ret_type, Some(CTypeLike::Void));
        assert_eq!(
            hash_free.params[0].ty,
            Some(typedef_pointer_type("hash_table"))
        );

        let nproc =
            signature_hint_for_role_name("num_processors", 0).expect("expected num_processors");
        assert_eq!(nproc.ret_type, Some(c_ulong_type()));
        assert_eq!(
            nproc.params[0].ty,
            Some(CTypeLike::Enum("nproc_query".to_string()))
        );

        let open_input =
            signature_hint_for_role_name("open_input_files", 0).expect("expected sort opener");
        assert_eq!(open_input.ret_type, Some(typedef_type("size_t")));
        assert_eq!(
            open_input.params[0].ty,
            Some(typedef_pointer_type("sortfile"))
        );
        assert_eq!(
            open_input.params[2].ty,
            Some(CTypeLike::Pointer(Box::new(CTypeLike::Pointer(Box::new(
                typedef_pointer_type("FILE"),
            )))))
        );

        let physmem =
            signature_hint_for_role_name("physmem_claimable", 0).expect("expected physmem");
        assert_eq!(physmem.ret_type, Some(CTypeLike::Float(64)));
        assert_eq!(physmem.params[0].ty, Some(CTypeLike::Float(64)));

        let randread =
            signature_hint_for_role_name("randread_new", 0).expect("expected randread_new");
        assert_eq!(
            randread.ret_type,
            Some(typedef_pointer_type("randread_source"))
        );
        assert_eq!(randread.params[1].ty, Some(typedef_type("size_t")));
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
