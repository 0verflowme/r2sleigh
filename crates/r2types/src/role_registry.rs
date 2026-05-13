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
    let count = current_param_count.max(4);
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

pub fn signature_hint_for_name_candidates<'a>(
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

pub fn type_projection_for_name_candidates<'a>(
    candidates: impl IntoIterator<Item = &'a str>,
    current_param_count: usize,
) -> Option<RoleTypeProjection> {
    signature_hint_for_name_candidates(candidates, current_param_count)
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

pub fn signature_hint_for_role_name(
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
        "entry.init0" => sig(CTypeLike::Void, Vec::new()),
        "diagnose" => diagnostic_signature(current_param_count),
        "usage" => sig(CTypeLike::Void, vec![p("status", c_int_type())]),
        "printf_fetchargs" => format_argument_fetch_signature(),
        "oprintf_" | "oprintf_.constprop.0" => format_output_signature(current_param_count),
        "_md5_process_block" | "md5_process_block" | "md5_process_bytes" => sig(
            CTypeLike::Void,
            vec![
                p("buffer", void_pointer_type()),
                p("len", typedef_type("size_t")),
                p("ctx", typedef_pointer_type("md5_ctx")),
            ],
        ),
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
            ],
        ),
        "version_etc" => version_etc_signature(current_param_count),
        "emit_bug_reporting_address" => sig(CTypeLike::Void, Vec::new()),
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
        "error" => error_signature(current_param_count),
        "error_at_line" => error_at_line_signature(current_param_count),
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
        "wc_lines_avx2" | "wc_lines_avx512" => sig(
            typedef_type("wc_lines"),
            vec![
                p("buf", signed_byte_pointer_type()),
                p("len", typedef_type("size_t")),
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
            | "calendar_date"
            | "char32_t"
            | "count_t"
            | "copy_debug"
            | "cp_options"
            | "cycle_check_state"
            | "dir_attr"
            | "dir_list"
            | "dir"
            | "errno_t"
            | "fcntl_arg"
            | "file"
            | "fileinfo"
            | "filetype"
            | "fsword"
            | "fstatus"
            | "fts"
            | "ftsent"
            | "fts_compar_fn"
            | "hash_table"
            | "idx_t"
            | "int"
            | "intmax_t"
            | "ino_t"
            | "line"
            | "linebuffer"
            | "long"
            | "mcel_t"
            | "mbbuf_t"
            | "mbstate_t"
            | "memory_ptr"
            | "mbfield_parser"
            | "md5_ctx"
            | "merge_node"
            | "merge_node_queue"
            | "mode_t"
            | "nproc_query"
            | "obstack"
            | "off_t"
            | "option"
            | "pid_t"
            | "ptrdiff_t"
            | "printf_directive"
            | "printf_status_t"
            | "quoting_options"
            | "quoting_style"
            | "randread_source"
            | "retval_t"
            | "rm_status"
            | "rm_options"
            | "savedir_option"
            | "sbyte_count_t"
            | "selabel_handle"
            | "size_t"
            | "sortfile"
            | "stat"
            | "strtol_error"
            | "tempname_args"
            | "tempname_tryfunc"
            | "timespec"
            | "tm"
            | "timezone_t"
            | "uid_t"
            | "unicode_callback_context"
            | "unicode_failure_callback"
            | "unicode_success_callback"
            | "unsigned int"
            | "unsigned long"
            | "uintmax_t"
            | "uintptr_t"
            | "va_list"
            | "wchar_t"
            | "wc_lines"
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
            "_md5_process_block",
            "_internal_fnwmatch",
            "_getopt_internal_r",
            "getopt_long",
            "digest_file.isra.0",
            "shaxxx_stream.isra.0",
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
            "openat_safer",
            "is_utf8_charset",
            "mcel_scan",
            "mcel_cmp",
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
            "write_bytes",
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
            "num_processors",
            "physmem_claimable",
            "fdutimensat",
            "gregorian_to_ethiopian",
            "cycle_check_init",
            "cycle_check",
        ] {
            assert!(
                signature_hint_for_role_name(name, 0).is_some(),
                "missing registry role for {name}"
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
    fn registry_projects_hash_pattern_and_getopt_roles() {
        let md5 =
            signature_hint_for_role_name("_md5_process_block", 0).expect("expected md5 signature");
        assert_eq!(md5.ret_type, Some(CTypeLike::Void));
        assert_eq!(md5.params[0].name, "buffer");
        assert_eq!(md5.params[1].ty, Some(typedef_type("size_t")));
        assert_eq!(md5.params[2].ty, Some(typedef_pointer_type("md5_ctx")));

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
        assert_eq!(version.params[4].ty, Some(typedef_type("va_list")));

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
        let hash_entries =
            signature_hint_for_role_name("hash_get_entries", 0).expect("expected hash entries");
        assert_eq!(hash_entries.ret_type, Some(typedef_type("size_t")));
        assert_eq!(
            hash_entries.params[1].ty,
            Some(CTypeLike::Pointer(Box::new(memory_ptr_type())))
        );

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
        assert!(semantic_typedef_is_authoritative("calendar_date"));
        assert!(semantic_typedef_is_authoritative("cycle_check_state"));
        assert!(semantic_typedef_is_authoritative("DIR"));
        assert!(semantic_typedef_is_authoritative("FTS"));
        assert!(semantic_typedef_is_authoritative("_Bool"));
        assert!(semantic_typedef_is_authoritative("fcntl_arg"));
        assert!(semantic_typedef_is_authoritative("long"));
        assert!(semantic_typedef_is_authoritative("memory_ptr"));
        assert!(semantic_typedef_is_authoritative("mode_t"));
        assert!(semantic_typedef_is_authoritative("md5_ctx"));
        assert!(semantic_typedef_is_authoritative("ptrdiff_t"));
        assert!(semantic_typedef_is_authoritative("wchar_t"));
        assert!(semantic_typedef_is_authoritative("quoting_options"));
        assert!(semantic_typedef_is_authoritative("selabel_handle"));
        assert!(semantic_typedef_is_authoritative("printf_directive"));
        assert!(semantic_typedef_is_authoritative("hash_table"));
        assert!(semantic_typedef_is_authoritative("fsword"));
        assert!(semantic_typedef_is_authoritative("mcel_t"));
        assert!(semantic_typedef_is_authoritative("nproc_query"));
        assert!(semantic_typedef_is_authoritative("randread_source"));
        assert!(semantic_typedef_is_authoritative("timezone_t"));
        assert!(semantic_typedef_is_authoritative("uid_t"));
        assert!(semantic_typedef_is_authoritative(
            "unicode_success_callback"
        ));
        assert!(semantic_typedef_is_authoritative("wc_lines"));
        assert!(semantic_typedef_is_authoritative("unsigned int"));
        assert!(semantic_typedef_is_authoritative("unsigned long"));
        assert!(semantic_typedef_is_authoritative("xtime_t"));
        assert!(semantic_typedef_is_authoritative("tempname_args"));
        assert!(semantic_typedef_is_authoritative("tempname_tryfunc"));
        assert!(semantic_typedef_is_authoritative("timespec"));
        assert!(semantic_typedef_is_authoritative("va_list"));
        assert!(!semantic_typedef_is_authoritative("sla_struct_deadbeef"));
    }
}
