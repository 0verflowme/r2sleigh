use std::env;
use std::fs;
use std::path::PathBuf;

const EXPORTED_ITEMS: &[&str] = &[
    "R2SLEIGH_ABI_V2",
    "R2SLEIGH_CAP_DECOMPILE_V2",
    "R2SLEIGH_CAP_TYPE_FUNCTION_V2",
    "R2SLEIGH_CAP_RESPONSE_INFO_V2",
    "R2SLEIGH_CAP_EXECUTION_CONTROL_V2",
    "R2SLEIGH_CAP_LIFT_CORE_V2",
    "R2SLEIGH_CAP_PLANNER_QUERY_V2",
    "R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2",
    "R2SLEIGH_CAPABILITIES_V2",
    "R2SLEIGH_RADARE_ABI_V2",
    "R2SLEIGH_RADARE_FUNCTION_SNAPSHOT_SCHEMA_V2",
    "R2SLEIGH_RADARE_SNAPSHOT_ACCESSOR_SCHEMA_V2",
    "R2SLEIGH_STATUS_OK_V2",
    "R2SLEIGH_STATUS_INVALID_ARGUMENT_V2",
    "R2SLEIGH_STATUS_ABI_MISMATCH_V2",
    "R2SLEIGH_STATUS_UNSUPPORTED_V2",
    "R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2",
    "R2SLEIGH_STATUS_ENGINE_ERROR_V2",
    "R2SLEIGH_STATUS_PANIC_V2",
    "R2SLEIGH_REQUEST_DECOMPILE_V2",
    "R2SLEIGH_REQUEST_TYPE_FUNCTION_V2",
    "R2SLEIGH_RESPONSE_INFO_SCHEMA_V2",
    "R2SLEIGH_OUTCOME_COMPLETED_V2",
    "R2SLEIGH_OUTCOME_REFUSED_V2",
    "R2SLEIGH_PHASE_SNAPSHOT_CONTEXT_V2",
    "R2SLEIGH_PHASE_LIFT_NORMALIZE_V2",
    "R2SLEIGH_PHASE_SSA_V2",
    "R2SLEIGH_PHASE_OBLIGATIONS_V2",
    "R2SLEIGH_PHASE_SYMBOLIC_V2",
    "R2SLEIGH_PHASE_TYPES_V2",
    "R2SLEIGH_PHASE_CERTIFICATION_V2",
    "R2SLEIGH_PHASE_STRUCTURING_V2",
    "R2SLEIGH_PHASE_NORMALIZATION_V2",
    "R2SLEIGH_PHASE_RENDERING_V2",
    "R2SLEIGH_PHASE_FFI_CONVERSION_V2",
    "R2SLEIGH_PHASE_COUNT_V2",
    "R2SLEIGH_PHASE_STATUS_NOT_EXECUTED_V2",
    "R2SLEIGH_PHASE_STATUS_EXECUTED_V2",
    "R2SLEIGH_PHASE_STATUS_FOLDED_V2",
    "R2SLEIGH_PHASE_STATUS_REUSED_V2",
    "R2SLEIGH_PHASE_STATUS_REFUSED_V2",
    "R2SLEIGH_SOURCE_STORAGE_RAM_V2",
    "R2SLEIGH_SOURCE_STORAGE_REGISTER_V2",
    "R2SLEIGH_SOURCE_STORAGE_UNIQUE_V2",
    "R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2",
    "R2SLEIGH_SOURCE_STORAGE_CUSTOM_V2",
    "R2SLEIGH_MAX_FUNCTION_BLOCKS_V2",
    "R2SLEIGH_MAX_SWITCH_CASES_V2",
    "R2SLEIGH_MAX_FUNCTION_INPUT_BYTES_V2",
    "R2SLEIGH_MAX_STRING_BYTES_V2",
    "R2SLEIGH_ANALYSIS_BLOCK_ESIL_V2",
    "R2SLEIGH_ANALYSIS_BLOCK_OP_JSON_V2",
    "R2SLEIGH_ANALYSIS_BLOCK_REGS_READ_V2",
    "R2SLEIGH_ANALYSIS_BLOCK_REGS_WRITE_V2",
    "R2SLEIGH_ANALYSIS_BLOCK_MEMORY_V2",
    "R2SLEIGH_ANALYSIS_BLOCK_VARNODES_V2",
    "R2SLEIGH_ANALYSIS_BLOCK_SSA_V2",
    "R2SLEIGH_ANALYSIS_BLOCK_DEFUSE_V2",
    "R2SLEIGH_ANALYSIS_FUNCTION_SSA_V2",
    "R2SLEIGH_ANALYSIS_FUNCTION_SSA_OPT_V2",
    "R2SLEIGH_ANALYSIS_FUNCTION_DEFUSE_V2",
    "R2SLEIGH_ANALYSIS_FUNCTION_DOMTREE_V2",
    "R2SLEIGH_ANALYSIS_FUNCTION_SLICE_V2",
    "R2SLEIGH_ANALYSIS_FUNCTION_TAINT_V2",
    "R2SLEIGH_ANALYSIS_FUNCTION_CFG_ASCII_V2",
    "R2SLEIGH_ANALYSIS_FUNCTION_CFG_JSON_V2",
    "R2SLEIGH_ANALYSIS_ENGINE_CACHE_STATS_V2",
    "R2SLEIGH_QUERY_BLOCK_VALUES_V2",
    "R2SLEIGH_QUERY_TAINT_SUMMARY_V2",
    "R2SLEIGH_QUERY_ANNOTATIONS_V2",
    "R2SLEIGH_QUERY_RECOVERED_VARS_V2",
    "R2SLEIGH_QUERY_DATA_REFS_V2",
    "R2SLEIGH_DATA_REF_SCHEMA_V2",
    "R2SLEIGH_PLANNER_QUERY_SCHEMA_V2",
    "R2SLEIGH_PLANNER_ANALYSIS_POLICY_V2",
    "R2SLEIGH_PLANNER_POST_ANALYSIS_V2",
    "R2SLEIGH_PLANNER_AUTO_CALLBACK_V2",
    "R2SLEIGH_MODE_FAST_V2",
    "R2SLEIGH_MODE_BALANCED_V2",
    "R2SLEIGH_MODE_FULL_V2",
    "R2SLEIGH_TYPE_WRITEBACK_OFF_V2",
    "R2SLEIGH_TYPE_WRITEBACK_BALANCED_V2",
    "R2SLEIGH_TYPE_WRITEBACK_AGGRESSIVE_V2",
    "R2SLEIGH_AUTO_CALLBACK_ANALYZE_FUNCTION_V2",
    "R2SLEIGH_AUTO_CALLBACK_RECOVER_VARS_V2",
    "R2SLEIGH_AUTO_CALLBACK_DATA_REFS_V2",
    "R2SLEIGH_AUTO_CALLBACK_POST_ANALYSIS_TAINT_V2",
    "R2SLEIGH_AUTO_CALLBACK_POST_ANALYSIS_XREF_V2",
    "R2SLEIGH_AUTO_CALLBACK_REASON_ALLOWED_V2",
    "R2SLEIGH_AUTO_CALLBACK_REASON_MODE_NOT_FULL_V2",
    "R2SLEIGH_AUTO_CALLBACK_REASON_TOO_MANY_BLOCKS_V2",
    "R2SLEIGH_AUTO_CALLBACK_REASON_TOO_LARGE_V2",
    "R2SLEIGH_AUTO_CALLBACK_REASON_TOO_COSTLY_V2",
    "R2SleighApiV2",
    "R2SleighByteViewV2",
    "R2SleighEngineRequestPayloadV2",
    "R2SleighPhaseTimingV2",
    "R2SleighResponseInfoV2",
    "R2SleighRequestV2",
    "R2SleighSessionConfigV2",
    "R2SleighSessionV2",
    "R2SleighResponseV2",
    "R2SleighOwnedBytesV2",
    "R2SleighSwitchCaseV2",
    "R2SleighDirectCallIdentityV2",
    "R2SleighStringViewV2",
    "R2SleighRadareSnapshotInputV2",
    "R2SleighRadareAccessorsV2",
    "R2SleighRadareSnapshotViewV2",
    "R2SleighRadareBlockViewV2",
    "R2SleighRadareSuccessorViewV2",
    "R2SleighRadareRegisterStorageViewV2",
    "R2SleighRadareCarrierProjectionV2",
    "R2SleighRadareParameterViewV2",
    "R2SleighRadareFunctionInterfaceViewV2",
    "R2SleighRadareCallSiteViewV2",
    "R2SleighRadareTypeGraphViewV2",
    "R2SleighRadareTypeViewV2",
    "R2SleighRadareAggregateViewV2",
    "R2SleighRadareAggregateMemberViewV2",
    "R2SleighRadareStackSlotViewV2",
    "R2SleighAnalysisRenderRequestV2",
    "R2SleighAnalysisQueryRequestV2",
    "R2SleighAnalysisResultViewV2",
    "R2SleighAnalysisResultV2",
    "R2SleighAnalysisPolicyV2",
    "R2SleighPostAnalysisPlanV2",
    "R2SleighAutoCallbackPlanV2",
    "R2SleighPlannerQueryRequestV2",
    "R2SleighPlannerQueryResponseV2",
    "r2sleigh_api_v2",
];

fn main() {
    let crate_dir = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let checked_header = crate_dir.join("r2sleigh_api_v2.h");
    let generated_header = PathBuf::from(env::var_os("OUT_DIR").unwrap()).join("r2sleigh_api_v2.h");

    println!("cargo:rerun-if-changed=src/ffi_v2.rs");
    println!("cargo:rerun-if-changed=r2sleigh_api_v2.h");
    println!("cargo:rerun-if-env-changed=R2SLEIGH_UPDATE_FFI_V2_HEADER");

    let config = cbindgen::Config {
        language: cbindgen::Language::C,
        cpp_compat: true,
        include_guard: Some("R2SLEIGH_API_V2_H".to_string()),
        after_includes: Some(
            "typedef struct R2ILContext R2ILContext;\ntypedef struct R2ILBlock R2ILBlock;"
                .to_string(),
        ),
        autogen_warning: Some(
            "/* Generated from Rust declarations in src/ffi_v2.rs. Do not edit. */".to_string(),
        ),
        documentation: true,
        usize_is_size_t: true,
        export: cbindgen::ExportConfig {
            include: EXPORTED_ITEMS.iter().map(|item| item.to_string()).collect(),
            ..Default::default()
        },
        ..Default::default()
    };

    let bindings = cbindgen::Builder::new()
        .with_src(crate_dir.join("src/ffi_v2.rs"))
        .with_config(config)
        .generate()
        .expect("generate r2sleigh V2 C header from Rust declarations");
    bindings.write_to_file(&generated_header);

    let generated = fs::read(&generated_header).expect("read generated V2 header");
    if env::var_os("R2SLEIGH_UPDATE_FFI_V2_HEADER").is_some() {
        fs::write(&checked_header, generated).expect("update checked V2 header");
        return;
    }
    let checked = fs::read(&checked_header).unwrap_or_default();
    assert_eq!(
        checked, generated,
        "r2sleigh_api_v2.h is stale; run R2SLEIGH_UPDATE_FFI_V2_HEADER=1 cargo check -p r2sleigh-plugin"
    );
}
