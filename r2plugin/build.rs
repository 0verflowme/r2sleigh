use std::env;
use std::fs;
use std::path::PathBuf;

const EXPORTED_ITEMS: &[&str] = &[
    "R2SLEIGH_ABI_V2",
    "R2SLEIGH_CAP_DECOMPILE_V2",
    "R2SLEIGH_CAP_TYPE_FUNCTION_V2",
    "R2SLEIGH_CAP_EXACT_FUNCTION_INTERFACE_V2",
    "R2SLEIGH_CAP_CALL_SITE_INTERFACES_V2",
    "R2SLEIGH_CAP_NATIVE_REQUEST_GRAPH_V2",
    "R2SLEIGH_CAP_RESPONSE_INFO_V2",
    "R2SLEIGH_CAP_EXECUTION_CONTROL_V2",
    "R2SLEIGH_CAP_EXACT_TYPE_LAYOUT_V2",
    "R2SLEIGH_CAP_EXACT_STACK_SLOT_ROLES_V2",
    "R2SLEIGH_CAPABILITIES_V2",
    "R2SLEIGH_RADARE_ABI_V2",
    "R2SLEIGH_STATUS_OK_V2",
    "R2SLEIGH_STATUS_INVALID_ARGUMENT_V2",
    "R2SLEIGH_STATUS_ABI_MISMATCH_V2",
    "R2SLEIGH_STATUS_UNSUPPORTED_V2",
    "R2SLEIGH_STATUS_LIMIT_EXCEEDED_V2",
    "R2SLEIGH_STATUS_ENGINE_ERROR_V2",
    "R2SLEIGH_STATUS_PANIC_V2",
    "R2SLEIGH_REQUEST_DECOMPILE_V2",
    "R2SLEIGH_REQUEST_TYPE_FUNCTION_V2",
    "R2SLEIGH_FUNCTION_CONTEXT_SCHEMA_V2",
    "R2SLEIGH_INTERPROC_SCOPE_SCHEMA_V2",
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
    "R2SLEIGH_SOURCE_RETURN_VOID_V2",
    "R2SLEIGH_SOURCE_RETURN_REGISTER_V2",
    "R2SLEIGH_SOURCE_STACK_BASE_BP_V2",
    "R2SLEIGH_SOURCE_STACK_BASE_SP_V2",
    "R2SLEIGH_SOURCE_STACK_ROLE_LOCAL_V2",
    "R2SLEIGH_SOURCE_STACK_ROLE_PARAMETER_HOME_V2",
    "R2SLEIGH_SOURCE_PARAMETER_INDEX_INVALID_V2",
    "R2SLEIGH_SOURCE_STORAGE_RAM_V2",
    "R2SLEIGH_SOURCE_STORAGE_REGISTER_V2",
    "R2SLEIGH_SOURCE_STORAGE_UNIQUE_V2",
    "R2SLEIGH_SOURCE_STORAGE_CONSTANT_V2",
    "R2SLEIGH_SOURCE_STORAGE_CUSTOM_V2",
    "R2SLEIGH_SOURCE_INTERFACE_SCHEMA_V2",
    "R2SLEIGH_SOURCE_CALL_SITE_SCHEMA_V2",
    "R2SLEIGH_SOURCE_TYPE_ID_INVALID_V2",
    "R2SLEIGH_SOURCE_TYPE_SIGNED_INTEGER_V2",
    "R2SLEIGH_SOURCE_TYPE_UNSIGNED_INTEGER_V2",
    "R2SLEIGH_SOURCE_TYPE_POINTER_V2",
    "R2SLEIGH_SOURCE_TYPE_STRUCT_V2",
    "R2SLEIGH_SOURCE_CARRIER_INVALID_V2",
    "R2SLEIGH_SOURCE_CARRIER_FULL_V2",
    "R2SLEIGH_SOURCE_CARRIER_LOW_BITS_V2",
    "R2SLEIGH_MAX_FUNCTION_BLOCKS_V2",
    "R2SLEIGH_MAX_FUNCTION_OPS_V2",
    "R2SLEIGH_MAX_FUNCTION_INPUT_BYTES_V2",
    "R2SLEIGH_MAX_AGGREGATE_BLOCKS_V2",
    "R2SLEIGH_MAX_AGGREGATE_OPS_V2",
    "R2SLEIGH_MAX_SCOPE_FUNCTIONS_V2",
    "R2SLEIGH_MAX_CONTEXT_ITEMS_V2",
    "R2SLEIGH_MAX_NESTED_ITEMS_V2",
    "R2SLEIGH_MAX_STRING_BYTES_V2",
    "R2SLEIGH_MAX_AGGREGATE_STRING_BYTES_V2",
    "R2SLEIGH_MAX_JSON_BYTES_V2",
    "R2SLEIGH_MAX_AGGREGATE_JSON_BYTES_V2",
    "R2SleighApiV2",
    "R2SleighByteViewV2",
    "R2SleighEngineRequestPayloadV2",
    "R2SleighContextParam",
    "R2SleighContextVar",
    "R2SleighContextBaseMember",
    "R2SleighContextEnumVariant",
    "R2SleighContextBaseType",
    "R2SleighContextCallee",
    "R2SleighFunctionContext",
    "R2SleighInterprocSeed",
    "R2SleighInterprocScope",
    "R2SleighInterprocSessionPlan",
    "R2SleighLiftQuality",
    "R2SleighPhaseTimingV2",
    "R2SleighResponseInfoV2",
    "R2SleighRequestV2",
    "R2SleighSessionConfigV2",
    "R2SleighSessionV2",
    "R2SleighResponseV2",
    "R2SleighSourceFunctionInterfaceV2",
    "R2SleighSourceParameterV2",
    "R2SleighSourceParameterTypeV2",
    "R2SleighSourceCarrierProjectionV2",
    "R2SleighSourceTypeV2",
    "R2SleighSourceAggregateMemberV2",
    "R2SleighSourceAggregateLayoutV2",
    "R2SleighSourceRegisterV2",
    "R2SleighSourceStackSlotV2",
    "R2SleighSourceStorageV2",
    "R2SleighSourceCallArgumentV2",
    "R2SleighSourceCallSiteInterfaceV2",
    "R2SleighStringViewV2",
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
            "typedef struct R2ILContext R2ILContext;\ntypedef struct R2ILBlock R2ILBlock;\ntypedef struct R2ILFunctionBlocks R2ILFunctionBlocks;"
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
