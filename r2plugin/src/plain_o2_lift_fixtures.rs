use super::*;
use crate::analysis::ssa::r2ssa_function_json;
use serde::Deserialize;
use serde_json::Value;
use std::sync::Arc;

const CAPTURE_JSON: &str = include_str!("../tests/plain_o2_lift_v1.json");
const ORIGIN_MANIFEST_JSON: &str =
    include_str!("../../tests/r2r/fixtures/plain_o2_v1/manifest.json");
const ORIGIN_CORE_JSON: &str =
    include_str!("../../tests/r2r/fixtures/plain_o2_v1/core-functions.json");
const TEST_FUNC_BINARY: &[u8] =
    include_bytes!("../../tests/r2r/bins/r2sleigh_test_func_x86_64_macho_O2_v1");
const VULN_TEST_BINARY: &[u8] =
    include_bytes!("../../tests/r2r/bins/r2sleigh_vuln_test_x86_64_macho_O2_v1");

#[derive(Debug, Deserialize)]
struct LiftCapture {
    schema_version: u32,
    fixture_set: String,
    origin_manifest: String,
    origin_core_capture: String,
    arch: String,
    custom_space_normalization: String,
    artifacts: Vec<ArtifactCapture>,
    functions: Vec<FunctionCapture>,
}

#[derive(Debug, Deserialize)]
struct ArtifactCapture {
    id: String,
    path: String,
    sha256: String,
    size_bytes: usize,
    fnv1a64: String,
}

#[derive(Debug, Deserialize)]
struct FunctionCapture {
    name: String,
    symbol: String,
    artifact: String,
    source: String,
    address: u64,
    file_offset: usize,
    bytes: String,
    bytes_fnv1a64: String,
    r2il_fnv1a64: String,
    ssa_fnv1a64: String,
    #[serde(default)]
    required_native_opcodes: Vec<String>,
    source_abi: SourceAbiCapture,
    blocks: Vec<BlockCapture>,
    ssa_blocks: Vec<SsaBlockCapture>,
}

#[derive(Debug, Deserialize)]
struct SourceAbiCapture {
    calling_convention: String,
    return_type: String,
    parameters: Vec<SourceParameterCapture>,
    aggregate: Option<SourceAggregateCapture>,
}

#[derive(Debug, Deserialize)]
struct SourceParameterCapture {
    name: String,
    register: String,
    #[serde(rename = "type")]
    type_name: String,
}

#[derive(Debug, Deserialize)]
struct SourceAggregateCapture {
    name: String,
    size_bytes: u64,
    align_bytes: u64,
    member_offsets: Vec<u64>,
}

#[derive(Debug, Deserialize)]
struct BlockCapture {
    address: u64,
    bytes: String,
    op_count: usize,
    ops_fnv1a64: String,
    op_kinds: String,
}

#[derive(Debug, Deserialize)]
struct SsaBlockCapture {
    address: u64,
    size: u32,
    phi_count: usize,
    op_count: usize,
    fnv1a64: String,
}

fn fixture() -> LiftCapture {
    serde_json::from_str(CAPTURE_JSON).expect("valid plain O2 Sleigh lift fixture")
}

fn decode_hex(hex: &str) -> Vec<u8> {
    assert_eq!(hex.len() % 2, 0, "hex input must have even length");
    hex.as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
            let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
            (hi << 4) | lo
        })
        .collect()
}

fn fnv1a64(bytes: &[u8]) -> String {
    let hash = bytes.iter().fold(0xcbf2_9ce4_8422_2325u64, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3)
    });
    format!("{hash:016x}")
}

fn canonical_json(value: Value) -> Value {
    match value {
        Value::Array(values) => {
            Value::Array(values.into_iter().map(canonical_json).collect::<Vec<_>>())
        }
        Value::Object(values) => {
            if values.len() == 1 && values.get("Custom").is_some_and(Value::is_number) {
                return serde_json::json!({ "Custom": "architecture_custom" });
            }
            let mut entries = values.into_iter().collect::<Vec<_>>();
            entries.sort_by(|left, right| left.0.cmp(&right.0));
            Value::Object(
                entries
                    .into_iter()
                    .map(|(key, value)| (key, canonical_json(value)))
                    .collect(),
            )
        }
        value => value,
    }
}

fn json_fnv1a64(value: Value) -> String {
    let encoded = serde_json::to_vec(&canonical_json(value)).expect("canonical JSON");
    fnv1a64(&encoded)
}

fn take_ffi_string(value: *mut c_char) -> String {
    assert!(!value.is_null(), "expected owned FFI string");
    let owned = unsafe { CStr::from_ptr(value) }
        .to_str()
        .expect("UTF-8 FFI string")
        .to_string();
    r2il_string_free(value);
    owned
}

fn artifact_bytes(artifact: &str) -> &'static [u8] {
    match artifact {
        "test_func-x86_64-macho-O2-v1" => TEST_FUNC_BINARY,
        "vuln_test-x86_64-macho-O2-v1" => VULN_TEST_BINARY,
        artifact => panic!("unknown plain O2 artifact {artifact}"),
    }
}

fn assert_origin(capture: &LiftCapture, function: &FunctionCapture) {
    assert_eq!(capture.schema_version, 1);
    assert_eq!(
        capture.fixture_set,
        "r2sleigh-plain-o2-x86_64-macho-sleigh-lift-v1"
    );
    assert_eq!(
        capture.origin_manifest,
        "tests/r2r/fixtures/plain_o2_v1/manifest.json"
    );
    assert_eq!(
        capture.origin_core_capture,
        "tests/r2r/fixtures/plain_o2_v1/core-functions.json"
    );
    assert_eq!(capture.arch, "x86-64");
    assert_eq!(
        capture.custom_space_normalization,
        "Process-local libsla custom-space handles are normalized to architecture_custom before semantic hashing."
    );

    let artifact = capture
        .artifacts
        .iter()
        .find(|artifact| artifact.id == function.artifact)
        .expect("fixture artifact");
    let binary = artifact_bytes(&artifact.id);
    assert_eq!(binary.len(), artifact.size_bytes);
    assert_eq!(fnv1a64(binary), artifact.fnv1a64);

    let manifest: Value = serde_json::from_str(ORIGIN_MANIFEST_JSON).expect("origin manifest");
    assert_eq!(manifest["fixture_set"], "r2sleigh-plain-o2-x86_64-macho-v1");
    let manifest_artifact = manifest["artifacts"]
        .as_array()
        .expect("manifest artifacts")
        .iter()
        .find(|candidate| candidate["id"] == artifact.id)
        .expect("manifest artifact");
    assert_eq!(manifest_artifact["path"], artifact.path);
    assert_eq!(manifest_artifact["sha256"], artifact.sha256);
    assert_eq!(manifest_artifact["size_bytes"], artifact.size_bytes);
    assert_eq!(manifest_artifact["source"], function.source);
    let manifest_symbol = manifest_artifact["required_symbols"]
        .as_array()
        .expect("required symbols")
        .iter()
        .find(|candidate| candidate["name"].as_str() == function.symbol.strip_prefix("sym."))
        .expect("manifest symbol");
    assert_eq!(
        manifest_symbol["start_vaddr"],
        format!("0x{:x}", function.address)
    );

    let function_bytes = decode_hex(&function.bytes);
    assert_eq!(fnv1a64(&function_bytes), function.bytes_fnv1a64);
    let occurrences = binary
        .windows(function_bytes.len())
        .enumerate()
        .filter_map(|(offset, bytes)| (bytes == function_bytes).then_some(offset))
        .collect::<Vec<_>>();
    assert_eq!(occurrences, vec![function.file_offset]);

    let core: Value = serde_json::from_str(ORIGIN_CORE_JSON).expect("origin core capture");
    let core_function = core["functions"]
        .as_array()
        .expect("core functions")
        .iter()
        .find(|candidate| candidate["name"] == function.symbol)
        .expect("core function");
    assert_eq!(core_function["addr"], function.address);
    assert_eq!(core_function["size"], function_bytes.len());
    assert_eq!(core_function["bytes"], function.bytes);
    let instructions = core_function["instructions"]
        .as_array()
        .expect("core instructions");
    for required_opcode in &function.required_native_opcodes {
        assert!(
            instructions.iter().any(|instruction| {
                instruction["opcode"]
                    .as_str()
                    .is_some_and(|opcode| opcode.starts_with(required_opcode))
            }),
            "{} must retain compiler-generated {required_opcode}",
            function.name
        );
    }
}

fn assert_source_snapshot(function: &FunctionCapture, ssa: &Value, blocks: &[R2ILBlock]) {
    assert_eq!(function.source_abi.calling_convention, "sysv_amd64");
    assert_eq!(function.source_abi.return_type, "int32_t");
    let prepared = ssa["prepared"].as_object().expect("prepared SSA facts");
    let formal_parameters = prepared["formal_parameters"]
        .as_array()
        .expect("formal parameters");
    for (parameter_index, parameter) in function.source_abi.parameters.iter().enumerate() {
        assert!(!parameter.name.is_empty());
        assert!(
            formal_parameters.iter().any(|formal| {
                formal["parameter"] == parameter_index
                    && formal["value"]
                        .as_str()
                        .is_some_and(|value| value.starts_with(&parameter.register))
            }),
            "{} source ABI parameter {} in {} must bind {}",
            function.name,
            parameter.name,
            parameter_index,
            parameter.register
        );
    }

    let (arch, _) = create_disassembler_for_arch("x86-64").expect("x86-64 disassembler");
    let prepared_ssa =
        r2ssa::SsaArtifact::for_patterns(blocks, Some(&arch)).expect("pattern SSA fixture");
    let inferred = r2types::recover_signature_params_from_ssa(
        &prepared_ssa.local_ssa_blocks(),
        Some("x86-64"),
        &std::collections::HashMap::new(),
        false,
        64,
    );
    for (parameter_index, parameter) in function.source_abi.parameters.iter().enumerate() {
        let inferred = inferred
            .iter()
            .find(|inferred| inferred.name == format!("arg{parameter_index}"))
            .unwrap_or_else(|| {
                panic!(
                    "missing inferred arg{parameter_index} for {}",
                    function.name
                )
            });
        if parameter.type_name.ends_with('*') {
            assert!(
                matches!(inferred.initial_ty, r2types::CTypeLike::Pointer(_)),
                "{} {} must remain pointer-shaped: {inferred:?}",
                function.name,
                parameter.name
            );
        } else {
            assert_eq!(
                r2types::render_signature_type(&inferred.initial_ty, 64),
                parameter.type_name,
                "{} {} scalar source type",
                function.name,
                parameter.name
            );
        }
    }

    if let Some(aggregate) = &function.source_abi.aggregate {
        assert_eq!(aggregate.name, "DemoStruct");
        assert_eq!(aggregate.size_bytes, 56);
        assert_eq!(aggregate.align_bytes, 4);
        assert_eq!(
            aggregate.member_offsets,
            (0..14).map(|index| index * 4).collect::<Vec<_>>()
        );
        let parameter_addresses = prepared["parameter_addresses"]
            .as_array()
            .expect("parameter addresses");
        for offset in [8, 52] {
            assert!(
                parameter_addresses.iter().any(|address| {
                    address["parameter"] == 0
                        && address["offset"] == offset
                        && address["terms"]
                            .as_array()
                            .is_some_and(|terms| terms.iter().any(|term| term["coefficient"] == 56))
                }),
                "{} must retain DemoStruct stride 56 at offset {offset}",
                function.name
            );
        }
    }
}

fn full_register_storage(arch: &ArchSpec, name: &str) -> r2ssa::CanonicalStorageId {
    let register = arch
        .registers
        .iter()
        .find(|register| register.name.eq_ignore_ascii_case(name))
        .unwrap_or_else(|| panic!("missing physical {name} register"));
    assert_eq!(register.size, 8, "{name} must be a full ABI carrier");
    r2ssa::CanonicalStorageId {
        space: r2ssa::CanonicalStorageSpace::Register,
        offset: register.offset,
        size: register.size,
    }
}

fn exact_branchless_source_snapshot(
    function: &FunctionCapture,
    arch: &ArchSpec,
) -> Arc<r2engine::EngineSourceSnapshot> {
    let revision = format!(
        "plain-o2-branchless-{}-{}",
        function.address, function.bytes_fnv1a64
    )
    .into_bytes();
    let parameter_count = function.source_abi.parameters.len();
    assert!(matches!(parameter_count, 1 | 2));
    let parameter_storages = [
        full_register_storage(arch, "RDI"),
        full_register_storage(arch, "RSI"),
    ];
    let return_storage = full_register_storage(arch, "RAX");
    let low32 = r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::LowBits, 0, 32);
    let graph = r2ssa::SourceTypeGraph::new(
        [r2ssa::SourceType::new(
            0,
            r2ssa::SourceTypeKind::SignedInteger,
            32,
            32,
        )],
        [],
    )
    .expect("exact signed-32 source graph");
    let interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
        revision.clone(),
        "sysv_amd64",
        parameter_storages
            .into_iter()
            .take(parameter_count)
            .enumerate()
            .map(|(index, storage)| r2ssa::SourceAbiParameterSpec::new(index as u32, storage)),
        r2ssa::SourceFunctionReturn::Register {
            storage: return_storage,
        },
        [],
        (0..parameter_count).map(|_| r2ssa::SourceLogicalValue::new(0, low32)),
        Some(r2ssa::SourceLogicalValue::new(0, low32)),
        Some(graph),
    )
    .expect("exact branchless source interface");
    Arc::new(
        r2engine::EngineSourceSnapshot::new(revision, Some(interface), [])
            .expect("exact branchless source snapshot"),
    )
}

fn exact_struct_array_source_snapshot(
    function: &FunctionCapture,
    arch: &ArchSpec,
) -> Arc<r2engine::EngineSourceSnapshot> {
    let revision = format!(
        "plain-o2-struct-array-{}-{}",
        function.address, function.bytes_fnv1a64
    )
    .into_bytes();
    let parameter_storages = [
        full_register_storage(arch, "RDI"),
        full_register_storage(arch, "RSI"),
        full_register_storage(arch, "RDX"),
    ];
    let return_storage = full_register_storage(arch, "RAX");
    let low32 = r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::LowBits, 0, 32);
    let full64 = r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::Full, 0, 64);
    let graph = r2ssa::SourceTypeGraph::new(
        [
            r2ssa::SourceType::new(0, r2ssa::SourceTypeKind::SignedInteger, 32, 32),
            r2ssa::SourceType::new(
                1,
                r2ssa::SourceTypeKind::Struct { aggregate_id: 0 },
                448,
                32,
            ),
            r2ssa::SourceType::new(
                2,
                r2ssa::SourceTypeKind::Pointer { target_type_id: 1 },
                64,
                64,
            ),
        ],
        [r2ssa::SourceAggregateLayout::new(
            0,
            1,
            448,
            32,
            "DemoStruct",
            (0..14).map(|index| {
                r2ssa::SourceAggregateMember::new(
                    index,
                    0,
                    u64::from(index) * 32,
                    32,
                    format!("member{index}"),
                )
            }),
        )],
    )
    .expect("exact natural struct-array source graph");
    let interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
        revision.clone(),
        "sysv_amd64",
        parameter_storages
            .into_iter()
            .enumerate()
            .map(|(index, storage)| r2ssa::SourceAbiParameterSpec::new(index as u32, storage)),
        r2ssa::SourceFunctionReturn::Register {
            storage: return_storage,
        },
        [],
        [
            r2ssa::SourceLogicalValue::new(2, full64),
            r2ssa::SourceLogicalValue::new(0, low32),
            r2ssa::SourceLogicalValue::new(0, low32),
        ],
        Some(r2ssa::SourceLogicalValue::new(0, low32)),
        Some(graph),
    )
    .expect("exact struct-array source interface");
    Arc::new(
        r2engine::EngineSourceSnapshot::new(revision, Some(interface), [])
            .expect("exact struct-array source snapshot"),
    )
}

fn exact_sum_array_source_snapshot(
    function: &FunctionCapture,
    arch: &ArchSpec,
) -> Arc<r2engine::EngineSourceSnapshot> {
    assert_eq!(function.name, "sum_array");
    assert_eq!(function.source_abi.parameters.len(), 2);
    let revision = format!(
        "plain-o2-sum-array-{}-{}",
        function.address, function.bytes_fnv1a64
    )
    .into_bytes();
    let return_storage = full_register_storage(arch, "RAX");
    let low32 = r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::LowBits, 0, 32);
    let full64 = r2ssa::SourceCarrierProjection::new(r2ssa::SourceCarrierKind::Full, 0, 64);
    let graph = r2ssa::SourceTypeGraph::new(
        [
            r2ssa::SourceType::new(0, r2ssa::SourceTypeKind::SignedInteger, 32, 32),
            r2ssa::SourceType::new(
                1,
                r2ssa::SourceTypeKind::Pointer { target_type_id: 0 },
                64,
                64,
            ),
        ],
        [],
    )
    .expect("exact sum-array source graph");
    let interface = r2ssa::SourceFunctionInterface::new_exact_with_logical_types(
        revision.clone(),
        "sysv_amd64",
        [
            r2ssa::SourceAbiParameterSpec::new(0, full_register_storage(arch, "RDI")),
            r2ssa::SourceAbiParameterSpec::new(1, full_register_storage(arch, "RSI")),
        ],
        r2ssa::SourceFunctionReturn::Register {
            storage: return_storage,
        },
        [],
        [
            r2ssa::SourceLogicalValue::new(1, full64),
            r2ssa::SourceLogicalValue::new(0, low32),
        ],
        Some(r2ssa::SourceLogicalValue::new(0, low32)),
        Some(graph),
    )
    .expect("exact sum-array source interface");
    Arc::new(
        r2engine::EngineSourceSnapshot::new(revision, Some(interface), [])
            .expect("exact sum-array source snapshot"),
    )
}

fn assert_branchless_production_route(
    function: &FunctionCapture,
    blocks: &[R2ILBlock],
    arch: &ArchSpec,
) {
    if !matches!(function.name.as_str(), "check_secret" | "complex_check") {
        return;
    }
    let response = r2engine::EngineSession::new(4).decompile_function_from_input(
        r2engine::EngineFunctionDecompileRequestInput::single_function(
            r2engine::EngineFunctionInput {
                function_name: function.symbol.clone(),
                function_addr: function.address,
                blocks: blocks.to_vec(),
                arch: Some(arch.clone()),
                source_snapshot: Some(exact_branchless_source_snapshot(function, arch)),
                semantic_metadata_enabled: true,
            },
            Some(64),
            r2types::ParsedExternalContext::default(),
            0,
        ),
    );
    assert_eq!(
        response.diagnostics.semantic_kernel_render,
        Some(r2engine::EngineSemanticKernelRender {
            region: r2engine::EngineSemanticKernelRegion::BranchlessGuardFunction,
            region_schema_version:
                r2dec::CERTIFIED_BRANCHLESS_GUARD_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            exact_obligation_closure: true,
        }),
        "{} must reach the exact production route: {}",
        function.name,
        response.output
    );
    assert!(response.output.contains("#include <stdint.h>"));
    if function.name == "check_secret" {
        assert!(response.output.contains("== UINT32_C(0xdead)"));
    } else {
        assert!(response.output.contains("sum_bits == UINT32_C(0x64)"));
        assert!(
            response
                .output
                .contains("difference_bits == UINT32_C(0x14)")
        );
    }
}

fn assert_struct_array_production_route(
    function: &FunctionCapture,
    blocks: &[R2ILBlock],
    arch: &ArchSpec,
) {
    if function.name != "test_struct_array_index" {
        return;
    }
    let response = r2engine::EngineSession::new(4).decompile_function_from_input(
        r2engine::EngineFunctionDecompileRequestInput::single_function(
            r2engine::EngineFunctionInput {
                function_name: function.symbol.clone(),
                function_addr: function.address,
                blocks: blocks.to_vec(),
                arch: Some(arch.clone()),
                source_snapshot: Some(exact_struct_array_source_snapshot(function, arch)),
                semantic_metadata_enabled: true,
            },
            Some(64),
            r2types::ParsedExternalContext::default(),
            0,
        ),
    );
    assert_eq!(
        response.diagnostics.semantic_kernel_render,
        Some(r2engine::EngineSemanticKernelRender {
            region: r2engine::EngineSemanticKernelRegion::StructArrayIndexFunction,
            region_schema_version:
                r2dec::CERTIFIED_STRUCT_ARRAY_INDEX_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            exact_obligation_closure: true,
        }),
        "{} must reach the exact production route: {}",
        function.name,
        response.output
    );
    assert!(
        response
            .output
            .contains("typedef struct r2s_type_DemoStruct")
    );
    assert!(response.output.contains("member2 = r2s_arg2_value"));
    assert!(response.output.contains("member13"));
}

fn assert_sum_array_production_route(
    function: &FunctionCapture,
    blocks: &[R2ILBlock],
    arch: &ArchSpec,
) {
    if function.name != "sum_array" {
        return;
    }
    let response = r2engine::EngineSession::new(4).decompile_function_from_input(
        r2engine::EngineFunctionDecompileRequestInput::single_function(
            r2engine::EngineFunctionInput {
                function_name: function.symbol.clone(),
                function_addr: function.address,
                blocks: blocks.to_vec(),
                arch: Some(arch.clone()),
                source_snapshot: Some(exact_sum_array_source_snapshot(function, arch)),
                semantic_metadata_enabled: true,
            },
            Some(64),
            r2types::ParsedExternalContext::default(),
            0,
        ),
    );
    assert_eq!(
        response.diagnostics.semantic_kernel_render,
        Some(r2engine::EngineSemanticKernelRender {
            region: r2engine::EngineSemanticKernelRegion::SumArrayFunction,
            region_schema_version: r2dec::CERTIFIED_SUM_ARRAY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            exact_obligation_closure: true,
        }),
        "{} must reach the exact production route: {}",
        function.name,
        response.output
    );
    assert!(response.output.contains("#include <stdint.h>"));
    assert!(response.output.contains("const int32_t *r2s_arg0_array"));
    assert!(response.output.contains("int32_t r2s_arg1_length"));
    assert!(response.output.contains("if (r2s_arg1_length <= 0)"));
    assert!(response.output.contains("uint32_t r2s_sum_sum_bits"));
    assert!(
        response
            .output
            .contains("r2s_sum_sum_bits += (uint32_t)r2s_arg0_array[r2s_index_index]")
    );
    assert!(!response.output.contains("__m128"));
    assert!(!response.output.contains("goto"));
}

fn assert_function_capture(function_name: &str) {
    let capture = fixture();
    let function = capture
        .functions
        .iter()
        .find(|function| function.name == function_name)
        .expect("function fixture");
    assert_origin(&capture, function);

    let function_bytes = decode_hex(&function.bytes);
    let concatenated = function
        .blocks
        .iter()
        .flat_map(|block| decode_hex(&block.bytes))
        .collect::<Vec<_>>();
    assert_eq!(concatenated, function_bytes);
    let mut expected_address = function.address;
    for block in &function.blocks {
        assert_eq!(block.address, expected_address);
        expected_address += decode_hex(&block.bytes).len() as u64;
    }

    let arch_name = CString::new("x86-64").expect("arch name");
    let context = r2il_arch_init(arch_name.as_ptr());
    assert!(!context.is_null(), "x86-64 context");
    let mut lifted = Vec::new();
    for expected in &function.blocks {
        let bytes = decode_hex(&expected.bytes);
        let block = r2il_lift_block(
            context,
            bytes.as_ptr(),
            bytes.len(),
            expected.address,
            u32::try_from(bytes.len()).expect("block length fits u32"),
        );
        if block.is_null() {
            let error = r2il_error(context);
            let error = if error.is_null() {
                "unknown lift failure".to_string()
            } else {
                unsafe { CStr::from_ptr(error) }
                    .to_string_lossy()
                    .into_owned()
            };
            panic!(
                "{} residual at 0x{:x} for {}: {error}",
                function.name, expected.address, expected.bytes
            );
        }
        let block_ref = unsafe { &*block };
        assert_eq!(block_ref.addr, expected.address);
        assert_eq!(block_ref.size as usize, bytes.len());
        assert_eq!(block_ref.ops.len(), expected.op_count);
        assert!(block_ref.switch_info.is_none());
        let kinds = block_ref
            .ops
            .iter()
            .map(|op| {
                serde_json::to_value(op)
                    .expect("R2IL op JSON")
                    .as_object()
                    .and_then(|value| value.keys().next())
                    .expect("externally tagged R2IL op")
                    .to_string()
            })
            .collect::<Vec<_>>()
            .join(",");
        assert_eq!(kinds, expected.op_kinds);
        assert_eq!(
            json_fnv1a64(serde_json::to_value(&block_ref.ops).expect("R2IL ops JSON")),
            expected.ops_fnv1a64
        );
        lifted.push(block);
    }

    let lifted_refs = lifted
        .iter()
        .map(|block| unsafe { &**block })
        .collect::<Vec<_>>();
    let r2il_capture = Value::Array(
        lifted_refs
            .iter()
            .map(|block| {
                serde_json::json!({
                    "addr": block.addr,
                    "size": block.size,
                    "ops": &block.ops,
                })
            })
            .collect(),
    );
    assert_eq!(json_fnv1a64(r2il_capture), function.r2il_fnv1a64);

    let lifted_ptrs = lifted
        .iter()
        .map(|block| *block as *const R2ILBlock)
        .collect::<Vec<_>>();
    let first_ssa = take_ffi_string(r2ssa_function_json(
        context,
        lifted_ptrs.as_ptr(),
        lifted_ptrs.len(),
    ));
    let second_ssa = take_ffi_string(r2ssa_function_json(
        context,
        lifted_ptrs.as_ptr(),
        lifted_ptrs.len(),
    ));
    assert_eq!(first_ssa, second_ssa, "deterministic SSA reconstruction");
    let ssa: Value = serde_json::from_str(&first_ssa).expect("prepared SSA JSON");
    assert_eq!(json_fnv1a64(ssa.clone()), function.ssa_fnv1a64);
    let ssa_blocks = ssa["blocks"].as_array().expect("SSA blocks");
    assert_eq!(ssa_blocks.len(), function.ssa_blocks.len());
    for (actual, expected) in ssa_blocks.iter().zip(&function.ssa_blocks) {
        assert_eq!(actual["addr"], expected.address);
        assert_eq!(actual["size"], expected.size);
        assert_eq!(
            actual["phis"].as_array().expect("SSA phis").len(),
            expected.phi_count
        );
        assert_eq!(
            actual["ops"].as_array().expect("SSA ops").len(),
            expected.op_count
        );
        assert_eq!(json_fnv1a64(actual.clone()), expected.fnv1a64);
    }

    let owned_blocks = lifted_refs
        .iter()
        .map(|block| (**block).clone())
        .collect::<Vec<_>>();
    assert_source_snapshot(function, &ssa, &owned_blocks);
    let engine_arch = unsafe { &*context }
        .arch
        .as_ref()
        .expect("x86-64 architecture")
        .clone();
    assert_branchless_production_route(function, &owned_blocks, &engine_arch);
    assert_struct_array_production_route(function, &owned_blocks, &engine_arch);
    assert_sum_array_production_route(function, &owned_blocks, &engine_arch);

    for block in lifted {
        r2il_block_free(block);
    }
    r2il_free(context);
}

#[test]
#[cfg(feature = "x86")]
fn plain_o2_sum_array_has_exact_vectorized_offline_lift() {
    assert_function_capture("sum_array");
}

#[test]
#[cfg(feature = "x86")]
fn plain_o2_complex_check_has_exact_offline_lift() {
    assert_function_capture("complex_check");
}

#[test]
#[cfg(feature = "x86")]
fn plain_o2_struct_array_index_has_exact_offline_lift() {
    assert_function_capture("test_struct_array_index");
}

#[test]
#[cfg(feature = "x86")]
fn plain_o2_check_secret_has_exact_offline_lift() {
    assert_function_capture("check_secret");
}
