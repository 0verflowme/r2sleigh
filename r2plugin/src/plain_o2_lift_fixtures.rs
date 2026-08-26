use super::*;
use crate::analysis::ssa::r2ssa_function_json;
use serde::Deserialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

const CAPTURE_JSON: &str = include_str!("../tests/plain_o2_lift_v3.json");
const ORIGIN_MANIFEST_JSON: &str =
    include_str!("../../tests/r2r/fixtures/plain_o2_v1/manifest.json");
const ORIGIN_CORE_JSON: &str =
    include_str!("../../tests/r2r/fixtures/plain_o2_v1/core-functions.json");
const TEST_FUNC_BINARY: &[u8] =
    include_bytes!("../../tests/r2r/bins/r2sleigh_test_func_x86_64_macho_O2_v1");
const VULN_TEST_BINARY: &[u8] =
    include_bytes!("../../tests/r2r/bins/r2sleigh_vuln_test_x86_64_macho_O2_v1");
const TEST_FUNC_SOURCE: &[u8] = include_bytes!("../../tests/e2e/test_func.c");
const VULN_TEST_SOURCE: &[u8] = include_bytes!("../../tests/e2e/vuln_test.c");

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

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
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
    drop_test_ffi_string(value);
    owned
}

fn artifact_bytes(artifact: &str) -> &'static [u8] {
    match artifact {
        "test_func-x86_64-macho-O2-v1" => TEST_FUNC_BINARY,
        "vuln_test-x86_64-macho-O2-v1" => VULN_TEST_BINARY,
        artifact => panic!("unknown plain O2 artifact {artifact}"),
    }
}

fn source_bytes(artifact: &str) -> &'static [u8] {
    match artifact {
        "test_func-x86_64-macho-O2-v1" => TEST_FUNC_SOURCE,
        "vuln_test-x86_64-macho-O2-v1" => VULN_TEST_SOURCE,
        artifact => panic!("unknown plain O2 artifact {artifact}"),
    }
}

fn assert_origin(capture: &LiftCapture, function: &FunctionCapture) {
    assert_eq!(capture.schema_version, 3);
    assert_eq!(
        capture.fixture_set,
        "r2sleigh-plain-o2-x86_64-macho-sleigh-lift-v3"
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
    assert_eq!(sha256(binary), artifact.sha256);
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
    assert_eq!(manifest_artifact["sha256"], sha256(binary));
    assert_eq!(
        manifest_artifact["source_sha256"],
        sha256(source_bytes(&artifact.id))
    );
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

fn assert_captured_abi_facts(function: &FunctionCapture, ssa: &Value, blocks: &[R2ILBlock]) {
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
                    && formal["value_id"].is_u64()
                    && formal["value"]["name"]
                        .as_str()
                        .is_some_and(|value| value.eq_ignore_ascii_case(&parameter.register))
                    && formal["value"]["version"].is_u64()
                    && formal["value"]["size"].is_u64()
                    && formal["canonical_storage"].is_object()
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
    let mut capture_mismatches = Vec::new();
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
        let actual_ops_hash =
            json_fnv1a64(serde_json::to_value(&block_ref.ops).expect("R2IL ops JSON"));
        if actual_ops_hash != expected.ops_fnv1a64 {
            capture_mismatches.push(format!(
                "block 0x{:x} R2IL hash: expected {}, actual {}",
                expected.address, expected.ops_fnv1a64, actual_ops_hash
            ));
        }
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
    let actual_r2il_hash = json_fnv1a64(r2il_capture);
    if actual_r2il_hash != function.r2il_fnv1a64 {
        capture_mismatches.push(format!(
            "function R2IL hash: expected {}, actual {}",
            function.r2il_fnv1a64, actual_r2il_hash
        ));
    }

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
    assert_eq!(
        ssa["schema_version"],
        crate::SSA_JSON_SCHEMA_VERSION,
        "prepared SSA JSON must carry the current document schema"
    );
    let actual_ssa_hash = json_fnv1a64(ssa.clone());
    if actual_ssa_hash != function.ssa_fnv1a64 {
        capture_mismatches.push(format!(
            "function SSA hash: expected {}, actual {}",
            function.ssa_fnv1a64, actual_ssa_hash
        ));
    }
    let ssa_blocks = ssa["blocks"].as_array().expect("SSA blocks");
    assert_eq!(ssa_blocks.len(), function.ssa_blocks.len());
    for (actual, expected) in ssa_blocks.iter().zip(&function.ssa_blocks) {
        assert_eq!(actual["addr"], expected.address);
        assert_eq!(actual["size"], expected.size);
        let actual_phi_count = actual["phis"].as_array().expect("SSA phis").len();
        if actual_phi_count != expected.phi_count {
            capture_mismatches.push(format!(
                "SSA block 0x{:x} phi count: expected {}, actual {}",
                expected.address, expected.phi_count, actual_phi_count
            ));
        }
        let actual_op_count = actual["ops"].as_array().expect("SSA ops").len();
        if actual_op_count != expected.op_count {
            capture_mismatches.push(format!(
                "SSA block 0x{:x} op count: expected {}, actual {}",
                expected.address, expected.op_count, actual_op_count
            ));
        }
        let actual_block_hash = json_fnv1a64(actual.clone());
        if actual_block_hash != expected.fnv1a64 {
            capture_mismatches.push(format!(
                "SSA block 0x{:x} hash: expected {}, actual {}",
                expected.address, expected.fnv1a64, actual_block_hash
            ));
        }
    }

    let owned_blocks = lifted_refs
        .iter()
        .map(|block| (**block).clone())
        .collect::<Vec<_>>();
    assert_captured_abi_facts(function, &ssa, &owned_blocks);

    assert!(
        capture_mismatches.is_empty(),
        "{} capture drift:\n{}",
        function.name,
        capture_mismatches.join("\n")
    );

    for block in lifted {
        drop_test_block(block);
    }
    drop_test_context(context);
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
