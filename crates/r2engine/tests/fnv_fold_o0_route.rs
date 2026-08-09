use std::fmt::Write;
use std::fs;
use std::process::Command;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use r2engine::{
    EngineFunctionDecompileRequestInput, EngineFunctionInput, EnginePhase, EnginePhaseStatus,
    EnginePlan, EngineSemanticKernelRegion, EngineSemanticKernelRender, EngineSession,
    EngineSourceSnapshot,
};
use r2il::{ArchSpec, R2ILBlock, R2ILOp, SpaceId, Varnode};
use r2sleigh_lift::{Disassembler, build_arch_spec};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierKind,
    SourceCarrierProjection, SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue,
    SourceStackSlotSpec, SourceType, SourceTypeGraph, SourceTypeKind, SsaArtifact,
    StackAddressBase,
};
use sha2::{Digest, Sha256};

const REAL_FNV_SOURCE_SHA256: &str =
    "6524278ba4cd32a72dcf9cbcc385275999a50c3449d0e97035736891bcddff09";
const REAL_FNV_O0_FUNCTION_SHA256: &str =
    "36af3c68ac0783e3d38125798a0644860fde98454361b46ebc72bd166b96f697";
const REAL_FNV_O0_BINARY_SHA256: &str =
    "295868f8dab7d5d3e3304b17bce6a19f8948cca620068492f081c658146fe3bb";
const REAL_FNV_O0_BINARY_PATH: &str = "tests/r2r/bins/r2sleigh_manual_limits_O0";
const REAL_FNV_O0_COMPILER_COMMAND: &str = "gcc -O0 -g -fno-inline -fno-omit-frame-pointer -fno-stack-protector -no-pie -o tests/r2r/bins/r2sleigh_manual_limits_O0 tests/gold/manual_limits.c";
const REAL_FNV_O0_BASE: u64 = 0x1_0000_075c;
const REAL_FNV_O0_BLOCKS: &[&str] = &[
    "ffc300d1e01700f9e11300f9687080d2a873aef208f6c1f2a88ce2f2e80f00f9ff0b00f901000014",
    "e80b40f9e91340f9080109eb42040054",
    "01000014",
    "e81740f9e90b40f90801098b08014039e83f0039e83f4039080501714b010054",
    "01000014",
    "e83f403908690171cc000054",
    "01000014",
    "e83f403908810011e83f003901000014",
    "e83f4039e90308aae80f40f9080109cae80f00f9e80f40f9693680d20920c0f2087d099be80f00f901000014",
    "e80b40f908050091e80b00f9dcffff17",
    "e00f40f9ffc30091c0035fd6",
];
const REVISION: &[u8] = b"engine-real-arm64-fnv-fold-o0-v1";

const EXPECTED_SEMANTIC_C: &str = "#include <stdint.h>\n\
\n\
uint64_t __FUNCTION__(const uint8_t *r2s_arg_bytes, uint64_t r2s_arg_length) {\n\
\tconst uint8_t *r2s_local_pointer = r2s_arg_bytes;\n\
\tuint64_t r2s_local_hash = UINT64_C(0x14650fb0739d0383);\n\
\tuint64_t r2s_local_remaining = r2s_arg_length;\n\
\twhile (r2s_local_remaining != UINT64_C(0x0)) {\n\
\t\tuint8_t r2s_local_byte = *r2s_local_pointer;\n\
\t\tuint32_t r2s_local_original = (uint32_t)r2s_local_byte;\n\
\t\tuint32_t r2s_local_range = (uint32_t)(r2s_local_original - UINT32_C(0x41));\n\
\t\tuint32_t r2s_local_lowercase = (uint32_t)(r2s_local_original | UINT32_C(0x20));\n\
\t\tuint32_t r2s_local_folded = (r2s_local_range < UINT32_C(0x1a)) ? r2s_local_lowercase : r2s_local_original;\n\
\t\tr2s_local_hash = (uint64_t)((r2s_local_hash ^ (uint64_t)r2s_local_folded) * UINT64_C(0x100000001b3));\n\
\t\tr2s_local_pointer = r2s_local_pointer + UINT64_C(0x1);\n\
\t\tr2s_local_remaining = (uint64_t)(r2s_local_remaining - UINT64_C(0x1));\n\
\t}\n\
\treturn r2s_local_hash;\n\
}\n";

fn decode_hex(encoded: &str) -> Vec<u8> {
    encoded
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let high = (pair[0] as char).to_digit(16).expect("hex digit") as u8;
            let low = (pair[1] as char).to_digit(16).expect("hex digit") as u8;
            (high << 4) | low
        })
        .collect()
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn real_storage(arch: &ArchSpec, register: &str) -> CanonicalStorageId {
    let register = arch
        .get_register(register)
        .expect("pinned AARCH64 register");
    CanonicalStorageId {
        space: CanonicalStorageSpace::Register,
        offset: register.offset,
        size: register.size,
    }
}

fn real_interface(arch: &ArchSpec, revision: &[u8]) -> SourceFunctionInterface {
    let sp = real_storage(arch, "sp");
    let slots = vec![
        SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, sp, 15, 1),
        SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, sp, 16, 8),
        SourceStackSlotSpec::new_local(StackAddressBase::StackPointer, sp, 24, 8),
        SourceStackSlotSpec::new_parameter_home(
            StackAddressBase::StackPointer,
            sp,
            32,
            8,
            1,
            real_storage(arch, "x1"),
        ),
        SourceStackSlotSpec::new_parameter_home(
            StackAddressBase::StackPointer,
            sp,
            40,
            8,
            0,
            real_storage(arch, "x0"),
        ),
    ];
    let types = SourceTypeGraph::new(
        [
            SourceType::new(0, SourceTypeKind::UnsignedInteger, 8, 8),
            SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
            SourceType::new(2, SourceTypeKind::UnsignedInteger, 64, 64),
        ],
        [],
    )
    .expect("real O0 FNV type graph");
    let full64 = SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64);
    SourceFunctionInterface::new_exact_with_logical_types(
        revision.to_vec(),
        "aapcs64",
        [
            SourceAbiParameterSpec::new(0, real_storage(arch, "x0")),
            SourceAbiParameterSpec::new(1, real_storage(arch, "x1")),
        ],
        SourceFunctionReturn::Register {
            storage: real_storage(arch, "x0"),
        },
        slots,
        [
            SourceLogicalValue::new(1, full64),
            SourceLogicalValue::new(2, full64),
        ],
        Some(SourceLogicalValue::new(2, full64)),
        Some(types),
    )
    .and_then(|interface| interface.with_return_address_storage(real_storage(arch, "x30")))
    .expect("real O0 FNV interface")
}

fn real_blocks_and_arch() -> (Vec<R2ILBlock>, ArchSpec) {
    let arch = build_arch_spec(
        sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
        sleigh_config::processor_aarch64::PSPEC_AARCH64,
        "aarch64",
    )
    .expect("AARCH64 architecture");
    let disassembler = Disassembler::from_sla(
        sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
        sleigh_config::processor_aarch64::PSPEC_AARCH64,
        "aarch64",
    )
    .expect("AARCH64 disassembler");
    let mut address = REAL_FNV_O0_BASE;
    let blocks = REAL_FNV_O0_BLOCKS
        .iter()
        .map(|encoded| {
            let bytes = decode_hex(encoded);
            let block = disassembler
                .lift_block(&bytes, address, bytes.len())
                .expect("pinned real ARM64 O0 FNV block");
            address += bytes.len() as u64;
            block
        })
        .collect::<Vec<_>>();
    let spaces = blocks
        .iter()
        .flat_map(|block| &block.ops)
        .filter_map(|op| match op {
            R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(!spaces.is_empty(), "real FNV lift must access memory");
    assert!(
        spaces.iter().all(|space| *space == SpaceId::Ram),
        "real ARM64 FNV accesses must use Ram: {spaces:?}"
    );
    (blocks, arch)
}

fn artifact(blocks: &[R2ILBlock], arch: &ArchSpec, revision: &[u8]) -> SsaArtifact {
    SsaArtifact::for_decompile_with_interface(blocks, Some(arch), real_interface(arch, revision))
        .expect("prepared real ARM64 O0 FNV artifact")
}

fn snapshot(arch: &ArchSpec, revision: &[u8]) -> Arc<EngineSourceSnapshot> {
    Arc::new(
        EngineSourceSnapshot::new(
            revision.to_vec(),
            Some(real_interface(arch, revision)),
            Vec::new(),
        )
        .expect("real O0 FNV source snapshot"),
    )
}

fn request(
    blocks: Vec<R2ILBlock>,
    arch: ArchSpec,
    source_snapshot: Arc<EngineSourceSnapshot>,
    function_name: &str,
) -> EngineFunctionDecompileRequestInput {
    EngineFunctionDecompileRequestInput::single_function(
        EngineFunctionInput {
            function_name: function_name.to_string(),
            function_addr: REAL_FNV_O0_BASE,
            blocks,
            arch: Some(arch),
            source_snapshot: Some(source_snapshot),
            semantic_metadata_enabled: true,
        },
        Some(64),
        r2types::ParsedExternalContext::default(),
        0,
    )
}

fn status(response: &r2engine::EngineDecompileResponse, phase: EnginePhase) -> EnginePhaseStatus {
    response
        .metrics
        .phase_timings
        .iter()
        .find(|timing| timing.phase == phase)
        .expect("stable engine phase inventory")
        .status
}

fn assert_exact_region(response: &r2engine::EngineDecompileResponse) {
    assert_eq!(
        response.diagnostics.semantic_kernel_render,
        Some(EngineSemanticKernelRender {
            region: EngineSemanticKernelRegion::CanonicalFnvFoldO0Function,
            region_schema_version: r2dec::CERTIFIED_FNV_FOLD_O0_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            exact_obligation_closure: true,
        })
    );
    assert_eq!(
        response.diagnostics.plan,
        Some(EnginePlan::SemanticStructured)
    );
    assert_eq!(
        response.diagnostics.route_reason.as_deref(),
        Some("r2cert authorized exact stack-backed O0 FNV-fold obligation closure")
    );
    assert!(response.diagnostics.render_permission.is_none());
    assert!(response.diagnostics.proof_coverage.is_none());
    assert!(response.diagnostics.refusal.is_none());
    assert!(response.diagnostics.warnings.is_empty());
}

fn assert_exact_semantic_c(output: &str, function_symbol: &str) {
    assert_eq!(
        output,
        EXPECTED_SEMANTIC_C.replace("__FUNCTION__", function_symbol),
        "engine semantic C changed independently pinned meaning"
    );
    for forbidden in [
        "goto",
        "break;",
        "saved_fp",
        "return_address",
        "home_reload",
        "frame_address",
        "frame",
        "stack",
        "stack_slot",
        "r2s_read",
        "r2s_write",
        "x30",
        "sp_",
    ] {
        assert!(
            !output.contains(forbidden),
            "O0 frame machinery leaked through {forbidden}:\n{output}"
        );
    }
}

fn reference_fnv(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0x1465_0fb0_739d_0383_u64, |hash, byte| {
        let folded = if byte.is_ascii_uppercase() {
            byte.to_ascii_lowercase()
        } else {
            *byte
        };
        (hash ^ u64::from(folded)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

fn compiled_results(source: &str, function_symbol: &str, probes: &[Vec<u8>]) -> Vec<u64> {
    let mut source = source.to_string();
    source.push_str("\n#include <inttypes.h>\n#include <stdio.h>\n\nint main(void) {\n");
    for (index, bytes) in probes.iter().enumerate() {
        write!(&mut source, "\tstatic const uint8_t case_{index}[] = {{")
            .expect("String writes cannot fail");
        if bytes.is_empty() {
            source.push_str("UINT8_C(0x0)");
        } else {
            for (byte_index, byte) in bytes.iter().enumerate() {
                if byte_index != 0 {
                    source.push_str(", ");
                }
                write!(&mut source, "UINT8_C(0x{byte:02x})").expect("String writes cannot fail");
            }
        }
        source.push_str("};\n");
        writeln!(
            &mut source,
            "\tprintf(\"%\" PRIu64 \"\\n\", {function_symbol}(case_{index}, UINT64_C(0x{:x})));",
            bytes.len()
        )
        .expect("String writes cannot fail");
    }
    source.push_str("\treturn 0;\n}\n");

    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock")
        .as_nanos();
    let directory =
        std::env::temp_dir().join(format!("r2engine-fnv-o0-{}-{nonce}", std::process::id()));
    fs::create_dir(&directory).expect("temporary directory");
    let source_path = directory.join("probe.c");
    let executable = directory.join("probe");
    fs::write(&source_path, source).expect("C source");
    let compiler = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let status = Command::new(compiler)
        .args(["-std=c11", "-Wall", "-Wextra", "-Wpedantic", "-Werror"])
        .arg(&source_path)
        .arg("-o")
        .arg(&executable)
        .status()
        .expect("C compiler");
    assert!(status.success());
    let output = Command::new(&executable)
        .output()
        .expect("compiled C probe");
    assert!(output.status.success());
    let results = String::from_utf8(output.stdout)
        .expect("UTF-8 output")
        .lines()
        .map(|line| line.parse::<u64>().expect("integer output"))
        .collect();
    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_file(&executable);
    let _ = fs::remove_dir(&directory);
    results
}

fn mutate_prime(blocks: &mut [R2ILBlock]) {
    let mut changed = 0;
    for op in blocks.iter_mut().flat_map(|block| &mut block.ops) {
        if let R2ILOp::Copy { src, .. } = op
            && src.space == SpaceId::Const
            && src.offset == 0x01b3
            && src.size == 8
        {
            *src = Varnode::constant(0x01b5, 8);
            changed += 1;
        }
    }
    assert_eq!(changed, 1, "one real-lift FNV prime low initializer");
}

#[test]
fn real_arm64_o0_public_engine_route_is_canonical_cached_and_name_independent() {
    let provenance = format!(
        "binary={REAL_FNV_O0_BINARY_PATH} binary_sha256={REAL_FNV_O0_BINARY_SHA256} command={REAL_FNV_O0_COMPILER_COMMAND}"
    );
    assert_eq!(
        sha256_hex(include_bytes!("../../../tests/gold/manual_limits.c")),
        REAL_FNV_SOURCE_SHA256,
        "source provenance changed: {provenance}"
    );
    assert_eq!(
        sha256_hex(include_bytes!(
            "../../../tests/r2r/bins/r2sleigh_manual_limits_O0"
        )),
        REAL_FNV_O0_BINARY_SHA256,
        "full-binary provenance changed: {provenance}"
    );
    let function_bytes = REAL_FNV_O0_BLOCKS
        .iter()
        .flat_map(|encoded| decode_hex(encoded))
        .collect::<Vec<_>>();
    assert_eq!(function_bytes.len(), 200, "{provenance}");
    assert_eq!(
        sha256_hex(&function_bytes),
        REAL_FNV_O0_FUNCTION_SHA256,
        "function-byte provenance changed: {provenance}"
    );

    let (blocks, arch) = real_blocks_and_arch();
    assert_eq!(blocks.len(), 11);
    let prepared = artifact(&blocks, &arch, REVISION);
    let facts = prepared
        .structured()
        .canonical_fnv_fold_o0
        .values()
        .collect::<Vec<_>>();
    let [fact] = facts.as_slice() else {
        panic!("exactly one real stack-backed O0 FNV fact")
    };
    assert!(fact.validate_against(&prepared));
    assert_eq!(fact.topology.entry, REAL_FNV_O0_BASE);
    assert_eq!(fact.topology.header, 0x1_0000_0784);
    assert_eq!(fact.topology.hash_block, 0x1_0000_07dc);
    assert_eq!(fact.topology.latch, 0x1_0000_0808);
    assert_eq!(fact.topology.exit, 0x1_0000_0818);

    let function_name = "sym.production_fnv_fold_o0";
    let function_symbol = "r2s_fn_sym_production_fnv_fold_o0";
    let session = EngineSession::new(4);
    let source_snapshot = snapshot(&arch, REVISION);
    let first = session.decompile_function_from_input(request(
        blocks.clone(),
        arch.clone(),
        Arc::clone(&source_snapshot),
        function_name,
    ));
    assert_exact_semantic_c(&first.output, function_symbol);
    assert_exact_region(&first);
    assert!(!first.metrics.cache_hit);
    assert_eq!(first.metrics.phase_timings.len(), EnginePhase::ALL.len());
    assert_eq!(
        status(&first, EnginePhase::Ssa),
        EnginePhaseStatus::Executed
    );
    assert_eq!(
        status(&first, EnginePhase::Certification),
        EnginePhaseStatus::Folded
    );
    assert_eq!(
        status(&first, EnginePhase::Structuring),
        EnginePhaseStatus::Folded
    );
    assert_eq!(
        status(&first, EnginePhase::Rendering),
        EnginePhaseStatus::Executed
    );

    let probes = vec![
        Vec::new(),
        b"A".to_vec(),
        b"Z".to_vec(),
        b"AbC".to_vec(),
        b"abc".to_vec(),
        vec![0x00, 0x40, 0x41, 0x5a, 0x5b, 0x7f, 0x80, 0xff],
        (0_u8..=u8::MAX).collect(),
    ];
    let expected = probes
        .iter()
        .map(|bytes| reference_fnv(bytes))
        .collect::<Vec<_>>();
    assert_eq!(
        compiled_results(&first.output, function_symbol, &probes),
        expected
    );

    let cached = session.decompile_function_from_input(request(
        blocks.clone(),
        arch.clone(),
        Arc::clone(&source_snapshot),
        function_name,
    ));
    assert!(
        cached.metrics.cache_hit,
        "expected repeated exact request to reuse analysis: {:?}",
        session.cache_metrics()
    );
    assert_eq!(cached.output, first.output);
    assert_exact_region(&cached);
    assert_eq!(status(&cached, EnginePhase::Ssa), EnginePhaseStatus::Reused);
    assert_eq!(
        status(&cached, EnginePhase::Obligations),
        EnginePhaseStatus::Reused
    );

    let changed_revision = b"engine-real-arm64-fnv-fold-o0-v2";
    let revised = session.decompile_function_from_input(request(
        blocks.clone(),
        arch.clone(),
        snapshot(&arch, changed_revision),
        function_name,
    ));
    assert!(!revised.metrics.cache_hit);
    assert_exact_semantic_c(&revised.output, function_symbol);
    assert_exact_region(&revised);

    let unrelated_name = "sym.deliberately_unrelated_label";
    let unrelated_symbol = "r2s_fn_sym_deliberately_unrelated_label";
    let renamed = session.decompile_function_from_input(request(
        blocks,
        arch,
        source_snapshot,
        unrelated_name,
    ));
    assert_exact_semantic_c(&renamed.output, unrelated_symbol);
    assert_exact_region(&renamed);
    assert_eq!(
        compiled_results(&renamed.output, unrelated_symbol, &probes),
        expected
    );
}

#[test]
fn real_arm64_o0_prime_mutation_refuses_certified_route() {
    let (mut blocks, arch) = real_blocks_and_arch();
    mutate_prime(&mut blocks);
    let near_miss = artifact(&blocks, &arch, REVISION);
    assert!(
        near_miss.structured().canonical_fnv_fold_o0.is_empty(),
        "a changed real-lift FNV prime must remove exact O0 applicability"
    );

    let response = EngineSession::new(4).decompile_function_from_input(request(
        blocks,
        arch.clone(),
        snapshot(&arch, REVISION),
        "sym.production_fnv_fold_o0",
    ));
    assert!(
        response.output.contains("r2dec residual:")
            && !response.output.contains("r2s_fn_")
            && !response.output.contains("certified_sub_"),
        "real O0 FNV prime near miss must remain residual without legacy CertifiedC:\n{}",
        response.output
    );
    assert!(response.diagnostics.semantic_kernel_render.is_none());
    let route = response
        .function_facts
        .decompile_route()
        .expect("near-miss engine route facts");
    assert_eq!(route.kind, r2types::DecompileRouteKind::Standard);
    assert_eq!(
        route.render_permission.kind,
        r2sym::RenderPermissionKind::Residual
    );
}
