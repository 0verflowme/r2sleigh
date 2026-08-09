use std::sync::Arc;

use r2engine::{
    EngineFunctionDecompileRequestInput, EngineFunctionInput, EnginePlan,
    EngineSemanticKernelRegion, EngineSemanticKernelRender, EngineSession, EngineSourceSnapshot,
};
use r2il::{AddressSpace, R2ILBlock, R2ILOp, Varnode};
use r2sleigh_lift::{Disassembler, build_arch_spec};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierKind,
    SourceCarrierProjection, SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue,
    SourceStackSlotSpec, SourceType, SourceTypeGraph, SourceTypeKind, SsaArtifact,
    StackAddressBase,
};

const O0_ENTRY: u64 = 0x1000_0610;
const O2_ENTRY: u64 = 0x1000_0620;
const O0_REVISION: &[u8] = b"engine-sum-array-o0-route-v1";
const O2_REVISION: &[u8] = b"engine-sum-array-o2-route-v1";
const O0_INSTRUCTION_COUNT: usize = 111;
const O2_INSTRUCTION_COUNT: usize = 672;

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

fn x86() -> (r2il::ArchSpec, Disassembler) {
    let arch = build_arch_spec(
        sleigh_config::processor_x86::SLA_X86_64,
        sleigh_config::processor_x86::PSPEC_X86_64,
        "x86-64",
    )
    .expect("x86-64 architecture");
    let disassembler = Disassembler::from_sla(
        sleigh_config::processor_x86::SLA_X86_64,
        sleigh_config::processor_x86::PSPEC_X86_64,
        "x86-64",
    )
    .expect("x86-64 disassembler");
    (arch, disassembler)
}

fn lift_blocks(base: u64, encoded: &[&str]) -> (r2il::ArchSpec, Vec<R2ILBlock>) {
    let (mut arch, disassembler) = x86();
    let mut address = base;
    let blocks = encoded
        .iter()
        .map(|encoded| {
            let bytes = decode_hex(encoded);
            let block = disassembler
                .lift_block(&bytes, address, bytes.len())
                .expect("pinned x86 block");
            address += bytes.len() as u64;
            block
        })
        .collect::<Vec<_>>();
    let lifted_spaces = blocks
        .iter()
        .flat_map(|block| &block.ops)
        .filter_map(|op| match op {
            R2ILOp::Load { space, .. } | R2ILOp::Store { space, .. } => Some(*space),
            _ => None,
        })
        .collect::<Vec<_>>();
    for space in lifted_spaces {
        if !arch.spaces.iter().any(|candidate| candidate.id == space) {
            arch.add_space(AddressSpace::new(space, "sleigh-data", 8));
        }
    }
    (arch, blocks)
}

fn o0_blocks() -> (r2il::ArchSpec, Vec<R2ILBlock>) {
    lift_blocks(
        O0_ENTRY,
        &[
            "554889e548897df88975f4c745f000000000c745ec00000000",
            "8b45ec3b45f47d1c",
            "488b45f848634dec8b04880345f08945f08b45ec83c0018945ecebdc",
            "8b45f05dc3",
        ],
    )
}

fn o2_blocks() -> (r2il::ArchSpec, Vec<R2ILBlock>) {
    lift_blocks(
        O2_ENTRY,
        &[
            "554889e585f67e0d",
            "89f183fe08730a",
            "31d231c0eb6b",
            "31c05dc3",
            "89ca81e2f8ffff7f89c8c1e80325ffffff0f48c1e005660fefc031f6660fefc90f1f8000000000",
            "f30f6f1437660ffec2f30f6f543710660ffeca4883c6204839f075e4",
            "660ffec8660f70c1ee660ffec1660f70c855660ffec8660f7ec839ca7411",
            "660f1f440000",
            "03049748ffc24839d175f5",
            "5dc3",
        ],
    )
}

fn storage(offset: u64) -> CanonicalStorageId {
    CanonicalStorageId {
        space: CanonicalStorageSpace::Register,
        offset,
        size: 8,
    }
}

fn types() -> SourceTypeGraph {
    SourceTypeGraph::new(
        [
            SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32),
            SourceType::new(1, SourceTypeKind::Pointer { target_type_id: 0 }, 64, 64),
        ],
        [],
    )
    .expect("sum-array source types")
}

fn interface(revision: &[u8], homes: bool) -> SourceFunctionInterface {
    let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
    let stack_slots = homes.then(|| {
        vec![
            SourceStackSlotSpec::new_local(StackAddressBase::FramePointer, storage(40), -20, 4),
            SourceStackSlotSpec::new_local(StackAddressBase::FramePointer, storage(40), -16, 4),
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                storage(40),
                -12,
                4,
                1,
                storage(48),
            ),
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                storage(40),
                -8,
                8,
                0,
                storage(56),
            ),
        ]
    });
    SourceFunctionInterface::new_exact_with_logical_types(
        revision.to_vec(),
        "sysv_amd64",
        [
            SourceAbiParameterSpec::new(0, storage(56)),
            SourceAbiParameterSpec::new(1, storage(48)),
        ],
        SourceFunctionReturn::Register {
            storage: storage(0),
        },
        stack_slots.unwrap_or_default(),
        [
            SourceLogicalValue::new(
                1,
                SourceCarrierProjection::new(SourceCarrierKind::Full, 0, 64),
            ),
            SourceLogicalValue::new(0, low32),
        ],
        Some(SourceLogicalValue::new(0, low32)),
        Some(types()),
    )
    .expect("exact sum-array source interface")
}

fn snapshot(revision: &[u8], homes: bool) -> Arc<EngineSourceSnapshot> {
    Arc::new(
        EngineSourceSnapshot::new(revision.to_vec(), Some(interface(revision, homes)), [])
            .expect("exact sum-array source snapshot"),
    )
}

fn artifact(
    blocks: &[R2ILBlock],
    arch: &r2il::ArchSpec,
    revision: &[u8],
    homes: bool,
) -> SsaArtifact {
    SsaArtifact::for_decompile_with_interface(blocks, Some(arch), interface(revision, homes))
        .expect("prepared exact sum-array artifact")
}

fn request(
    entry: u64,
    blocks: Vec<R2ILBlock>,
    arch: r2il::ArchSpec,
    revision: &[u8],
    homes: bool,
    function_name: &str,
) -> EngineFunctionDecompileRequestInput {
    EngineFunctionDecompileRequestInput::single_function(
        EngineFunctionInput {
            function_name: function_name.to_string(),
            function_addr: entry,
            blocks,
            arch: Some(arch),
            source_snapshot: Some(snapshot(revision, homes)),
            semantic_metadata_enabled: true,
        },
        Some(64),
        r2types::ParsedExternalContext::default(),
        0,
    )
}

fn assert_closed_renderer(
    artifact: &SsaArtifact,
    expected_lowering: &str,
    expected_instructions: usize,
) -> r2dec::CertifiedSumArraySemanticCFunction {
    let function = r2dec::CertifiedSumArraySemanticCFunction::from_artifact(artifact)
        .expect("exact sum-array renderer");
    assert_eq!(
        function.schema_version(),
        r2dec::CERTIFIED_SUM_ARRAY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION
    );
    assert!(function.audit().has_exact_sum_array_function());
    assert_eq!(
        format!("{:?}", function.program().lowering()),
        expected_lowering
    );
    assert_eq!(
        function.certificate().instruction_inventory().len(),
        expected_instructions
    );
    assert_eq!(
        function.certificate().obligation_dispositions().len(),
        artifact.obligations().obligations().len()
    );
    assert!(function.certificate().validate(artifact.obligations()));
    function
}

fn assert_exact_route(response: &r2engine::EngineDecompileResponse) {
    assert_eq!(
        response.diagnostics.semantic_kernel_render,
        Some(EngineSemanticKernelRender {
            region: EngineSemanticKernelRegion::SumArrayFunction,
            region_schema_version: r2dec::CERTIFIED_SUM_ARRAY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            exact_obligation_closure: true,
        })
    );
    assert_eq!(
        response.diagnostics.plan,
        Some(EnginePlan::SemanticStructured)
    );
    assert_eq!(
        response.diagnostics.route_reason.as_deref(),
        Some("r2cert authorized exact sum-array obligation closure")
    );
    assert!(response.diagnostics.render_permission.is_none());
    assert!(response.diagnostics.proof_coverage.is_none());
    assert!(response.diagnostics.refusal.is_none());
}

fn assert_strict_sum_loop(output: &str, function_name: &str) {
    assert!(output.contains("#include <stdint.h>"));
    assert!(output.contains(&format!(
        "int32_t r2s_fn_{function_name}(const int32_t *r2s_arg0_array, int32_t r2s_arg1_length)"
    )));
    assert!(output.contains("if (r2s_arg1_length <= 0)"));
    assert!(output.contains("uint32_t r2s_sum_sum_bits = UINT32_C(0)"));
    assert!(output.contains("for (int32_t r2s_index_index = 0;"));
    assert!(output.contains("r2s_sum_sum_bits += (uint32_t)r2s_arg0_array[r2s_index_index]"));
    assert!(output.contains("return r2s_i32_from_bits(r2s_sum_sum_bits)"));
    for forbidden in ["__m128", "goto", "saved_fp", "stack_slot", "home_reload"] {
        assert!(
            !output.contains(forbidden),
            "machine lowering leaked through {forbidden}:\n{output}"
        );
    }
}

#[test]
fn exact_o0_and_real_672_instruction_o2_reach_one_closed_production_region() {
    for (
        entry,
        revision,
        homes,
        expected_lowering,
        expected_instructions,
        function_name,
        (arch, blocks),
    ) in [
        (
            O0_ENTRY,
            O0_REVISION,
            true,
            "O0ScalarHomes",
            O0_INSTRUCTION_COUNT,
            "sym_production_sum_array_o0",
            o0_blocks(),
        ),
        (
            O2_ENTRY,
            O2_REVISION,
            false,
            "O2Vectorized",
            O2_INSTRUCTION_COUNT,
            "sym_production_sum_array_o2",
            o2_blocks(),
        ),
    ] {
        let prepared = artifact(&blocks, &arch, revision, homes);
        let function = assert_closed_renderer(&prepared, expected_lowering, expected_instructions);
        let expected = function
            .with_cosmetic_names(function_name, "array", "length", "index", "sum_bits")
            .render_certified_c()
            .expect("strict semantic C");
        let response = EngineSession::new(4).decompile_function_from_input(request(
            entry,
            blocks,
            arch,
            revision,
            homes,
            function_name,
        ));
        assert_eq!(response.output, expected);
        assert_exact_route(&response);
        assert_strict_sum_loop(&response.output, function_name);
    }
}

#[test]
fn mutated_o2_read_and_foreign_candidate_never_reach_sum_array_render_authority() {
    let (o0_arch, o0_source) = o0_blocks();
    let o0 = artifact(&o0_source, &o0_arch, O0_REVISION, true);
    let (arch, mut blocks) = o2_blocks();
    let pristine = artifact(&blocks, &arch, O2_REVISION, false);
    let candidate = assert_closed_renderer(&pristine, "O2Vectorized", O2_INSTRUCTION_COUNT);
    assert!(
        r2dec::check_sum_array_differential(
            &o0,
            &candidate,
            [r2dec::SumArrayDifferentialInput::new(1, [7])],
        )
        .is_err(),
        "a certificate-bound typed candidate must refuse a foreign lowering and origin"
    );

    let address = blocks[5]
        .ops
        .iter_mut()
        .find_map(|op| match op {
            R2ILOp::Load { addr, .. } if addr.size == 8 => Some(addr),
            _ => None,
        })
        .expect("first O2 vector address");
    *address = Varnode::unique(0xbeef_0000, 8);
    let mutated = artifact(&blocks, &arch, O2_REVISION, false);
    assert!(mutated.structured().sum_arrays.is_empty());
    assert!(mutated.structured().sum_array_o2.is_empty());
    assert!(r2dec::CertifiedSumArraySemanticCFunction::from_artifact(&mutated).is_err());

    let response = EngineSession::new(4).decompile_function_from_input(request(
        O2_ENTRY,
        blocks,
        arch,
        O2_REVISION,
        false,
        "sym_production_sum_array_o2_mutated",
    ));
    assert_ne!(
        response.diagnostics.semantic_kernel_render,
        Some(EngineSemanticKernelRender {
            region: EngineSemanticKernelRegion::SumArrayFunction,
            region_schema_version: r2dec::CERTIFIED_SUM_ARRAY_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            exact_obligation_closure: true,
        })
    );
    assert!(
        !response
            .output
            .contains("r2s_fn_sym_production_sum_array_o2_mutated")
    );
    assert!(!response.output.contains("r2s_i32_from_bits"));
}
