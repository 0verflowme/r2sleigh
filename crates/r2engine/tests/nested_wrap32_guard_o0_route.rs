use std::sync::Arc;

use r2engine::{
    EngineFunctionDecompileRequestInput, EngineFunctionInput, EnginePlan,
    EngineSemanticKernelRegion, EngineSemanticKernelRender, EngineSession, EngineSourceSnapshot,
};
use r2il::{AddressSpace, ArchSpec, R2ILBlock, R2ILOp};
use r2sleigh_lift::{Disassembler, build_arch_spec};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, MachineBuildError, SourceAbiParameterSpec,
    SourceCallResult, SourceCallSiteIdentity, SourceCallSiteInterface, SourceCarrierKind,
    SourceCarrierProjection, SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue,
    SourceStackSlotSpec, SourceType, SourceTypeGraph, SourceTypeKind, SsaArtifact,
    StackAddressBase,
};

const BASE: u64 = 0x1000_0880;
const REVISION: &[u8] = b"engine-nested-wrap32-real-o0-revision-1";
const RAX_OFFSET: u64 = 0;
const RBP_OFFSET: u64 = 40;
const RSI_OFFSET: u64 = 48;
const RDI_OFFSET: u64 = 56;

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

fn storage(offset: u64) -> CanonicalStorageId {
    CanonicalStorageId {
        space: CanonicalStorageSpace::Register,
        offset,
        size: 8,
    }
}

fn interface(revision: &[u8]) -> SourceFunctionInterface {
    let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
    SourceFunctionInterface::new_exact_with_logical_types(
        revision.to_vec(),
        "sysv_amd64",
        [
            SourceAbiParameterSpec::new(0, storage(RDI_OFFSET)),
            SourceAbiParameterSpec::new(1, storage(RSI_OFFSET)),
        ],
        SourceFunctionReturn::Register {
            storage: storage(RAX_OFFSET),
        },
        [
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                storage(RBP_OFFSET),
                -8,
                4,
                0,
                storage(RDI_OFFSET),
            ),
            SourceStackSlotSpec::new_parameter_home(
                StackAddressBase::FramePointer,
                storage(RBP_OFFSET),
                -12,
                4,
                1,
                storage(RSI_OFFSET),
            ),
            SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                storage(RBP_OFFSET),
                -16,
                4,
            ),
            SourceStackSlotSpec::new_local(
                StackAddressBase::FramePointer,
                storage(RBP_OFFSET),
                -20,
                4,
            ),
        ],
        [
            SourceLogicalValue::new(0, low32),
            SourceLogicalValue::new(0, low32),
        ],
        Some(SourceLogicalValue::new(0, low32)),
        Some(
            SourceTypeGraph::new(
                [SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32)],
                [],
            )
            .expect("signed i32 graph"),
        ),
    )
    .expect("exact nested wrap32 source interface")
}

fn real_fixture() -> (Vec<R2ILBlock>, ArchSpec) {
    let mut arch = build_arch_spec(
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
    let mut address = BASE;
    let blocks = [
        "554889e5897df88975f48b45f80345f48945f08b45f82b45f48945ec837df0647511",
        "837dec147509",
        "c745fc01000000eb09",
        "eb00",
        "c745fc00000000",
        "8b45fc5dc3",
    ]
    .into_iter()
    .map(|encoded| {
        let bytes = decode_hex(encoded);
        let block = disassembler
            .lift_block(&bytes, address, bytes.len())
            .expect("pinned complex_check O0 block");
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
    for space in spaces {
        if !arch.spaces.iter().any(|candidate| candidate.id == space) {
            arch.add_space(AddressSpace::new(space, "sleigh-data", 8));
        }
    }
    (blocks, arch)
}

fn snapshot(
    revision: &[u8],
    call_sites: impl IntoIterator<Item = SourceCallSiteInterface>,
) -> Arc<EngineSourceSnapshot> {
    Arc::new(
        EngineSourceSnapshot::new(revision.to_vec(), Some(interface(revision)), call_sites)
            .expect("exact nested wrap32 source snapshot"),
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
            function_addr: BASE,
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

#[test]
fn real_o0_nested_wrap32_public_engine_route_is_exact_strict_semantic_c() {
    let (blocks, arch) = real_fixture();
    let prepared =
        SsaArtifact::for_decompile_with_interface(&blocks, Some(&arch), interface(REVISION))
            .expect("prepared real complex_check O0 artifact");
    let fact = prepared
        .structured()
        .nested_wrap32_guard_o0
        .values()
        .next()
        .expect("one retained exact nested wrap32 O0 fact");
    assert_eq!(prepared.structured().nested_wrap32_guard_o0.len(), 1);
    assert_eq!(
        fact.schema_version,
        r2ssa::NESTED_WRAP32_GUARD_O0_FACT_SCHEMA_VERSION
    );
    assert_eq!(fact.instruction_inventory.len(), 126);

    let response = EngineSession::new(4).decompile_function_from_input(request(
        blocks,
        arch,
        snapshot(REVISION, []),
        "complex.check",
    ));
    assert_eq!(
        response.diagnostics.semantic_kernel_render,
        Some(EngineSemanticKernelRender {
            region: EngineSemanticKernelRegion::NestedWrap32GuardO0Function,
            region_schema_version:
                r2dec::CERTIFIED_NESTED_WRAP32_GUARD_O0_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            exact_obligation_closure: true,
        })
    );
    assert_eq!(
        response.diagnostics.plan,
        Some(EnginePlan::SemanticStructured)
    );
    assert_eq!(
        response.diagnostics.route_reason.as_deref(),
        Some("r2cert authorized exact nested wrap32 O0 obligation closure")
    );
    assert!(response.diagnostics.refusal.is_none());
    assert_eq!(
        response.output,
        concat!(
            "#include <stdint.h>\n\n",
            "int32_t r2s_fn_complex_check(int32_t r2s_arg0_first, int32_t r2s_arg1_second) {\n",
            "\tuint32_t r2s_first_bits = (uint32_t)r2s_arg0_first;\n",
            "\tuint32_t r2s_second_bits = (uint32_t)r2s_arg1_second;\n",
            "\tuint32_t r2s_sum_bits = (uint32_t)(r2s_first_bits + r2s_second_bits);\n",
            "\tif (r2s_sum_bits != UINT32_C(0x64)) {\n",
            "\t\treturn INT32_C(0);\n",
            "\t} else {\n",
            "\t\tuint32_t r2s_difference_bits = (uint32_t)(r2s_first_bits - r2s_second_bits);\n",
            "\t\tif (r2s_difference_bits != UINT32_C(0x14)) {\n",
            "\t\t\treturn INT32_C(0);\n",
            "\t\t} else {\n",
            "\t\t\treturn INT32_C(1);\n",
            "\t\t}\n",
            "\t}\n",
            "}\n",
        )
    );
}

fn unmatched_call_site(revision: &[u8]) -> SourceCallSiteInterface {
    SourceCallSiteInterface::new(
        revision.to_vec(),
        SourceCallSiteIdentity::new(
            BASE,
            0,
            CanonicalStorageId {
                space: CanonicalStorageSpace::Constant,
                offset: 0xdead_beef,
                size: 8,
            },
        ),
        true,
        "sysv_amd64",
        [],
        false,
        false,
        SourceCallResult::Void,
    )
    .expect("well-formed but unmatched source callsite")
}

#[test]
fn retained_exact_fact_that_fails_downstream_refuses_without_downgrade() {
    let (blocks, arch) = real_fixture();
    let call_site = unmatched_call_site(REVISION);
    let prepared = SsaArtifact::for_decompile_with_interfaces(
        &blocks,
        Some(&arch),
        Some(interface(REVISION)),
        vec![call_site.clone()],
    )
    .expect("prepared retained-fact artifact");
    assert_eq!(
        prepared.structured().nested_wrap32_guard_o0.len(),
        1,
        "the downstream failure must not be simulated by removing applicability"
    );
    assert!(
        !prepared
            .machine_context()
            .call_site_interfaces_are_coherent(),
        "the retained exact fact must encounter an independently invalid downstream context"
    );
    assert_eq!(
        r2dec::CertifiedNestedWrap32GuardO0SemanticCFunction::from_artifact(&prepared)
            .expect_err("certification must reject the unmatched callsite"),
        r2dec::NestedWrap32GuardO0SemanticCFunctionError::Machine(
            MachineBuildError::MachineContextMismatch,
        )
    );

    let response = EngineSession::new(4).decompile_function_from_input(request(
        blocks,
        arch,
        snapshot(REVISION, [call_site]),
        "complex.check",
    ));
    let reason = response
        .diagnostics
        .route_reason
        .as_deref()
        .expect("evidence-backed engine refusal reason");
    assert!(reason.contains("exact nested wrap32 O0 fact failed certification"));
    assert!(reason.contains("MachineContextMismatch"));
    assert_eq!(
        response.diagnostics.plan,
        Some(EnginePlan::RefuseWithEvidence)
    );
    assert!(response.diagnostics.semantic_kernel_render.is_none());
    assert!(
        response
            .output
            .contains("r2dec fallback: skipped decompilation")
    );
    assert!(response.output.contains(reason));
    assert!(!response.output.contains("int32_t r2s_fn_complex_check"));
    assert!(!response.output.contains("r2dec residual:"));
    let route = response
        .function_facts
        .decompile_route()
        .expect("refusal route facts");
    assert_eq!(route.kind, r2types::DecompileRouteKind::FallbackComment);
    assert_eq!(
        route.render_permission.kind,
        r2sym::RenderPermissionKind::Refuse
    );
}
