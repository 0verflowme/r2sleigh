use std::sync::Arc;

use r2engine::{
    EngineFunctionDecompileRequestInput, EngineFunctionInput, EngineSemanticKernelRegion,
    EngineSession, EngineSourceSnapshot,
};
use r2il::{AddressSpace, ArchSpec, Endianness, R2ILBlock, R2ILOp, RegisterDef, SpaceId, Varnode};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, SourceAbiParameterSpec, SourceCarrierKind,
    SourceCarrierProjection, SourceFunctionInterface, SourceFunctionReturn, SourceLogicalValue,
    SourceType, SourceTypeGraph, SourceTypeKind,
};

const DATA: SpaceId = SpaceId::Custom(7);

fn register(offset: u64, size: u32) -> Varnode {
    Varnode::register(offset, size)
}

fn constant(value: u64, size: u32) -> Varnode {
    Varnode::constant(value, size)
}

fn unique(next: &mut u64, size: u32) -> Varnode {
    let value = Varnode::unique(*next, size);
    *next += 0x80;
    value
}

fn unique_at_previous(next: &u64, size: u32) -> Varnode {
    Varnode::unique(next.saturating_sub(0x80), size)
}

fn arch() -> ArchSpec {
    let mut arch = ArchSpec::new("x86-64");
    arch.addr_size = 8;
    arch.alignment = 1;
    for (name, offset, size) in [
        ("AL", 0, 1),
        ("EAX", 0, 4),
        ("RAX", 0, 8),
        ("ECX", 8, 4),
        ("RCX", 8, 8),
        ("RSP", 32, 8),
        ("RBP", 40, 8),
        ("ESI", 48, 4),
        ("RSI", 48, 8),
        ("EDI", 56, 4),
        ("RDI", 56, 8),
        ("CF", 512, 1),
        ("PF", 514, 1),
        ("ZF", 518, 1),
        ("SF", 519, 1),
        ("OF", 523, 1),
        ("RIP", 648, 8),
    ] {
        arch.add_register(RegisterDef::new(name, offset, size));
    }
    arch.add_space(AddressSpace::new(DATA, "x86-data", 8));
    arch.set_memory_endianness(Endianness::Little);
    arch
}

fn storage(offset: u64) -> CanonicalStorageId {
    CanonicalStorageId {
        space: CanonicalStorageSpace::Register,
        offset,
        size: 8,
    }
}

fn source_snapshot(parameter_count: usize, revision: &[u8]) -> Arc<EngineSourceSnapshot> {
    let types = SourceTypeGraph::new(
        [SourceType::new(0, SourceTypeKind::SignedInteger, 32, 32)],
        [],
    )
    .expect("signed int type graph");
    let low32 = SourceCarrierProjection::new(SourceCarrierKind::LowBits, 0, 32);
    let interface = SourceFunctionInterface::new_exact_with_logical_types(
        revision.to_vec(),
        "sysv_amd64",
        [storage(56), storage(48)]
            .into_iter()
            .take(parameter_count)
            .enumerate()
            .map(|(index, storage)| SourceAbiParameterSpec::new(index as u32, storage)),
        SourceFunctionReturn::Register {
            storage: storage(0),
        },
        [],
        (0..parameter_count).map(|_| SourceLogicalValue::new(0, low32)),
        Some(SourceLogicalValue::new(0, low32)),
        Some(types),
    )
    .expect("exact branchless interface");
    Arc::new(
        EngineSourceSnapshot::new(revision.to_vec(), Some(interface), [])
            .expect("exact source snapshot"),
    )
}

fn push_frame_prefix(block: &mut R2ILBlock, next: &mut u64) {
    let saved = unique(next, 8);
    block.push(R2ILOp::Copy {
        dst: saved.clone(),
        src: register(40, 8),
    });
    block.push(R2ILOp::IntSub {
        dst: register(32, 8),
        a: register(32, 8),
        b: constant(8, 8),
    });
    block.push(R2ILOp::Store {
        space: DATA,
        addr: register(32, 8),
        val: saved,
    });
    block.push(R2ILOp::Copy {
        dst: register(40, 8),
        src: register(32, 8),
    });
}

fn push_flag_packet(block: &mut R2ILBlock, next: &mut u64, value: Varnode) {
    block.push(R2ILOp::IntSLess {
        dst: register(519, 1),
        a: value.clone(),
        b: constant(0, 4),
    });
    block.push(R2ILOp::IntEqual {
        dst: register(518, 1),
        a: value.clone(),
        b: constant(0, 4),
    });
    let low = unique(next, 4);
    block.push(R2ILOp::IntAnd {
        dst: low.clone(),
        a: value,
        b: constant(0xff, 4),
    });
    let population = unique(next, 1);
    block.push(R2ILOp::PopCount {
        dst: population.clone(),
        src: low,
    });
    let parity = unique(next, 1);
    block.push(R2ILOp::IntAnd {
        dst: parity.clone(),
        a: population,
        b: constant(1, 1),
    });
    block.push(R2ILOp::IntEqual {
        dst: register(514, 1),
        a: parity,
        b: constant(0, 1),
    });
}

fn push_zero_flags(block: &mut R2ILBlock) {
    block.push(R2ILOp::Copy {
        dst: register(512, 1),
        src: constant(0, 1),
    });
    block.push(R2ILOp::Copy {
        dst: register(523, 1),
        src: constant(0, 1),
    });
}

fn push_frame_suffix(block: &mut R2ILBlock, next: &mut u64) {
    let restored = unique(next, 8);
    block.push(R2ILOp::Copy {
        dst: restored.clone(),
        src: constant(0, 8),
    });
    block.push(R2ILOp::Load {
        dst: restored,
        space: DATA,
        addr: register(32, 8),
    });
    block.push(R2ILOp::IntAdd {
        dst: register(32, 8),
        a: register(32, 8),
        b: constant(8, 8),
    });
    block.push(R2ILOp::Copy {
        dst: register(40, 8),
        src: unique_at_previous(next, 8),
    });
    block.push(R2ILOp::Load {
        dst: register(648, 8),
        space: DATA,
        addr: register(32, 8),
    });
    block.push(R2ILOp::IntAdd {
        dst: register(32, 8),
        a: register(32, 8),
        b: constant(8, 8),
    });
    block.push(R2ILOp::Return {
        target: register(648, 8),
    });
}

fn simple_block(entry: u64, expected: u64) -> R2ILBlock {
    let mut block = R2ILBlock::new(entry, 17);
    let mut next = 0x10000;
    push_frame_prefix(&mut block, &mut next);
    push_zero_flags(&mut block);
    block.push(R2ILOp::IntXor {
        dst: register(0, 4),
        a: register(0, 4),
        b: register(0, 4),
    });
    block.push(R2ILOp::IntZExt {
        dst: register(0, 8),
        src: register(0, 4),
    });
    push_flag_packet(&mut block, &mut next, register(0, 4));
    let copied = unique(&mut next, 4);
    block.push(R2ILOp::Copy {
        dst: copied.clone(),
        src: register(56, 4),
    });
    block.push(R2ILOp::IntLess {
        dst: register(512, 1),
        a: copied.clone(),
        b: constant(expected, 4),
    });
    block.push(R2ILOp::IntSBorrow {
        dst: register(523, 1),
        a: copied.clone(),
        b: constant(expected, 4),
    });
    let difference = unique(&mut next, 4);
    block.push(R2ILOp::IntSub {
        dst: difference.clone(),
        a: copied,
        b: constant(expected, 4),
    });
    push_flag_packet(&mut block, &mut next, difference);
    block.push(R2ILOp::Copy {
        dst: register(0, 1),
        src: register(518, 1),
    });
    push_frame_suffix(&mut block, &mut next);
    block
}

fn dual_block(entry: u64) -> R2ILBlock {
    let mut block = R2ILBlock::new(entry, 24);
    let mut next = 0x20000;
    push_frame_prefix(&mut block, &mut next);
    let scaled = unique(&mut next, 8);
    block.push(R2ILOp::IntMult {
        dst: scaled.clone(),
        a: register(56, 8),
        b: constant(1, 8),
    });
    let sum64 = unique(&mut next, 8);
    block.push(R2ILOp::IntAdd {
        dst: sum64.clone(),
        a: register(48, 8),
        b: scaled,
    });
    block.push(R2ILOp::Subpiece {
        dst: register(8, 4),
        src: sum64,
        offset: 0,
    });
    block.push(R2ILOp::IntZExt {
        dst: register(8, 8),
        src: register(8, 4),
    });
    block.push(R2ILOp::IntLess {
        dst: register(512, 1),
        a: register(56, 4),
        b: register(48, 4),
    });
    block.push(R2ILOp::IntSBorrow {
        dst: register(523, 1),
        a: register(56, 4),
        b: register(48, 4),
    });
    block.push(R2ILOp::IntSub {
        dst: register(56, 4),
        a: register(56, 4),
        b: register(48, 4),
    });
    block.push(R2ILOp::IntZExt {
        dst: register(56, 8),
        src: register(56, 4),
    });
    push_flag_packet(&mut block, &mut next, register(56, 4));
    push_zero_flags(&mut block);
    block.push(R2ILOp::IntXor {
        dst: register(8, 4),
        a: register(8, 4),
        b: constant(100, 4),
    });
    block.push(R2ILOp::IntZExt {
        dst: register(8, 8),
        src: register(8, 4),
    });
    push_flag_packet(&mut block, &mut next, register(8, 4));
    push_zero_flags(&mut block);
    block.push(R2ILOp::IntXor {
        dst: register(56, 4),
        a: register(56, 4),
        b: constant(20, 4),
    });
    block.push(R2ILOp::IntZExt {
        dst: register(56, 8),
        src: register(56, 4),
    });
    push_flag_packet(&mut block, &mut next, register(56, 4));
    push_zero_flags(&mut block);
    block.push(R2ILOp::IntXor {
        dst: register(0, 4),
        a: register(0, 4),
        b: register(0, 4),
    });
    block.push(R2ILOp::IntZExt {
        dst: register(0, 8),
        src: register(0, 4),
    });
    push_flag_packet(&mut block, &mut next, register(0, 4));
    push_zero_flags(&mut block);
    block.push(R2ILOp::IntOr {
        dst: register(56, 4),
        a: register(56, 4),
        b: register(8, 4),
    });
    block.push(R2ILOp::IntZExt {
        dst: register(56, 8),
        src: register(56, 4),
    });
    push_flag_packet(&mut block, &mut next, register(56, 4));
    block.push(R2ILOp::Copy {
        dst: register(0, 1),
        src: register(518, 1),
    });
    push_frame_suffix(&mut block, &mut next);
    block
}

fn decompile(
    function_name: &str,
    function_addr: u64,
    blocks: Vec<R2ILBlock>,
    parameter_count: usize,
) -> r2engine::EngineDecompileResponse {
    let revision = format!("branchless-engine-{function_addr:x}").into_bytes();
    EngineSession::new(4).decompile_function_from_input(
        EngineFunctionDecompileRequestInput::single_function(
            EngineFunctionInput {
                function_name: function_name.to_string(),
                function_addr,
                blocks,
                arch: Some(arch()),
                source_snapshot: Some(source_snapshot(parameter_count, &revision)),
                semantic_metadata_enabled: true,
            },
            Some(64),
            r2types::ParsedExternalContext::default(),
            0,
        ),
    )
}

fn assert_branchless_region(response: &r2engine::EngineDecompileResponse) {
    assert_eq!(
        response.diagnostics.plan,
        Some(r2engine::EnginePlan::FastLocal)
    );
    assert_eq!(
        response.diagnostics.route_reason.as_deref(),
        Some("r2cert authorized exact branchless-guard obligation closure")
    );
    assert_eq!(
        response.diagnostics.semantic_kernel_render,
        Some(r2engine::EngineSemanticKernelRender {
            region: EngineSemanticKernelRegion::BranchlessGuardFunction,
            region_schema_version:
                r2dec::CERTIFIED_BRANCHLESS_GUARD_SEMANTIC_C_FUNCTION_SCHEMA_VERSION,
            exact_obligation_closure: true,
        })
    );
    assert!(response.diagnostics.proof_coverage.is_none());
    assert!(response.diagnostics.render_permission.is_none());
    assert!(response.diagnostics.refusal.is_none());
}

#[test]
fn production_engine_selects_simple_and_dual_branchless_guards() {
    let simple = decompile(
        "sym.check_secret",
        0x1000,
        vec![simple_block(0x1000, 0xdead)],
        1,
    );
    assert_branchless_region(&simple);
    assert!(
        simple
            .output
            .contains("int32_t r2s_fn_sym_check_secret(int32_t")
    );
    assert!(simple.output.contains("== UINT32_C(0xdead)"));

    let dual = decompile("sym.complex_check", 0x2000, vec![dual_block(0x2000)], 2);
    assert_branchless_region(&dual);
    assert!(
        dual.output
            .contains("int32_t r2s_fn_sym_complex_check(int32_t")
    );
    assert!(dual.output.contains("sum_bits == UINT32_C(0x64)"));
    assert!(dual.output.contains("difference_bits == UINT32_C(0x14)"));
}

#[test]
fn branchless_guard_selection_is_name_and_address_independent() {
    for (name, address) in [("not_a_secret", 0x44), ("123 !!!", 0xfedc_ba98)] {
        let response = decompile(name, address, vec![simple_block(address, 0xdead)], 1);
        assert_branchless_region(&response);
        assert!(response.output.contains("== UINT32_C(0xdead)"));
    }
}

#[test]
fn mutated_branchless_guard_cannot_downgrade_to_another_certified_c_route() {
    let mut near_miss = simple_block(0x3000, 0xdead);
    near_miss.ops[17] = R2ILOp::IntSub {
        dst: Varnode::unique(0x10400, 4),
        a: Varnode::unique(0x10380, 4),
        b: constant(0xdeac, 4),
    };
    let response = decompile("check_secret", 0x3000, vec![near_miss], 1);
    assert!(response.diagnostics.semantic_kernel_render.is_none());
    assert!(!response.output.contains("UINT32_C(0xdead)"));
    assert!(!response.output.contains("r2s_fn_check_secret"));
}
