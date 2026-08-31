//! Genuine embedded lifts through optimized SSA and typed machine projection.

use r2sleigh_lift::{Disassembler, TrustedSleighProfile};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, FunctionPrepareMode, MachineProjection,
    MachineUseDisposition, MachineUseSlice, MachineWriteDisposition, MachineWriteProjection,
    SsaArtifact, UseSite,
};

fn declared_register_storage(arch: &r2il::ArchSpec, name: &str) -> CanonicalStorageId {
    let register = arch
        .get_register(name)
        .unwrap_or_else(|| panic!("embedded specification is missing {name}"));
    CanonicalStorageId {
        space: CanonicalStorageSpace::Register,
        offset: register.offset,
        size: register.size,
    }
}

fn genuine_optimized_projection(
    profile: TrustedSleighProfile,
    instruction: &[u8],
) -> (SsaArtifact, MachineProjection, r2il::ArchSpec) {
    assert!(!instruction.is_empty() && instruction.len() <= 16);
    let disassembler =
        Disassembler::from_trusted_profile(profile).expect("trusted embedded profile");
    let mut bytes = [0_u8; 16];
    bytes[..instruction.len()].copy_from_slice(instruction);
    let lifted = disassembler
        .lift_genuine_block(&bytes, 0x1000, instruction.len())
        .expect("complete genuine instruction lift");
    let arch = lifted.authority().arch_spec().clone();
    let blocks = [lifted.block().clone()];
    let artifact = SsaArtifact::for_decompile(&blocks, Some(&arch))
        .expect("decompiler-optimized SSA artifact");
    assert_eq!(artifact.mode(), FunctionPrepareMode::Decompile);
    let projection = MachineProjection::from_artifact(&artifact).expect("typed machine projection");
    assert!(
        projection.failures().is_empty(),
        "simple register write must project without residual failures: {:?}",
        projection.failures()
    );
    (artifact, projection, arch)
}

fn genuine_projection_allowing_residuals(
    profile: TrustedSleighProfile,
    instructions: &[u8],
) -> (SsaArtifact, MachineProjection, r2il::ArchSpec) {
    assert!(!instructions.is_empty() && instructions.len() <= 16);
    let disassembler =
        Disassembler::from_trusted_profile(profile).expect("trusted embedded profile");
    let mut bytes = [0_u8; 16];
    bytes[..instructions.len()].copy_from_slice(instructions);
    let lifted = disassembler
        .lift_genuine_block(&bytes, 0x1000, instructions.len())
        .expect("complete genuine instruction lift");
    let arch = lifted.authority().arch_spec().clone();
    let blocks = [lifted.block().clone()];
    let artifact = SsaArtifact::for_decompile(&blocks, Some(&arch))
        .expect("decompiler-optimized SSA artifact");
    let projection = MachineProjection::from_artifact(&artifact).expect("typed machine projection");
    (artifact, projection, arch)
}

fn exact_single_write_between_storages(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    source: CanonicalStorageId,
    destination: CanonicalStorageId,
) -> MachineWriteProjection {
    let writes = artifact
        .graph()
        .insts
        .iter()
        .filter(|inst| {
            inst.output
                .and_then(|output| artifact.graph().value(output))
                .and_then(|value| value.canonical_storage)
                == Some(destination)
                && inst.inputs.iter().any(|input| {
                    artifact
                        .graph()
                        .value(*input)
                        .and_then(|value| value.canonical_storage)
                        == Some(source)
                })
        })
        .collect::<Vec<_>>();
    assert_eq!(
        writes.len(),
        1,
        "source-to-destination storage write must have exactly one surviving definition, got {:?}",
        writes
            .iter()
            .map(|write| (write, projection.write_disposition(write.id)))
            .collect::<Vec<_>>()
    );
    match projection
        .write_disposition(writes[0].id)
        .copied()
        .expect("dense storage write disposition")
    {
        MachineWriteDisposition::Exact(write) => write,
        MachineWriteDisposition::Refused(reason) => {
            panic!("storage write must be exact, got {reason:?}")
        }
    }
}

fn exact_uses_from_storage(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    storage: CanonicalStorageId,
) -> Vec<MachineUseSlice> {
    let uses = artifact
        .graph()
        .insts
        .iter()
        .flat_map(|inst| {
            inst.inputs
                .iter()
                .enumerate()
                .filter_map(move |(input_idx, input)| {
                    (artifact
                        .graph()
                        .value(*input)
                        .and_then(|value| value.canonical_storage)
                        == Some(storage))
                    .then_some(UseSite {
                        inst: inst.id,
                        input_idx,
                    })
                })
        })
        .collect::<Vec<_>>();
    assert!(!uses.is_empty(), "storage must have a surviving use");
    uses.into_iter()
        .map(|site| {
            match projection
                .use_disposition(site)
                .copied()
                .expect("dense storage use disposition")
            {
                MachineUseDisposition::Exact(slice) => slice,
                MachineUseDisposition::MemoryAddress(address) => {
                    panic!("expected bit slice, got contextual address {address:?}")
                }
                MachineUseDisposition::Refused(reason) => {
                    panic!("storage use must be exact, got {reason:?}")
                }
            }
        })
        .collect()
}

#[test]
fn genuine_x86_eax_write_survives_as_one_carrier_zero_extension() {
    let (artifact, projection, arch) = genuine_optimized_projection(
        TrustedSleighProfile::X86_64,
        &[0x89, 0xd8], // mov eax, ebx
    );
    let rax = declared_register_storage(&arch, "RAX");
    let ebx = declared_register_storage(&arch, "EBX");

    assert_eq!(
        exact_single_write_between_storages(&artifact, &projection, ebx, rax),
        MachineWriteProjection::ZeroExtend {
            from_width_bits: 32,
            to_width_bits: 64,
        }
    );
}

#[test]
fn genuine_aarch64_w0_write_survives_as_one_carrier_zero_extension() {
    let (artifact, projection, arch) = genuine_optimized_projection(
        TrustedSleighProfile::Aarch64Le,
        &[0xe0, 0x03, 0x01, 0x2a], // mov w0, w1
    );
    let x0 = declared_register_storage(&arch, "x0");
    let w1 = declared_register_storage(&arch, "w1");

    assert_eq!(
        exact_single_write_between_storages(&artifact, &projection, w1, x0),
        MachineWriteProjection::ZeroExtend {
            from_width_bits: 32,
            to_width_bits: 64,
        }
    );
}

#[test]
fn genuine_x86_ah_write_survives_as_one_high_slice_insert() {
    let (artifact, projection, arch) = genuine_optimized_projection(
        TrustedSleighProfile::X86_64,
        &[0x88, 0xdc], // mov ah, bl
    );
    let ah = declared_register_storage(&arch, "AH");
    let bl = declared_register_storage(&arch, "BL");

    assert_eq!(
        exact_single_write_between_storages(&artifact, &projection, bl, ah),
        MachineWriteProjection::Insert {
            bit_offset: 8,
            width_bits: 8,
            carrier_width_bits: 64,
        }
    );
}

#[test]
fn genuine_x86_ah_read_is_relative_to_rax() {
    let (artifact, projection, arch) = genuine_optimized_projection(
        TrustedSleighProfile::X86_64,
        &[0x88, 0xe3], // mov bl, ah
    );
    let ah = declared_register_storage(&arch, "AH");

    let slices = exact_uses_from_storage(&artifact, &projection, ah);
    assert_eq!(slices.len(), 1);
    assert!(slices.iter().all(|slice| {
        slice.bit_offset() == 8
            && slice.width_bits() == 8
            && slice.carrier_width_bits() == 64
            && slice.conversion().is_none()
    }));
}

#[test]
fn genuine_x86_ah_zero_extend_preserves_rax_relative_source_slice() {
    let (artifact, projection, arch) = genuine_optimized_projection(
        TrustedSleighProfile::X86_64,
        &[0x0f, 0xb6, 0xc4], // movzx eax, ah
    );
    let ah = declared_register_storage(&arch, "AH");

    let slices = exact_uses_from_storage(&artifact, &projection, ah);
    assert_eq!(slices.len(), 1);
    let slice = slices[0];
    assert_eq!(slice.bit_offset(), 8);
    assert_eq!(slice.width_bits(), 8);
    assert_eq!(slice.carrier_width_bits(), 64);
    let conversion = slice
        .conversion()
        .expect("movzx use must retain conversion");
    assert_eq!(conversion.kind(), r2ssa::MachineCastKind::ZeroExtend);
    assert_eq!(conversion.to_width_bits(), 32);
}

#[test]
fn genuine_x86_eax_read_is_relative_to_rax() {
    let (artifact, projection, arch) = genuine_optimized_projection(
        TrustedSleighProfile::X86_64,
        &[0x89, 0xc3], // mov ebx, eax
    );
    let eax = declared_register_storage(&arch, "EAX");

    let slices = exact_uses_from_storage(&artifact, &projection, eax);
    assert!(slices.iter().all(|slice| {
        slice.bit_offset() == 0 && slice.width_bits() == 32 && slice.carrier_width_bits() == 64
    }));
}

#[test]
fn genuine_x86_xmm_subpieces_retain_the_source_owned_512_bit_carrier() {
    let disassembler = Disassembler::from_trusted_profile(TrustedSleighProfile::X86_64)
        .expect("trusted embedded profile");
    let lifted = disassembler
        .lift_genuine_block(&[0x90], 0x1000, 1)
        .expect("genuine x86 authority");
    let arch = lifted.authority().arch_spec().clone();
    let xmm2 = declared_register_storage(&arch, "XMM2");
    let blocks = [r2il::R2ILBlock {
        addr: 0x1000,
        size: 1,
        ops: vec![r2il::R2ILOp::Subpiece {
            dst: r2il::Varnode::unique(0x10, 4),
            src: r2il::Varnode::register(xmm2.offset, xmm2.size),
            offset: 4,
        }],
        switch_info: None,
        op_metadata: Default::default(),
    }];
    let artifact = SsaArtifact::raw(&blocks, Some(&arch)).expect("x86 vector subpiece SSA");
    let projection = MachineProjection::from_artifact(&artifact).expect("machine projection");

    let slices = exact_uses_from_storage(&artifact, &projection, xmm2);
    assert!(slices.iter().any(|slice| {
        slice.width_bits() == 32
            && slice.carrier_width_bits() == 512
            && slice.conversion().is_none()
    }));
}

fn assert_aarch64_opaque_vector_userop_feeds_exact_wide_uses(
    instructions: &[u8],
    expected_userop: u32,
) {
    let (artifact, projection, _) =
        genuine_projection_allowing_residuals(TrustedSleighProfile::Aarch64Le, instructions);
    let graph = artifact.graph();
    let callother = graph
        .insts
        .iter()
        .find(|inst| {
            matches!(
                &inst.payload,
                r2ssa::InstPayload::Op(r2ssa::SSAOp::CallOther { userop, .. })
                    if *userop == expected_userop
            )
        })
        .unwrap_or_else(|| panic!("genuine lift is missing CallOther({expected_userop})"));
    let output = callother.output.expect("vector userop result");
    assert!(matches!(
        projection
            .failure_for_output(output)
            .map(r2ssa::MachineProjectionFailure::error),
        Some(r2ssa::MachineBuildError::UnsupportedOperation { inst, op })
            if *inst == callother.id
                && matches!(&**op, r2ssa::SSAOp::CallOther { userop, .. }
                    if *userop == expected_userop)
    ));
    let uses = graph
        .uses_of
        .get(output.0 as usize)
        .expect("dense uses for userop output");
    assert!(
        !uses.is_empty(),
        "test block must consume the userop result"
    );
    assert!(uses.iter().all(|site| {
        matches!(
            projection.use_disposition(*site),
            Some(MachineUseDisposition::Exact(slice))
                if slice.carrier_width_bits() == 256 && slice.conversion().is_none()
        )
    }));
}

/// `NEON_ext` is no longer opaque: the lift gives it its semantics.
///
/// `EXT` takes the vector's width of bytes from the concatenation of its second
/// operand above its first, starting at a byte index, which is exactly a shift
/// down, a shift up and an or. Expanding it there is what lets the projection
/// and everything after it stay free of vector-specific machinery -- and what
/// lets `crc32_bitwise` at arm64 -O2 render at all, since a `CallOther` carries
/// no semantics and refuses the whole function.
#[test]
fn genuine_aarch64_neon_ext_is_expanded_into_exact_operations() {
    let (artifact, projection, _) = genuine_projection_allowing_residuals(
        TrustedSleighProfile::Aarch64Le,
        &[
            0x43, 0x40, 0x02, 0x6e, // ext v3.16b, v2.16b, v2.16b, 8
            0x42, 0x1c, 0x23, 0x2e, // eor v2.8b, v2.8b, v3.8b
        ],
    );
    let graph = artifact.graph();
    assert!(
        !graph.insts.iter().any(|inst| matches!(
            &inst.payload,
            r2ssa::InstPayload::Op(r2ssa::SSAOp::CallOther { userop, .. }) if *userop == 150
        )),
        "the lift must give NEON_ext its semantics rather than leave it opaque"
    );
    // The expansion is a 64-bit rotate for this index, so both shifts are there
    // and neither is refused by the projection.
    for (shifted, amount) in [(false, 64_u64), (true, 64)] {
        let inst = graph
            .insts
            .iter()
            .find(|inst| match &inst.payload {
                r2ssa::InstPayload::Op(r2ssa::SSAOp::IntLeft { .. }) if shifted => true,
                r2ssa::InstPayload::Op(r2ssa::SSAOp::IntRight { .. }) if !shifted => true,
                _ => false,
            })
            .unwrap_or_else(|| panic!("the expansion must shift by {amount}"));
        assert!(
            projection
                .failure_for_output(inst.output.expect("shift result"))
                .is_none(),
            "an expanded operation must project exactly"
        );
    }
}

#[test]
fn genuine_aarch64_neon_ushl_is_opaque_but_its_result_uses_keep_exact_geometry() {
    assert_aarch64_opaque_vector_userop_feeds_exact_wide_uses(
        &[
            0x01, 0x44, 0xa1, 0x6e, // ushl v1.4s, v0.4s, v1.4s
            0x00, 0x1c, 0xa1, 0x4e, // orr v0.16b, v0.16b, v1.16b
        ],
        294,
    );
}
