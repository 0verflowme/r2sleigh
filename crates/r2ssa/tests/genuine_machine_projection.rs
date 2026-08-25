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

fn exact_single_write_to_storage(
    artifact: &SsaArtifact,
    projection: &MachineProjection,
    storage: CanonicalStorageId,
) -> MachineWriteProjection {
    let writes = artifact
        .graph()
        .insts
        .iter()
        .filter(|inst| {
            inst.output
                .and_then(|output| artifact.graph().value(output))
                .and_then(|value| value.canonical_storage)
                == Some(storage)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        writes.len(),
        1,
        "storage must have exactly one surviving definition, got {writes:?}"
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

    assert_eq!(
        exact_single_write_to_storage(&artifact, &projection, rax),
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

    assert_eq!(
        exact_single_write_to_storage(&artifact, &projection, x0),
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

    assert_eq!(
        exact_single_write_to_storage(&artifact, &projection, ah),
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
