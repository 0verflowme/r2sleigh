//! Genuine embedded lifts through optimized SSA and typed machine projection.

use r2sleigh_lift::{Disassembler, TrustedSleighProfile};
use r2ssa::{
    CanonicalStorageId, CanonicalStorageSpace, FunctionPrepareMode, MachineProjection,
    MachineWriteDisposition, MachineWriteProjection, SsaArtifact,
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
        }
    );
}
