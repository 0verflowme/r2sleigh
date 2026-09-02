//! A prepared SSA artifact built from a list of R2IL operations, the way the
//! decompiler's own tests build one, so import and canonicalisation can be
//! exercised without radare2.

#![allow(dead_code)]

use r2il::{
    ArchSpec, R2ILBlock, R2ILOp, RegisterBitSlice, RegisterDef, RegisterProjection,
    RegisterProjectionDisposition, RegisterStorage, Varnode,
};
use r2ssa::{MachineProjection, SsaArtifact, ValueId};

pub const RAX: u64 = 0x00;
pub const RDI: u64 = 0x10;
pub const RSI: u64 = 0x18;
pub const RBP: u64 = 0x20;
pub const RSP: u64 = 0x28;
pub const RIP: u64 = 0x30;

pub fn arch() -> ArchSpec {
    let mut arch = ArchSpec::new("x86-64");
    let registers = [
        ("RAX", RAX),
        ("RDI", RDI),
        ("RSI", RSI),
        ("RBP", RBP),
        ("RSP", RSP),
        ("RIP", RIP),
    ];
    for (name, offset) in registers {
        let storage = RegisterStorage { offset, size: 8 };
        arch.add_register(RegisterDef::new(name, offset, 8));
        arch.register_projections.push(RegisterProjection {
            written: storage,
            disposition: RegisterProjectionDisposition::Bound {
                carrier: storage,
                slice: RegisterBitSlice {
                    lsb_bit_offset: 0,
                    size_bits: 64,
                },
            },
        });
    }
    arch
}

pub fn reg(offset: u64, size: u32) -> Varnode {
    Varnode::register(offset, size)
}

pub fn tmp(offset: u64, size: u32) -> Varnode {
    Varnode::unique(offset, size)
}

pub fn konst(value: u64, size: u32) -> Varnode {
    Varnode::constant(value, size)
}

pub fn artifact(ops: Vec<R2ILOp>) -> SsaArtifact {
    let mut block = R2ILBlock::new(0x1000, 4);
    for op in ops {
        block.push(op);
    }
    let storage = |offset| r2ssa::CanonicalStorageId {
        space: r2ssa::CanonicalStorageSpace::Register,
        offset,
        size: 8,
    };
    let interface = r2ssa::SourceFunctionInterface::new_exact(
        b"r2rewrite-fixture".to_vec(),
        "sysv64",
        std::iter::empty::<r2ssa::SourceAbiParameterSpec>(),
        r2ssa::SourceFunctionReturn::Register {
            storage: storage(RAX),
        },
        std::iter::empty::<r2ssa::SourceStackSlotSpec>(),
    )
    .and_then(|interface| interface.with_return_address_storage(storage(RIP)))
    .and_then(|interface| interface.with_stack_pointer_storage(storage(RSP)))
    .expect("exact fixture interface");
    let arch = arch();
    SsaArtifact::for_decompile_with_interface(&[block], Some(&arch), interface)
        .expect("prepared SSA should build")
        .with_name("r2rewrite_fixture")
}

pub fn projection(artifact: &SsaArtifact) -> MachineProjection {
    MachineProjection::from_artifact(artifact).expect("machine projection")
}

/// The value id of the SSA variable spelled `name` (`RAX_1`, `tmp:100_1`).
pub fn value_named(artifact: &SsaArtifact, name: &str) -> ValueId {
    let graph = artifact.graph();
    graph
        .values
        .iter()
        .find(|value| value.var.to_string() == name)
        .map(|value| value.id)
        .unwrap_or_else(|| {
            let names: Vec<String> = graph.values.iter().map(|v| v.var.to_string()).collect();
            panic!("no value named {name}; have {names:?}")
        })
}
